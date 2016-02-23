#lang racket/base

(require racket/contract/private/arrow
         racket/contract/private/prop
         racket/contract/private/guts
         racket/contract/private/opt
         racket/contract/private/misc
         racket/contract/private/blame
         racket/contract/private/generate
         racket/contract/private/arrow-higher-order
         syntax/location
         racket/private/performance-hint
         (for-syntax racket/base
                     racket/contract
                     racket/stxparam-exptime
                     syntax/name
                     "arr-a-parse.rkt"                  
                     (rename-in
                      syntax/private/boundmap
                      ;; the private version of the library 
                      ;; (the one without contracts)
                      ;; has these old, wrong names in it.
                      [make-module-identifier-mapping make-free-identifier-mapping]
                      [module-identifier-mapping-get free-identifier-mapping-get]
                      [module-identifier-mapping-put! free-identifier-mapping-put!]
                      [module-identifier-mapping-for-each free-identifier-mapping-for-each])))

(provide (rename-out [->a/m ->a]))

(define (build-??-args ctc blame)
  (define arg-ctc-projs (map (λ (x) (contract-projection (->a-arg-contract x))) (->a-arg-ctcs ctc)))
  (define indy-arg-ctc-projs (map (λ (x) (contract-projection (cdr x)))
                                  (->a-indy-arg-ctcs ctc)))
  (define rng-ctc-projs (map (λ (x) (contract-projection (cdr x))) (->a-rng-ctcs ctc)))
  (define indy-rng-ctc-projs (map (λ (x) (contract-projection (cdr x))) 
                                  (->a-indy-rng-ctcs ctc)))
  (define has-rest (->a-rest ctc))
  (define here (->a-here ctc))
  
  (define blames (for/list ([blame-info (->a-blame-info ctc)])
                           (define name (vector-ref blame-info 0))
                           (define indy? (vector-ref blame-info 1))
                           (define dom? (vector-ref blame-info 2))
                           (define non-indy-blame
                             (blame-add-context
                              blame 
                              (format (if dom? "the ~a argument of" "the ~a result of")
                                      name)
                              #:swap? dom?))
                           (if indy?
                               (blame-replace-negative non-indy-blame here)
                               non-indy-blame)))
  (define swapped-blame (blame-swap blame))
  (define indy-dom-blame (blame-replace-negative swapped-blame here))
  (define indy-rng-blame (blame-replace-negative blame here))
  
  (define partial-doms 
    (for/list ([dom-proj (in-list arg-ctc-projs)]
               [pr (in-list (->a-arg-ctcs ctc))])
              (dom-proj (blame-add-context swapped-blame 
                                           (format "the ~a argument of" (->a-arg-name pr))))))
  (define partial-indy-doms
    (for/list ([dom-proj (in-list indy-arg-ctc-projs)]
               [dom-pr (in-list (->a-indy-arg-ctcs ctc))])
              (dom-proj (blame-add-context indy-dom-blame 
                                           (format "the ~a argument of" (car dom-pr))))))
  
  (define partial-rngs 
    (for/list ([rng-proj (in-list rng-ctc-projs)]
               [pr (in-list (->a-rng-ctcs ctc))]
               [n (in-naturals 1)])
              (define name (car pr))
              (rng-proj (blame-add-context blame 
                                           (if (eq? '_ name)
                                               (if (null? (cdr rng-ctc-projs))
                                                   "the result of"
                                                   (format "the ~a result of" (n->th n)))
                                               (format "the ~a result of" name))))))
  (define partial-indy-rngs 
    (for/list ([rng-proj (in-list indy-rng-ctc-projs)]
               [rng-pr (in-list (->a-indy-rng-ctcs ctc))])
              (rng-proj (blame-add-context indy-rng-blame (format "the ~a result of" 
                                                                  (car rng-pr))))))
  (list* (λ (val mtd?)
           (if has-rest
               (check-procedure/more val mtd?
                                     (->a-mandatory-args ctc) 
                                     (->a-mandatory-kwds ctc)
                                     (->a-opt-kwds ctc)
                                     blame)
               (check-procedure val mtd?
                                (->a-mandatory-args ctc) (->a-opt-args ctc)
                                (->a-mandatory-kwds ctc) (->a-opt-kwds ctc)
                                blame)))
         ctc
         blame swapped-blame ;; used by the #:pre and #:post checking
         (append blames
                 (->a-pre/post-procs ctc)
                 (->a-auth-proc ctc)
                 partial-doms
                 (->a-arg-dep-ctcs ctc)
                 partial-indy-doms
                 partial-rngs
                 (->a-rng-dep-ctcs ctc)
                 partial-indy-rngs)))

(define arr->a-proj
  (λ (ctc)
    (define func (->a-mk-wrapper ctc))
    (λ (blame)
      (define ???-args (build-??-args ctc blame))
      (apply func ???-args))))


(define (exercise->a ctc)
  (define arg-deps (->a-arg-dep-ctcs ctc))
  (cond
    [(and (null? arg-deps) (not (->a-rest ctc)))
     (λ (fuel)
       (define gens (for/list ([arg-ctc (in-list (->a-arg-ctcs ctc))]
                               #:when (and (not (->a-arg-optional? arg-ctc))
                                           (not (->a-arg-kwd arg-ctc))))
                              (contract-random-generate/choose (->a-arg-contract arg-ctc) fuel)))
       (define kwd-gens (for/list ([arg-ctc (in-list (->a-arg-ctcs ctc))]
                                   #:when (and (not (->a-arg-optional? arg-ctc))
                                               (->a-arg-kwd arg-ctc)))
                                  (contract-random-generate/choose (->a-arg-contract arg-ctc) fuel)))
       (define dom-kwds (for/list ([arg-ctc (in-list (->a-arg-ctcs ctc))]
                                   #:when (and (not (->a-arg-optional? arg-ctc))
                                               (->a-arg-kwd arg-ctc)))
                                  (->a-arg-kwd arg-ctc)))
       (cond
         [(andmap values gens)
          (define env (contract-random-generate-get-current-environment))
          (values (λ (f)
                    (call-with-values
                     (λ ()
                       (define kwd-args 
                         (for/list ([kwd-gen (in-list kwd-gens)])
                                   (kwd-gen)))
                       (define regular-args 
                         (for/list ([gen (in-list gens)])
                                   (gen)))
                       (keyword-apply 
                        f
                        dom-kwds
                        kwd-args
                        regular-args))
                     (λ results
                       (void)
                       ;; what to do here? (nothing, for now)
                       ;; better: if we did actually stash the results we knew about.
                       '(for ([res-ctc (in-list rng-ctcs)]
                              [result (in-list results)])
                             (contract-random-generate-stash env res-ctc result)))))
                  ;; better here: if we promised the results we knew we could deliver
                  '())]
         [else
          (values void '())]))]
    [else
     (λ (fuel) (values void '()))]))

;; name : symbol?
;; kwd : (or/c #f keyword?)
;; optional? : boolean?
;; contract : contract?
(struct ->a-arg (name kwd optional? contract) #:transparent)

;; blame-info    : (listof (vector symbol boolean?[indy?] boolean?[swap?]))
;; arg-ctcs      : (listof ->a-arg?)
;; arg-dep-ctcs  : (-> ??? (listof contract))
;; indy-arg-ctcs : (listof (cons symbol? contract))
;; rng-ctcs      : (listof (cons symbol? contract))
;; rng-dep-ctcs  : (-> ??? (listof contract))
;; indy-rng-ctcs : (listof (cons symbol? contract))
;; mandatory-args, opt-args : number
;; mandatory-kwds, opt-kwds : (listof keyword?) sorted by keyword<?
;; rest : (or/c symbol? #f)
;; here : quoted-spec for use in assigning indy blame
;; mk-wrapper : creates the a wrapper function that implements the contract checking
(struct ->a (blame-info 
             arg-ctcs arg-dep-ctcs indy-arg-ctcs
             rng-ctcs rng-dep-ctcs indy-rng-ctcs
             pre/post-procs auth-proc
             mandatory-args opt-args mandatory-kwds opt-kwds rest
             mtd? here mk-wrapper mk-val-first-wrapper name-info)
  #:property prop:custom-write custom-write-property-proc
  #:property prop:contract
  (build-contract-property
   #:val-first-projection
   (λ (ctc)
     (define blame-accepting-proj (arr->a-proj ctc))
     (λ (blame)
       (λ (val)
         (wrapped-extra-arg-arrow
          (λ (neg-party)
            ((blame-accepting-proj (blame-add-missing-party blame neg-party)) val))
          (->a-mk-val-first-wrapper ctc)))))
   #:late-neg-projection
   (λ (ctc)
     (define blame-accepting-proj (arr->a-proj ctc))
     (λ (blame)
       (λ (val neg-party)
         ((blame-accepting-proj (blame-add-missing-party blame neg-party)) val))))
   #:projection arr->a-proj
   #:name (λ (ctc) 
            (define (arg/ress->spec infos ctcs dep-ctcs skip?)
              (let loop ([infos infos]
                         [ctcs ctcs]
                         [dep-ctcs dep-ctcs])
                (cond
                  [(null? infos) '()]
                  [else 
                   (let* ([info (car infos)]
                          [dep/nodep (list-ref info 0)]
                          [var (list-ref info 1)]
                          [vars (list-ref info 2)]
                          [kwd (list-ref info 3)])
                     (case dep/nodep
                       [(nodep)
                        (if (skip? info)
                            (loop (cdr infos) (cdr ctcs) dep-ctcs)
                            `(,@(if kwd
                                    (list kwd)
                                    (list))
                              [,var ,(contract-name (car ctcs))]
                              .
                              ,(loop (cdr infos) (cdr ctcs) dep-ctcs)))]
                       [(dep)
                        (define body-src (list-ref info 5))
                        (if (skip? info)
                            (loop (cdr infos) ctcs (cdr dep-ctcs))
                            `(,@(if kwd
                                    (list kwd)
                                    (list))
                              [,var ,vars ,body-src]
                              .
                              ,(loop (cdr infos) ctcs (cdr dep-ctcs))))]))])))
            (let* ([name-info (->a-name-info ctc)]
                   [args-info (vector-ref name-info 0)]
                   [rest-info (vector-ref name-info 1)]
                   [pre-infos  (vector-ref name-info 2)]
                   [auth-infos (vector-ref name-info 3)]
                   [rng-info  (vector-ref name-info 4)]
                   [post-infos (vector-ref name-info 5)])
              `(->a ,(arg/ress->spec args-info
                                     (map ->a-arg-contract (->a-arg-ctcs ctc))
                                     (->a-arg-dep-ctcs ctc)
                                     (λ (x) (list-ref x 4)))
                    ,@(let ([rests (arg/ress->spec args-info
                                                   (map ->a-arg-contract (->a-arg-ctcs ctc))
                                                   (->a-arg-dep-ctcs ctc)
                                                   (λ (x) (not (list-ref x 4))))])
                        (if (null? rests)
                            '()
                            (list rests)))
                    ,@(if rest-info
                          (case (car rest-info)
                            [(nodep) `(#:rest 
                                       [,(list-ref rest-info 1)
                                        ,(contract-name
                                          (car 
                                           (reverse
                                            (map ->a-arg-contract (->a-arg-ctcs ctc)))))])]
                            [(dep) `(#:rest [,(list-ref rest-info 1)
                                             ,(list-ref rest-info 2)
                                             ,(list-ref rest-info 3)])])
                          '())
                    ,@(apply
                       append
                       (for/list ([pre-info pre-infos])
                                 (define ids (list-ref pre-info 0))
                                 (define name (list-ref pre-info 1))
                                 (define code (list-ref pre-info 2))
                                 (cond
                                   [(string? name)
                                    `(#:pre/name ,ids ,name ,code)]
                                   [(equal? name 'bool)
                                    `(#:pre ,ids ,code)]
                                   [(equal? name 'desc)
                                    `(#:pre/desc ,ids ,code)])))
                    ,@(apply
                       append
                       (for/list ([auth-info auth-infos])
                                 (define ids (list-ref auth-info 0))
                                 (define code (list-ref auth-info 1))
                                 `(#:auth ,ids ,code)))

                    
                    ,(cond
                       [(not rng-info)
                        'any]
                       [else
                        (let ([infos (arg/ress->spec rng-info
                                                     (map cdr (->a-rng-ctcs ctc))
                                                     (->a-rng-dep-ctcs ctc)
                                                     (λ (x) #f))])
                          (cond
                            [(or (null? infos) (not (null? (cdr infos))))
                             `(values ,@infos)]
                            [else
                             (car infos)]))])
                    
                    ,@(apply
                       append
                       (for/list ([post-info post-infos])
                                 (define ids (list-ref post-info 0))
                                 (define name (list-ref post-info 1))
                                 (define code (list-ref post-info 2))
                                 (cond
                                   [(string? name)
                                    `(#:post/name ,ids ,name ,code)]
                                   [(equal? name 'bool)
                                    `(#:post ,ids ,code)]
                                   [(equal? name 'desc)
                                    `(#:post/desc ,ids ,code)]))))))
   #:first-order
   (λ (ctc)
     (let ([has-rest (->a-rest ctc)]
           [mtd? (->a-mtd? ctc)]
           [mand-args (->a-mandatory-args ctc)]
           [opt-args (->a-opt-args ctc)]
           [mand-kwds (->a-mandatory-kwds ctc)]
           [opt-kwds (->a-opt-kwds ctc)])
       (λ (val)
         (if has-rest
             (check-procedure/more val mtd? mand-args mand-kwds opt-kwds #f)
             (check-procedure val mtd? mand-args opt-args mand-kwds opt-kwds #f)))))
   #:exercise exercise->a
   #:stronger (λ (this that) (eq? this that)))) ;; WRONG

;; find-ordering : (listof arg) -> (values (listof arg) (listof number)) 
;; sorts the arguments according to the dependency order.
;; returns them in the reverse of that order, ie expressions that need
;; to be evaluted first come later in the list.
(define-for-syntax (find-ordering args)
  
  #|
This uses a variation of the topological sorting algorithm
from Wikipedia attributed to Kahn (1962). It doesn't run in
linear time since it uses a linear scan at each step to find
the 'least' argument contract to pick. (Picking the least arg
ensures that args that are independent of each other are still
evaluted left-to-right.)
  |#
  
  (define numbers (make-hasheq)) ;; this uses eq?, but it could use a number in the 'arg' struct
  (define id->arg/res (make-free-identifier-mapping))
  (for ([arg (in-list args)]
        [i (in-naturals)])
       (hash-set! numbers arg i)
       (free-identifier-mapping-put! id->arg/res (arg/res-var arg) arg))
  
  (define comes-before (make-free-identifier-mapping))
  (define comes-after (make-free-identifier-mapping))
  (for ([arg (in-list args)])
       (free-identifier-mapping-put! comes-before (arg/res-var arg) '())
       (free-identifier-mapping-put! comes-after (arg/res-var arg) '()))
  (for ([arg (in-list args)])
       (when (arg/res-vars arg)
         (define arg-id (arg/res-var arg))
         (for ([dep-id (in-list (arg/res-vars arg))])
              (define dep (free-identifier-mapping-get id->arg/res dep-id (λ () #f)))
              (when dep
                ;; dep = #f should happen only when we're handling the result
                ;; contracts and dep-id is one of the argument contracts.
                ;; in that case, we can just ignore the edge since we know
                ;; it will be bound already
                (free-identifier-mapping-put!
                 comes-before
                 arg-id
                 (cons dep (free-identifier-mapping-get comes-before arg-id)))
                (free-identifier-mapping-put!
                 comes-after
                 dep-id
                 (cons arg (free-identifier-mapping-get comes-after dep-id)))))))
  
  (define sorted '())
  (define no-incoming-edges
    (for/list ([arg (in-list args)]
               #:when (null? (free-identifier-mapping-get comes-before (arg/res-var arg))))
              arg))
  
  (define (pick-next-node)
    (define least-node
      (let loop ([nodes (cdr no-incoming-edges)]
                 [least-node (car no-incoming-edges)])
        (cond
          [(null? nodes) least-node]
          [else
           (define node (car nodes))
           (cond
             [(< (hash-ref numbers node) (hash-ref numbers least-node))
              (loop (cdr nodes) node)]
             [else
              (loop (cdr nodes) least-node)])])))
    (set! no-incoming-edges (remove least-node no-incoming-edges))
    least-node)
  
  (define (remove-edge from to)
    (free-identifier-mapping-put!
     comes-before
     (arg/res-var to)
     (remove from (free-identifier-mapping-get comes-before (arg/res-var to))))
    (free-identifier-mapping-put!
     comes-after
     (arg/res-var from)
     (remove to (free-identifier-mapping-get comes-after (arg/res-var from)))))
  
  (let loop ()
    (unless (null? no-incoming-edges)
      (define n (pick-next-node))
      (set! sorted (cons n sorted))
      (for ([m (in-list (free-identifier-mapping-get comes-after (arg/res-var n)))])
           (remove-edge n m)
           (when (null? (free-identifier-mapping-get comes-before (arg/res-var m)))
             (set! no-incoming-edges (cons m no-incoming-edges))))
      (loop)))
  
  (values sorted
          (for/list ([arg (in-list sorted)])
                    (hash-ref numbers arg))))

;; args/vars->arglist : (listof arg?) (vectorof identifier?) -> syntax
;; (vector-length vars) = (length args)
;; builds the parameter list for the wrapper λ
(define-for-syntax (args/vars->arglist an-astx vars this-param)
  (let ([args (astx-args an-astx)])
    #`(#,@(if this-param
              (list this-param)
              '())
       .
       #, 
       (let loop ([args args]
                  [i 0])
         (cond
           [(null? args) (if (astx-rst an-astx)
                             #'rest-args
                             #'())]
           [else
            (let* ([arg (car args)]
                   [kwd (arg-kwd arg)]
                   [opt? (arg-optional? arg)]
                   [arg-exp
                    (cond
                      [(and kwd opt?)
                       #`(#,kwd [#,(vector-ref vars i) the-unsupplied-arg])]
                      [kwd
                       #`(#,kwd #,(vector-ref vars i))]
                      [opt?
                       #`([#,(vector-ref vars i) the-unsupplied-arg])]
                      [else
                       #`(#,(vector-ref vars i))])])
              
              #`(#,@arg-exp
                 .
                 #,(loop (cdr args) (+ i 1))))])))))

(define-for-syntax (all-but-last lst)
  (reverse (cdr (reverse lst))))

;; vars : (listof identifier)
;;    vars will contain one identifier for each arg, plus one more for rst,
;;    unless rst is #f, in which case it just contains one identifier for each arg.
;;
;; FIXME: Currently, none of the resulting argument checkers attempt to preserve tail
;; recursion.  If all of the result contracts (which would need to be passed to
;; this function as well as results-checkers) can be evaluated early, then we can
;; preserve tail recursion in the fashion of -> etc.
(define-for-syntax (args/vars->arg-checker result-checkers args rst vars this-param)
  (let ([opts? (ormap arg-optional? args)]
        [this-params (if this-param (list this-param) '())])
    (cond
      [(and opts? (ormap arg-kwd args))
       (let* ([arg->var (make-hash)]
              [kwd-args (filter arg-kwd args)]
              [non-kwd-args (filter (λ (x) (not (arg-kwd x))) args)])
         
         (for ([arg (in-list args)]
               [var (in-vector vars)])
              (hash-set! arg->var arg var))
         
         (let ([sorted-kwd/arg-pairs 
                (sort
                 (map (λ (arg) (cons (arg-kwd arg) (hash-ref arg->var arg))) kwd-args)
                 (λ (x y) (keyword<? (syntax-e (car x)) (syntax-e (car y)))))])
           
           ;; has both optional and keyword args
           #`(keyword-return/no-unsupplied 
              #,(if (null? result-checkers) #f (car result-checkers)) 
              '#,(map car sorted-kwd/arg-pairs)
              (list #,@(map cdr sorted-kwd/arg-pairs))
              #,(if rst
                    #'rest-args
                    #''())
              #,@this-params
              #,@(map (λ (arg) (hash-ref arg->var arg)) non-kwd-args))))]
      [opts?
       ;; has optional args, but no keyword args
       #`(return/no-unsupplied #,(if (null? result-checkers) #f (car result-checkers))
                               #,(if rst
                                     #'rest-args
                                     #''())
                               #,@this-params
                               #,@(if rst
                                      (all-but-last (vector->list vars))
                                      (vector->list vars)))] 
      [else
       (let*-values ([(rev-regs rev-kwds)
                      (for/fold ([regs null]
                                 [kwds null])
                                ([arg (in-list args)]
                                 [i (in-naturals)])
                        (if (arg-kwd arg)
                            (values regs (cons (vector-ref vars i) kwds))
                            (values (cons (vector-ref vars i) regs) kwds)))]
                     [(regular-arguments keyword-arguments)
                      (values (reverse rev-regs) (reverse rev-kwds))])
         (cond
           [(and (null? keyword-arguments) rst)
            #`(apply values #,@result-checkers #,@this-params #,@regular-arguments rest-args)]
           [(null? keyword-arguments)
            #`(values #,@result-checkers #,@this-params #,@regular-arguments)]
           [rst
            #`(apply values #,@result-checkers (list #,@keyword-arguments) 
                     #,@this-params #,@regular-arguments rest-args)]
           [else
            #`(values #,@result-checkers (list #,@keyword-arguments) 
                      #,@this-params #,@regular-arguments)]))])))

(define (return/no-unsupplied res-checker rest-args . args)
  (if res-checker
      (apply values res-checker 
             (append (filter (λ (x) (not (eq? x the-unsupplied-arg))) args) rest-args))
      (apply values (append (filter (λ (x) (not (eq? x the-unsupplied-arg))) args) rest-args))))

(define (keyword-return/no-unsupplied res-checker kwds kwd-args rest-args . args)
  (let-values ([(supplied-kwds supplied-kwd-args)
                (let loop ([kwds kwds]
                           [kwd-args kwd-args])
                  (cond
                    [(null? kwds) (values '() '())]
                    [else 
                     (let-values ([(kwds-rec args-rec) (loop (cdr kwds) (cdr kwd-args))])
                       (cond
                         [(eq? (car kwd-args) the-unsupplied-arg)
                          (values kwds-rec args-rec)]
                         [else
                          (values (cons (car kwds) kwds-rec)
                                  (cons (car kwd-args) args-rec))]))]))])
    (cond
      [(and res-checker (null? supplied-kwd-args))
       (apply values res-checker
              (append (filter (λ (x) (not (eq? x the-unsupplied-arg))) args) rest-args))]
      [(null? supplied-kwd-args)
       (apply values (append (filter (λ (x) (not (eq? x the-unsupplied-arg))) args) rest-args))]
      [res-checker
       (apply values res-checker supplied-kwd-args 
              (append (filter (λ (x) (not (eq? x the-unsupplied-arg))) args) rest-args))]
      [else
       (apply values supplied-kwd-args 
              (append (filter (λ (x) (not (eq? x the-unsupplied-arg))) args) rest-args))])))

(define-for-syntax (maybe-generate-temporary x)
  (and x (car (generate-temporaries (list x)))))

(define (signal-pre/post pre? val kind blame condition-result . var-infos)
  (define vars-str
    (apply
     string-append
     (for/list ([var-info (in-list var-infos)])
               (format "\n      ~s: ~e" 
                       (list-ref var-info 0)
                       (list-ref var-info 1)))))
  (define msg
    (cond
      [(string? kind) (string-append kind vars-str)]
      [(or (equal? kind 'bool)
           (and (equal? kind 'desc)
                (equal? condition-result #f)))
       (string-append 
        (if pre? "#:pre" "#:post")
        " condition violation"
        (if (null? var-infos)
            ""
            "; variables are:")
        vars-str)]
      [else
       (pre-post/desc-result->string condition-result pre? '->a)]))
  (raise-blame-error blame val "~a" msg))


(define (signal-auth val blame condition-result . var-infos)

  (define vars-str
    (apply
     string-append
     (for/list ([var-info (in-list var-infos)])
               (format "\n      ~s: ~e" 
                       (list-ref var-info 0)
                       (list-ref var-info 1)))))

  (define msg
    (string-append
     (format "expected a higher-order contract given ~e" condition-result)
     (if (null? var-infos)
         ""
         (string-append "; variables are:" vars-str))))
  
  (raise-blame-error blame val "~a" msg))

(define-for-syntax (add-pre-cond an-astx indy-arg-vars ordered-args indy-res-vars ordered-ress
                                 call-stx)
  #`(begin #,@(for/list ([pre (in-list (astx-pre an-astx))]
                         [i (in-naturals)])
                        (define id (string->symbol (format "pre-proc~a" i)))
                        #`(let ([condition-result
                                 (#,id #,@(map (λ (var) (arg/res-to-indy-var indy-arg-vars
                                                                             ordered-args
                                                                             indy-res-vars
                                                                             ordered-ress
                                                                             var))
                                               (pre/post-vars pre)))])
                            (unless #,(if (equal? (pre/post-kind pre) 'desc)
                                          #'(equal? condition-result #t)
                                          #'condition-result)
                              (signal-pre/post #t
                                               val
                                               '#,(pre/post-kind pre)
                                               swapped-blame
                                               condition-result
                                               #,@(map (λ (x) #`(list '#,x 
                                                                      #,(arg/res-to-indy-var indy-arg-vars 
                                                                                             ordered-args 
                                                                                             indy-res-vars 
                                                                                             ordered-ress 
                                                                                             x)))
                                                       (pre/post-vars pre))))))
           #,call-stx))

(define-for-syntax (add-auth an-astx indy-arg-vars ordered-args indy-res-vars ordered-ress)
  (let ([auth-proc (astx-auth an-astx)])
    (cond [(null? auth-proc)
           #'(λ (blame)
               (λ (val)
                 val))]
          [else
           (let ([auth (car (astx-auth an-astx))])
                     (define id (string->symbol "auth-proc0"))
                     #`(let ([condition-result
                              (#,id #,@(map (λ (var) (arg/res-to-indy-var indy-arg-vars
                                                                          ordered-args
                                                                          indy-res-vars
                                                                          ordered-ress
                                                                          var))
                                            (auth-vars auth)))])
                         (if (and (contract? condition-result) (not (flat-contract? condition-result)))
                               (contract-projection condition-result)
                               (signal-auth val
                                            blame
                                            condition-result
                                            #,@(map (λ (x) #`(list '#,x 
                                                                   #,(arg/res-to-indy-var indy-arg-vars 
                                                                                          ordered-args 
                                                                                          indy-res-vars 
                                                                                          ordered-ress 
                                                                                          x)))
                                                    (auth-vars auth))))))])))


(define-for-syntax (add-post-cond an-istx indy-arg-vars ordered-args indy-res-vars ordered-ress
                                  call-stx)
  #`(begin #,@(for/list ([post (in-list (astx-post an-istx))]
                         [i (in-naturals)])
                (define id (string->symbol (format "post-proc~a" i)))
                #`(let ([condition-result
                         (#,id #,@(map (λ (var) (arg/res-to-indy-var indy-arg-vars 
                                                                     ordered-args 
                                                                     indy-res-vars 
                                                                     ordered-ress 
                                                                     var))
                                       (pre/post-vars post)))])
                (unless #,(if (equal? (pre/post-kind post) 'desc)
                              #'(equal? condition-result #t)
                              #'condition-result)
                  (signal-pre/post
                   #f
                   val
                   '#,(pre/post-kind post)
                   blame
                   condition-result
                   #,@(map (λ (x) #`(list '#,x #,(arg/res-to-indy-var indy-arg-vars 
                                                                      ordered-args 
                                                                      indy-res-vars 
                                                                      ordered-ress 
                                                                      x)))
                           (pre/post-vars post))))))
           #,call-stx))

;; add-wrapper-let :
;;   syntax? -- placed into the body position of the generated let expression
;;   boolean? -- indicates if this is an arg or a res; affects only how blame-var-table is filled in
;;   (listof arg/res) -- sorted version of the arg/res structs, ordered by evaluation order
;;   (listof int) -- indices that give the mapping from the ordered-args to the original order
;;   (listof identifier) -- arg/res-proj-vars, bound to projections with ordinary blame
;;   (listof identifier) -- indy-arg/res-proj-args, bound to projections with indy blame
;;   (listof identifier) -- wrapper-arg/ress, bound to the original, unwrapped values, sorted like 
;;        original arg/ress. the generated lets rebind these variables to their projected 
;;        counterparts, with normal blame
;;   (listof identifier) -- indy-arg/res-vars, bound to wrapped values with indy blame, 
;;        sorted like the second input
;;   (listof identifier) (listof arg/var) (listof identifier) (listof arg/var)
;;        the last four inputs are used only to call arg/res-to-indy-var. 
;; adds nested lets that bind the wrapper-args and the indy-arg/res-vars to projected values, 
;; with 'body' in the body of the let also handles adding code to check to see if unsupplied
;; args are present (skipping the contract check, if so) 
(define-for-syntax (add-wrapper-let body swapped-blame? neg-calls?
                                    ordered-arg/reses indicies
                                    arg/res-proj-vars indy-arg/res-proj-vars 
                                    wrapper-arg/ress indy-arg/res-vars
                                    indy-arg-vars ordered-args indy-res-vars ordered-ress)
  
  (define (add-unsupplied-check an-arg/res wrapper-arg stx)
    (if (and (arg? an-arg/res)
             (arg-optional? an-arg/res))
        #`(if (eq? #,wrapper-arg the-unsupplied-arg)
              #,wrapper-arg
              #,stx)
        stx))
  
  (for/fold ([body body])
            ([indy-arg/res-var (in-list indy-arg/res-vars)]
             [an-arg/res (in-list ordered-arg/reses)]
             [index indicies]
             [i (in-naturals)])
    (let ([wrapper-arg (vector-ref wrapper-arg/ress index)]
          [arg/res-proj-var (vector-ref arg/res-proj-vars index)]
          [indy-arg/res-proj-var (vector-ref indy-arg/res-proj-vars index)])
      
      (let ([indy-binding
             ;; if indy-arg/res-proj-var is #f, that means that we don't need that binding, so skip it
             (if indy-arg/res-proj-var
                 (list 
                  #`[#,indy-arg/res-var 
                     #,(add-unsupplied-check
                        an-arg/res
                        wrapper-arg
                        (if (arg/res-vars an-arg/res)
                            #`(#,arg/res-proj-var
                               #,@(map (λ (var) 
                                         (arg/res-to-indy-var indy-arg-vars
                                                              ordered-args
                                                              indy-res-vars
                                                              ordered-ress
                                                              var))
                                       (arg/res-vars an-arg/res))
                               #,wrapper-arg 
                               #,(build-blame-identifier #t swapped-blame? (arg/res-var an-arg/res)))
                            #`(#,indy-arg/res-proj-var #,wrapper-arg)))])
                 (list))])
        #`(let (#,@indy-binding
                [#,wrapper-arg 
                 #,(add-unsupplied-check
                    an-arg/res
                    wrapper-arg
                    (cond
                      [(and (eres? an-arg/res) (arg/res-vars an-arg/res))
                       #`(un-dep #,(eres-eid an-arg/res) 
                                 #,wrapper-arg
                                 #,(build-blame-identifier #f 
                                                           swapped-blame? 
                                                           (arg/res-var an-arg/res)))]
                      [(arg/res-vars an-arg/res)
                       #`(#,arg/res-proj-var 
                          #,@(map (λ (var) (arg/res-to-indy-var indy-arg-vars 
                                                                ordered-args 
                                                                indy-res-vars 
                                                                ordered-ress 
                                                                var))
                                  (arg/res-vars an-arg/res))
                          #,wrapper-arg 
                          #,(build-blame-identifier #f swapped-blame? (arg/res-var an-arg/res)))]
                      [else
                       #`(#,arg/res-proj-var #,wrapper-arg)]))])
            #,body)))))


;;   (identifier arg -o> identifier) -- maps the original var in the arg to the corresponding indy-var
;;      free-identifier-mapping[id -o> (listof (list/c boolean?[indy?] boolean?[dom?]))]
;; mutates blame-var-table to record which 
;; blame records needs to be computed (and passed in)
(define-for-syntax (build-blame-ids ordered-args ordered-reses)
  (define blame-var-table (make-free-identifier-mapping))
  (define needed-blame-vars (make-hash))
  
  (define (add-blame-var indy? dom? id)
    (define olds (free-identifier-mapping-get blame-var-table id (λ () '())))
    (define new (list indy? dom?))
    (unless (member new olds)
      (free-identifier-mapping-put! blame-var-table id (cons new olds))))
  
  (define (build-some ordered-arg/reses swapped-blame?)
    (for ([an-arg/res (in-list ordered-arg/reses)])
         (when (arg/res-vars an-arg/res)
           (add-blame-var #t swapped-blame? (arg/res-var an-arg/res))
           (if (eres? an-arg/res)
               (add-blame-var #f swapped-blame? (arg/res-var an-arg/res))
               (add-blame-var #f swapped-blame? (arg/res-var an-arg/res))))))
  
  (build-some ordered-args #t)
  (build-some ordered-reses #f)
  
  (define blame-ids '())
  (free-identifier-mapping-for-each
   blame-var-table
   (λ (id prs)
     (for ([pr (in-list prs)])
          (define indy? (list-ref pr 0))
          (define dom? (list-ref pr 1))
          (set! blame-ids (cons (cons (build-blame-identifier indy? dom? id)
                                      (vector (syntax-e id) indy? dom?))
                                blame-ids)))))
  (sort blame-ids symbol<? #:key (λ (x) (syntax-e (car x)))))

(define-for-syntax (build-blame-identifier indy? dom? id)
  (datum->syntax id
                 (string->symbol
                  (string-append (symbol->string (syntax-e id))
                                 (if indy? "-indy" "")
                                 (if dom? "-dom" "-rng")
                                 "-blame"))))

;; Returns an empty list if no result contracts and a list of a single syntax value
;; which should be a function from results to projection-applied versions of the same
;; if there are result contracts.
(define-for-syntax (build-result-checkers an-astx
                                          ordered-ress res-indices
                                          res-proj-vars indy-res-proj-vars
                                          wrapper-ress indy-res-vars
                                          ordered-args indy-arg-vars)
  (cond
    [(astx-ress an-astx)
     (list
      #`(case-lambda
          [#,(vector->list wrapper-ress)
           (with-continuation-mark
               contract-continuation-mark-key blame
             #,(add-wrapper-let 
                (add-post-cond an-astx indy-arg-vars ordered-args indy-res-vars ordered-ress 
                               #`(values #,@(vector->list wrapper-ress)))
                #f #f
                ordered-ress res-indices
                res-proj-vars indy-res-proj-vars 
                wrapper-ress indy-res-vars
                indy-arg-vars ordered-args indy-res-vars ordered-ress))]
          [args
           (bad-number-of-results blame val
                                  #,(vector-length wrapper-ress)
                                  args)]))]
    [else
     null]))

(define-for-syntax (add-eres-lets an-astx res-proj-vars
                                  indy-arg-vars ordered-args indy-res-vars ordered-ress 
                                  stx)
  (cond
    [(and (astx-ress an-astx)
          (andmap eres? (astx-ress an-astx)))
     (for/fold ([body stx])
               ([an-arg/res (in-list (reverse (astx-ress an-astx)))]
                [res-proj-var (in-vector res-proj-vars (- (vector-length res-proj-vars) 1) -1 -1)])
       (if (arg/res-vars an-arg/res)
           #`(let ([#,(eres-eid an-arg/res)
                    (#,res-proj-var #,@(map (λ (var) (arg/res-to-indy-var indy-arg-vars 
                                                                          ordered-args 
                                                                          indy-res-vars 
                                                                          ordered-ress 
                                                                          var))
                                            (arg/res-vars an-arg/res)))])
               #,body)
           body))]
    [else stx]))

(define-for-syntax (mk-wrapper-func/blame-id-info stx an-astx used-indy-vars)
  
  (define-values (wrapper-proc-arglist
                  blame-ids args+rst
                  ordered-args arg-indices
                  ordered-ress res-indices
                  arg-proj-vars indy-arg-proj-vars
                  res-proj-vars indy-res-proj-vars)
    (build-wrapper-proc-arglist an-astx used-indy-vars))
  
  (define wrapper-args (list->vector 
                        (append (generate-temporaries (map arg/res-var (astx-args an-astx)))
                                (if (astx-rst an-astx)
                                    (list #'rest-args)
                                    '()))))
  (define indy-arg-vars (generate-temporaries (map arg/res-var ordered-args)))
  
  (define wrapper-ress 
    (list->vector (generate-temporaries (map arg/res-var (or (astx-ress an-astx) '())))))
  (define indy-res-vars
    (generate-temporaries (map arg/res-var ordered-ress)))
  
  
  (define this-param (and (syntax-parameter-value #'making-a-method)
                          (car (generate-temporaries '(this)))))
  

  (define wrapper-body
    (add-wrapper-let 
     (add-pre-cond 
      an-astx 
      indy-arg-vars ordered-args indy-res-vars ordered-ress
      (add-eres-lets
       an-astx
       res-proj-vars
       indy-arg-vars ordered-args indy-res-vars ordered-ress 
       (args/vars->arg-checker
        (build-result-checkers
         an-astx
         ordered-ress res-indices
         res-proj-vars indy-res-proj-vars
         wrapper-ress indy-res-vars
         ordered-args indy-arg-vars)
        (astx-args an-astx)
        (astx-rst an-astx)
        wrapper-args
        this-param)))
     #t #f
     ordered-args arg-indices
     arg-proj-vars indy-arg-proj-vars 
     wrapper-args indy-arg-vars
     indy-arg-vars ordered-args indy-res-vars ordered-ress))

  (define wrapper-val
    (add-wrapper-let
     (add-auth
      an-astx 
      indy-arg-vars
      ordered-args
      indy-res-vars
      ordered-ress)
     #t #f
     ordered-args arg-indices
     arg-proj-vars indy-arg-proj-vars 
     wrapper-args indy-arg-vars
     indy-arg-vars ordered-args indy-res-vars ordered-ress))
      
       
    
  (values
   (map cdr blame-ids)
   (with-syntax ([arg-checker (or (syntax-local-infer-name stx) 'arg-checker)])
     #`(λ #,wrapper-proc-arglist
         (λ (val)
           (chk val #,(and (syntax-parameter-value #'making-a-method) #t))
           (impersonate-procedure
            (let* ([auth-wrapper
                   (λ #,(args/vars->arglist an-astx wrapper-args this-param)
                     ((#,wrapper-val blame) val))]
                  [val (make-keyword-procedure
                        (λ (kwds kwd-args . args)
                          (with-continuation-mark
                              contract-continuation-mark-key blame
                            (keyword-apply (keyword-apply auth-wrapper kwds kwd-args args) kwds kwd-args args)))
                        (λ args
                          (with-continuation-mark
                              contract-continuation-mark-key blame
                            (apply (apply auth-wrapper args) args))))])
                  val)
            (let ([arg-checker
                   (λ #,(args/vars->arglist an-astx wrapper-args this-param)
                     #,wrapper-body)])
              (make-keyword-procedure
               (λ (kwds kwd-args . args)
                 (with-continuation-mark
                     contract-continuation-mark-key blame
                   (keyword-apply arg-checker kwds kwd-args args)))
               (λ args
                 (with-continuation-mark
                     contract-continuation-mark-key blame
                   (apply arg-checker args)))))
            impersonator-prop:contracted ctc
            impersonator-prop:blame blame))))))

(define-for-syntax (arg/res-to-indy-var indy-arg-vars ordered-args indy-res-vars ordered-ress var)
  (define (try vars ordered)
    (let loop ([iargs vars]
               [args ordered])
      (cond
        [(null? args) #f]
        [else
         (let ([arg (arg/res-var (car args))]
               [iarg (car iargs)])
           (cond
             [(free-identifier=? var arg) iarg]
             [else (loop (cdr iargs) (cdr args))]))])))
  (or (try indy-arg-vars ordered-args)
      (try indy-res-vars ordered-ress)
      (error '->a "internal error; did not find a matching var for ~s" var)))

(define-for-syntax (build-wrapper-proc-arglist an-astx used-indy-vars)
  
  (define args+rst (append (astx-args an-astx)
                           (if (astx-rst an-astx)
                               (list (astx-rst an-astx))
                               '())))
  (define-values (ordered-args arg-indices) (find-ordering args+rst))
  (define-values (ordered-ress res-indices) (if (astx-ress an-astx)
                                                (find-ordering (astx-ress an-astx))
                                                (values '() '())))
  
  
  (define arg-proj-vars (list->vector (generate-temporaries (map arg/res-var args+rst))))
  
  (define blame-ids (build-blame-ids ordered-args ordered-ress))
  
  ;; this list is parallel to arg-proj-vars (so use arg-indices to find the right ones)
  ;; but it contains #fs in places where we don't need the indy projections (because the corresponding
  ;; argument is not dependened on by anything)
  (define indy-arg-proj-vars 
    (list->vector (map (λ (x) (maybe-generate-temporary
                               (and (free-identifier-mapping-get used-indy-vars 
                                                                 (arg/res-var x)
                                                                 (λ () #f))
                                    (arg/res-var x)))) 
                       args+rst)))
  
  (define res-proj-vars
    (list->vector (generate-temporaries (map arg/res-var (or (astx-ress an-astx) '())))))
  
  
  ;; this list is parallel to res-proj-vars (so use res-indices to find the right ones)
  ;; but it contains #fs in places where we don't need the indy projections (because the 
  ;; corresponding result is not dependened on by anything)
  (define indy-res-proj-vars (list->vector (map (λ (x)
                                                  (maybe-generate-temporary
                                                   (and (free-identifier-mapping-get used-indy-vars 
                                                                                     (arg/res-var x)
                                                                                     (λ () #f))
                                                        (arg/res-var x))))
                                                (or (astx-ress an-astx)
                                                    '()))))
  
  (define wrapper-proc-arglist
    #`(chk ctc blame swapped-blame #,@(map car blame-ids)

           
           
           ;; the pre-condition procs
           #,@(for/list ([pres (astx-pre an-astx)]
                         [i (in-naturals)])
                        (string->symbol (format "pre-proc~a" i)))

           ;; the auth procs
           #,@(for/list ([auths (astx-auth an-astx)]
                         [i (in-naturals)])
                        (string->symbol (format "auth-proc~a" i)))

           ;; the post-condition procs
           #,@(for/list ([pres (astx-post an-astx)]
                         [i (in-naturals)])
                        (string->symbol (format "post-proc~a" i)))
           
           ;; first the non-dependent arg projections
           #,@(filter values (map (λ (arg/res arg-proj-var) 
                                    (and (not (arg/res-vars arg/res)) arg-proj-var))
                                  args+rst
                                  (vector->list arg-proj-vars)))
           ;; then the dependent arg projections
           #,@(filter values (map (λ (arg/res arg-proj-var)
                                    (and (arg/res-vars arg/res) arg-proj-var))
                                  args+rst
                                  (vector->list arg-proj-vars)))
           ;; then the non-dependent indy arg projections
           #,@(filter values (map (λ (arg/res arg-proj-var)
                                    (and (not (arg/res-vars arg/res)) arg-proj-var))
                                  args+rst
                                  (vector->list indy-arg-proj-vars)))
           
           ;; then the non-dependent res projections
           #,@(filter values (map (λ (arg/res res-proj-var)
                                    (and (not (arg/res-vars arg/res)) res-proj-var))
                                  (or (astx-ress an-astx) '())
                                  (vector->list res-proj-vars)))
           ;; then the dependent res projections
           #,@(filter values (map (λ (arg/res res-proj-var)
                                    (and (arg/res-vars arg/res) res-proj-var))
                                  (or (astx-ress an-astx) '())
                                  (vector->list res-proj-vars)))
           ;; then the non-dependent indy res projections
           #,@(filter values (map (λ (arg/res res-proj-var)
                                    (and (not (arg/res-vars arg/res)) res-proj-var))
                                  (or (astx-ress an-astx) '())
                                  (vector->list indy-res-proj-vars)))))
  
  (values wrapper-proc-arglist
          blame-ids args+rst
          ordered-args arg-indices
          ordered-ress res-indices
          arg-proj-vars indy-arg-proj-vars
          res-proj-vars indy-res-proj-vars))

(define-for-syntax (mk-val-first-wrapper-func/blame-id-info an-astx used-indy-vars)
  (define-values (wrapper-proc-arglist
                  blame-ids args+rst
                  ordered-args arg-indices
                  ordered-ress res-indices
                  arg-proj-vars indy-arg-proj-vars
                  res-proj-vars indy-res-proj-vars)
    (build-wrapper-proc-arglist an-astx used-indy-vars))
  
  (define wrapper-args (list->vector 
                        (append (generate-temporaries (map arg/res-var (astx-args an-astx)))
                                (if (astx-rst an-astx)
                                    (list #'rest-args)
                                    '()))))
  (define indy-arg-vars (generate-temporaries (map arg/res-var ordered-args)))
  
  (define wrapper-ress 
    (list->vector (generate-temporaries (map arg/res-var (or (astx-ress an-astx) '())))))
  (define indy-res-vars
    (generate-temporaries (map arg/res-var ordered-ress)))
  
  
  (define this-param (and (syntax-parameter-value #'making-a-method)
                          (car (generate-temporaries '(this)))))
  
  #`(λ #,wrapper-proc-arglist 
      (λ (f)
        (λ (neg-party #,@(args/vars->arglist an-astx wrapper-args this-param))
          #,(add-wrapper-let 
             (build-call-to-original-function 
              (astx-args an-astx)
              (astx-rst an-astx)
              wrapper-args
              this-param)
             #t #t
             ordered-args arg-indices
             arg-proj-vars indy-arg-proj-vars 
             wrapper-args indy-arg-vars
             indy-arg-vars ordered-args indy-res-vars ordered-ress)))))

(define-for-syntax (build-call-to-original-function args rst vars this-param)
  (define argument-list
    (apply
     append
     (for/list ([arg (in-list args)]
                [var (in-vector vars)])
               (cond
                 [(arg-kwd arg)
                  (list (arg-kwd arg) var)]
                 [else
                  (list var)]))))
  (if rst 
      #`(apply f #,@argument-list rest-args)
      #`(f #,@argument-list)))

(begin-encourage-inline
  (define (un-dep ctc obj blame)
    (let ([ctc (coerce-contract '->a ctc)])
      (((contract-projection ctc) blame) obj))))

(define-for-syntax (mk-used-indy-vars an-astx)
  (let ([vars (make-free-identifier-mapping)])
    
    ;; add in regular arguments' uses
    (for ([an-arg (in-list (astx-args an-astx))])
         (when (arg/res-vars an-arg)
           (for ([var (in-list (arg/res-vars an-arg))])
                (free-identifier-mapping-put! vars var #t))))
    
    ;; add in rest argument uses
    (when (astx-rst an-astx)
      (let ([an-arg/rst (astx-rst an-astx)])
        (when (arg/res-vars an-arg/rst)
          (for ([var (in-list (arg/res-vars an-arg/rst))])
               (free-identifier-mapping-put! vars var #t)))))
    
    ;; pre-condition
    (for ([pre (in-list (astx-pre an-astx))])
         (for ([var (in-list (pre/post-vars pre))])
              (free-identifier-mapping-put! vars var #t)))
    
    ;; auth
    (for ([auth (in-list (astx-auth an-astx))])
         (for ([var (in-list (auth-vars auth))])
              (free-identifier-mapping-put! vars var #t)))
    
    ;; results
    (when (astx-ress an-astx)
      (for ([a-res (in-list (astx-ress an-astx))])
           (when (arg/res-vars a-res)
             (for ([var (in-list (arg/res-vars a-res))])
                  (free-identifier-mapping-put! vars var #t)))))
    
    ;; post-condition
    (for ([post (in-list (astx-post an-astx))])
         (for ([var (in-list (pre/post-vars post))])
              (free-identifier-mapping-put! vars var #t)))
    
    vars))

(define-syntax (->a/m stx)
  (define an-astx (parse-->a stx))
  (define used-indy-vars (mk-used-indy-vars an-astx))
  (define-values (blame-ids wrapper-func) (mk-wrapper-func/blame-id-info stx an-astx used-indy-vars))
  (define val-first-wrapper-func (mk-val-first-wrapper-func/blame-id-info an-astx used-indy-vars))
  (define args+rst (append (astx-args an-astx)
                           (if (astx-rst an-astx)
                               (list (astx-rst an-astx))
                               '())))
  (define this->a (gensym 'this->a))
  (with-syntax ([(arg-exp-xs ...) 
                 (generate-temporaries 
                  (filter values (map (λ (arg)
                                        (and (not (arg/res-vars arg)) (arg/res-var arg)))
                                      args+rst)))]
                [((arg-names arg-kwds arg-is-optional?s arg-exps) ...)
                 (filter values (map (λ (arg) (and (not (arg/res-vars arg)) 
                                                   (list
                                                    (arg/res-var arg)
                                                    (and (arg? arg) (arg-kwd arg))
                                                    (and (arg? arg) (arg-optional? arg))
                                                    (syntax-property
                                                     (syntax-property
                                                      (arg/res-ctc arg)
                                                      'racket/contract:negative-position
                                                      this->a)
                                                     'racket/contract:contract-on-boundary 
                                                     (gensym '->a-indy-boundary)))))
                                     args+rst))]
                
                [(res-exp-xs ...) 
                 (if (astx-ress an-astx)
                     (generate-temporaries (filter values (map (λ (res) (and (not (arg/res-vars res))
                                                                             (arg/res-var res)))
                                                               (astx-ress an-astx))))
                     '())]
                [((res-names res-exps) ...)
                 (if (astx-ress an-astx)
                     (filter values (map (λ (res) (and (not (arg/res-vars res)) 
                                                       (list
                                                        (arg/res-var res)
                                                        (syntax-property
                                                         (syntax-property 
                                                          (arg/res-ctc res)
                                                          'racket/contract:positive-position
                                                          this->a)
                                                         'racket/contract:contract-on-boundary 
                                                         (gensym '->a-indy-boundary)))))
                                         (astx-ress an-astx)))
                     '())])
    
    (define (find-orig-vars arg arg/ress-to-look-in)
      (for/list ([an-id (in-list (arg/res-vars arg))])
                (define ans
                  (for/or ([o-arg (in-list arg/ress-to-look-in)])
                          (and (free-identifier=? an-id (arg/res-var o-arg))
                               (arg/res-var o-arg))))
                (unless ans
                  (error 'contract/arr-i.rkt:find-orig-vars 
                         "could not find ~s in ~s\n"
                         an-id arg/ress-to-look-in))
                ans))
    
    #`(let ([arg-exp-xs (coerce-contract '->a arg-exps)] ...
            [res-exp-xs (coerce-contract '->a res-exps)] ...)
        #,(syntax-property
           #`(->a 
              ;; the information needed to make the blame records and their new contexts
              '#,blame-ids
              ;; all of the non-dependent argument contracts
              (list (->a-arg 'arg-names 'arg-kwds arg-is-optional?s arg-exp-xs) ...)
              ;; all of the dependent argument contracts
              (list #,@(for/list ([arg (in-list args+rst)]
                                  #:when (arg/res-vars arg))
                                 (define orig-vars (find-orig-vars arg args+rst))
                                 (define ctc-stx
                                   (syntax-property
                                    (syntax-property 
                                     (arg/res-ctc arg)
                                     'racket/contract:negative-position 
                                     this->a)
                                    'racket/contract:contract-on-boundary
                                    (gensym '->a-indy-boundary)))
                                 #`(λ (#,@orig-vars val blame)
                                     #,@(arg/res-vars arg)
                                     ;; this used to use opt/direct, but 
                                     ;; opt/direct duplicates code (bad!)
                                     (un-dep #,ctc-stx val blame))))
              ;; then the non-dependent argument contracts that are themselves dependend on
              (list #,@(filter values
                               (map (λ (arg/res indy-id) 
                                      (and (free-identifier-mapping-get used-indy-vars
                                                                        (arg/res-var arg/res)
                                                                        (λ () #f))
                                           #`(cons '#,(arg/res-var arg/res) #,indy-id)))
                                    (filter (λ (arg/res) (not (arg/res-vars arg/res))) args+rst)
                                    (syntax->list #'(arg-exp-xs ...)))))
              
              
              #,(if (astx-ress an-astx)
                    #`(list (cons 'res-names res-exp-xs) ...)
                    #''())
              #,(if (astx-ress an-astx) 
                    #`(list #,@(for/list ([arg (in-list 
                                                (astx-ress an-astx))]
                                          #:when (arg/res-vars arg))
                                         (define orig-vars 
                                           (find-orig-vars 
                                            arg 
                                            (append (astx-ress an-astx)
                                                    args+rst)))
                                         (define arg-stx
                                           (syntax-property
                                            (syntax-property 
                                             (arg/res-ctc arg)
                                             'racket/contract:positive-position
                                             this->a)
                                            'racket/contract:contract-on-boundary 
                                            (gensym '->a-indy-boundary)))
                                         (if (eres? arg)
                                             #`(λ #,orig-vars
                                                 #,@(arg/res-vars arg)
                                                 (opt/c #,arg-stx))
                                             #`(λ (#,@orig-vars val blame)
                                                 ;; this used to use opt/direct, but 
                                                 ;; opt/direct duplicates code (bad!)
                                                 #,@(arg/res-vars arg)
                                                 (un-dep #,arg-stx val blame)))))
                    #''())
              #,(if (astx-ress an-astx)
                    #`(list #,@(filter values
                                       (map (λ (arg/res indy-id) 
                                              (and (free-identifier-mapping-get used-indy-vars 
                                                                                (arg/res-var arg/res)
                                                                                (λ () #f))
                                                   #`(cons '#,(arg/res-var arg/res) #,indy-id)))
                                            (filter (λ (arg/res) 
                                                      (not (arg/res-vars arg/res)))
                                                    (astx-ress an-astx))
                                            (syntax->list #'(res-exp-xs ...)))))
                    #''())
              
              #,(let ([func (λ (pre/post) #`(λ #,(pre/post-vars pre/post)
                                              #,(pre/post-exp pre/post)))])
                  #`(list #,@(for/list ([pre (in-list (astx-pre an-astx))])
                                       (func pre))
                          #,@(for/list ([post (in-list (astx-post an-astx))])
                                       (func post))))

              #,(let ([func (λ (auth) #`(λ #,(auth-vars auth)
                                              #,(auth-exp auth)))])
                  #`(list #,@(for/list ([auth (in-list (astx-auth an-astx))])
                                       (func auth))))
              
              #,(length (filter values (map (λ (arg) (and (not (arg-kwd arg)) 
                                                          (not (arg-optional? arg))))
                                            (astx-args an-astx))))
              #,(length (filter values (map (λ (arg) (and (not (arg-kwd arg)) (arg-optional? arg)))
                                            (astx-args an-astx))))
              '#,(sort (filter values (map (λ (arg) (and (not (arg-optional? arg)) 
                                                         (arg-kwd arg) 
                                                         (syntax-e (arg-kwd arg))))
                                           (astx-args an-astx))) 
                       keyword<?)
              '#,(sort (filter values (map (λ (arg) (and (arg-optional? arg)
                                                         (arg-kwd arg)
                                                         (syntax-e (arg-kwd arg))))
                                           (astx-args an-astx))) 
                       keyword<?)
              '#,(and (astx-rst an-astx) (arg/res-var (astx-rst an-astx)))
              #,(and (syntax-parameter-value #'making-a-method) #t)
              (quote-module-name)
              #,wrapper-func
              #,val-first-wrapper-func
              '#(#,(for/list ([an-arg (in-list (astx-args an-astx))])
                             `(,(if (arg/res-vars an-arg) 'dep 'nodep)
                               ,(syntax-e (arg/res-var an-arg)) 
                               ,(if (arg/res-vars an-arg)
                                    (map syntax-e (arg/res-vars an-arg))
                                    '())
                               ,(and (arg-kwd an-arg)
                                     (syntax-e (arg-kwd an-arg)))
                               ,(arg-optional? an-arg)
                               ,(arg/res-quoted-dep-src-code an-arg)))
                 #,(if (astx-rst an-astx)
                       (if (arg/res-vars (astx-rst an-astx))
                           `(dep ,(syntax-e (arg/res-var (astx-rst an-astx)))
                                 ,(map syntax-e (arg/res-vars (astx-rst an-astx)))
                                 ,(arg/res-quoted-dep-src-code (astx-rst an-astx)))
                           `(nodep ,(syntax-e (arg/res-var (astx-rst an-astx)))))
                       #f)
                 #,(for/list ([pre (in-list (astx-pre an-astx))])
                             (list (map syntax-e (pre/post-vars pre))
                                   (pre/post-kind pre)
                                   (pre/post-quoted-dep-src-code pre)))
                 #,(for/list ([auth (in-list (astx-auth an-astx))])
                             (list (map syntax-e (auth-vars auth))
                                   (auth-quoted-dep-src-code auth)))
                 #,(and (astx-ress an-astx)
                        (for/list ([a-res (in-list (astx-ress an-astx))])
                                  `(,(if (arg/res-vars a-res) 'dep 'nodep)
                                    ,(if (eres? a-res)
                                         '_
                                         (syntax-e (arg/res-var a-res)))
                                    ,(if (arg/res-vars a-res)
                                         (map syntax-e (arg/res-vars a-res))
                                         '())
                                    #f
                                    #f
                                    ,(arg/res-quoted-dep-src-code a-res))))
                 #,(for/list ([post (in-list (astx-post an-astx))])
                             (list (map syntax-e (pre/post-vars post))
                                   (pre/post-kind post)
                                   (pre/post-quoted-dep-src-code post)))))
           'racket/contract:contract 
           (let ()
             (define (find-kwd kwd)
               (for/or ([x (in-list (syntax->list stx))])
                       (and (eq? (syntax-e x) kwd)
                            x)))
             (define pre (find-kwd '#:pre))
             (define auth (find-kwd '#:auth))
             (define post (find-kwd '#:post))
             (define orig (list (car (syntax-e stx))))
             (vector this->a 
                     ;; the ->a in the original input to this guy
                     (if post (cons post orig) orig)
                     (if auth (list 'boo) '())
                     (if pre (list pre) '())))))))


