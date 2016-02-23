#lang racket

(provide current-delegations
         current-principal
         closure-delegations
         closure-principal
         closure-args
         authority-contract?
         define-authority-contracts
         (contract-out
          [do-create (->* ()
                          (#:check (or/c labeled? #f)
                           #:add delegation-list?
                           #:remove delegation-list?
                           #:add-lifetime delegation-list?
                           #:closure-principal (or/c principal? #f))
                          create-actions?)]
          [do-apply (->* ()
                         (#:check (or/c labeled? #f)
                          #:add delegation-list?
                          #:remove delegation-list?
                          #:add-scoped delegation-list?
                          #:add-lifetime delegation-list?
                          #:set!-principal (or/c principal? #f)
                          #:set-principal (or/c principal? #f)
                          #:on-return (or/c return-hook/c #f))
                         apply-actions?)]
          [do-return (->* ()
                          (#:add delegation-list?
                           #:remove delegation-list?
                           #:add-lifetime delegation-list?)
                          return-actions?)])
         (except-out (all-from-out "flam/authorization.rkt")
                     make-delegation-set
                     print-delegation-set
                     add-delegations
                     remove-delegations))

(require "flam/authorization.rkt")

(define (mark-parameter-first param)
  (let ([val (continuation-mark-set-first #f (mark-parameter-key param))])
    (if val
        (unbox val)
        (mark-parameter-default param))))

(define (mark-parameter-list param)
  (let ([val (continuation-mark-set->list (current-continuation-marks) (mark-parameter-key param))])
    (append (map unbox val) (list (mark-parameter-default param)))))

(define (mark-parameter-set param new-val)
  (let ([val (continuation-mark-set-first #f (mark-parameter-key param))])
    (if val
        (set-box! val new-val)
        (set-mark-parameter-default! param new-val))))

(struct mark-parameter (key [default #:mutable]))

(define (make-mark-parameter default)
  (let ([key (make-continuation-mark-key)])
    (mark-parameter key default)))

(define-values (prop:authority-contract authority-contract? authority-contract-accessor)
  (make-struct-type-property 'authority-contract))
(define-values (prop:authority-closure authority-closure? authority-closure-accessor)
  (make-impersonator-property 'authority-closure))

(struct create-actions (check to-add to-remove to-lifetime principal))
(struct apply-actions  (check to-add to-remove to-scope to-lifetime
                        set-principal scope-principal return-hook))
(struct return-actions (to-add to-remove to-lifetime))

(define (do-create #:check [check #f] #:add [to-add empty] #:remove [to-remove empty]
                   #:add-lifetime [to-lifetime empty] #:closure-principal [principal #f])
  (create-actions check to-add to-remove to-lifetime principal))

(define (do-apply #:check [check #f] #:add [to-add empty] #:remove [to-remove empty]
                  #:add-scoped [to-scope empty] #:add-lifetime [to-lifetime empty]
                  #:set!-principal [set-principal #f] #:set-principal [scope-principal #f]
                  #:on-return [return-hook #f])
  (apply-actions check to-add to-remove to-scope to-lifetime set-principal scope-principal return-hook))

(define (do-return #:add [to-add empty] #:remove [to-remove empty] #:add-lifetime [to-lifetime empty])
  (return-actions to-add to-remove to-lifetime))

(define return-hook/c (-> (listof any/c) return-actions?))

(define (create-actions-values current-principal c)
  (values (create-actions-check c)
          (create-actions-to-add c)
          (create-actions-to-remove c)
          (create-actions-to-lifetime c)
          (if (create-actions-principal c)
              (create-actions-principal c)
              current-principal)))

(define (apply-actions-values a)
  (values (apply-actions-check a)
          (apply-actions-to-add a)
          (apply-actions-to-remove a)
          (apply-actions-to-scope a)
          (apply-actions-to-lifetime a)
          (apply-actions-set-principal a)
          (apply-actions-scope-principal a)
          (apply-actions-return-hook a)))

(define (return-actions-values r)
  (values (return-actions-to-add r)
          (return-actions-to-remove r)
          (return-actions-to-lifetime r)))

(struct authority-contract-spec (name create-hook apply-hook combinator?))

(struct authority-region/c (name combinator)
  #:property prop:authority-contract #t
  #:property prop:contract
  (build-contract-property
   #:name
   (λ (ctc) (authority-region/c-name ctc))
   #:first-order
   (λ (ctc) (λ (val) (procedure? val)))
   #:projection
   (λ (ctc)
     (λ (blame)
       (λ (val)
         (unless (procedure? val)
           (raise-blame-error
            blame val
            '(expected: "~a" given: "~e")
            "procedure" val))
         (let ([comb (authority-region/c-combinator ctc)])
           (comb (blame-swap blame) val)))))))

(define (authority-contracts #:search [search-list #f] . hooks)
  (define delegations (make-delegation-set))
  (define lifetime-delegations (make-weak-hash))

  (define (current-delegations scoped-delegations)
    (foldl (λ (s ds) (apply add-delegations ds (set->list s)))
           (for/fold ([all-delegations delegations])
                     ([ds scoped-delegations])
             (add-delegations all-delegations ds))
           (hash-values lifetime-delegations)))
  
  (define (auth-add-delegations to-add)
    (let-values ([(ls ds) (partition (λ (d) (lifetime? d)) to-add)])
      (for ([lt ls])
        (match lt
          [(lifetime _ _ b)
           (let ([key (weak-box-value b)])
             (when key
               (hash-update! lifetime-delegations key
                             (λ (ds) (set-add ds lt))
                             (λ () (set lt)))))]))
      (set! delegations (apply add-delegations delegations ds))))

  (define (auth-remove-delegations to-remove)
    (let-values ([(ls ds) (partition (λ (d) (lifetime? d)) to-remove)])
      (for ([lt ls])
        (match lt
          [(lifetime _ _ b)
           (let ([key (weak-box-value b)])
             (when key
               (hash-update! lifetime-delegations key
                             (λ (ds) (set-remove ds lt)))))]))
      (set! delegations (apply remove-delegations delegations ds))
      (let ([as-set (list->set ds)])
        (hash-map lifetime-delegations
                  (λ (k s)
                    (let ([new-s (set-subtract s as-set)])
                      (when (not (equal? s new-s))
                        (hash-set! lifetime-delegations k new-s))))))))

  (define (auth-update-delegations to-add to-remove)
    (auth-remove-delegations to-remove)
    (auth-add-delegations to-add))

  (define (combinator-generator prop principal-param delegation-param create-authority-region apply-authority-region)
    (λ hook-args
      (λ (blame proc)
        (let*-values ([(principal) (mark-parameter-first principal-param)]
                      [(scoped-delegations) (mark-parameter-list delegation-param)]
                      [(closure-delegations) (current-delegations scoped-delegations)]
                      [(check to-add to-remove for-lifetime closure-principal)
                       (create-actions-values principal
                                              (apply create-authority-region closure-delegations principal hook-args))]
                      [(closure-authority) (cons closure-delegations closure-principal)])
          (match check
            [(labeled (actsfor l r) ll)
             (unless (acts-for? (current-delegations scoped-delegations) l r ll #:search search-list)
               (raise-blame-error
                blame proc
                (format "~a ⋡ ~a @ ~a~n" l r ll)))]
            [#f (void)])
          (define wrapper
            (make-keyword-procedure
             (λ (kwds kwd-args . other-args)
               (do-region (mark-parameter-first principal-param) (mark-parameter-list delegation-param) kwd-args other-args))
             (λ args
               (do-region (mark-parameter-first principal-param) (mark-parameter-list delegation-param) #f args))))
          (define (add-lifetime-delegations delegations)
            (map (match-lambda
                   [(labeled r l)
                    (hash-update! lifetime-delegations wrapper
                                  (λ (ds) (set-add ds (make-lifetime r l (make-weak-box wrapper))))
                                  (λ () (set (make-lifetime r l (make-weak-box wrapper)))))])
                 delegations))
          (auth-update-delegations to-add to-remove)
          (add-lifetime-delegations for-lifetime)
          (define (do-region principal scoped-delegations kwd-args other-args)
            (let*-values ([(check to-add to-remove to-scope to-lifetime
                                  set-principal new-principal on-return)
                           (apply-actions-values
                            (apply apply-authority-region
                                   (current-delegations scoped-delegations)
                                   principal
                                   closure-delegations
                                   closure-principal
                                   (map (λ (arg) (if (authority-closure? arg) (authority-closure-accessor arg) #f))
                                        (if kwd-args (append kwd-args other-args) other-args))
                                   hook-args))])
              (match check
                [(labeled (actsfor l r) ll)
                 (unless (acts-for? (current-delegations scoped-delegations) l r ll #:search search-list)
                   (raise-blame-error
                    blame proc
                    (format "~a ⋡ ~a @ ~a~n" l r ll)))]
                [#f (void)])
              (auth-update-delegations to-add to-remove)
              (add-lifetime-delegations to-lifetime)
              (let ([result-handler
                     (if on-return
                         (λ results
                           (let-values ([(principal) (mark-parameter-first principal-param)]
                                        [(scoped-delegations) (mark-parameter-list delegation-param)]
                                        [(to-add to-remove to-lifetime)
                                         (return-actions-values
                                          (on-return (map (λ (res) (if (authority-closure? res) (authority-closure-accessor res) #f)) results)))])
                             (auth-update-delegations to-add to-remove)
                             (add-lifetime-delegations to-lifetime)
                             (apply values results)))
                         #f)]
                    [new-scoped-delegations
                     (if (not (empty? to-scope))
                         (apply add-delegations (first scoped-delegations) to-scope) ; XXX shouldn't need this
                         #f)])
                (when set-principal
                  (mark-parameter-set principal-param set-principal))
                (if kwd-args
                    (cond
                      [(and new-principal new-scoped-delegations result-handler)
                       (apply values
                              result-handler
                              'mark (mark-parameter-key principal-param) (box new-principal)
                              'mark (mark-parameter-key delegation-param) (box new-scoped-delegations)
                              kwd-args
                              other-args)]
                      [(and new-principal new-scoped-delegations)
                       (apply values
                              'mark (mark-parameter-key principal-param) (box new-principal)
                              'mark (mark-parameter-key delegation-param) (box new-scoped-delegations)
                              kwd-args
                              other-args)]
                      [(and new-principal result-handler)
                       (apply values
                              result-handler
                              'mark (mark-parameter-key principal-param) (box new-principal)
                              kwd-args
                              other-args)]
                      [(and new-scoped-delegations result-handler)
                       (apply values
                              result-handler
                              'mark (mark-parameter-key delegation-param) (box new-scoped-delegations)
                              kwd-args
                              other-args)]
                      [new-principal
                       (apply values
                              'mark (mark-parameter-key principal-param) (box new-principal)
                              kwd-args
                              other-args)]
                      [new-scoped-delegations
                       (apply values
                              'mark (mark-parameter-key delegation-param) (box new-scoped-delegations)
                              kwd-args
                              other-args)]
                      [result-handler
                       (apply values result-handler kwd-args other-args)]
                      [else
                       (apply values kwd-args other-args)])
                    (cond
                      [(and new-principal new-scoped-delegations result-handler)
                       (apply values
                              result-handler
                              'mark (mark-parameter-key principal-param) (box new-principal)
                              'mark (mark-parameter-key delegation-param) (box new-scoped-delegations)
                              other-args)]
                      [(and new-principal new-scoped-delegations)
                       (apply values
                              'mark (mark-parameter-key principal-param) (box new-principal)
                              'mark (mark-parameter-key delegation-param) (box new-scoped-delegations)
                              other-args)]
                      [(and new-principal result-handler)
                       (apply values
                              result-handler
                              'mark (mark-parameter-key principal-param) (box new-principal)
                              other-args)]
                      [(and new-scoped-delegations result-handler)
                       (apply values
                              result-handler
                              'mark (mark-parameter-key delegation-param) (box new-scoped-delegations)
                              other-args)]
                      [new-principal
                       (apply values
                              'mark (mark-parameter-key principal-param) (box new-principal)
                              other-args)]
                      [new-scoped-delegations
                       (apply values
                              'mark (mark-parameter-key delegation-param) (box new-scoped-delegations)
                              other-args)]
                      [result-handler
                       (apply values result-handler other-args)]
                      [else
                       (apply values other-args)])))))
          (chaperone-procedure proc wrapper prop closure-authority prop:authority-closure closure-authority)))))
  
  (let* ([props
          (map (match-lambda
                 [(authority-contract-spec n _ _ _)
                  (define-values (prop:authority-region authority-region? authority-region-accessor)
                    (make-impersonator-property n))
                  (list prop:authority-region authority-region? authority-region-accessor)])
               hooks)]
         [principal-param (make-mark-parameter ⊤)]
         [delegation-param (make-mark-parameter (make-delegation-set))]
         [combinators (map (λ (prop hooks)
                             (match (cons prop hooks)
                               [(cons (list p _ _) (authority-contract-spec _ c a _))
                                (combinator-generator p principal-param delegation-param c a)]))
                           props hooks)]
         [contracts
          (map (λ (combinator hook)
                 (match hook
                   [(authority-contract-spec n _ _ #t) (λ args (authority-region/c n (apply combinator args)))]
                   [(authority-contract-spec n _ _ #f) (authority-region/c n (combinator))]))
               combinators hooks)])
    (apply values (flatten (map (λ (prop ctc)
                                  (match prop
                                    [(list _ pred accessor) (list ctc pred accessor)]))
                                props contracts)))))

(require (for-syntax racket/list))
(require racket/stxparam)

(define-for-syntax (make-names names)
  (flatten (map (λ (n) (list n
                             (datum->syntax n
                                            (string->symbol
                                             (string-append
                                              (symbol->string (syntax->datum n))
                                              "?")))
                             (datum->syntax n
                                (string->symbol
                                 (string-append
                                  (symbol->string (syntax->datum n))
                                  "-authority")))))
                (syntax->list names))))

(define-syntax-parameter current-delegations
  (lambda (stx)
    (raise-syntax-error #f "can only be used inside of authority contract spec" stx)))
(define-syntax-parameter current-principal
  (lambda (stx)
    (raise-syntax-error #f "can only be used inside of authority contract spec" stx)))
(define-syntax-parameter closure-delegations
  (lambda (stx)
    (raise-syntax-error #f "can only be used inside of authority contract spec" stx)))
(define-syntax-parameter closure-principal
  (lambda (stx)
    (raise-syntax-error #f "can only be used inside of authority contract spec" stx)))
(define-syntax-parameter closure-args
  (lambda (stx)
    (raise-syntax-error #f "can only be used inside of authority contract spec" stx)))

(define-for-syntax (authority-spec stx)
  (syntax-case stx ()
    [(x (y ...) #:on-create e_1 #:on-apply e_2)
     #'(authority-contract-spec
        (quote x)
        (λ (d p y ...)
          (syntax-parameterize ([current-delegations (make-rename-transformer #'d)]
                                [current-principal (make-rename-transformer #'p)])
            e_1))
        (λ (d p cd cp a y ...)
          (syntax-parameterize ([current-delegations (make-rename-transformer #'d)]
                                [current-principal (make-rename-transformer #'p)]
                                [closure-delegations (make-rename-transformer #'cd)]
                                [closure-principal (make-rename-transformer #'cp)]
                                [closure-args (make-rename-transformer #'a)])
            e_2))
        #t)]
    [(x #:on-create e_1 #:on-apply e_2)
     #'(authority-contract-spec
        (quote x)
        (λ (d p)
          (syntax-parameterize ([current-delegations (make-rename-transformer #'d)]
                                [current-principal (make-rename-transformer #'p)])
            e_1))
        (λ (d p cd cp a)
          (syntax-parameterize ([current-delegations (make-rename-transformer #'d)]
                                [current-principal (make-rename-transformer #'p)]
                                [closure-delegations (make-rename-transformer #'cd)]
                                [closure-principal (make-rename-transformer #'cp)]
                                [closure-args (make-rename-transformer #'a)])
            e_2))
        #f)]))

(define-syntax (define-authority-contracts stx)
  (syntax-case stx ()
    [(define-authority-contracts #:search s
       (x r ...) ...)
     #`(define-values #,(make-names #'(x ...))
         (authority-contracts
          #:search s
          #,@(map (λ (s) (authority-spec s)) (syntax->list #'((x r ...) ...)))))]
    [(define-authority-contracts spec ...)
     #'(define-authority-contracts #:search #f spec ...)]))

(module+ test
  (require rackunit)
  
  (define p (make-mark-parameter 0))
  
  (define (get-p)
    (displayln (continuation-mark-set->list (current-continuation-marks) (mark-parameter-key p)))
    (mark-parameter-first p))
  
  (get-p)
  
  (define wrapped
    (chaperone-procedure
     get-p
     (λ () (values 'mark (mark-parameter-key p) (box 1)))))
  
  (wrapped))
