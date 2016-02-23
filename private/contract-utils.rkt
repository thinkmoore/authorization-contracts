#lang racket

(require (for-syntax syntax/parse)
         (for-syntax syntax/parse/lib/function-header)
         (for-syntax syntax/define)
         (for-syntax syntax/id-table)
         (for-syntax syntax/kerncase)
         (for-template racket/base))

(provide (for-syntax build-name)
         build-external-defines
         make-define/contract/free-vars
         make-define/contract/free-vars/contract
         make-define/contract/free-vars/contract/free-vars)

(define-for-syntax (build-name name base pre?)
  (datum->syntax
   name
   (if pre?
       (string->symbol
        (string-append
         (symbol->string (syntax->datum name))
         base))
       (string->symbol
        (string-append
         base
         (symbol->string (syntax->datum name)))))))

(define-syntax (build-external-defines stx)
  (syntax-case stx ()
    [(_ id names)
     (with-syntax ([(new-name ...) (map
                                    (λ (x)
                                      (build-name
                                       #'id
                                       (string-append ":" (symbol->string x))
                                       #t))
                                    (syntax->datum #'names))]
                   [(name ...) #'names])
       #'(begin
           (define new-name name) ...))]))


(define-for-syntax scope-chain-property (gensym))
(define-for-syntax bound-property (gensym))

(define-for-syntax (new-scope-chain) (list (make-free-id-table)))

(define-for-syntax (extend-scope-chain chain) (cons (make-free-id-table) chain))

(define-for-syntax (print-scope-chain chain)
  (printf "====================~n")
  (define (print-it chain)
    (let ([f (car chain)]
          [r (cdr chain)])
      (unless (null? r)
        (print-it r))
      (free-id-table-for-each f
                              (λ (k v) (printf "~a~n" k)))
      (printf "---------------------~n")))
  (print-it chain))

(define-for-syntax (get-scope-chain stx)
  (let ([sc (syntax-property stx scope-chain-property)])
    (if sc sc (new-scope-chain))))

(define-for-syntax (add-free-identifiers chain ids)
  (let ([current (car chain)])
    (map (λ (id) (free-id-table-set! current id #t)) (syntax->list ids))))

(define-for-syntax (bound? chain id)
  (let ([current (car chain)]
        [parent  (cdr chain)])
    (cond
      [(free-id-table-ref current id (λ () #f)) #t]
      [(and (null? parent) (syntax-property id bound-property)) #t]
      [(null? parent) #f]
      [else (bound? parent id)])))

(define-for-syntax (create-scope-with-bindings chain ids)
  (let ([sc (extend-scope-chain chain)])
    (add-free-identifiers sc ids)
    sc))

(define-for-syntax (set-scope stx scope-chain)
  (syntax-property stx scope-chain-property scope-chain))

(define-syntax (contract-free-variables stx)
  (let ([scope (get-scope-chain stx)])
    (syntax-case stx ()
      [(contract-free-variables blame-id ctc-id stx)
       (let ([expanded (local-expand #'stx (syntax-local-context) (list #'define-values #'contract-id))])
         (apply-free-variable-contracts #'blame-id #'ctc-id
                                        (set-scope expanded scope)))])))

(define-for-syntax (contract-free-variables-in-scope blame-id ctc-id stx scope-chain)
  (set-scope #`(contract-free-variables #,blame-id #,ctc-id #,stx) scope-chain))

(define-for-syntax (apply-free-variable-contracts blame-id ctc-id stx)
  (define code-insp
    (variable-reference->module-declaration-inspector (#%variable-reference)))
  (let ([sc (get-scope-chain stx)])
    (kernel-syntax-case (syntax-disarm stx code-insp) #f
     [(define-values (id ...) expr)
      (begin
        (add-free-identifiers sc #'(id ...))
        (quasisyntax/loc stx
          (define-values (id ...)
            #,(contract-free-variables-in-scope blame-id ctc-id #'expr sc))))]
     [(define-syntaxes (id ...) expr)
      (begin
        (add-free-identifiers sc #'(id ...))
        (quasisyntax/loc stx
          (define-syntaxes (id ...)
            #,(contract-free-variables-in-scope blame-id ctc-id #'expr sc))))]
     [(#%plain-lambda params expr0 expr ...)
      (syntax-parse #'params
                    [fs:formals
                     (syntax-case #'fs.params ()
                       [(p ...)
                        (let ([new-sc (create-scope-with-bindings sc #'fs.params)])
                          (quasisyntax/loc stx
                            (#%plain-lambda params
                                            (let-syntax ([p (make-set!-transformer
                                                             (lambda (stx)
                                                               (syntax-case stx (set!)
                                                                 [(set! i v) #`(set! #,(syntax-property #'p bound-property #t) v)]
                                                                 [(i a (... ...)) #`(#,(syntax-property #'p bound-property #t) a (... ...))]
                                                                 [i (identifier? #'i) (syntax-property #'p bound-property #t)])))] ...)
                                              #,(contract-free-variables-in-scope blame-id ctc-id #'expr0 new-sc)
                                              #,@(map (λ (expr) (contract-free-variables-in-scope blame-id ctc-id expr new-sc))
                                                      (syntax->list #'(expr ...)))))))])])]
     [(case-lambda (params expr0 expr ...) ...)
      (quasisyntax/loc stx 
        (case-lambda
          #,@(map (λ (stx)
                    (syntax-parse stx
                      [(params:formals expr0 expr ...)
                       (syntax-case #'params.params ()
                         [(p ...)
                          (let ([sc (create-scope-with-bindings sc #'params.params)])
                            (quasisyntax/loc stx
                              (params (let-syntax ([p (make-set!-transformer
                                                       (lambda (stx)
                                                         (syntax-case stx (set!)
                                                           [(set! i v) #`(set! #,(syntax-property #'p bound-property #t) v)]
                                                           [(i a (... ...)) #`(#,(syntax-property #'p bound-property #t) a (... ...))]
                                                           [i (identifier? #'i) (syntax-property #'p bound-property #t)])))] ...)
                                        #,(contract-free-variables-in-scope blame-id ctc-id #'expr0 sc)
                                        #,@(map (λ (e)
                                                  (contract-free-variables-in-scope blame-id ctc-id e sc))
                                                (syntax->list #'(expr ...)))))))])]))
                  (syntax->list #'((params expr0 expr ...) ...)))))]
     [(if expr0 expr1 expr2)
      (quasisyntax/loc stx
        (if #,(contract-free-variables-in-scope blame-id ctc-id #'expr0 sc)
            #,(contract-free-variables-in-scope blame-id ctc-id #'expr1 sc)
            #,(contract-free-variables-in-scope blame-id ctc-id #'expr2 sc)))]
     [(begin expr0 expr ...)
      (quasisyntax/loc stx
        (begin #,(contract-free-variables-in-scope blame-id ctc-id #'expr0 sc)
               #,@(map (λ (e) (contract-free-variables-in-scope blame-id ctc-id e sc))
                       (syntax->list #'(expr ...)))))]
     [(begin0 expr0 expr ...)
      (quasisyntax/loc stx
        (begin0 #,(contract-free-variables-in-scope blame-id ctc-id #'expr0 sc)
                #,@(map (λ (e) (contract-free-variables-in-scope blame-id ctc-id e sc))
                        (syntax->list #'(expr ...)))))]
     [(let-values ([(id ...) expr] ...) body0 body ...)
      (let ([body-scope (create-scope-with-bindings sc #'(id ... ...))])
        (quasisyntax/loc stx
          (let-values
              (#,@(map
                   (λ (stx)
                     (syntax-case stx ()
                       [[(id ...) expr]
                        #`[(id ...) #,(contract-free-variables-in-scope blame-id ctc-id #'expr sc)]]))
                   (syntax->list #'([(id ...) expr] ...))))
            #,(contract-free-variables-in-scope blame-id ctc-id #'body0 body-scope)
            #,@(map (λ (e) (contract-free-variables-in-scope blame-id ctc-id e body-scope))
                    (syntax->list  #'(body ...))))))]
     [(letrec-values ([(id ...) expr] ...) body0 body ...)
      (let ([sc (create-scope-with-bindings sc #'(id ... ...))])
        (quasisyntax/loc stx
          (letrec-values
           #,@(map
               (λ (stx)
                 (syntax-case stx ()
                   [[(id ...) expr]
                    #`[(id ...) #,(contract-free-variables-in-scope blame-id ctc-id #'expr sc)]]))
               (syntax->list #'([(id ...) expr] ...)))
           #,(contract-free-variables-in-scope blame-id ctc-id #'body0 sc)
           #,@(map (λ (e) (contract-free-variables-in-scope blame-id ctc-id e sc))
                   (syntax->list #'(body ...))))))]
     [(set! id expr)
      (if (bound? sc #'id)
          (syntax/loc stx id)
          (quasisyntax/loc stx (contract-id id ,blame-id #,ctc-id)))]
     [(void ids ...) #'(void ids ...)]
     [(quote datum)
      (syntax/loc stx (quote datum))]
     [(quote-syntax datum)
      (syntax/loc stx (quote-syntax datum))]
     [(with-continuation-mark expr0 expr1 expr2)
      (quasisyntax/loc stx
        (with-continuation-mark
          #,(contract-free-variables-in-scope blame-id ctc-id #'expr0 sc)
          #,(contract-free-variables-in-scope blame-id ctc-id #'expr1 sc)
          #,(contract-free-variables-in-scope blame-id ctc-id #'expr2 sc)))]
     [(#%plain-app expr0 expr ...)
      (quasisyntax/loc stx
        (#%plain-app #,(contract-free-variables-in-scope blame-id ctc-id #'expr0 sc)
                     #,@(map (λ (e) (contract-free-variables-in-scope blame-id ctc-id e sc))
                             (syntax->list #'(expr ...)))))]
     [id (identifier? #'id)
         (if (bound? sc #'id)
             (syntax/loc stx id)
             (quasisyntax/loc stx (contract-id id #,blame-id #,ctc-id)))]
     [(#%top . id)
      (if (bound? sc #'id)
          (syntax/loc stx (#%top . id))
          (quasisyntax/loc stx (#%top . (contract-id id #,blame-id #,ctc-id))))]
     [(#%variable-reference id)
      (raise-syntax-error #f "Unexpected #%variable-reference id" stx)]
     [(#%variable-reference (#%top . id))
      (raise-syntax-error #f "Unexpected form #%variable-reference (#%top . id)" stx)]
     [(#%variable-reference)
      (raise-syntax-error #f "Unexpected form #%variable-reference" stx)]
     [other (raise-syntax-error #f "Unexpected form (other)" stx)])))

(define-syntax (contract-id stx)
  (syntax-case stx ()
    [(contract-id id blame-id ctc-id)
     (let ([result
            (syntax/loc stx (with-contract #:region definition blame-id #:result ctc-id id))])
       result)]))

(define-syntax (define/contract/free-vars stx)
  (syntax-parse stx
    #:literals (define/contract/free-vars)
    [(define/contract/free-vars header:function-header res-ctc:expr var-ctc:expr body:expr ...+)
     (with-syntax ([(var-ctc-id) (generate-temporaries '(var-ctc))])
       (quasisyntax/loc stx
         (define/contract header.name
           res-ctc
           (let ([var-ctc-id var-ctc])
             (contract-free-variables header.name var-ctc-id
                                      #,(syntax/loc stx (define header body ...)))
             header.name))))]))

(define-syntax (make-define/contract/free-vars stx)
  (syntax-case stx ()
    [(make-define/contract/free-vars def-name res-ctc var-ctc)
     #'(define-syntax def-name
         (make-set!-transformer
          (lambda (stx)
            (syntax-parse stx
              #:literals (set!)
              [(set! define/c e)
               (raise-syntax-error 'set! (format "cannot mutate ~a" 'def-name))]
              [(define/c head:function-header body0 body (... ...))
               (syntax/loc stx
                 (define/contract/free-vars head res-ctc var-ctc body0 body (... ...)))]))))]))

(define-syntax (make-define/contract/free-vars/contract stx)
    (syntax-case stx ()
      [(make-define/contract/free-vars/contract def-name res-ctc var-ctc)
       #'(define-syntax def-name
           (make-set!-transformer
            (lambda (stx)
              (syntax-parse stx
                #:literals (set!)
                [(set! define/c e)
                 (raise-syntax-error 'set! (format "cannot mutate ~a" 'def-name))]
                [(define/c head:function-header add-res-ctc body0 body (... ...))
                 (syntax/loc stx
                   (define/contract/free-vars head (and/c add-res-ctc res-ctc) var-ctc body0 body (... ...)))]))))]))

(define-syntax (make-define/contract/free-vars/contract/free-vars stx)
    (syntax-case stx ()
      [(make-define/contract/free-vars/contract/free-vars def-name res-ctc var-ctc)
       #'(define-syntax def-name
           (make-set!-transformer
            (lambda (stx)
              (syntax-parse stx
                #:literals (set!)
                [(set! define/c e)
                 (raise-syntax-error 'set! (format "cannot mutate ~a" 'def-name))]
                [(define/c head:function-header add-res-ctc add-var-ctc body0 body (... ...))
                 (syntax/loc stx
                   (define/contract/free-vars head (and/c add-res-ctc res-ctc) (and/c add-var-ctc var-ctc) body0 body (... ...)))]))))]))
