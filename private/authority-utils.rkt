#lang racket

(require (for-syntax syntax/parse)
         (for-syntax syntax/define)
         (for-syntax syntax/boundmap)
         (for-syntax syntax/kerncase)
         (for-syntax racket/unit-exptime)
         (for-template racket/base)
         "arr-a.rkt")


(provide ->a
         make-define/a
         build-external-defines
         build-external-defines-no-prefix
         (for-syntax get-names build-name))

(define-for-syntax get-names
  (λ unit-sigs
    (define (get-names id) (let-values ([(a b c d) (signature-members id id)]) b))
    (foldr (λ (f r) (append (get-names f) r)) '() unit-sigs)))

(define-for-syntax (build-name name base pre?)
  (datum->syntax
   name
   (string->symbol
    (if pre?
        (string-append
         (symbol->string (syntax->datum name))
         base)
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
                                       (string-append ":" (symbol->string x)) #t))
                                    (syntax->datum #'names))]
                   [(name ...) #'names])
       #'(begin
           (define new-name name) ...))]))

(define-syntax (build-external-defines-no-prefix stx)
  (syntax-case stx ()
    [(_ names)
     (with-syntax ([(name ...) #'names])
       #'(begin
           (define name name) ...))]))

(define-for-syntax (merge t)
  (define m (make-module-identifier-mapping))
  (reverse
   (let loop ([t t] [a null])
     (cond
       [(null? t) a]
       [(identifier? t)
        (if (module-identifier-mapping-get m t (lambda () #f))
            a
            (begin
              (module-identifier-mapping-put! m t #t)
              (cons t a)))]
       [(pair? t) (loop (cdr t) (loop (car t) a))]
       [else (error "internal error")]))))

(define-for-syntax (module-bindings e)
  (define code-insp 
    (variable-reference->module-declaration-inspector (#%variable-reference)))    
  (merge
   (let module-bindings ([e e])
     (kernel-syntax-case (syntax-disarm e code-insp) #f
       [id
        (identifier? #'id)
        (if (list? (identifier-binding #'id))
            (list #'id)
            null)]
       [(#%top . id) null]
       [(quote q) null]
       [(quote-syntax q) null]
       [(#%plain-lambda formals expr ...)
        (map module-bindings (syntax->list #'(expr ...)))]
       [(case-lambda [formals expr ...] ...)
        (map module-bindings (syntax->list
                              #'((#%plain-lambda formals expr ...) ...)))]
       [(let-values ([(id ...) rhs] ...) expr ...)
        (cons (module-bindings #'(#%plain-lambda (id ... ...) expr ...))
              (map module-bindings (syntax->list #'(rhs ...))))]
       [(letrec-values ([(id ...) rhs] ...) expr ...)
        (module-bindings #'(#%plain-lambda (id ... ...) rhs ... expr ...))]
       [(letrec-syntaxes+values stx-bindings ([(id ...) rhs] ...) expr ...)
        (module-bindings #'(#%plain-lambda (id ... ...) rhs ... expr ...))]
       [(kw expr ...)
        (ormap (lambda (k) (free-identifier=? k #'kw))
               (list #'if #'begin #'begin0 #'set! #'#%plain-app #'#%expression
                     #'#%variable-reference #'with-continuation-mark))
        (map module-bindings (syntax->list #'(expr ...)))]
       [(define-values (id ...) expr)
        (module-bindings #'expr)]
       [(kw . _)
        (error 'module-bindings "unknown core form: ~a" (syntax->datum #'kw))]))))

(define-for-syntax (simplify stx)
  (syntax-case stx ()
    [(_ name (head args) res-ctc var-ctc body0 body ...)
     #'(define (head args) body0 body ...)]
    [(_ name id res-ctc var-ctc body)
     #'(define id body)]))

(define-for-syntax (get-module-bindings stx)
  (module-bindings 
   (local-expand 
    (simplify stx) 
    'top-level 
    '())))

(define-syntax (pre-define/a/pure stx)  
  (syntax-parse stx
    [(pre-define/a def-name:id name:id res-ctc var-ctc body)
     (with-syntax ([(free-var ...) (get-module-bindings stx)])
       (syntax/loc stx
         (define name
           (let-syntax ([free-var (make-set!-transformer
                                   (lambda (stx)
                                     (syntax-case stx (set!)
                                       [(set! i arg)
                                        (raise-syntax-error  (syntax->datum #'def-name)
                                                             "cannot mutate module binding"
                                                             #'i)]
                                       [id (identifier? #'id)  #'free-var])))] 
                        ...)
             (with-contract #:region definition name
                            ([name res-ctc])
                            #:freevars ([free-var var-ctc] ...)
                            (define name body))
             name))))]
    [(pre-define/a def-name:id name:id res-ctc var-ctc body0 body ...)
     (raise-syntax-error (syntax->datum #'def-name)
                         "multiple expressions after identifier")]
    [(pre-define/a def-name:id name+args res-ctc var-ctc body0 body ...)
     (let-values ([(name body-expr)
                   (normalize-definition
                    (datum->syntax #'define-stx 
                                   (list* (syntax->datum #'def-name)
                                          #'name+args
                                          #'body0
                                          #'(body ...)))
                    #'lambda #t #t)])
       (with-syntax ([name name]
                     [body-expr body-expr]
                     [(free-var ...) (get-module-bindings stx)])
         (syntax/loc stx
           (define name
             (let-syntax ([free-var (make-set!-transformer
                                     (lambda (stx)
                                       (syntax-case stx (set!)
                                         [(set! i arg)
                                          (raise-syntax-error  (syntax->datum #'def-name)
                                                               "cannot mutate module binding"
                                                               #'i)]
                                         [id (identifier? #'id)  #'free-var])))] 
                          ...)
               (with-contract #:region function name
                              ([name res-ctc])
                              #:freevars ([free-var var-ctc] ...)
                              (define name body-expr))
               name)))))]))

(define-syntax (pre-define/a stx)  
  (syntax-parse stx
    [(pre-define/a def-name:id name:id res-ctc var-ctc body)
     (with-syntax ([(free-var ...) (get-module-bindings stx)]
                   [res-ctc (values #'res-ctc)]
                   [var-ctc (values #'var-ctc)])
       (syntax/loc stx
         (with-contract #:region definition name
                        ([name res-ctc])
                        #:freevars ([free-var var-ctc] ...)
                        (define name body))))]
    [(pre-define/a/pure def-name:id name:id res-ctc var-ctc body0 body ...)
     (raise-syntax-error (syntax->datum #'def-name)
                         "multiple expressions after identifier")]
    [(pre-define/a/pure def-name:id name+args res-ctc var-ctc body0 body ...)
     (let-values ([(name body-expr)
                   (normalize-definition
                    (datum->syntax #'define-stx 
                                   (list* (syntax->datum #'def-name)
                                          #'name+args
                                          #'body0
                                          #'(body ...)))
                    #'lambda #t #t)])
       (with-syntax ([name name]
                     [body-expr body-expr]
                     [(free-var ...) (get-module-bindings stx)])
         (syntax/loc stx
           (define name
             (let ()
               (with-contract #:region function name
                              ([name res-ctc])
                              #:freevars ([free-var var-ctc] ...)
                              (define name body-expr))
               name)))))]))

(define-for-syntax (context-check id)
  (let ([context (syntax-local-context)])
    (when (or (eq? context 'expression)
              (list? context))
      (raise-syntax-error 
       id
       "not in a top-level, module or module-begin context"))))

(define-syntax (make-define/a stx)
  (context-check 'make-define/a)
  (syntax-case stx ()
    [(make-define/a def-name res-ctc var-ctc #:pure)
     #'(define-syntax def-name
         (make-set!-transformer
          (lambda (stx)
            (syntax-case stx (set!)
              [(set! define/a e)
               (raise-syntax-error 'set!c(format "cannot mutate ~a" 'def-name))]
              [(define/a head body (... ...))
               (with-syntax ([_ (context-check 'def-name)])
                 #'(pre-define/a/pure define/a head res-ctc var-ctc body (... ...)))]
              [define/a 
                (raise-syntax-error 'def-name "bad syntax")]))))]
    [(make-define/a def-name res-ctc var-ctc)
     #'(define-syntax def-name
         (make-set!-transformer
          (lambda (stx)
            (syntax-case stx (set!)
              [(set! define/a e) 
               (raise-syntax-error 'set! (format "cannot mutate ~a" 'def-name))]
              [(define/a head body (... ...))
               (with-syntax ([_ (context-check 'def-name)])
                 #'(pre-define/a define/a head res-ctc var-ctc body (... ...)))]
              [define/a 
                (raise-syntax-error 'def-name "bad syntax")]))))]))
