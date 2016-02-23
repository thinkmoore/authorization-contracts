#lang racket

(provide define-monitor run
         (except-out (all-from-out "authority-contracts.rkt")
                     define-authority-contracts))

(require "authority-contracts.rkt")

(define-for-syntax (build-names names source)
  (map
   (λ (name)
     (datum->syntax 
      source
      name)) 
   (syntax->datum names)))

(define-for-syntax (build-prefixed-names names prefix source)
  (map
   (λ (name)
     (datum->syntax 
      source
      (string->symbol
       (string-append 
         (symbol->string (syntax->datum prefix))
         ":"
         (symbol->string name)))))
   (syntax->datum names)))

(define-syntax (run stx)
  (syntax-case stx ()
    [(run monitor) #'(monitor)]
    [(run monitor #:prefix-in prefix) #'(monitor prefix)]))

(define-syntax build-monitor
  (syntax-rules ()
    [(build-monitor monitor names package)
     (define-syntax (monitor stx)
       (syntax-case stx ()
         [(monitor)
          (with-syntax ([names (build-names #'names #'monitor)])
            #'(define-values names
                (package)))]
         [(monitor prefix)
          (with-syntax ([names (build-prefixed-names #'names #'prefix #'monitor)])
            #'(define-values names
                (package)))]))]
    [(build-monitor monitor names snames  package (s ...))
     (define-syntax (monitor stx)
       (syntax-case stx ()
         [(monitor)
          (with-syntax ([names (build-names #'names #'monitor)]
                        [snames (build-names #'snames #'monitor)])
            #`(begin
                (define-values names
                  (package))
                s ...))]
         [(monitor prefix)
          (with-syntax ([names (build-prefixed-names #'names #'prefix #'monitor)]
                        [snames (build-prefixed-names #'snames #'prefix #'monitor)])
            #'(begin
                (define-values names
                  (package))
                  s ...))]))]))
     
    

(define-syntax (pack stx)
  (syntax-case stx ()
    [(_ (id ...) (action ...) (extra ...))
     (with-syntax ([package (datum->syntax stx 'package)])
     #`(define (package)
         (define-authority-contracts
           action ...)
         extra ...
         (values id ...)))]))

(define-syntax (define-monitor stx)
  (syntax-case stx (monitor-interface action extra syntax)
    [(_ name
        (monitor-interface id ...)
        (action a ...))
     #'(begin
         (pack (id ...) (a ...) ())
         (build-monitor name (id ...) package))]
    [(_ name
        (monitor-interface id ...)
        (action a ...)
        (extra ae ...))
     #'(begin
         (pack (id ...) (a ...) (ae ...))
         (build-monitor name (id ...) package))]
    [(_ name
        (monitor-interface id ...)
        (monitor-syntax-interface sid ...)
        (action a ...)
        (syntax s ...))
     #'(begin
         (pack (id ...) (a ...) ())
         (build-monitor name (id ...) (sid ...) package (s ...)))]
    [(_ name
        (monitor-interface id ...)
        (monitor-syntax-interface sid ...)
        (action a ...)
        (extra e ...)
        (syntax s ...))
     #'(begin
         (pack (id ...) (a ...) (e ...))
         (build-monitor name (id ...) (sid ...) package (s ...)))]))




