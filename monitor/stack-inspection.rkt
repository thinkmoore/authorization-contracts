#lang racket

(require authorization-contracts)

(require (for-syntax syntax/to-string)
         (for-syntax racket/unit-exptime))

(provide stack-inspection)

(define active (dim 'active))
(define enable (dim 'enable))
(define static (dim 'static))

(define (use-static l r ll ds)
    (if (and (not (proj? l))
             (match r
               [(proj top _) #t]
               [_ #f]))
        (set (normalize (▹ l static)))
        (set)))

(define-monitor stack-inspection
  
  (monitor-interface make-permission permission?
                     check-permission/c enable-permission/c
                     do-privileged/c context/c
                     unprivileged/c privileged/c
                     coerce-to-unprivileged)

  (monitor-syntax-interface define/rights)
  
  
  (action #:search (list use-static search-delegates-left)

    [check-permission/c (perm)
     #:on-create (do-create)
     #:on-apply  (do-apply #:check (≽@ (▹ current-principal active) (▹ ⊤ perm) (▹ ⊤ perm)))]

    [enable-permission/c (perm)
     #:on-create (do-create)
     #:on-apply  (do-apply #:add (list (≽@ (▹ current-principal enable perm)
                                           (▹ current-principal static perm)
                                           current-principal)))]

    [privileged/c (perms)
     #:on-create (do-create #:check (≽@ current-principal ⊤ ⊤))
     #:on-apply  (let* ([callee (pcpl (gensym 'frame))]
                        [static-principal (normalize (disj (list->set (map (λ (p) (▹ ⊤ p)) perms))))]
                        [scoped-delegations
                         (list
                          (≽@ (▹ callee static) static-principal ⊤)
                          (≽@ (▹ callee enable) (▹ current-principal active) current-principal)
                          (≽@ (▹ callee active) (∨ (▹ callee enable) (▹ callee static)) callee))])
                   (do-apply #:add-scoped scoped-delegations
                             #:set-principal callee))]

    [do-privileged/c
     #:on-create (do-create)
     #:on-apply  (do-apply #:add-scoped (list (≽@ (▹ current-principal enable)
                                                  (▹ current-principal static)
                                                  current-principal)))]

    [context/c
     #:on-create (do-create #:add-lifetime (list (≽@ (← ⊤ current-delegations) ⊤ ⊤)))
     #:on-apply  (let* ([callee (pcpl (gensym 'frame))]
                        [closure-pcpl (→ closure-principal closure-delegations)]
                        [scoped-delegations
                         (list
                          (≽@ (▹ callee static) (▹ closure-pcpl active) ⊤)
                          (≽@ (▹ callee enable) (▹ current-principal active) current-principal)
                          (≽@ (▹ callee active) (∨ (▹ callee enable) (▹ callee static)) callee))])
                   (do-apply #:add-scoped scoped-delegations
                             #:set-principal callee))]

    [unprivileged/c
     #:on-create (do-create)
     #:on-apply  (do-apply #:set-principal ⊥)])

  (extra

   (define (make-permission name) (dim name))
   (define (permission? val) (dim? val))
   
   (define coerce-to-unprivileged
     (make-contract #:name "coerce-to-unprivileged"
                    #:projection
                    (λ (blame)
                      (λ (val)
                        (cond
                          [(privileged/c? val) val]
                          [(unprivileged/c? val) val]
                          [(context/c? val) val]
                          [(procedure? val)
                           (((contract-projection unprivileged/c) blame) val)]
                          [else val]))))))

  (syntax

   (make-define/contract/free-vars/contract define/auth/contract
                                           (membrane/c coerce-to-unprivileged
                                                       coerce-to-unprivileged)
                                           (membrane/c coerce-to-unprivileged
                                                       coerce-to-unprivileged))
   
   (define-syntax define/rights
     (make-set!-transformer
      (lambda (stx)
                (syntax-case stx (set!)
                  [(set! binder e) (raise-syntax-error 
                                    'set!
                                    (format "cannot mutate ~a" 'define/right))]
                  [(define/right (head . args) (right (... ...)) ctc body (... ...))
                   #'(define/auth/contract (head . args) (and/c ctc (privileged/c (list right (... ...))))
                       body (... ...))]
                  [(define/right head (right (... ...)) ctc body)
                   #'(define/auth head (and/c ctc (privileged/c (list right (... ...))))
                       body)]))))))


