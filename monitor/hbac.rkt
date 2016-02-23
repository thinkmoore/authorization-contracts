#lang racket

(require authorization-contracts)

(require (prefix-in control: racket/control))

(require (for-syntax syntax/to-string)
         (for-syntax racket/unit-exptime))

(provide history-based)

(define active  (dim 'active))
(define enable  (dim 'enable))
(define static  (dim 'static))

(define (use-static l r ll ds)
    (if (and (not (proj? l))
             (match r
               [(proj top _) #t]
               [_ #f]))
        (set (normalize (▹ l static)))
        (set)))

(define-monitor history-based
  
 (monitor-interface make-permission permission?
                    check-permission/c grant/c accept/c
                    unprivileged/c privileged/c
                    coerce-to-unprivileged)

  (monitor-syntax-interface define/rights)
  
  

  (action #:search (list use-static search-delegates-left)

    [check-permission/c (perm)
     #:on-create (do-create)
     #:on-apply  (do-apply #:check (≽@ (▹ current-principal active) (▹ ⊤ perm) (▹ ⊤ perm)))]
    
    [privileged/c (perms)
     #:on-create (do-create #:check (≽@ current-principal ⊤ ⊤))
     #:on-apply  (let* ([callee (pcpl (gensym 'frame))]
                        [static-principal (normalize (disj (list->set (map (λ (p) (▹ ⊤ p)) perms))))]
                        [to-remove
                         (filter
                          (match-lambda
                            [(labeled (actsfor l r) ll)
                             #:when (and (equal? l (normalize (▹ current-principal enable)))
                                         (not (equal? r (normalize (▹ current-principal static)))))
                             #t]
                            [_ #f])
                          (delegation-set->list current-delegations))]
                        [to-add
                         (cons
                          (≽@ (▹ callee enable) (▹ current-principal active) current-principal)
                          (map (match-lambda
                                 [(labeled (actsfor l r) ll)
                                  (labeled (actsfor l (normalize (∨ r (▹ callee static)))) ll)])
                               to-remove))]
                        [to-scope
                         (list
                          (≽@ (▹ callee static) static-principal ⊤)
                          (≽@ (▹ callee active) (∨ (▹ callee enable) (▹ callee static)) callee))])
                   (do-apply #:add to-add
                             #:remove to-remove
                             #:add-scoped to-scope
                             #:set-principal callee))]
    [grant/c
     #:on-create (do-create)
     #:on-apply  (do-apply #:add-scoped (list (≽@ (▹ current-principal enable)
                                                  (▹ current-principal static)
                                                  current-principal)))]
    [accept-context/c
     #:on-create (do-create #:add-lifetime (list (≽@ (← ⊤ current-delegations) ⊤ ⊤)))
     #:on-apply  (do-apply #:add    (delegation-set->list closure-delegations)
                           #:remove (delegation-set->list current-delegations)
                           #:set-principal closure-principal)]
    [unprivileged/c
     #:on-create (do-create)
     #:on-apply  (do-apply #:set-principal ⊥)])

 (extra

  (define (make-permission name) (dim name))

  (define (permission? val) (dim? val))
  
  (define accept/c
    (make-contract #:name "accept/c"
                   #:projection
                   (λ (blame)
                     (λ (val)
                       (make-keyword-procedure
                        (λ (kwds kwd-args . other-args)
                          (call/cc
                           (λ (k) (let ([cont (with-contract #:region expression
                                                accept/c
                                                #:result accept-context/c
                                                k)])
                                    (call-with-values
                                     (λ () (keyword-apply val kwds kwd-args other-args))
                                     cont)))))
                        (λ args
                          (call/cc
                           (λ (k) (let ([cont (with-contract #:region expression
                                                accept/c
                                                #:result accept-context/c
                                                k)])
                                    (call-with-values
                                     (λ () (apply val args))
                                     cont))))))))))
  
  
  (define coerce-to-unprivileged
    (make-contract #:name "coerce-to-unprivileged"
                   #:projection
                   (λ (blame)
                     (λ (val)
                       (cond
                         [(unprivileged/c? val) val]
                         [(privileged/c? val) val]
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
        [(set! define/rights e) (raise-syntax-error 
                          'set!
                          (format "cannot mutate ~a" 'define/rights))]
        [(define/rights (head . args) (right (... ...)) ctc body (... ...))
         #'(define/auth/contract (head . args)
             (and/c ctc (privileged/c (list right (... ...))))
             body (... ...))]
        [(define/rights head (right (... ...)) ctc body)
         #'(define/auth head
             (and/c ctc (privileged/c (list right (... ...))))
             body)]))))))
