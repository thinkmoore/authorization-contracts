#lang racket

(require authorization-contracts)

(provide ocap)


  (define invoke (dim 'invoke))
  (define caps (dim 'caps))

  (define (search-caps l r ll ds)
    (if (pcpl? l)
        (set (▹ l caps))
        (set)))

(define-monitor ocap

  (monitor-interface capability/c unprivileged-capability/c
                     capability/c? unprivileged-capability/c?
                     coerce-to-unprivileged-capability)

  (monitor-syntax-interface define/cap)
  
  (action #:search (list search-caps search-delegates-left)

    [capability/c
     #:on-create
     (let* ([child (pcpl (gensym 'capability))]
            [parent current-principal]
            [parenthood (≽@ (▹ parent caps) (▹ child invoke) child)]
            [endowment  (≽@ (▹ child caps) (→ (▹ parent caps) current-delegations) parent)]
            [validity   (≽@ (← parent current-delegations) parent parent)])
       (do-create #:add-lifetime (list parenthood endowment validity) #:closure-principal child))
     #:on-apply
     (let ([introductions
            (filter-map
             (λ (arg)
               (let ([arg-cap (cdr arg)])
                 (≽@ (▹ closure-principal caps) (▹ arg-cap invoke) current-principal)))
             closure-args)]
           [return-hook
            (λ (results)
              (let ([result-introductions
                     (filter-map
                      (λ (res)
                        (if res
                            (make-lifetime (≽ (▹ current-principal caps)
                                              (▹ (cdr res) invoke))
                                           closure-principal (car res))
                            #f))
                      results)])
                (do-return #:add result-introductions)))])
       (do-apply
        #:check (≽@ current-principal (▹ closure-principal invoke) (▹ closure-principal invoke))
        #:add-lifetime introductions
        #:set-principal closure-principal
        #:on-return return-hook))]

    [unprivileged-capability/c
     #:on-create
     (let* ([child (pcpl (gensym 'unprivileged))]
            [parent current-principal]
            [parenthood (≽@ (▹ parent caps) (▹ child invoke) child)])
       (do-create #:add-lifetime (list parenthood) #:closure-principal child))
     #:on-apply
     (let ([introductions
            (filter-map
             (λ (arg)
               (let ([arg-cap (get-principal arg)])
                 (≽@ (▹ closure-principal caps) (▹ arg-cap invoke) current-principal)))
             closure-args)]
           [return-hook
            (λ (results)
              (let ([result-introductions
                     (filter-map
                      (λ (res)
                        (let ([res-cap (get-principal res)])
                          (if res-cap
                              (make-lifetime (≽ (▹ current-principal caps)
                                                (▹ res-cap invoke))
                                             closure-principal res)
                              #f)))
                      results)])
                (do-return #:add result-introductions)))])
       (do-apply
        #:check (≽@ current-principal (▹ closure-principal invoke) (▹ closure-principal invoke))
        #:add-lifetime introductions
        #:set-principal closure-principal
        #:on-return return-hook))])

  (extra

   (define (get-principal val)
     (cond
       [(capability/c? val) (cdr (capability/c-authority val))]
       [(unprivileged-capability/c? val) (cdr (unprivileged-capability/c-authority val))]
       [else #f]))

   (define coerce-to-unprivileged-capability
     (make-contract #:name "coerce-to-unprivileged-capability"
                    #:projection
                    (λ (blame)
                     (λ (val)
                       (cond
                         [(capability/c? val) val]
                         [(unprivileged-capability/c? val) val]
                         [(procedure? val)
                          (((contract-projection unprivileged-capability/c) blame) val)]
                         [else val]))))))


  
(syntax

 (define-syntax define/cap
             (make-set!-transformer
              (λ (stx)
                (syntax-case stx (set!)
                  [(set! binder e) (raise-syntax-error
                                    'set!
                                    (format "cannot mutate ~a" 'binder))]
                  [(binder head body0 body (... ...))
                   #`(define/contract head
                       capability/c
                       body0 body (... ...))]))))))
