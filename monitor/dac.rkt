#lang racket

(require authorization-contracts)

(provide dac)

(define use (dim 'use))

(define invoke (dim 'invoke))


(define-monitor dac
  
  (monitor-interface make-object/c make-user/c grant/c revoke/c)
  
  (action
   
   [make-object/c (name setuser)
                  #:on-create (do-create #:closure-principal (▹ current-principal (dim name)))
                  #:on-apply  (let ([owner  (proj-principal closure-principal)]
                                    [objdim (set-first (proj-dims closure-principal))])
                                (do-apply #:check (≽@ current-principal
                                                      (▹ closure-principal objdim use)
                                                      (▹ closure-principal objdim use))
                                          #:set-principal (if setuser owner #f)))]
   
   [make-user/c (name set-auth)
                #:on-create (let ([new-pcpl (pcpl name)])
                              (do-create #:add-lifetime (list (≽@ current-principal
                                                                  (▹ new-pcpl use invoke)
                                                                  new-pcpl))
                                         #:closure-principal new-pcpl))
                #:on-apply (do-apply #:check (≽@ current-principal
                                                 (▹ closure-principal use invoke)
                                                 closure-principal)
                                     #:set!-principal (if set-auth closure-principal #f)
                                     #:set-principal  (if set-auth #f closure-principal))]
   
   [grant/c (object recipient)
            #:on-create (do-create)
            #:on-apply  (let ([recipient-principal (recipient-principal recipient)]
                              [object-principal    (object-principal object)])
                          (do-apply #:add (list (make-lifetime (≽ recipient-principal
                                                                  object-principal)
                                                               current-principal
                                                               object))))]
   
   [revoke/c (object recipient)
             #:on-create (do-create)
             #:on-apply  (let ([recipient-principal (normalize (▹ (recipient-principal recipient) use))]
                               [object-principal    (object-principal object)])
                           (define (equal-recipient? p)
                             (equal? p recipient-principal))
                           (define (matching-target? p)
                             (equal? p object-principal))
                           (define (to-remove delegations current)
                             (filter (λ (d)
                                       (match d
                                         [(labeled (actsfor (? equal-recipient? l) (? matching-target? r)) ll)
                                          #:when (acts-for? current ll ll)
                                          #t]
                                         [_ #f]))))
                           (do-apply #:remove (to-remove current-delegations current-principal)))])
  
  (extra
   
   (define (recipient-principal recipient)
     (cdr (make-user/c-authority recipient)))
   
   
   (define (object-principal object)
     (cond
       [(make-user/c? object)
        (▹ (cdr (make-user/c-authority object)) invoke)]
       [(make-object/c? object)
        (let* ([pcpl (cdr (make-object/c-authority object))])
          (normalize (▹ pcpl use)))]))))

