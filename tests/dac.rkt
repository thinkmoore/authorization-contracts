#lang racket

(require authorization-contracts authorization-contracts/monitor/dac)

(require rackunit)
(require "test-utils.rkt")

(run dac #:prefix-in dac)

(define/contract (run-as-userA thunk)
  (dac:make-user/c 'userA #f)
  (thunk))

(define/contract (run-as-userB thunk)
  (dac:make-user/c 'userB #f)
  (thunk))

(define run-as-userC
  (run-as-userA
   (λ ()
     (define/contract (run-as-userC thunk)
       (dac:make-user/c 'userC #f)
       (thunk))
     run-as-userC)))

(define objA
  (run-as-userA
   (λ ()
     (define/contract (objectA)
       (dac:make-object/c 'objectA #f)
       42)
     objectA)))

(define objA-setuser
  (run-as-userA
   (λ ()
     (define/contract (objectA-setuser thunk)
       (dac:make-object/c 'objectA-setuser #t)
       (thunk))
     objectA-setuser)))

(define/contract (deprivilege)
  (dac:make-user/c 'unprivileged #t)
  (void))

(define grant-with-args/c
  (make-contract
   #:name "grant-with-args/c"
   #:first-order (λ (val) (and (procedure? val)
                               (equal? (procedure-arity val) 2)))
   #:projection
   (λ (blame)
     (λ (val)
       (unless (and (procedure? val)
                    (equal? (procedure-arity val) 2))
         (raise-blame-error
          blame
          val
          (format "expected a procedure given: ~a" val)))
       (λ (object recipient)
         ((((contract-projection (dac:grant/c object recipient)) blame) val) object recipient))))))

(define revoke-with-args/c
  (make-contract
   #:name "revoke-with-args/c"
   #:first-order (λ (val) (and (procedure? val)
                               (equal? (procedure-arity val) 2)))
   #:projection
   (λ (blame)
     (λ (val)
       (unless (and (procedure? val)
                    (equal? (procedure-arity val) 2))
         (raise-blame-error
          blame
          val
          (format "expected a procedure given: ~a" val)))
       (λ (object recipient)
         ((((contract-projection (dac:revoke/c object recipient)) blame) val) object recipient))))))

(define/contract (do-grant object recipient)
  grant-with-args/c
  (void))

(do-grant run-as-userA deprivilege)
(do-grant run-as-userB deprivilege)

(deprivilege)

(timed-test-case-exn
 "no-rights"
 exn:fail:contract?
 (λ () (run-as-userB objA)))

(timed-test-case-exn
 "closure-no-rights"
 exn:fail:contract?
 (λ () (run-as-userB (λ () (objA-setuser objA)))))

(timed-test-case-no-exn
 "closure-with-rights"
 (λ ()
   (run-as-userA (λ () (do-grant objA-setuser run-as-userB)))
   (run-as-userB (λ () (objA-setuser objA)))))

(timed-test-case-no-exn
 "with-rights"
 (λ () (run-as-userA objA)))

(timed-test-case-no-exn
 "with-granted-rights"
 (λ ()
   (run-as-userA (λ () (do-grant objA run-as-userB)))
   (run-as-userB objA)))

(timed-test-case-exn
 "unprivileged"
 exn:fail:contract?
 objA)

(timed-test-case-exn
 "still-no-rights"
 exn:fail:contract?
 (λ () (run-as-userC objA)))

(timed-test-case-exn
 "dynamic-extent"
 exn:fail:contract?
 (λ () (run-as-userA (λ () (run-as-userC objA)))))
