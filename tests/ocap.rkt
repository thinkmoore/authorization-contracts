#lang racket

(require authorization-contracts authorization-contracts/monitor/ocap)

(require "test-utils.rkt")

(run ocap)

(define/cap (test-parenthood)
  (define/cap (child) 0)
  (child))

(define/cap (test-endowment-positive)
  (define/cap (a-child) 0)
  (define/cap (b-child) (a-child))
  (b-child))

(define/cap (test-endowment-negative)
  (define/cap (a-child) (b-child))
  (define/cap (b-child) 0)
  (a-child))

(define/cap (test-introduction-positive)
  (define/cap (caller proc)
    (proc))
  (define/cap (callee) 0)
  (caller callee))

(define/cap (test-introduction-negative)
  (let ([cheat #f])
    (define/cap (caller)
      (cheat))
    (define/cap (callee) 0)
    (set! cheat callee)
    (caller)))

(define/cap (test-introduction-return)
  (define/cap (callee)
    (define/cap (child) 0)
    child)
  (let ([child (callee)])
    (child)))

(define/cap (test-introduction-return-negative-setup)
  (define/cap (caller f)
    (hidden))
  (define/cap (hidden) 0)
  (define/cap (callee) 0)
  (caller #f))

(define/cap (test-introduction-return-negative)
  (define/cap (caller f)
    (f)
    (hidden))
  (define/cap (hidden) 0)
  (define/cap (callee) 0)
  (caller callee))

(define/cap (test-mutual-hidden-endowment call-a)
  (let ([childA-ref #f]
        [childB-ref #f])
    (define/cap (make-childA)
      (define/cap (childA call?)
        (when call? (childB-ref #f)))
      (set! childA-ref childA))
    (define/cap (make-childB)
      (define/cap (childB call?)
        (when call? (childA-ref #f)))
      (set! childB-ref childB))
    (make-childA)
    (make-childB)
    (if call-a
        (childA-ref #t)
        (childB-ref #t))))

(timed-test-case-no-exn
 "parenthood"
 test-parenthood)

(timed-test-case-no-exn
 "endowment-positive"
 test-endowment-positive)

(timed-test-case-exn
 "endowment-negative"
 exn:fail:contract?
 test-endowment-negative)

(timed-test-case-no-exn
 "introduction-positive"
 test-introduction-positive)

(timed-test-case-exn
 "introduction-negative"
 exn:fail:contract?
 test-introduction-negative)

(collect-garbage)

(timed-test-case-no-exn
 "introduction-return"
 test-introduction-return)

(collect-garbage)

(timed-test-case-exn
 "introduction-return-negative-setup"
 exn:fail:contract?
 test-introduction-return-negative-setup)

(collect-garbage)

(timed-test-case-exn
 "introduction-return-negative"
 exn:fail:contract?
 test-introduction-return-negative)

(collect-garbage)

(timed-test-case-exn
 "mutually-hidden-children-A"
 exn:fail:contract?
 (λ () (test-mutual-hidden-endowment #t)))

(collect-garbage)

(timed-test-case-exn
 "mutually-hidden-children-B"
 exn:fail:contract?
 (λ () (test-mutual-hidden-endowment #f)))
