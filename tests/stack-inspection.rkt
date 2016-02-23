#lang racket

(require authorization-contracts authorization-contracts/monitor/stack-inspection)

(require rackunit)
(require "test-utils.rkt")

(run stack-inspection #:prefix-in si)

(define foo (si:make-permission 'foo))
(define bar (si:make-permission 'bar))

(si:define/rights (A-useFoo) (foo)
  (si:check-permission/c foo)
  42)

(si:define/rights (A-do-privileged-useFoo) (foo)
  si:do-privileged/c
  (A-useFoo))

(si:define/rights (A-useFooIfTrue b) (foo)
  any/c
  (when b (A-do-privileged-useFoo)))

(si:define/rights (B-useFoo) (bar)
  (si:check-permission/c bar)
  42)

(si:define/rights (B-A-useFoo) (bar)
  any/c
  (A-useFoo))

(si:define/rights (A-grant-B-useFoo) (foo)
  si:do-privileged/c
  (B-useFoo))

(si:define/rights (B-A-grant-useFoo) (bar)
  any/c
  (A-useFooIfTrue #t))

(si:define/rights (A-grant-useFoo-with-context ctx) (foo)
  si:do-privileged/c
  (ctx A-useFoo))

(si:define/rights (make-A-context) (foo)
  (-> si:context/c)
  (λ (p) (p)))

(si:define/rights (make-privileged-A-context) (foo)
  si:do-privileged/c
  (make-A-context))

(si:define/rights (A-grant-useFoo-A-ctx) (foo)
  any/c
  (A-grant-useFoo-with-context (make-A-context)))

(si:define/rights (A-grant-useFoo-A-grant-ctx) (foo)
  any/c
  (A-grant-useFoo-with-context (make-privileged-A-context)))

(si:define/rights (make-B-context) (bar)
  (-> si:context/c)
  (λ (p) (p)))

(si:define/rights (make-privileged-B-context) (bar)
  si:do-privileged/c
  (make-B-context))

(si:define/rights (A-grant-useFoo-B-ctx) (bar)
  any/c
  (A-grant-useFoo-with-context (make-privileged-B-context)))

(define/contract (do-cheat)
  si:do-privileged/c
  (A-useFoo))

(define (cheater)
  ((make-privileged-A-context) do-cheat))

(timed-test-case-no-exn
 "with-perm"
 (λ () (A-useFooIfTrue #t)))

(timed-test-case-exn
 "no-perm"
 exn:fail:contract?
 (λ () (A-useFoo)))

(timed-test-case-exn
 "wrong-perm"
 exn:fail:contract?
 B-useFoo)

(timed-test-case-exn
 "no-perm-multiple-callers"
 exn:fail:contract?
 B-A-useFoo)

(timed-test-case-exn
 "do-privileged-unauthorized-callee"
 exn:fail:contract?
 A-grant-B-useFoo)

(timed-test-case-no-exn
 "do-privileged-authorized-callee"
 B-A-grant-useFoo)

(timed-test-case-exn
 "with-context-unauthorized"
 exn:fail:contract?
 A-grant-useFoo-B-ctx)

(timed-test-case-exn
 "with-context-unauthorized-but-static"
 exn:fail:contract?
 A-grant-useFoo-A-ctx)

(timed-test-case-no-exn
 "with-context-authorized"
 A-grant-useFoo-A-grant-ctx)

(timed-test-case-exn
 "closure-cheat"
 exn:fail:contract?
 cheater)
