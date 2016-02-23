#lang racket

(require authorization-contracts authorization-contracts/monitor/hbac)

(require rackunit)
(require "test-utils.rkt")

(run history-based #:prefix-in hb)

(define foo (hb:make-permission 'foo))
(define bar (hb:make-permission 'bar))

(hb:define/rights (asFoo-useFoo) (foo)
  (hb:check-permission/c foo)
  42)

(hb:define/rights (asBar-useBar) (bar)
  (hb:check-permission/c bar)
  42)

(hb:define/rights (asBar-useFoo) (bar)
  any/c
  (asFoo-useFoo))

(hb:define/rights (asFoo-grant-asFoo-useFoo) (foo)
  hb:grant/c
  (asFoo-useFoo))

(hb:define/rights (asFoo-grant-asBar-useFoo) (foo)
  hb:grant/c
  (asBar-useFoo))

(hb:define/rights (asBar-grant-asBar-useBar) (bar)
  hb:grant/c
  (asBar-useBar))

(hb:define/rights (asBar-useBar-then-useFoo) (foo)
  any/c
  (asBar-grant-asBar-useBar)
  (asFoo-useFoo))

(hb:define/rights (accept-asBar-grant-asBar-useBar) (foo)
  hb:accept/c
  (asBar-grant-asBar-useBar))

(hb:define/rights (accept-asBar-useBar-then-useFoo) (foo)
  any/c
  (accept-asBar-grant-asBar-useBar)
  (asFoo-useFoo))

(hb:define/rights (asFoo-grant-after-asBar) (foo)
  hb:grant/c
  (asBar-useBar-then-useFoo))

(hb:define/rights (asFoo-grant-after-accept-asBar) (foo)
  any/c
  (accept-asBar-grant-asBar-useBar)
  (asFoo-grant-asFoo-useFoo))

(timed-test-case-exn
 "disabled permissions"
 exn:fail:contract?
 asFoo-useFoo)

(timed-test-case-exn
 "no permissions"
 exn:fail:contract?
 asBar-useFoo)

(timed-test-case-no-exn
 "enabled permissions"
 asFoo-grant-asFoo-useFoo)

(timed-test-case-exn
 "grant but no permission"
 exn:fail:contract?
 asFoo-grant-asBar-useFoo)

(timed-test-case-exn
 "history"
 exn:fail:contract?
 asFoo-grant-after-asBar)

(timed-test-case-no-exn
 "accept"
 asFoo-grant-after-accept-asBar)
