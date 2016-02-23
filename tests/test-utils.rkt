#lang racket

(provide timed-test-case-no-exn timed-test-case-exn)

(require rackunit math/statistics)

(define (print-results sys real gbg)
  (printf "System time:~n  mean: ~ams\tsd: ~ams\tmin: ~ams\tmax: ~ams~n"
          (round (mean sys))
          (round (stddev sys))
          (round (apply min sys))
          (round (apply max sys)))
  (printf "Real time:~n  mean: ~ams\tsd: ~ams\tmin: ~ams\tmax: ~ams~n"
          (round (mean real))
          (round (stddev real))
          (round (apply min real))
          (round (apply max real)))
  (printf "GC time:~n  mean: ~ams\tsd: ~ams\tmin: ~ams\tmax: ~ams~n~n"
          (round (mean gbg))
          (round (stddev gbg))
          (round (apply min gbg))
          (round (apply max gbg))))

(define iterations 10)

(define-syntax timed-test-case-no-exn
  (syntax-rules (iterations)
    [(_ name body)
     (timed-test-case-no-exn #:iters iterations name body)]
    [(_ #:iters iters name body)
     (test-case
      name
      (printf "starting test ~a~n" name)
      (let-values ([(sys real gbg)
             (for/fold ([sys  empty]
                        [real empty]
                        [gbg  empty])
                       ([i (in-range iters)])
               (let-values ([(res s r g) (time-apply check-not-exn (list body))])
                 (values (cons s sys) (cons r real) (cons g gbg))))])
        (print-results sys real gbg)))]))

(define-syntax timed-test-case-exn
  (syntax-rules (iterations)
    [(_ name exn body)
     (timed-test-case-exn #:iters iterations name exn body)]
    [(_ #:iters iters name exn body)
     (test-case
      name
      (printf "starting test ~a~n" name)
      (let-values ([(sys real gbg)
             (for/fold ([sys  empty]
                        [real empty]
                        [gbg  empty])
                       ([i (in-range iters)])
               (let-values ([(res s r g) (time-apply check-exn (list exn body))])
                 (values (cons s sys) (cons r real) (cons g gbg))))])
        (print-results sys real gbg)))]))
