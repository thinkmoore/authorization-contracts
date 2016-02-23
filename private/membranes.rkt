#lang racket

(provide membrane/c)

(define (membrane-name ctc)
  (build-compound-type-name 'membrane/c
                            (contract-name (membrane-ctc-inside ctc))
                            (contract-name (membrane-ctc-outside ctc))))

(define (membrane/c inside outside #:allow [allow (λ (v) #f)])
  (membrane inside outside allow))

(struct membrane (ctc-inside ctc-outside allow)
  #:property prop:contract
  (build-contract-property
   #:name 
   membrane-name
   #:first-order
   (λ (ctc)
     (λ (val)
       ((contract-first-order (membrane-ctc-inside ctc)) val)))
   #:projection
   (λ (ctc)
     (λ (blame)
       (λ (val)
         (let ([wrapped (wrap val ctc blame (membrane-allow ctc))])
           (contract-pos (membrane-ctc-inside ctc) blame wrapped)))))))

(define (membrane-swap m)
  (membrane (membrane-ctc-outside m) (membrane-ctc-inside m) (membrane-allow m)))

(define (contract-pos ctc blame val)
  (((contract-projection ctc) blame) val))

(define (contract-neg ctc blame val)
  (((contract-projection (membrane-swap ctc)) (blame-swap blame)) val))

(define (first-order? val)
  (or (number? val)
      (string? val)
      (symbol? val)
      (boolean? val)
      (null? val)
      (void? val)))

(define (wrap val ctc blame allowed)
  (cond [(allowed val) val]
        [(procedure? val) (procedure-wrapper val ctc blame)]
        [(vector? val) (vector-wrapper val ctc blame)]
        [(hash? val) (hash-wrapper val ctc blame)]
        [(struct? val) (struct-wrapper val ctc blame)]
        [(box? val) (box-wrapper val ctc blame)]
        [(channel? val) (channel-wrapper val ctc blame)]
        [(continuation-prompt-tag? val) (prompt-wrapper val ctc blame)]
        [(continuation-mark-key? val) (mark-wrapper val ctc blame)]
        [(list? val) (list-wrapper val ctc blame)]
        [(cons? val) (cons-wrapper val ctc blame)]
        [(first-order? val) val]
        [else
         (raise-blame-error blame val
                            "Value ~e cannot flow through membrane!"
                            val)]))

(define (procedure-wrapper val ctc blame)
  (impersonate-procedure
   val
   (make-keyword-procedure
    (λ (kws kw-args . args)
      (let* ([wrap-arg (λ (arg) (contract-neg ctc blame arg))]
             [wrap-result (λ (res) (contract-pos ctc blame res))]
             [wrapped-kw-args (map wrap-arg kw-args)]
             [wrapped-args (map wrap-arg args)]
             [result-wrapper (λ results (apply values (map wrap-result results)))])
        (apply values (list* result-wrapper wrapped-kw-args wrapped-args))))
    (λ args
      (let* ([wrap-arg (λ (arg) (contract-neg ctc blame arg))]
             [wrap-result (λ (res) (contract-pos ctc blame res))]
             [wrapped-args (map wrap-arg args)]
             [result-wrapper (λ results (apply values (map wrap-result results)))])
        (apply values (cons result-wrapper wrapped-args)))))))

(define (vector-wrapper val ctc blame)
  (impersonate-vector
   val
   (λ (vec ind get) (contract-pos ctc blame get))
   (λ (vec ind put) (contract-neg ctc blame put))))

(define (hash-wrapper val ctc blame)
  (impersonate-hash
   val
   (λ (hash key)
     (let ([wrapped-key (contract-neg ctc blame key)]
           [result-wrapper (λ (hash key res) (contract-pos ctc blame res))])
       (values wrapped-key result-wrapper)))
   (λ (hash key val)
     (let ([wrapped-key (contract-neg ctc blame key)]
           [wrapped-val (contract-neg ctc blame val)])
       (values wrapped-key wrapped-val)))
   (λ (hash key)
     (contract-neg ctc blame key))
   (λ (hash key)
     (contract-pos ctc blame key))
   #f))

(define (struct-wrapper val ctc blame)
  (define (opaque-error)
    (raise-blame-error
     (blame-swap blame) val
     "Opaque struct ~a cannot flow through membrane!"
     val))
  (define (extract-functions struct-type)
    (define-values (sym init auto ref set! imms par skip?)
      (struct-type-info type))
    (define-values (fun/chap-list _)
      (for/fold ([res null]
                 [imms imms])
                ([n (in-range (+ init auto))])
        (if (and (pair? imms) (= (first imms) n))
            ;; field is immutable
            (raise-blame-error
             (blame-swap blame) val
             "Struct ~a with immutable fields cannot flow through membrane!"
             val)
            ;; field is mutable
            (values
             (list* (make-struct-field-accessor ref n)
                    (λ (s v) (contract-pos ctc blame v))
                    (make-struct-field-mutator set! n)
                    (λ (s v) (contract-neg ctc blame v))
                    res)
             imms))))
    (cond
      [skip? (opaque-error)]
      [par (cons fun/chap-list (extract-functions par))]
      [else fun/chap-list]))
  (define-values (type skipped?) (struct-info val))
  (when skipped? (opaque-error))
  (apply impersonate-struct val (extract-functions type)))

(define (box-wrapper val ctc blame)
  (impersonate-box
   val
   (λ (box res) (contract-pos ctc blame res))
   (λ (box val) (contract-neg ctc blame val))))

(define (channel-wrapper val ctc blame)
  (impersonate-channel
   val
   (λ (channel) (values channel (λ (res) (contract-pos ctc blame res))))
   (λ (channel val) (contract-neg ctc blame val))))

(define (prompt-wrapper val ctc blame)
  (impersonate-prompt-tag
   val
   (λ (thunk) (contract-neg ctc blame val))
   (λ vals (apply values (map (λ (v) (contract-neg ctc blame v)) vals)))
   (λ vals (apply values (map (λ (v) (contract-neg ctc blame v)) vals)))))

(define (mark-wrapper val ctc blame)
  (impersonate-continuation-mark-key
   val
   (λ (res) (contract-pos ctc blame res))
   (λ (val) (contract-neg ctc blame val))))

(define (list-wrapper val ctc blame)
  (map (λ (v) (contract-pos ctc blame v)) val))

(define (cons-wrapper val ctc blame)
  (let ([fst (contract-pos ctc blame (car val))]
        [snd (contract-pos ctc blame (cdr val))])
    (cons fst snd)))

(module+ test
  (require rackunit)
  
  (test-case
   "procedure membrane"
   (define/contract (inc n)
     (membrane/c (or/c (integer? . -> . integer?) integer?) integer?)
     (+ n 1))
   (check-not-exn (λ () (inc 5)))
   (check-exn exn:fail:contract? (λ () (inc 'a))))
  
  (test-case
   "keyword procedure membrane"
   (define/contract (inc n #:by by)
     (membrane/c (or/c (integer? #:by integer? . -> . integer?) integer?) integer?)
     (+ n by))
   (check-not-exn (λ () (inc 5 #:by 1)))
   (check-exn exn:fail:contract? (λ () (inc 5 #:by 'a))))
  
  (test-case
   "vector get"
   (define/contract int-vec
     (membrane/c (or/c (-> vector?) vector? integer?) integer?)
     (make-vector 1 1))
   (define/contract sym-vec
     (membrane/c (or/c (-> vector?) vector? integer?) integer?)
     (make-vector 1 'a))
   (check-not-exn (λ () (vector-ref int-vec 0)))
   (check-exn exn:fail:contract? (λ () (vector-ref sym-vec 0))))
  
  (test-case
   "vector put"
   (define/contract int-vec
     (membrane/c (or/c (-> vector?) vector? integer?) integer?)
     (make-vector 1 1))
   (check-not-exn (λ () (vector-set! int-vec 0 1)))
   (check-exn exn:fail:contract? (λ () (vector-set! int-vec 0 'a))))
  
  (test-case
   "struct"
   (struct foo ((bar #:mutable)) #:transparent)
   (define/contract aFoo
     (membrane/c (or/c foo? integer?) integer?)
     (foo 1))
   (define/contract notAFoo
     (membrane/c (or/c foo? integer?) integer?)
     (foo 'a))
   (check-not-exn (λ () (foo-bar aFoo)))
   (check-exn exn:fail:contract? (λ () (foo-bar notAFoo))))
  
  (test-case
   "list membrane"
   (define (inc n) (+ n 1))
   (define/contract fns
     (membrane/c (or/c list? integer? (integer? . -> . integer?)) integer?)
     (list inc inc))
   (check-not-exn (λ () ((first fns) 5)))
   (check-exn exn:fail:contract? (λ () ((second fns) 'a))))
  
  (test-case
   "cons membrane"
   (define (inc n) (+ n 1))
   (define/contract fns
     (membrane/c (or/c cons? integer? (integer? . -> . integer?)) integer?)
     (cons inc (cons inc inc)))
   (check-not-exn (λ () ((car fns) 5)))
   (check-exn exn:fail:contract? (λ () ((cdr (cdr fns)) 'a))))
  
  #;(test-case
   "higher-order"
   (define/contract (test-good f x)
     (membrane/c (or/c integer? symbol? ((symbol? . -> . integer?) symbol? . -> . integer?))
                 (or/c (symbol? . -> . integer?) symbol?))
     (f x))
   (define/contract (test-bad f x)
     (membrane/c (or/c integer? symbol? ((symbol? . -> . integer?) symbol? . -> . integer?))
                 (or/c (symbol? . -> . integer?) symbol?))
     x)
   (define (stoi s) 0)
   (check-not-exn (λ () (test-good stoi 'a)))
   (check-exn exn:fail:contract? (λ () (test-good stoi 0)))
   (check-exn exn:fail:contract? (λ () (test-bad stoi 'a)))))

