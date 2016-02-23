#lang racket

(require racket/list)

(provide (contract-out
          [struct top ()]
          [struct bot ()]
          [struct pcpl ((name symbol?))]
          [struct dim ((name symbol?))]
          [struct proj ((principal principal?) (dims (set/c proj-dim?)))]
          [struct conj ((principals (set/c principal?)))]
          [struct disj ((principals (set/c principal?)))]
          [struct leftclo ((principal principal?) (world delegation-set?))]
          [struct rightclo ((principal principal?) (world delegation-set?))])
         (struct-out delegation-set)
         delegation-set
         ⊤ ⊥ ∨ ∧ ▹ ← →
         proj-dim?
         primitive-principal?
         primitive-principals
         principal?
         normalized?
         (contract-out [normalize (principal? . -> . normalized?)]
                       [full-projection (normalized? . -> . (set/c proj-dim?))]
                       [subtract-dim (normalized? proj-dim? . -> . normalized?)]
                       [subtract-dims (normalized? (set/c proj-dim?) . -> . normalized?)]))

(define-syntax define/contract-off
  (syntax-rules ()
    [(_ h c body ...)
     (define h body ...)]))

; Principal data types
(struct delegation-set (id parent extend delegations proved pruned failed stats)
  #:methods gen:equal+hash
  [(define (equal-proc ds1 ds2 recursive-equal?)
     (= (delegation-set-id ds1)
        (delegation-set-id ds2)))
   (define (hash-proc ds recursive-equal-hash)
     (recursive-equal-hash (delegation-set-id ds)))
   (define (hash2-proc ds recursive-equal-hash)
     (recursive-equal-hash (delegation-set-id ds)))]
  #:methods gen:custom-write
  [(define (write-proc ds port mode)
     (fprintf port "#<delegation-set: ~a>" (delegation-set-id ds)))])

(struct top ()
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc pcpl port mode)
     (fprintf port "⊤"))])
(struct bot ()
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc pcpl port mode)
     (fprintf port "⊥"))])
(struct pcpl (name)
  #:methods gen:custom-write
  [(define (write-proc pcpl port mode)
     (fprintf port "~a" (pcpl-name pcpl)))])
(struct dim (name)
  #:methods gen:custom-write
  [(define (write-proc pcpl port mode)
     (fprintf port "~a" (dim-name pcpl)))])
(struct proj (principal dims)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc pcpl port mode)
     (fprintf port "(▹ ~a" (proj-principal pcpl))
     (set-for-each (proj-dims pcpl) (λ (d) (fprintf port " ~a" d)))
     (fprintf port ")"))])
(struct conj (principals)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc pcpl port mode)
     (let* ([ps (conj-principals pcpl)]
            [fst (set-first ps)]
            [rst (set-rest ps)])
       (fprintf port "(∧ ~a" fst)
       (set-for-each rst (λ (p) (fprintf port " ~a" p)))
       (fprintf port ")")))])
(struct disj (principals)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc pcpl port mode)
     (let* ([ps (disj-principals pcpl)]
            [fst (set-first ps)]
            [rst (set-rest ps)])
       (fprintf port "(∨ ~a" fst)
       (set-for-each rst (λ (p) (fprintf port " ~a" p)))
       (fprintf port ")")))])
(struct leftclo (principal world)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc pcpl port mode)
     (fprintf port "(← ~a ~a)" (leftclo-principal pcpl) (leftclo-world pcpl)))])
(struct rightclo (principal world)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc pcpl port mode)
     (fprintf port "(→ ~a ~a)" (rightclo-principal pcpl) (rightclo-world pcpl)))])

(define ⊤ (top))
(define ⊥ (bot))

(define-syntax ∧
  (syntax-rules ()
    [(_ p ...)
     (conj (set p ...))]))

(define-syntax ∨
  (syntax-rules ()
    [(_ p ...)
     (disj (set p ...))]))

(define-syntax ▹
  (syntax-rules ()
    [(_ p d ...)
     (proj p (set d ...))]))

(define-syntax ←
  (syntax-rules ()
    [(_ p w)
     (leftclo p w)]))

(define-syntax →
  (syntax-rules ()
    [(_ p w)
     (rightclo p w)]))

(define (proj-dim? d)
  (or (symbol? d) (dim? d)))

(define (primitive-principal? p)
  (or (pcpl? p)
      (top? p)
      (bot? p)))

(define (principal? p)
  (or (primitive-principal? p)
      (match p
        [(proj p2 d) (and (andmap proj-dim? (set->list d))
                          (principal? p2))]
        [(conj ps) (andmap principal? (set->list ps))]
        [(disj ps) (andmap principal? (set->list ps))]
        [(leftclo p w) (and (principal? p) (delegation-set? w))]
        [(rightclo p w) (and (principal? p) (delegation-set? w))]
        [_ #f])))

(define/contract-off (normalized-proj-free? p)
  (any/c . -> . boolean?)
  (define (normalized-conj? p)
    (if (conj? p)
        (andmap normalized-disj? (set->list (conj-principals p)))
        (normalized-disj? p)))
  (define (normalized-disj? p)
    (if (disj? p)
        (andmap primitive-principal? (set->list (disj-principals p)))
        (primitive-principal? p)))
  (normalized-conj? p))

(define/contract-off (normalized-closure-free? p)
  (any/c . -> . boolean?)
  (define (normalized-top-conj? p)
    (if (conj? p)
        (andmap normalized-top-disj? (set->list (conj-principals p)))
        (normalized-top-disj? p)))
  (define (normalized-top-disj? p)
    (if (disj? p)
        (andmap normalized-proj? (set->list (disj-principals p)))
        (normalized-proj? p)))
  (define (normalized-proj? p)
    (if (proj? p)
        (and
         (andmap proj-dim? (set->list (proj-dims p)))
         (normalized-proj-free? (proj-principal p)))
        (normalized-proj-free? p)))
  (or (normalized-top-conj? p) (normalized-proj-free? p)))

(define/contract-off (normalized? p)
  (any/c . -> . boolean?)
  (define (normalized-top-conj? p)
    (if (conj? p)
        (andmap normalized-top-disj? (set->list (conj-principals p)))
        (normalized-top-disj? p)))
  (define (normalized-top-disj? p)
    (if (disj? p)
        (andmap normalized-closure? (set->list (disj-principals p)))
        (normalized-closure? p)))
  (define (normalized-closure? p)
    (cond
      [(leftclo? p)  (normalized? (leftclo-principal  p))]
      [(rightclo? p) (normalized? (rightclo-principal p))]
      [else          (normalized-closure-free? p)]))
  (or (normalized-top-conj? p) (normalized-closure-free? p)))

(define (full-projection p)
  (if (or (not (normalized-closure-free? p))
          (normalized-proj-free? p))
      (set)
      (match p
        [(proj _ ds) ds]
        [(conj ps) (apply set-intersect (set-map ps full-projection))]
        [(disj ps) (apply set-intersect (set-map ps full-projection))])))

(define (subtract-dim p d)
  (if (or (not (normalized-closure-free? p))
          (normalized-proj-free? p))
      p
      (match p
        [(proj pp ds)
         (let ([new-ds (set-remove ds d)])
           (to-proj pp new-ds))]
        [(conj ps)
         (conjoin-normals (list->set (set-map ps (λ (p) (subtract-dim p d)))))]
        [(disj ps)
         (disjoin-normals (list->set (set-map ps (λ (p) (subtract-dim p d)))))])))

(define (subtract-dims p ds)
  (foldl (λ (d p) (subtract-dim p d)) p (set->list ds)))

(define (primitive-principals p)
  (cond
    [(primitive-principal? p) (set p)]
    [(conj? p) (foldl set-union (set) (set-map (conj-principals p) primitive-principals))]
    [(disj? p) (foldl set-union (set) (set-map (disj-principals p) primitive-principals))]
    [(proj? p) (primitive-principals (proj-principal p))]
    [(leftclo? p) (primitive-principals (leftclo-principal p))]
    [(rightclo? p) (primitive-principals (rightclo-principal p))]))

(define (normalize p)
  (cond
    [(primitive-principal? p) p]
    [(conj? p) (normalize-conj p)]
    [(disj? p) (normalize-disj p)]
    [(proj? p) (normalize-proj p)]
    [(leftclo? p) (normalize-leftclo p)]
    [(rightclo? p) (normalize-rightclo p)]))

(define/contract-off (conjoin-proj-free-normals ps)
  ((set/c normalized-proj-free?) . -> . normalized-proj-free?)
  (let* ([nps (for/fold ([acc (set)])
                        ([p ps])
                (match p
                  [(conj pcpls) (set-union pcpls acc)]
                  [_ (set-union (set p) acc)]))]
         [dropbot (set-remove (absorb-conj nps) ⊥)])
    (cond
      [(equal? 0 (set-count dropbot)) ⊥]
      [(equal? 1 (set-count dropbot)) (set-first dropbot)]
      [(set-member? dropbot ⊤) ⊤]
      [else (conj dropbot)])))

(define/contract-off (gather ps)
  ((set/c principal?) . -> . (hash/c (or/c 'none (set/c proj-dim?)) (set/c principal?)))
  (let ([gathered (make-hash)])
    (set-for-each ps
                  (match-lambda
                    [(proj p ds) (hash-update! gathered ds (λ (v) (set-add v p)) (set p))]
                    [p (hash-update! gathered 'none (λ (v) (set-add v p)) (set p))]))
    gathered))

(define/contract-off (gather-closures ps)
  ((set/c principal?) . -> . (hash/c (or/c 'none (cons/c (or/c 'left 'right) delegation-set?))
                                     (set/c principal?)))
  (let ([gathered (make-hash)])
    (set-for-each ps
                  (match-lambda
                    [(leftclo p w)  (hash-update! gathered
                                                  (cons 'left w)
                                                  (λ (v) (set-add v p))
                                                  (set p))]
                    [(rightclo p w) (hash-update! gathered
                                                  (cons 'right w)
                                                  (λ (v) (set-add v p))
                                                  (set p))]
                    [p (hash-update! gathered 'none (λ (v) (set-add v p)) (set p))]))
    gathered))

(define (to-conj ps)
  (if (= 1 (set-count ps))
      (set-first ps)
      (conj ps)))

(define (to-disj ps)
  (if (= 1 (set-count ps))
      (set-first ps)
      (disj ps)))

(define (to-proj p ds)
  (if (set-empty? ds)
      p
      (proj p ds)))

(define/contract-off (conjoin-closure-free-normals ps)
  ((set/c normalized-closure-free?) . -> . normalized-closure-free?)
  (let*-values ([(nps free) (for/fold ([acc (set)]
                                       [free (set)])
                                      ([p ps])
                              (if (normalized-proj-free? p)
                                  (values acc (set-add free p))
                                  (match p
                                    [(conj pcpls) (values (set-union pcpls acc) free)]
                                    [_ (values (set-union (set p) acc) free)])))])
               (let* ([nps (if (set-empty? free)
                               nps
                               (set-add nps (conjoin-proj-free-normals free)))]
                      [gathered (gather (absorb-conj nps))]
                      [flattened (list->set (map (λ (entry)
                                                   (match entry
                                                     [(cons 'none ps) (to-conj (absorb-conj ps))]
                                                     [(cons ds ps) (proj (conjoin-normals (absorb-conj ps)) ds)]))
                                                 (hash->list gathered)))]
                      [dropbot (set-remove (absorb-conj flattened) ⊥)])
                 (cond
                   [(equal? 0 (set-count dropbot)) ⊥]
                   [(equal? 1 (set-count dropbot)) (set-first dropbot)]
                   [(set-member? dropbot ⊤) ⊤]
                   [else (conj dropbot)]))))

(define/contract-off (conjoin-normals ps)
  ((set/c normalized?) . -> . normalized?)
  (let*-values ([(nps free) (for/fold ([acc (set)]
                                       [free (set)])
                                      ([p ps])
                              (if (normalized-closure-free? p)
                                  (values acc (set-add free p))
                                  (match p
                                    [(conj pcpls) (values (set-union pcpls acc) free)]
                                    [_ (values (set-union (set p) acc) free)])))])
               (let* ([nps (if (set-empty? free)
                               nps
                               (set-add nps (conjoin-closure-free-normals free)))]
                      [gathered (gather-closures (absorb-conj nps))]
                      [flattened (list->set (map (λ (entry)
                                                   (match entry
                                                     [(cons 'none ps) (to-conj ps)]
                                                     [(cons (cons 'left w) ps)
                                                      (leftclo (conjoin-normals (absorb-conj ps)) w)]
                                                     [(cons (cons 'right w) ps)
                                                      (rightclo (conjoin-normals (absorb-conj ps)) w)]))
                                                 (hash->list gathered)))]
                      [dropbot (set-remove (absorb-conj flattened) ⊥)])
                 (cond
                   [(equal? 0 (set-count dropbot)) ⊥]
                   [(equal? 1 (set-count dropbot)) (set-first dropbot)]
                   [(set-member? dropbot ⊤) ⊤]
                   [else (conj dropbot)]))))

(define/contract-off (normalize-conj p)
  (conj? . -> . normalized?)
  (let* ([ps (conj-principals p)]
         [nps (list->set (set-map ps normalize))])
    (conjoin-normals nps)))

(define (do-compare-conj this that)
  (match (cons this that)
    [(cons (disj thisps) (disj thatps))
     (cond
       [(equal? thisps thatps) (set this)]
       [(subset? thisps thatps) (set that)]
       [(subset? thatps thisps) (set this)]
       [else (set)])]
    [(cons (disj thisps) that)
     (cond
       [(set-member? thisps that) (set this)]
       [else (set)])]
    [(cons this (disj thatps))
     (cond
       [(set-member? thatps this) (set that)]
       [else (set)])]
    [(cons this that)
     (cond
       [(equal? this that) (set this)]
       [else (set)])]))

(define (do-compare-disj this that)
  (match (cons this that)
    [(cons (conj thisps) (conj thatps))
     (cond
       [(equal? thisps thatps) (set this)]
       [(subset? thisps thatps) (set that)]
       [(subset? thatps thisps) (set this)]
       [else (set)])]
    [(cons (conj thisps) that)
     (cond
       [(set-member? thisps that) (set this)]
       [else (set)])]
    [(cons this (conj thatps))
     (cond
       [(set-member? thatps this) (set that)]
       [else (set)])]
    [(cons this that)
     (cond
       [(equal? this that) (set this)]
       [else (set)])]))

(define/contract-off (absorb-disj ps)
  ((set/c normalized?) . -> . (set/c normalized?))
  (for/fold ([absorbed (set)])
            ([p ps])
    (let ([absorptions (set-map absorbed (λ (o) (do-compare-disj p o)))])
      (set-subtract (set-add absorbed p)
                    (foldl set-union (set) absorptions)))))

(define/contract-off (absorb-conj ps)
  ((set/c normalized?) . -> . (set/c normalized?))
  (for/fold ([absorbed (set)])
            ([p ps])
    (let ([absorptions (set-map absorbed (λ (o) (do-compare-conj p o)))])
      (set-subtract (set-add absorbed p)
                    (foldl set-union (set) absorptions)))))

(define/contract-off (disjoin-proj-free-normals ps)
  ((set/c normalized-proj-free? #:kind 'dont-care) . -> . normalized-proj-free?)
  (define conjunct-sets (mutable-set))
  (define (process p)
    (cond
      [(conj? p) (set-add! conjunct-sets (conj-principals p))]
      [(disj? p) (set-union! conjunct-sets
                             (list->set (set-map (disj-principals p) set)))]
      [else      (set-add! conjunct-sets (set p))]))
  (set-for-each (absorb-disj ps) process)
  (let* ([conjunct-lists (map set->list (set->list conjunct-sets))]
         [prod (apply cartesian-product conjunct-lists)]
         [disjuncts (list->set (map (λ (l)
                                      (let* ([pcpls (list->set l)]
                                             [droptop (set-remove pcpls ⊤)])
                                        (cond
                                          [(equal? 0 (set-count droptop)) ⊤]
                                          [(equal? 1 (set-count droptop)) (set-first droptop)]
                                          [(set-member? droptop ⊥) ⊥]
                                          [else (disj droptop)])))
                                    prod))])
    (conjoin-proj-free-normals (absorb-conj disjuncts))))

(define/contract-off (disjoin-closure-free-normals ps)
  ((set/c normalized-closure-free?) . -> . normalized?)
  (define conjunct-sets (mutable-set))
  (define free (mutable-set))
  (define (process p)
    (cond
      [(conj? p) (set-add! conjunct-sets (conj-principals p))]
      [(disj? p) (set-union! conjunct-sets
                             (list->set (set-map (disj-principals p) set)))]
      [else      (set-add! conjunct-sets (set p))]))  
  (set-for-each (absorb-disj ps)
                (λ (p)
                  (if (normalized-proj-free? p)
                      (set-add! free p)
                      (process p))))
  (unless (set-empty? free)
    (process (disjoin-proj-free-normals free)))
  (let* ([conjunct-lists (map set->list (set->list conjunct-sets))]
         [prod (apply cartesian-product conjunct-lists)]
         [disjuncts (list->set (map (λ (l)
                                      (let* ([pcpls (list->set l)]
                                             [gathered (gather pcpls)]
                                             [flattened (list->set (map (λ (entry)
                                                                          (match entry
                                                                            [(cons 'none ps) (to-disj (absorb-disj ps))]
                                                                            [(cons ds ps) (proj (disjoin-normals (absorb-disj ps)) ds)]))
                                                                        (hash->list gathered)))]
                                             [droptop (set-remove flattened ⊤)])
                                        (cond
                                          [(equal? 0 (set-count droptop)) ⊤]
                                          [(equal? 1 (set-count droptop)) (set-first droptop)]
                                          [(set-member? droptop ⊥) ⊥]
                                          [else (disj droptop)])))
                                    prod))])
    (conjoin-normals (absorb-conj disjuncts))))

(define/contract-off (disjoin-normals ps)
  ((set/c normalized?) . -> . normalized?)
  (define conjunct-sets (mutable-set))
  (define free (mutable-set))
  (define (process p)
    (cond
      [(conj? p) (set-add! conjunct-sets (conj-principals p))]
      [(disj? p) (set-union! conjunct-sets
                             (list->set (set-map (disj-principals p) set)))]
      [else      (set-add! conjunct-sets (set p))]))
  (set-for-each (absorb-disj ps)
                (λ (p)
                  (if (normalized-closure-free? p)
                      (set-add! free p)
                      (process p))))
  (unless (set-empty? free)
    (process (disjoin-closure-free-normals (list->set (set->list free)))))
  (let* ([conjunct-lists (map set->list (set->list conjunct-sets))]
         [prod (apply cartesian-product conjunct-lists)]
         [disjuncts (list->set (map (λ (l)
                                      (let* ([pcpls (list->set l)]
                                             [gathered (gather-closures pcpls)]
                                             [flattened
                                              (list->set (map (λ (entry)
                                                                (match entry
                                                                  [(cons 'none ps) (to-disj (absorb-disj ps))]
                                                                  [(cons (cons 'left w) ps)
                                                                   (leftclo (disjoin-normals (absorb-disj ps)) w)]
                                                                  [(cons (cons 'right w) ps)
                                                                   (rightclo (disjoin-normals (absorb-disj ps)) w)]))
                                                              (hash->list gathered)))]
                                             [droptop (set-remove flattened ⊤)])
                                        (cond
                                          [(equal? 0 (set-count droptop)) ⊤]
                                          [(equal? 1 (set-count droptop)) (set-first droptop)]
                                          [(set-member? droptop ⊥) ⊥]
                                          [else (disj droptop)])))
                                    prod))])
    (conjoin-normals (absorb-conj disjuncts))))

(define/contract-off (normalize-disj p)
  (disj? . -> . normalized?)
  (let* ([ps (disj-principals p)]
         [nps (list->set (set-map ps normalize))])
    (disjoin-normals nps)))

(define/contract-off (project-normal p ds)
  (normalized? (set/c proj-dim?) . -> . normalized?)
  (if (set-empty? ds)
      p
      (cond
        [(primitive-principal? p)
         (match p
           [(bot) ⊥]
           [(top) (proj ⊤ ds)]
           [(pcpl n) (proj p ds)])]
        [(normalized-proj-free? p)
         (proj p ds)]
        [else
         (match p
           [(conj ps) (conjoin-normals (list->set (set-map ps (λ (p) (project-normal p ds)))))]
           [(disj ps) (disjoin-normals (list->set (set-map ps (λ (p) (project-normal p ds)))))]
           [(leftclo p w) (leftclo-normal (project-normal p ds) w)]
           [(rightclo p w) (rightclo-normal (project-normal p ds) w)]
           [(proj p2 ds2) (proj p2 (set-union ds2 ds))])])))

(define/contract-off (normalize-proj p)
  (proj? . -> . normalized?)
  (let ([ds (proj-dims p)]
        [np (normalize (proj-principal p))])
    (project-normal np ds)))

(define/contract-off (leftclo-normal p w)
  (normalized? delegation-set? . -> . normalized?)
  (cond
    [(primitive-principal? p)
     (match p
       [(bot) ⊥]
       [(top) (leftclo ⊤ w)]
       [(pcpl n) (leftclo p w)])]
    [(normalized-closure-free? p)
     (leftclo p w)]
    [else
     (match p
       [(conj ps) (conjoin-normals (list->set (set-map ps (λ (p) (leftclo-normal p w)))))]
       [(disj ps) (disjoin-normals (list->set (set-map ps (λ (p) (leftclo-normal p w)))))]
       [(leftclo p2 w2) #:when (equal? w w2) p]
       [_ (leftclo p w)])]))

(define/contract-off (rightclo-normal p w)
  (normalized? delegation-set? . -> . normalized?)
  (cond
    [(primitive-principal? p)
     (match p
       [(bot) (rightclo ⊥ w)]
       [(top) ⊤]
       [(pcpl n) (rightclo p w)])]
    [(normalized-closure-free? p)
     (rightclo p w)]
    [else
     (match p
       [(conj ps) (conjoin-normals (list->set (set-map ps (λ (p) (rightclo-normal p w)))))]
       [(disj ps) (disjoin-normals (list->set (set-map ps (λ (p) (rightclo-normal p w)))))]
       [(rightclo p2 w2) #:when (equal? w w2) p]
       [_ (rightclo p w)])]))

(define/contract-off (normalize-leftclo p)
  (leftclo? . -> . normalized?)
  (let ([w (leftclo-world p)]
        [np (normalize (leftclo-principal p))])
    (leftclo-normal np w)))

(define/contract-off (normalize-rightclo p)
  (rightclo? . -> . normalized?)
  (let ([w (rightclo-world p)]
        [np (normalize (rightclo-principal p))])
    (rightclo-normal np w)))

(module+ test
  (require rackunit)

  ; Atomic principals
  (define A (pcpl 'A))
  (define B (pcpl 'B))
  (define C (pcpl 'C))

  (define a (dim 'a))
  (define b (dim 'b))

  ; Worlds
  (define DSA (delegation-set 0 'A #f (set) #f #f #f #f))
  (define DSB (delegation-set 1 'B #f (set) #f #f #f #f))

  ; Simple
  (test-case
   "refl"
   (check-equal? (normalize A) A))

  ; Commutativity
  (test-case
   "conjComm"
   (define one (∧ A B))
   (define two (∧ B A))
   (check-equal? (normalize one) (normalize two)))
  (test-case
   "disjComm"
   (define one (∨ A B))
   (define two (∨ B A))
   (check-equal? (normalize one) (normalize two)))
  (test-case
   "projComm"
   (define one (▹ (▹ A a) b))
   (define two (▹ (▹ A b) a))
   (check-equal? (normalize one) (normalize two)))

  ; Associativity
  (test-case
   "conjAssoc"
   (define one (∧ (∧ A B) C))
   (define two (∧ A (∧ B C)))
   (check-equal? (normalize one) (normalize two)))
  (test-case
   "disjAssoc"
   (define one (∨ (∨ A B) C))
   (define two (∨ A (∨ B C)))
   (check-equal? (normalize one) (normalize two)))

  ; Absorbtion
  (test-case
   "conjDisjAbsorb"
   (define one (∧ A (∨ A B)))
   (check-equal? (normalize one) A))
  (test-case
   "disjConjAbsorb"
   (define one (∨ A (∧ A B)))
   (check-equal? (normalize one) A))

  ; Idempotence
  (test-case
   "conjIdemp"
   (define one (∧ A A))
   (check-equal? (normalize one) A))
  (test-case
   "diskIdemp"
   (define one (∨ A A))
   (check-equal? (normalize one) A))
  (test-case
   "projIdemp"
   (define one (▹ (▹ A a) a))
   (define two (▹ A a))
   (check-equal? (normalize one) (normalize two)))
  (test-case
   "leftCloIdemp"
   (define one (← A DSA))
   (define two (← (← A DSA) DSA))
   (check-equal? (normalize one) (normalize two)))
  (test-case
   "rightCloIdemp"
   (define one (→ A DSA))
   (define two (→ (→ A DSA) DSA))
   (check-equal? (normalize one) (normalize two)))

  ; Identities
  (test-case
   "conjIdent"
   (define one (∧ A ⊥))
   (check-equal? (normalize one) A))
  (test-case
   "disjIdent"
   (define one (∨ A ⊤))
   (check-equal? (normalize one) A))
  (test-case
   "conjTop"
   (define one (∧ A ⊤))
   (check-equal? (normalize one) ⊤))
  (test-case
   "disjBot"
   (define one (∨ A ⊥))
   (check-equal? (normalize one) ⊥))
  (test-case
   "projBot"
   (define one (▹ ⊥ a))
   (check-equal? (normalize one) ⊥))
  (test-case
   "leftCloBot"
   (define one (← ⊥ DSA))
   (check-equal? (normalize one) ⊥))
  (test-case
   "rightCloTop"
   (define one (→ ⊤ DSA))
   (check-equal? (normalize one) ⊤))

  ; Distributivity
  (test-case
   "conjDistDisj"
   (define one (∧ A (∨ B C)))
   (define two (∨ (∧ A B) (∧ A C)))
   (check-equal? (normalize one) (normalize two)))
  (test-case
   "projDistConj"
   (define one (▹ (∧ A B) a))
   (define two (∧ (▹ A a) (▹ B a)))
   (check-equal? (normalize one) (normalize two)))
  (test-case
   "projDistDisj"
   (define one (▹ (∨ A B) a))
   (define two (∨ (▹ A a) (▹ B a)))
   (check-equal? (normalize one) (normalize two)))
  (test-case
   "leftCloDistConj"
   (define one (← (∧ A B) DSA))
   (define two (∧ (← A DSA) (← B DSA)))
   (check-equal? (normalize one) (normalize two)))
  (test-case
   "leftCloDistDisj"
   (define one (← (∨ A B) DSA))
   (define two (∨ (← A DSA) (← B DSA)))
   (check-equal? (normalize one) (normalize two)))
  (test-case
   "leftCloDistProj"
   (define one (← (▹ (∨ A B) a) DSA))
   (define two (∨ (▹ (← A DSA) a) (▹ (← B DSA) a)))
   (check-equal? (normalize one) (normalize two))))
