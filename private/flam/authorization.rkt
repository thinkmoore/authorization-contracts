#lang racket

(require "principals.rkt")

(provide (except-out (all-from-out "principals.rkt")
                     (struct-out delegation-set))
         (struct-out actsfor)
         (struct-out labeled)
         (except-out (struct-out lifetime)
                     create-lifetime)
         make-lifetime
         (contract-out [make-delegation-set (->* () #:rest delegation-list? delegation-set?)]
                       [print-delegation-set (delegation-set? . -> . void)]
                       [add-delegations (->* (delegation-set?)
                                             #:rest (or/c (list/c delegation-set?) delegation-list?)
                                             delegation-set?)]
                       [remove-delegations (->* (delegation-set?)
                                                #:rest (or/c (list/c delegation-set?) delegation-list?)
                                                delegation-set?)]
                       [delegation-set->list (delegation-set? . -> . delegation-list?)]
                       [delegation-set-for-each (delegation-set? (labeled? . -> . any) . -> . void)]
                       [delegation-set? (any/c . -> . boolean?)])
         delegation-list?
         ≽ @ ≽@
         search-strategy/c
         (contract-out [search-delegates-left search-strategy/c]
                       [search-delegates-right search-strategy/c]
                       [acts-for? (->* (delegation-set?
                                        normalized?
                                        normalized?
                                        normalized?)
                                       (#:search (or/c #f (listof search-strategy/c))
                                        #:verbose (or/c 'none 'stats 'result 'all))
                                       boolean?)]))

(struct actsfor (left right)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc af port mode)
     (fprintf port "~a ≽ ~a" (actsfor-left af) (actsfor-right af)))])
(struct labeled (rel label)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc l port mode)
     (fprintf port "(~a @ ~a)" (labeled-rel l) (labeled-label l)))])

(struct query-record (labeled world trigger)
  #:methods gen:equal+hash
  [(define (equal-proc q1 q2 recursive-equal?)
     (and (recursive-equal? (query-record-labeled q1) (query-record-labeled q2))
          (recursive-equal? (query-record-world q1) (query-record-world q2))))
   (define (hash-proc q recursive-equal-hash)
     (bitwise-xor
      (recursive-equal-hash (query-record-labeled q))
      (recursive-equal-hash (query-record-world q))))
   (define (hash2-proc q recursive-equal-hash)
     (bitwise-xor
      (recursive-equal-hash (query-record-labeled q))
      (recursive-equal-hash (query-record-world q))))]
  #:methods gen:custom-write
  [(define (write-proc q port mode)
     (fprintf port "(? ~a in ~a)" (query-record-labeled q) (query-record-world q)))])

(define (make-stats)
  (make-hash (list (cons 'proved 0)
                   (cons 'pruned 0)
                   (cons 'failed 0)
                   (cons 'missed 0))))

(struct lifetime labeled (value)
  #:constructor-name create-lifetime
  #:methods gen:equal+hash
  [(define (equal-proc d1 d2 recursive-equal?)
     (and (recursive-equal? (labeled-rel d1)
                           (labeled-rel d2))
          (recursive-equal? (labeled-label d1)
                            (labeled-label d2))))
   (define (hash-proc d recursive-equal-hash)
     (bitwise-xor
      (recursive-equal-hash (labeled-rel d))
      (recursive-equal-hash (labeled-label d))))
   (define (hash2-proc d recursive-equal-hash)
     (bitwise-xor
      (recursive-equal-hash (labeled-rel d))
      (recursive-equal-hash (labeled-label d))))]
  #:methods gen:custom-write
  [(define (write-proc l port mode)
     (fprintf port "(~a @ ~a in lifetime)"
              (labeled-rel l)
              (labeled-label l)
;              (weak-box-value (lifetime-value l))
              ))])

(define (make-lifetime r l k)
  (create-lifetime r l (if (weak-box? k) k (make-weak-box k))))

(define delegation-list? (listof labeled?))

(define delegation-set-cache (make-weak-hash))
(define delegation-set-next-id 1)

(define (hash-cons-delegation-set parent extend delegations proved pruned failed stats)
  ;; (let ([cached (hash-ref delegation-set-cache delegations #f)])
  ;;   (if cached
  ;;       cached
  ;;       (let ([new-ds (delegation-set delegation-set-next-id
  ;;                                     parent
  ;;                                     extend
  ;;                                     delegations
  ;;                                     proved
  ;;                                     pruned
  ;;                                     failed
  ;;                                     stats)])
  ;;         (set! delegation-set-next-id (+ 1 delegation-set-next-id))
  ;;         (hash-set! delegation-set-cache delegations new-ds)
  ;;         new-ds)))
  (set! delegation-set-next-id (+ 1 delegation-set-next-id))
  (delegation-set delegation-set-next-id #f #f delegations proved pruned failed stats))

(define (make-delegation-set . delegations)
  (hash-cons-delegation-set #f #f
   (apply set delegations)
   (make-hash) (make-hash) (make-hash)
   (make-stats)))

(define (print-delegation-set ds)
  (printf "Delegation set ~a:~n" (delegation-set-id ds))
  (set-for-each (delegation-set-delegations ds)
                (λ (d) (printf "~a~n" d))))

(define (add-delegations ds . delegation-args)
  (let ([delegations (if (and (eq? (length delegation-args) 1)
                              (delegation-set? (first delegation-args)))
                         (delegation-set-delegations (first delegation-args))
                         (list->set delegation-args))])
    (hash-cons-delegation-set
     ds #t
     (set-union (delegation-set-delegations ds)
                delegations)
     (hash-copy (delegation-set-proved ds)) (make-hash) (make-hash)
     (make-stats))))

(define (remove-delegations ds . delegation-args)
  (let ([delegations (if (and (eq? (length delegation-args) 1)
                              (delegation-set? (first delegation-args)))
                         (delegation-set-delegations (first delegation-args))
                         (list->set delegation-args))])
    (hash-cons-delegation-set
     ds #f
     (set-subtract (delegation-set-delegations ds)
                   delegations)
     (make-hash) (make-hash) (hash-copy (delegation-set-failed ds))
     (make-stats))))

(define (delegation-set->list ds)
  (set->list (delegation-set-delegations ds)))

(define (delegation-set-for-each ds proc)
  (set-for-each (delegation-set-delegations ds)
                proc))

(define-syntax ≽
  (syntax-rules ()
    [(_ l r) (actsfor l r)]))

(define-syntax ≽@
  (syntax-rules ()
    [(_ l r ll)
     (labeled (actsfor (normalize l) (normalize r)) (normalize ll))]))

(define-syntax @
  (syntax-rules ()
    [(_ r ll)
     (labeled r ll)]))

(struct result (type data) #:prefab)

(define (proved? res)
  (match res
    [(result 'proved _) #t]
    [_ #f]))

(struct proof (name query subqueries) #:prefab)

(define (delegation? q)
  (match q
    [(labeled (actsfor left right) label)
     (and (normalized? label)
          (normalized? left)
          (normalized? right))]
    [_ #f]))

; proof : (proof labeled (set/c proof)))

(define current-delegation-set (make-parameter #f))

(define (current-parent)
  (delegation-set-parent (current-delegation-set)))

(define (current-extend)
  (delegation-set-extend (current-delegation-set)))

(define (current-delegations)
  (delegation-set-delegations (current-delegation-set)))

(define (current-proved-cache)
  (delegation-set-proved (current-delegation-set)))

(define (current-pruned-cache)
  (delegation-set-pruned (current-delegation-set)))

(define (current-failed-cache)
  (delegation-set-failed (current-delegation-set)))

(define (current-cache-stats)
  (delegation-set-stats (current-delegation-set)))

(define (check-cache q)
  (let ([stats (current-cache-stats)])
    (define (check-subcache cache name)
      (let ([result (hash-ref (cache) q #f)])
        (when result
          (hash-update! stats name (λ (v) (+ v 1))))
        result))
    (let ([result (or (check-subcache current-proved-cache 'proved)
                      (check-subcache current-pruned-cache 'pruned)
                      (check-subcache current-failed-cache 'failed))])
      (unless result
        (hash-update! stats 'missed (λ (v) (+ v 1))))
      result)))

(define (print-cache-stats)
  (let ([stats (current-cache-stats)])
    (printf "PROVED cache hits: ~a~n"
            (hash-ref stats 'proved))
    (printf "PRUNED cache hits: ~a~n"
            (hash-ref stats 'pruned))
    (printf "FAILED cache hits: ~a~n"
            (hash-ref stats 'failed))
    (printf "Cache misses:      ~a~n~n"
            (hash-ref stats 'missed))))

(define (insert-result query query-result)
  (remove-result query)
  (match query-result
    [(result 'proved _)
     (begin
       (when (and (not (current-extend)) (current-parent))
         (parameterize ([current-delegation-set (current-parent)])
           (insert-result query query-result)))
       (hash-set! (current-proved-cache) query query-result))]
    [(result 'pruned _) (hash-set! (current-pruned-cache) query query-result)]
    [(result 'failed _)
     (begin
       (when (and (current-extend) (current-parent))
         (parameterize ([current-delegation-set (current-parent)])
           (insert-result query query-result)))
       (hash-set! (current-failed-cache) query query-result))]))

(define (remove-result query)
  (hash-remove! (current-proved-cache) query)
  (hash-remove! (current-pruned-cache) query)
  (hash-remove! (current-failed-cache) query))

(define (cache-for-each-pruned proc)
  (hash-for-each (current-pruned-cache)
                 (λ (q r)
                   (match r
                     [(result 'pruned progress-condition)
                      (proc q progress-condition)]
                     [_ void]))))

(define (update-cache q q-result)
  (insert-result q q-result)
  (match q-result
    [(result 'proved data)
     (cache-for-each-pruned
      (λ (q progress-condition)
        (let ([new-progress-condition (set-remove progress-condition q)])
          (if (set-empty? new-progress-condition)
              (remove-result q)
              (insert-result q (result 'pruned new-progress-condition))))))]
    [(result 'pruned data)
     (cache-for-each-pruned
      (λ (q progress-condition)
        (when (set-member? progress-condition q)
          (let ([new-progress-condition (set-union (set-remove progress-condition q) data)])
            (insert-result q (result 'pruned new-progress-condition))))))]
    [(result 'failed data)
     (let ([new-failed (mutable-set)])
       (cache-for-each-pruned
        (λ (q progress-condition)
          (let ([new-progress-condition (set-remove progress-condition q)])
            (if (set-empty? new-progress-condition)
                (begin
                  (remove-result q)
                  (set-add! new-failed q))
                (insert-result q (result 'pruned new-progress-condition))))))
       (set-for-each new-failed (λ (q) (update-cache q (result 'failed #f)))))]))

(define (acts-for? delegation-set left right label #:trigger [trigger #f] #:search [search-list #f] #:verbose [verb 'none])
  (unless search-list
    (set! search-list (list search-delegates-left search-delegates-right)))
  (parameterize ([current-delegation-set delegation-set])
    (let* ([q (query-record (labeled (actsfor left right) label) delegation-set #f)]
           [res (acts-for-proof q #:search search-list #:verbose verb)])
      (when (or (eq? verb 'stats) (eq? verb 'all))
        (print-cache-stats))
      (when (or (eq? verb 'result) (eq? verb 'all))
        (printf "acts-for query in:~n")
        (print-delegation-set delegation-set)
        (match res
          [(result 'proved _) (printf "proved~n")]
          [(result 'pruned _) (printf "pruned~n")]
          [(result 'failed _) (printf "failed~n")])
        (printf "=> ~a ->~n~a~n~n" q res))
      (proved? res))))

(define (acts-for-proof q #:search [search-list empty] #:verbose [verb 'none])
  (or (check-cache q)
      (begin
        (update-cache q (result 'pruned (set q)))
        (let ([res (match q
                     [(query-record inner w trigger)
                      (if (not (equal? w (current-delegation-set)))
                          (parameterize ([current-delegation-set w])
                            (let ([w-res (acts-for-proof q #:search search-list #:verbose verb)])
                              (match w-res
                                [(result 'proved prf) (result 'proved (proof "ACTS-FOR?" q (set prf)))]
                                [_ w-res])))
                          (find-acts-for-proof q #:search search-list #:verbose verb))])])
          (update-cache q res)
          (when (eq? verb 'all)
            (printf "acts-for subquery: ~a ->~n~a~n~n" q res))
          res))))

(define search-functions (make-parameter #f))

(define (find-acts-for-proof q #:search search-list #:verbose verb)
  (parameterize ([search-functions search-list])
    (let ([progress-condition (set)])
      (let-values ([(success-rule subproofs)
                    (for/fold ([success-rule #f]
                               [subproofs (set)])
                              ([rule rules])
                      #:break success-rule
                      (let-values ([(rule-name premise-alternatives) (rule q)])
                        (if premise-alternatives
                            (let-values ([(success-rule rule-conditions subproofs stop)
                                          (for/fold ([success-rule rule-name]
                                                     [rule-conditions (set)]
                                                     [subproofs (set)]
                                                     [stop #f])
                                                    ([premise-list premise-alternatives])
                                            #:break stop
                                            (let-values ([(success-rule rule-conditions subproofs _)
                                                          (for/fold ([success-rule rule-name]
                                                                     [rule-conditions rule-conditions]
                                                                     [subproofs subproofs]
                                                                     [break-now #f])
                                                                    ([premise premise-list])
                                                            #:break break-now
                                                            (let ([subquery-result (acts-for-proof premise #:search search-list #:verbose verb)])
                                                              (match subquery-result
                                                                [(result 'proved data)
                                                                 (values success-rule rule-conditions (set-add subproofs data) #f)]
                                                                [(result 'pruned data)
                                                                 (values #f (set-union rule-conditions data) subproofs #f)]
                                                                [(result 'failed data)
                                                                 (values #f (set) subproofs #t)])))])
                                              (unless success-rule
                                                (set! progress-condition (set-union progress-condition rule-conditions)))
                                              (values success-rule rule-conditions subproofs success-rule)))])
                              (values success-rule subproofs))
                            (values #f empty))))])
        (let ([result-struct (cond
                               [success-rule                          (result 'proved (proof success-rule q subproofs))]
                               [(set-empty? progress-condition)       (result 'failed #f)]
                               [else                                  (result 'pruned progress-condition)])])
          (when (query-record-trigger q)
            ((query-record-trigger q) result-struct))
          result-struct)))))

(define (get-projs pcpl)
  (match pcpl
    [(proj p ds) ds]
    [_ (set)]))

(define (shared-proj pcpls)
  (let ([fst (set-first pcpls)]
        [rst (set-rest pcpls)])
    (foldl (λ (cur dims) (set-intersect dims (get-projs cur)))
           (get-projs fst)
           (set->list rst))))

(define (drop-proj pcpls dims)
  (list->set (set-map pcpls
                      (match-lambda
                        [(proj p ds)
                         (let ([dropped (set-subtract ds dims)])
                           (if (set-empty? dropped)
                               p
                               (proj p dropped)))]))))

(define-syntax query
  (syntax-rules ()
    [(_ inner world)
     (query-record inner world #f)]))

(define-syntax query-report-on
  (syntax-rules ()
    [(_ inner world res message)
     (query-record inner world (match-lambda
                                 [(result type _)
                                  (if (or (eq? res 'any) (eq? res type))
                                      (printf message)
                                      #f)]))]))

(define-syntax query-report
  (syntax-rules ()
    [(_ inner world)
     (query-record inner world (match-lambda
                                 [(result 'failed _)
                                  (printf "Query ~a in ~a failed.~n" inner world)]
                                 [(result 'pruned _)
                                  (printf "Query ~a in ~a pruned.~n" inner world)]
                                 [(result 'proved prf)
                                  (printf "Query ~a in ~a proved.~n~a~n" inner world prf)]))]))

(define-syntax query-report-failure
  (syntax-rules ()
    [(_ inner world)
     (query-record inner world (match-lambda
                                 [(result 'failed _)
                                  (printf "Query ~a in ~a failed.~n" inner world)]
                                 [(result 'pruned _)
                                  (printf "Query ~a in ~a pruned.~n" inner world)]
                                 [_ #f]))]))

(define-syntax query-report-success
  (syntax-rules ()
    [(_ inner world)
     (query-record inner world (match-lambda
                                 [(result 'proved prf)
                                  (printf "Query ~a in ~a proved.~n~a~n" inner world prf)]
                                 [_ #f]))]))

; Rule : delegation set -> query -> (values string (or/c #f (list/c (list/c subgoal))))

(define (rule-bot q)
  (match q
    [(query-record (labeled (actsfor _ (? bot?)) _) w _) (values "BOT" empty)]
    [_ (values "BOT" #f)]))

(define (rule-top q)
  (match q
    [(query-record (labeled (actsfor (? top?) _) _) w _) (values "TOP" empty)]
    [_ (values "TOP" #f)]))

(define (rule-refl q)
  (match q
    [(query-record (labeled (actsfor left right) _) w _) #:when (equal? left right) (values "REFL" empty)]
    [_ (values "REFL" #f)]))

(define (rule-proj-right q)
  (match q
    [(query-record (labeled (actsfor lp rp) _) w _)
     (let* ([lds (full-projection lp)]
            [rds (full-projection rp)])
       (if (and (subset? lds rds) (equal? (subtract-dims lp lds) (subtract-dims rp rds)))
           (values "PROJ-RIGHT" empty)
           (values "PROJ-RIGHT" #f)))]))

(define (rule-conj-left q)
  (match q
    [(query-record (labeled (actsfor (conj lps) rp) l) w _) #:when (set-member? lps rp)
     (values "CONJ-LEFT" (list))]
    [(query-record (labeled (actsfor (conj lps) rp) l) w _)
     (values "CONJ-LEFT" (set-map lps (λ (lp) (list (query (labeled (≽ lp rp) l) w)))))]
    [_ (values "CONJ-LEFT" #f)]))

(define (rule-conj-right q)
  (match q
    [(query-record (labeled (actsfor lp (conj rps)) l) w _)
     (values "CONJ-RIGHT" (list (set-map rps (λ (rp) (query (labeled (≽ lp rp) l) w)))))]
    [_ (values "CONJ-RIGHT" #f)]))

(define (rule-disj-left q)
  (match q
    [(query-record (labeled (actsfor (disj lps) rp) l) w _)
     (values "DISJ-LEFT" (list (set-map lps (λ (lp) (query (labeled (≽ lp rp) l) w)))))]
    [_ (values "DISJ-LEFT" #f)]))

(define (rule-disj-proj-left q)
  (match q
    [(query-record (labeled (actsfor (proj (disj lps) ds) rp) l) w _)
     (values "DISJ-PROJ-LEFT" (list (set-map lps (λ (lp) (query (≽@ (proj lp ds) rp l) w)))))]
    [_ (values "DISJ-PROJ-LEFT" #f)]))

(define (rule-disj-right q)
  (match q
    [(query-record (labeled (actsfor lp (disj rps)) l) w _) #:when (set-member? rps lp)
     (values "DISJ-RIGHT" (list))]
    [(query-record (labeled (actsfor lp (disj rps)) l) w _)
     (values "DISJ-RIGHT" (set-map rps (λ (rp) (list (query (labeled (≽ lp rp) l) w)))))]
    [_ (values "DISJ-RIGHT" #f)]))

(define (rule-world-left q)
  (match q
    [(query-record (labeled (actsfor lp (leftclo rp wc)) l) w _)
     (values "WORLD-LEFT"
             (let ([possible-labels (mutable-set l ;lp rp l ⊥ ⊤
                                     )])
               (set-map possible-labels
                        (λ (ll)
                          (list (query (labeled (≽ (normalize (← ll wc)) l) l) w)
                                (query (labeled (≽ lp rp) ll) wc))))))]
    [_ (values "WORLD-LEFT" #f)]))

(define (rule-world-left-proj q)
  (match q
    [(query-record (labeled (actsfor (leftclo lp wc) rp) l) w _)
     (values "WORLD-LEFT-PROJ"
             (let* ([ds (full-projection lp)]
                    [new-lp (subtract-dims lp ds)]
                    [new-rp (subtract-dims rp ds)])
               (if (not (equal? lp new-lp))
                   (list (list (query (≽@ (← new-lp wc) new-rp l) w)))
                   #f)))]
    [_ (values "WORLD-LEFT-PROJ" #f)]))

(define (rule-world-right q)
  (match q
    [(query-record (labeled (actsfor (rightclo lp wc) rp) l) w _)
     (values "WORLD-RIGHT"
             (let ([possible-labels (mutable-set l lp ;rp l ⊤
                                                 )])
               (set-map possible-labels
                        (λ (ll)
                          (list (query (labeled (≽ (normalize (← ll wc)) l) l) w)
                                (query (labeled (≽ lp rp) ll) wc))))))]
    [_ (values "WORLD-RIGHT" #f)]))

(define (rule-delegate q)
  (match q
    [(query-record (labeled r l) w _)
     (let ([delegation-matches (filter (match-lambda
                                         [(labeled (? (λ (dr) (equal? dr r)) dr) dl) #t]
                                         [_ #f]) (set->list (current-delegations)))])
       (values "DEL" (if (empty? delegation-matches)
                         #f
                         (map (match-lambda
                                [(labeled r dl) (list (let ([inner (labeled (≽ dl l) l)])
                                                        (query inner w)))])
                              delegation-matches))))]))

(define (power-set s)
  (if (set-empty? s)
      (set (set))
      (let ([fst (set-first s)]
            [recur (power-set (set-rest s))])
        (set-union recur (list->set (set-map recur (λ (s) (set-add s fst))))))))

(define search-strategy/c (principal? principal? principal? (set/c delegation?) . -> . (set/c principal?)))

(define (search-delegates-left l r ll ds)
  (foldl set-union (set)
         (set-map ds
                  (match-lambda
                    [(labeled (actsfor dql dqr) dl) #:when (equal? l dql) (set dqr)]
                    [_ (set)]))))

(define (search-delegates-right l r ll ds)
  (foldl set-union (set)
         (set-map ds
                  (match-lambda
                    [(labeled (actsfor dql dqr) dl) #:when (equal? r dqr) (set dql)]
                    [_ (set)]))))

(define (rule-trans-left q)
  (match q
    [(query-record (labeled (actsfor ql qr) l) w _)
     (let ([subgoal-alternatives (mutable-set)])
       (set-for-each (current-delegations)
                     (match-lambda
                       [(labeled (actsfor dql dqr) dl)
                        (begin
                          (when (equal? ql dql)
                            (set-add! subgoal-alternatives
                                      (list (query (labeled (actsfor ql dqr) l) w)
                                            (query (labeled (actsfor dqr qr) l) w))))
                          (let ([lp (full-projection ql)]
                                [rp (full-projection qr)])
                            (set-for-each (power-set (set-intersect lp rp))
                                          (λ (ds)
                                            (let ([proj-dql (normalize (proj dql ds))]
                                                  [proj-dqr (normalize (proj dqr ds))])
                                              (when (and (equal? ql proj-dql)
                                                         (not (equal? proj-dqr dqr)))
                                                (set-add! subgoal-alternatives
                                                          (list (query (labeled (actsfor ql proj-dqr) l) w)
                                                                (query (labeled (actsfor proj-dqr qr) l) w)))))))))]))
       (values "TRANS-LEFT" (if (set-empty? subgoal-alternatives)
                           #f
                           (set->list subgoal-alternatives))))]))

(define (rule-trans-right q)
  (match q
    [(query-record (labeled (actsfor ql qr) l) w _)
     (let ([subgoal-alternatives (mutable-set)])
       (set-for-each (current-delegations)
                     (match-lambda
                       [(labeled (actsfor dql dqr) dl)
                        (begin
                          (when (equal? qr dqr)
                            (set-add! subgoal-alternatives
                                      (list (query (labeled (actsfor ql dql) l) w)
                                            (query (labeled (actsfor dql qr) l) w))))
                          (let ([lp (full-projection ql)]
                                [rp (full-projection qr)])
                            (set-for-each (power-set (set-intersect lp rp))
                                          (λ (ds)
                                            (let ([proj-dql (normalize (proj dql ds))]
                                                  [proj-dqr (normalize (proj dqr ds))])
                                              (when (and (equal? qr proj-dqr)
                                                         (not (equal? proj-dql dql)))
                                                (set-add! subgoal-alternatives
                                                          (list (query (labeled (actsfor ql proj-dql) l) w)
                                                                (query (labeled (actsfor proj-dql qr) l) w)))))))))]))
       (values "TRANS-RIGHT" (if (set-empty? subgoal-alternatives)
                                 #f
                                 (set->list subgoal-alternatives))))]))

(define (rule-trans-search q)
  (match q
    [(query-record (labeled (actsfor ql qr) ll) w _)
     (let* ([search-answers (map (λ (f) (f ql qr ll (current-delegations))) (search-functions))]
            [possible (foldl set-union (set) search-answers)])
       (values "TRANS-SEARCH"
               (if (set-empty? possible)
                   #f
                   (set-map possible
                            (λ (p)
                              (list (query (labeled (actsfor ql p) ll) w)
                                    (query (labeled (actsfor p qr) ll) w)))))))]))

(define rules (list rule-bot rule-top rule-refl
                    rule-delegate 
                    rule-conj-left rule-conj-right
                    rule-disj-left rule-disj-proj-left
                    rule-disj-right
                    rule-proj-right
                    rule-trans-search
                    rule-world-left rule-world-right
                    rule-world-left-proj))

(define A (pcpl 'A))
(define B (pcpl 'B))
(define C (pcpl 'C))

(module+ test
  (require rackunit)

  ; Atomic principals
  (define A (pcpl 'A))
  (define B (pcpl 'B))
  (define C (pcpl 'C))
  (define D (pcpl 'D))

  (define a (dim 'A))
  (define b (dim 'B))
  (define foo (dim 'foo))

  (define no-dels (make-delegation-set))
  (define a-b-c-dels
    (make-delegation-set (labeled (≽ B A) A)
                         (labeled (≽ C B) B)))
  (define b-or-c-dels
    (make-delegation-set (labeled (≽ B A) A)
                         (labeled (≽ C A) A)))

  (test-case
   "bottom"
   (check-true (acts-for? no-dels A ⊥ ⊥)))

  (test-case
   "bottom-false"
   (check-false (acts-for? no-dels ⊥ A ⊥)))

  (test-case
   "top"
   (check-true (acts-for? no-dels ⊤ A ⊥)))

  (test-case
   "top-false"
   (define cheat-set (make-delegation-set (labeled (≽ A ⊤) A)))
   (check-false (acts-for? cheat-set A ⊤ ⊤)))

  (test-case
   "refl-principal"
   (check-true (acts-for? no-dels A A ⊥)))

  (test-case
   "refl-principal-false"
   (check-false (acts-for? no-dels A B (∨ A B))))

  (test-case
   "refl-proj"
   (check-true (acts-for? no-dels (▹ A a) (▹ A a) ⊥)))

  (test-case
   "refl-proj-false-pcpl"
   (check-false (acts-for? no-dels (▹ A a) (▹ B a) ⊥)))

  (test-case
   "refl-proj-false-dim"
   (check-false (acts-for? no-dels (▹ A a) (▹ A b) ⊥)))

  (test-case
   "refl-conj"
   (check-true (acts-for? no-dels (∧ (▹ A a) (▹ B b)) (∧ (▹ B b) (▹ A a)) ⊥)))

  (test-case
   "refl-conj-false"
   (check-false (acts-for? no-dels (∧ (▹ A a) (▹ B b)) (∧ (▹ C b) (▹ A a)) ⊥)))

  (test-case
   "refl-disj"
   (check-true (acts-for? no-dels (∨ (▹ A a) (▹ B b)) (∨ (▹ B b) (▹ A a)) ⊥)))

  (test-case
   "refl-disj-false"
   (check-false (acts-for? no-dels (∨ (▹ A a) (▹ B b)) (∨ (▹ C b) (▹ D a)) ⊥)))

  (test-case
   "proj"
   (check-false (acts-for? a-b-c-dels (▹ B a) (▹ A a) ⊥)))

  (test-case
   "proj-false"
   (check-false (acts-for? a-b-c-dels (▹ B a) (▹ A b) ⊥)))

  (test-case
   "proj-subset"
   (define proj-dels (make-delegation-set (labeled (actsfor (▹ A a) (▹ B a)) ⊤)))
   (check-false (acts-for? proj-dels (▹ A a b) (▹ B a b) ⊥)))
  
  (test-case
   "proj-right"
   (check-true (acts-for? a-b-c-dels A (▹ A a) ⊥)))

  (test-case
   "proj-right-subproj"
   (check-true (acts-for? a-b-c-dels (▹ A a) ⊥ (normalize (▹ (▹ A a) b)))))

  (test-case
   "proj-right-subproj-false"
   (check-false (acts-for? a-b-c-dels (normalize (▹ (▹ A a) b)) (▹ A a) ⊥)))

  (test-case
   "proj-right-false"
   (check-false (acts-for? a-b-c-dels A (▹ B a) ⊥)))

  (test-case
   "lift-proj"
   (define dels (make-delegation-set (labeled (actsfor A (∨ B C)) ⊤)))
   (check-false (acts-for? dels (▹ A foo) (normalize (▹ (∨ B C) foo)) ⊥)))

  (test-case
   "conj-left"
   (check-true (acts-for? a-b-c-dels (∧ A B) B ⊥)))

  (test-case
   "conj-left-false"
   (check-false (acts-for? b-or-c-dels (∧ B C) D ⊥)))

  (test-case
   "conj-right"
   (check-true (acts-for? a-b-c-dels C (∧ A B) ⊥)))

  (test-case
   "conj-right-false"
   (check-false (acts-for? a-b-c-dels A (∧ A B) ⊥)))

  (test-case
   "disj-left"
   (check-true (acts-for? b-or-c-dels (∨ B C) A ⊥)))

  (test-case
   "disj-left-false"
   (check-false (acts-for? b-or-c-dels (∨ B D) A ⊥)))

  (test-case
   "disj-right"
   (check-true (acts-for? b-or-c-dels B (∨ A C) ⊥)))

  (test-case
   "disj-right-false"
   (check-false (acts-for? b-or-c-dels D (∨ B C) ⊥)))

  (test-case
   "trans"
   (check-true (acts-for? a-b-c-dels C A ⊥)))

  (test-case
   "trans-false"
   (check-false (acts-for? a-b-c-dels A C ⊥)))

  (test-case
   "delegation"
   (check-true (acts-for? a-b-c-dels C A A)))

  (test-case
   "delegation-false"
   (define cheater-dels
     (make-delegation-set (labeled (≽ B A) A)
                          (labeled (≽ C B) C)))
   (check-false (acts-for? cheater-dels C A A)))

  (test-case
   "duplicate-subgoals"
   (check-false (acts-for? (make-delegation-set (labeled (≽ C A) C)) (∨ B C) A ⊥)))

  (test-case
   "jif test case"
   (check-true (acts-for? (make-delegation-set)
                          (normalize (∧ (∨ A C) (∨ A D) (∨ B C) (∨ B D)))
                          (normalize (∨ (∧ A B) (∧ C D)))
                          ⊥)))
                         
  (test-case
   "delegation-projection"
   (define dels
     (make-delegation-set (labeled (≽ A B) ⊤)
                          (labeled (≽ B (▹ C a)) ⊤)))
   (check-false (acts-for? dels (▹ A a) (▹ C a) ⊥)))
  
  (test-case
   "left-closure"
   (define new-world
     (make-delegation-set (labeled (≽ (← A a-b-c-dels) A) ⊤)))
   (check-true (acts-for? new-world B A ⊥)))
  (test-case
   "right-closure"
   (define new-world
     (make-delegation-set (labeled (≽ B (→ A a-b-c-dels)) ⊤)))
   (check-true (acts-for? new-world B A ⊥))))
