(load "4-propositional-logic.scm")


;; (Naive) Proof Search for implicational logic ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; apply function f to every pair of elements from list l
(define (apply-pairwise f l)
  (apply append
         (map (lambda (p1) (map (lambda (p2) (f p1 p2)) l))
              l)))
;; checks if f1 can type-correctly be applied to f2
(define (applicable? f1 f2)
  (and (is-implication? f1) (equal? (cadr f1) f2)))
;; apply two assumptions from the context to one another,
;; return resulting (term formula)-pair.
(define (app a-pair1 a-pair2)
  (list (list (car a-pair1) (car a-pair2)) (caddr (cadr a-pair1))))


(define (search-proof goal context)
  (cond 
    ((member goal (map cadr context))
     ;; (1) gf already in the context => return its assumption variable
     (caar (my-filter (lambda (p) (equal? (cadr p) goal)) context)))
    ((is-implication? goal)
     ;; (2) implication => use abstraction (-> intro rule) to move premise to context
     (let* ((a-var         (gen-var "a" (map car context)))
            (a-formula     (cadr goal))
            (subgoal       (caddr goal))
            (subgoal-proof (search-proof subgoal
                             (append (list (list a-var a-formula)) context))))
       (if subgoal-proof (list 'lambda (list a-var) subgoal-proof) #f)))
    (else
     ;; (3) otherwise add forward inferences to context, retry.
     (let* ((infer-with (lambda (p1 p2)
               (if (applicable? (cadr p1) (cadr p2)) (list (app p1 p2)) '())))
            (infs (apply append (apply-pairwise infer-with context))))
       (if (null? infs) #f (search-proof goal (append infs context)))))))


(search-proof '(-> (-> (-> a b) a) a) '()) ;; => #f

(search-proof '(-> (-> a (-> b c)) (-> (-> a b) (-> a c))) '())
;; => (lambda (a0) (lambda (a1) (lambda (a2) ((a0 a2) (a1 a2)))))

(search-proof '(-> (-> a b) (-> (-> b c) (-> a c))) '())
;; => (lambda (a0) (lambda (a1) (lambda (a2) (a1 (a0 a2)))))
;; => (\ a0 -> (\ a1 -> (\ a2 -> (a1 (a0 a2)))))









;; Propositional proof search ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A *partial proof* is a quardruple
;;   (goal partial-term partial-term-context subgoals)
;; where:
;;   goal         = formula to be derived
;;   partial-term = a derivation term, which may contain variables of form '?_0, '?_1, '?_14, ..
;;                  each occurring ?_n must appear in subgoals
;;   subgoals     = a list of triples (var subformula context), where var is of form '?_n


;; Returns a new partial proof of formula 'goal'.
(define (start-proof goal)
  (list (goal '?_0 '() '())))

(define (proof-finished? partial-proof)
  (let ((goal     (1st partial-proof))
        (term     (2nd partial-proof))
        (context  (3rd partial-proof))
        (subgoals (4th partial-proof)))
    (and (null? subgoals)
         (is-derivation-of? goal term context))))
  

;; Attempts to complete a given partial-proof.
;; Returns a new partial proof, with ?_n replaced where possible.
(define (complete-proof partial-proof)
  #f)

(define (search-proof formula)
  (let ((proof-attempt (search-proof (start-proof formula))))
    (if (proof-finished? proof-attempt)
        (list (2nd proof-attempt) (3rd proof-attempt))
        #f)))
        

;; A *tactic* is any function that modifies a partial proof.











