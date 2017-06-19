;; (simply typed) lambda terms is used to represent derivations
(load "2-untyped-lambda-calculus.scm")

;; Minimal implicational logic & derivations ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (is-implication? formula)
  (and (list? formula)
       (= (length formula) 3)
       (eq? (car formula) '->)
       (is-formula? (cadr formula))
       (is-formula? (caddr formula))))

(define (is-formula? formula)
  (or (is-variable? formula) (is-implication? formula)))


(define (is-valid-derivation? term context)
  (and (is-lambda-term? term)
       (cond
         ((is-variable? term)
          (unique-assoc term context)
         ((is-application? term)
          (let ((f1 (infer-formula (car term) context))
                (f2 (infer-formula (cadr term) context)))
            (and (is-valid-derivation? (car term) context)
                 (is-valid-derivation? (cadr term) context)
                 (is-implication? f1)
                 (eq? (cadr f1) f2))))
         ((is-abstraction? term)
          (and (is-valid-derivation? (caddr term) context)
               (unique-assoc (caadr term) context)))))))

(define (infer-formula term context)
  (cond
    ((is-variable? term)
     (cadr (assoc term context)))
    ((is-application? term)
     (caddr (infer-formula (car term) context)))
    ((is-abstraction? term)
     (let ((antecedent (infer-formula (caadr term) context))
           (consequent (infer-formula (caddr term) context)))
       (list '-> antecedent consequent)))))

(define (is-derivation-of? term context formula)
  (and (is-valid-derivation? term context)
       (is-formula? formula)
       (equal? (infer-formula term context) formula)))
      

;; Proof checking examples:
;(define proposition1 '(-> (-> A (-> B C)) (-> (-> A B) (-> A C))))
;(define term1        '(lambda (u) (lambda (w) (lambda (v) ((u v) (w v))))))
;(define context1     '((u (-> A (-> B C))) (v A) (w (-> A B))))

;(is-formula? proposition1)
;(infer-formula term1 context1)
;(is-valid-derivation? term1 context1)
;(is-derivation-of? term1 context1 proposition1)


;; (Naive) Proof Search ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (applicable? f1 f2)
  (and (is-implication? f1) (equal? (cadr f1) f2)))
;; apply two assumptions from the context to one another,
;; return resulting (term formula)-pair.
(define (app a-pair1 a-pair2)
  (list (list (car a-pair1) (car a-pair2)) (caddr (cadr a-pair1))))

;; TODO: Fails to use vacuous assumptions (weakening).
(define (search-proof goal context)
  (cond 
    ((member goal (map cadr context))
     ;; (1) gf already in the context => return its assumption variable
     (caar (my-filter (lambda (p) (equal? (cadr p) goal)) context)))
    ((is-implication? goal)
     ;; (2) implication => use abstraction (-> intro)
     (let* ((a-var         (gen-var "a" (map car context)))
            (a-formula     (cadr goal))
            (subgoal       (caddr goal))
            (subgoal-proof (search-proof subgoal
                             (append (list (list a-var a-formula)) context))))
       (if subgoal-proof (list 'lambda (list a-var) subgoal-proof) #f)))
    (else
     ;; (3) otherwise add forward inferences to context, retry.
     (let* ((infer-with (lambda (p1) (lambda (p2)
               (if (applicable? (cadr p1) (cadr p2)) (list (app p1 p2)) '()))))
            (infs (apply append (map (lambda (p1)
                  (apply append (map (infer-with p1) context))) context))))
       (if (null? infs) #f (search-proof goal (append infs context)))))))


;(search-proof '(-> (-> (-> a b) a) a) '()) ;; => #f

;(search-proof '(-> (-> a (-> b c)) (-> (-> a b) (-> a c))) '())
;; => (lambda (a0) (lambda (a1) (lambda (a2) ((a0 a2) (a1 a2)))))

;(search-proof '(-> (-> a b) (-> (-> b c) (-> a c))) '())
;; => (lambda (a0) (lambda (a1) (lambda (a2) (a1 (a0 a2)))))
