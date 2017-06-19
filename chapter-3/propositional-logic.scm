
;; lambda terms will be used to represent derivations
(load "lambda-calculus.scm")


;; Propositional logic with "->" primitive & inductively defined connectives ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (all connectives are in prefix notation)

(define (is-implication? formula)
  (and (list? formula)
       (= (length formula) 3)
       (eq? (car formula) '->)
       (is-formula? (cadr formula))
       (is-formula? (caddr formula))))

;; global variable for storing currently defined sentential connectives/operators
(define CONNECTIVES '())
;; each connective is a triple (name-symbol arity introduction-clauses) where
;;   - arity is the list of arguments for the connective
;;   - introduction-clauses is a list of formulas of shape
;;         (some-formula -> (new-connective ..))

(define (_ARITY name)     (2nd (assoc name CONNECTIVES)))
(define (_I-CLAUSES name) (3rd (assoc name CONNECTIVES)))

(define (is-defined-connective? formula)
  (and (list? formula)
       ;; (1) is in CONNECTIVES
       (member? (1st formula) (map car CONNECTIVES))
       ;; (2) has correct number of arguments
       (= (length formula) (+ 1 (length (_ARITY (1st formula)))))
       ;; (3) each argument is a formula
       (and (map is-formula? (cdr formula)))))

(define (is-formula? formula)
  (or (is-variable? formula)
      (is-implication? formula)
      (is-defined-connective? formula)))


;; Extends the language by with a defined connective
;; e.g. (add-connective '& '(A B) '((-> A (-> B (& A B)))))
;;   - arity is the list of arguments for the connective
;;   - i-clauses is a (non-empty) list of introduction clauses of shape
;;        (some-formula -> (new-connective ..)
;;     the new connective may only appear "strictly positive" in 'some-formula.
(define (define-connective name arity i-clauses)
  (if #t ;; TODO: check form + strict positivity
      (set! CONNECTIVES
            (cons (list name arity i-clauses) CONNECTIVES))
      (error "ERROR: not a valid definition")))

(define (display-connectives)
  (for-each (lambda (C) (display C) (newline)) CONNECTIVES))

;; returns the general elimination rule for the given connective,
;; derived from its introduction rules
(define (elimination-clause name arity i-clauses)
  (let ((evar (gen-var "C" arity)))
    (list '-> (append (list name) arity)
          (list '-> ;; TODO: express "the competitor evar satisfies all i-clauses"
                (append (list evar) arity)))))


;; Test: Define usual connectives
(define-connective 'neg  '(A)   '((-> (-> A bot) (neg A))))
(define-connective '&    '(A B) '((-> A (-> B (& A B)))))
(define-connective 'v    '(A B) '((-> A (v A B))
                                  (-> B (v A B))))
;(define-connective 'weak-v  '(A B) '(-> (neg (-> (neg A) (neg B))) (weak-v A B)))
(display-connectives)


;; a list of implicitly defined term constants (corresponding to currently defined connectives)
;;   for each defined connective 'name, define term constants
;;      'name+_n' and 'name-'
;;   They express the n-th introduction rule or the elimination rule
;;   for the defined connective. Their type is given by the i-clauses of 'name.
;; TODO finish
(define (_IE-TERM-CONSTANTS)
  (let ((introduction-constants (apply append (map (lambda (name arity i-clauses)
                                                     (map (lambda (i-clause)
                                                            (list (symbol-append name '+_N) i-clause))
                                                          i-clauses))
                                                   CONNECTIVES)))
        (elimination-constants (map (lambda (name arity i-clauses)
                                     (list (symbol-append name '-) (elimination-clause name)))
                                   CONNECTIVES)))
       (append introduction-constants elimination-constants)))


;; term (list (list var formula) ..) -> boole
(define (is-valid-derivation? term context)
  (let ((context (append context (_DEFINED-TERM-CONSTANTS))))
    (and (is-lambda-term? term)
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

;; term (list (list var formula) ..) -> formula
(define (infer-formula term context)
  (let ((context (append context (_DEFINED-TERM-CONSTANTS))))
    (cond
      ((is-variable? term)
       (cadr (assoc term context)))
      ((is-application? term)
       (caddr (infer-formula (car term) context)))
      ((is-abstraction? term)
       (let ((antecedent (infer-formula (caadr term) context))
             (consequent (infer-formula (caddr term) context)))
         (list '-> antecedent consequent))))))

(define (is-derivation-of? term context formula)
  (let ((context (append context (_DEFINED-TERM-CONSTANTS))))
    (and (is-valid-derivation? term context)
         (is-formula? formula)
         (equal? (infer-formula term context) formula))))
      










