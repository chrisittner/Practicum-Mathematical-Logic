
;; lambda terms will be used to represent derivations
(load "lambda-calculus.scm")


;; Propositional logic with "->" primitive & further defined connectives ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (is-implication? formula)
  (and (list? formula)
       (= (length formula) 3)
       (eq? (car formula) '->)
       (is-formula? (cadr formula))
       (is-formula? (caddr formula))))




(define (is-formula? formula)
  (or (is-variable? formula) (is-implication? formula)))



;; defining new sentential connectives/operators ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (BLOCKED-SYMBOLS) '())

(define CONNECTIVES '())
(define (_ARITY name)     (2nd (assoc name CONNECTIVES)))
(define (_I-CLAUSES name) (3rd (assoc name CONNECTIVES)))

(define (add-connective name arity i-clauses)
  (if #t ;; check form + strict positivity
      (set! CONNECTIVES
            (append (list name arity i-clauses) CONNECTIVES))
      (error "bla")))

;; this (1) extends the formula language by the connective 'name' and
;;      (2) extends the proof term language by functions symbols 'name+_n' and 'name-'
;; TODO: update is-formula, is-derivation, check-derivation
;; TODO: -display current connectives (formula language)
;;       -display current rules/term languag

;; for PDF: add consistency, normalisation, conservativity proof, if applicable

;; returns the general elimination rule for the given connective,
;; derived from its introduction rules
(define (elimination-clause name)
  (let ((evar (gen-var "C" (_ARITY name))))
    (list '-> (append (list name) (_ARITY name))
          (list '-> ;competitor-satisfies-clauses
                (append (list evar) (_ARITY name)))))

(add-connective 'neg  '(A)   '((-> (-> A bot) (neg A))))
(add-connective 'lor  '(A B) '((-> A (lor A B))
                               (-> B (lor A B))))                               
(add-connective 'land '(A B) '((-> A (-> B (land A B)))))
;(add-connective 'weak-or  '(A B) '(-> (neg (-> (neg A) (neg B))) (lor A B)))






;; term (list (list var formula) ..) -> boole
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

;; term (list (list var formula) ..) -> formula
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
      





;; Interactive helper for bottom-to-top derivation construction

;; We need the following global state triple:
;; (1) a goal formula
;; (2) a partial derivation term (a derivation term with '?_1' variables)
;; (3) a list of open subgoals, their formula types and their contexts, the first one being currently active
(define PPROOF-STATE '())

(define (_GOAL)     (1st PPROOF-STATE))
(define (_PPROOF)   (2nd PPROOF-STATE))
(define (_SUBGOALS) (3rd PPROOF-STATE))

(define (_CURGOAL-VAR) (1st (1st (_SUBGOALS))))
(define (_CURGOAL)     (2nd (1st (_SUBGOALS))))
(define (_CONTEXT)     (3rd (1st (_SUBGOALS))))

;; TODO
(define (print-proof-state)
  ;; print context
  ;; print current subgoal)
  '())

(define (set-goal formula context)
  (begin (set! PPROOF-STATE (list formula '?_0 (list '?_0 context)))
         (print-proof-state)))

;; moves antecedent(s) of current subgoal into context.
;; requires subgoal to be of (nested) implication form.
;; takes one or more names.
(define (assume name . more-names)
    (if (not (is-implication? (_CURGOAL)))
        (error "cannot assume: active subgoal not in implication form"))
        (let* ((antecedent  (2nd (_CURGOAL)))
               (consequent  (3rd (_CURGOAL)))
               (new-subgoal consequent)
               (new-context (append (list name antecedent) (_CONTEXT)))
               (new-pproof  (substitute (_PPROOF)
                                (_CURGOAL-VAR)
                                (list 'lambda (list name) (_CURGOAL-VAR)))))
          (begin
            (set! PPROOF-STATE
                  (list (_GOAL)
                        new-pproof
                        (append (list (_CURGOAL-VAR) new-subgoal new-context)
                                (cdr (_SUBGOALS)))))
            (if (not (null? more-names))
                (apply assume more-names)
                (print-proof-state)))))
        
;; use
;; intro
;; elim
;; inst
  
;(define (use avar)
;  ;; check if (1) in context or (2) a saved proof
;  (let ((aformula (cdr (assoc avar (_CONTEXT)))))
;    (cond
;      ((and (not (equal? (_CURGOAL) aformula)) (is-implication? aformula))
;       (do (              ;create new subgoal for antecedent 
;             )
;         (and (not (equal? (_CURGOAL) aformula)) (is-implication? aformula))))
;      ((equal? (_CURGOAL) aformula)
;          (set! PPROOF-STATE (list (_GOAL)
;                                   (substitute (_PPROOF) (_CURGOAL-VAR) avar)
;                                   (cdr (_SUBGOALS))))
;          ; print update and proof-state "ok, can be obtained from..."
;          )
;      (else (error "cannot use..")))))

(define THEOREMS '())

(define (save-proof name)
  (if #f ;proof is finished
      (begin
        (set! THEOREMS (append (list name (_GOAL) (_PPROOF)) THEOREMS))
        ; print saved...
        )
      (error "cannot save an unfinished proof")))











