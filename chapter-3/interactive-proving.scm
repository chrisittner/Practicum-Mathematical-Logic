;; lambda terms will be used to represent derivations
(load "propositional-logic.scm")

;; Interactive helper to construct derivations from bottom to top ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; We use the following global variable to keep track of the current derivation
(define PPROOF-STATE '())
;; It will contain a triple consisting of:
;; (1) a goal formula
;; (2) a partial derivation term (a derivation term with variables of form  '?_1, '?_14, ..)
;; (3) a list of open subgoalsm the first one being the currently active subgoal.
;;     Each subgoal has the form: (subgoal-variable subgoal-formula subgoal-context)


(define (_GOAL)     (1st PPROOF-STATE))
(define (_PPROOF)   (2nd PPROOF-STATE))
(define (_SUBGOALS) (3rd PPROOF-STATE))

(define (_CURGOAL-VAR) (1st (1st (_SUBGOALS))))
(define (_CURGOAL)     (2nd (1st (_SUBGOALS))))
(define (_CONTEXT)     (3rd (1st (_SUBGOALS))))

;; TODO
(define (print-proof-state)
  ;; print context
  ;; print current subgoal
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
        

;; TODO  use
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


;; TODO: intro

;; TODO: elim

;; TODO: inst-with

(define THEOREMS '())

(define (save-proof name)
  (if #f ;; TODO: if proof is finished
      (begin
        (set! THEOREMS (append (list name (_GOAL) (_PPROOF)) THEOREMS))
        ; print saved...
        )
      (error "cannot save an unfinished proof")))




