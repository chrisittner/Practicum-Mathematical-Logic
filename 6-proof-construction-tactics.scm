(load "4-propositional-logic.scm")

;; Proof construction and tactics ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A *partial proof* is a quardruple
;;   (goal partial-term partial-term-context subgoals)
;; where:
;;   goal     = formula to be derived
;;   ppterm   = "partial proof term"
;;              a derivation term, which may contain variables of form
;;                 '?_0, '?_1, '?_14, ..
;;              each occurring ?_n must appear in subgoals
;;   ppterm-context = ...
;;   subgoals = a list of triples (var subformula local-context), where var is of
;;                  form '?_n

;; Returns a new partial proof of formula 'goal'.
(define (start-proof goal)
  (list goal '?_0 '() (list (list '?_0 goal '())))) ;; TODO: fill context from formula?!

(define (display-pproof pproof)
  (let ((goal     (1st pproof))
        (ppterm   (2nd pproof))
        (context  (3rd pproof))
        (subgoals (4th pproof)))
    (display "\n## Partial proof of ") (display goal)
    (display "\n ppterm:   ") (display ppterm)
    (display "\n context:  ") (display context)
    (display "\n subgoals: ") (display subgoals)
    (newline)))
    
  

;; Returns derivation term+context in case the proof is finished, #f otherwise.
(define (qed pproof)
  (let ((goal     (1st pproof))
        (ppterm   (2nd pproof))
        (context  (3rd pproof))
        (subgoals (4th pproof)))
    (if (and (null? subgoals) (is-derivation-of? goal ppterm context))
        (list ppterm context)
        #f)))

;; A proof *tactic* is a procedure that modifies a partial proof such that
;; the derivation (term) remains type-correct.

;; Tactics can implement steps/moves towards proving the goal-formula.
;; They typically extend the partial derivation term by simplifying the current
;; (= first) subgoal. Root-first ("bottom to top") construction of derivation
;; trees is done via tactics. Tactics may have preconditions on the current
;; goal or context and produce an error if they are not applicable.
;;
;; Basic tactics implemented below are:
;;  * (assume pproof name . more-names)
;;             If active subgoal is an implication, apply ->+-rule to move
;;             antecedent into the context with assumption label 'name'.
;;             If more than one name is given, *assume* is used repeatedly.
;;  * (use pproof a-name)
;;             Apply assumption with label 'a-name' from context, generating new
;;             subgoals for assumption premises, if necessary.
;;  * (assumption pproof)
;;             

;; Tactic *assume*: moves antecedent(s) of current subgoal into context.
;; requires subgoal to be of (nested) implication form takes one or more names.
(define (assume pproof name . more-names)
  (let* ((goal     (1st pproof))
         (ppterm   (2nd pproof))
         (context  (3rd pproof))
         (subgoals (4th pproof))
         (curgoal  (if (null? subgoals)
                       (error "*use* failed: no subgoals")
                       (1st subgoals)))
         (cur-formula (2nd curgoal)))
    (if (not (is-implication? cur-formula))
        (error "*assume* failed: current subgoal not of implication form")
        (let* ((antecedent  (2nd cur-formula))
               (consequent  (3rd cur-formula))
               (cur-goalvar (1st curgoal)) ;; e.g '?_31
               (new-goalvar (1st curgoal)) ;; make new name instead of reusing?
               (new-subgoal (list new-goalvar consequent
                                 (cons (list name antecedent) (3rd curgoal))))
               (new-ppterm  (replace ppterm cur-goalvar
                                        (list 'lambda (list name) new-goalvar)))
               (new-context (cons (list name antecedent) context))
               (new-pproof  (list goal new-ppterm new-context
                                  (cons new-subgoal (cdr subgoals)))))
          (if (not (null? more-names))
              (apply assume (cons new-pproof more-names))
              (begin
                ;(display-pproof)
                new-pproof))))))

;; Tactic *use*: Infer current subgoal from given assumption in the context.
;; Requires that the assumption has form A1 -> A1 -> .. -> G, where G is the
;; current subgoal formula. Creates a new subgoal for each of the A1,.., An.
(define (use pproof a-name)
  (let* ((ppterm  (2nd pproof))
         (subgoals (4th pproof))
         (curgoal  (if (null? subgoals)
                       (error "*use* failed: no subgoals")
                       (1st subgoals)))
         (cur-goalvar (1st curgoal))
         (cur-formula (2nd curgoal))
         (cur-context (3rd curgoal)))
    (if
     (not (member a-name (map 1st cur-context)))
     (error "use failed: assumption variable not in local context")
     (let* ((a-formula (2nd (assoc a-name cur-context)))
            (a-premises
             (letrec ((get-premises
                       (lambda (f1 f2)
                         (cond ((equal? f1 f2) '())
                               ((is-implication? f1)
                                (cons (2nd f1)
                                      (get-premises (3rd f1) f2)))
                               (else (error "*use* failed: assumption
                                  formula does not match subgoal formula"))))))
               (get-premises a-formula cur-formula)))
            (new-goalvars (map (lambda (a-p) (gen-var "?_" (map 1st subgoals)))
                               a-premises))
            (new-subgoals (map (lambda (a-p goalvar)
                                 (list goalvar a-p cur-context))
                               a-premises new-goalvars))
            (new-ppterm (replace ppterm
                                    cur-goalvar
                                    (curry-term a-name new-goalvars)))
            (new-pproof (list (1st pproof) new-ppterm (3rd pproof)
                              (append new-subgoals (cdr subgoals)))))
       new-pproof))))

;; Tactic *assumption*: Look if the current subgoal is equal to some assumption
;; in the context. If so, prove the subgoal by replacing the assumption
;; variable for the subgoal variable. Otherwise, raise an error.
(define (assumption pproof)
  (let* ((ppterm   (2nd pproof))
         (subgoals (4th pproof))
         (curgoal  (if (null? subgoals)
                       (error "*assumption* failed: no subgoals")
                       (1st subgoals)))
         (cur-goalvar (1st curgoal))
         (cur-formula (2nd curgoal))
         (cur-context (3rd curgoal)))
    (if (not (member cur-formula (map 2nd cur-context)))
        (error "*assumption* failed: current goal not in context")
        (let* ((a-pair (1st (my-filter (lambda (c) (equal? cur-formula (2nd c)))
                                       cur-context)))
               (a-name (1st a-pair)))
          (list (1st pproof)
                (replace ppterm cur-goalvar a-name)
                (3rd pproof)
                (cdr subgoals))))))

(define p1 (start-proof '(-> A (-> (-> A B) B))))
(display-pproof p1)
(define p2 (assume p1 'u 'v))
(display-pproof p2)
(define p3 (use p2 'v))
(display-pproof p3)
(define p4 (use p3 'u))
(display-pproof p4)
(newline)
(qed p4)

;(assumption p2)

;(prop-set-goal "(A -> B -> C) -> (A -> B) -> A -> C")
;(prop-assume "u" "v" "w")
;(prop-use-with "u" "w" "?")
;(prop-use-with "v" "w")


;; TODO
(define (intro pproof k)
  (let* ((ppterm  (2nd pproof))
         (subgoals (4th pproof))
         (curgoal  (if (null? subgoals)
                       (error "*intro* failed: no subgoals")
                       (1st subgoals)))
         (cur-goalvar (1st curgoal))
         (cur-formula (2nd curgoal))
         (cur-context (3rd curgoal))
         (connective  (1st cur-formula))
         (rule-const  (symbol-append connective '+_ (number->symbol k))))
    (cond
      ((not (member connective (map 1st CONNECTIVES)))
       (error "*intro* failed: goal not formed with a defined connective"))
      ((not (member rule-const (map 1st (_IE-TERM-CONSTANTS))))
       (error "*intro* failed: " k "th introduction rule does not exist"))
      (else
       (let* ((specs (2nd (is-specialization-of?
                           (cons connective (_ARGUMENTS connective))
                           cur-formula))))
         #f
         ;-- add to local context
         ;-- use
         )))))

;; TODO
;(define (elim pproof)
;    (use pproof connective "-"))








;; OPTIONAL:

;;-----------------------------------
;; Tactic *use-with*: like *use*, but accepts additional arguments to supply
;; (some of) the premises A1,..,An directly, instead of creating subgoals.
;(define (use-with pproof a-name . supplied-premises)
;  ;: 1. use 2. deal with subgoals
;                (mk-premise-term (lambda (supplied-premise a-premise)
;                    (cond ((eq? supplied-premise '?) ;; -> make new subgoal
;                            (list (gen-var "?_" ..) a-premise cur-context))
;                          ((member supplied-premise cur-context)
;                            (if (equal? a-premise
;                                        (2nd (assoc supplied-premise cur-context))))
;                                (list supplied-premise)
;                             )))



;; (define (inst-with pproof name with-name . more-with-names))
;; (define (cut pproof cut-formula))
;; (define (admit pproof))
;; (define (efq pproof) (elim pproof "F"))










;; Tactic *auto*: Attempts to complete a given pproof.
;; Returns a new partial proof, with ?_n replaced where possible.
(define (auto pproof)
  #f)
;; Idea implement the 'complete-proof' tactic as a combination of basic tactics.

(define (search-proof formula)
  (qed (auto (start-proof formula))))
    
