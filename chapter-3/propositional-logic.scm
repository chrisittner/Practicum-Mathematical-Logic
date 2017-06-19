;; Helper Functions ;;
;;;;;;;;;;;;;;;;;;;;;;

(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

;; For DrRacket+R5RS compatibility, because 'filter' not present in R5RS
(define (my-filter pred list)
  (cond ((null? list) '())
        ((pred (car list))
         (cons (car list) (my-filter pred (cdr list))))
        (else (my-filter pred (cdr list)))))

(define (list-remove-item item list)
  (my-filter (lambda (x) (not (equal? x item))) list))

;; return a fresh variable symbol starting with 'prefix' that is not in set 'used-vars'
(define (gen-var prefix used-vars . counter)
  (let* ((counter (if (null? counter) 0 (car counter)))
        (candidate-var (string->symbol
                        (string-append prefix (number->string counter)))))
    (if (not (member candidate-var used-vars))
        candidate-var (gen-var prefix used-vars (+ 1 counter)))))

;; check if var is assigned a unique type in context
(define (unique-assoc var context)
  (= 1 (length (my-filter (lambda (p) (eq? var (car p))) context))))


;; Lambda Terms ;;
;;;;;;;;;;;;;;;;;;

(define is-variable? symbol?)

(define (is-application? term)
  (and (= (length term) 2)
       (is-lambda-term? (car term))
       (is-lambda-term? (cadr term))))

(define (is-abstraction? term)
  (and (= (length term) 3)
       (eq? (car term) 'lambda)
       (list? (cadr term))
       (= (length (cadr term)) 1)
       (symbol? (caadr term))
       (is-lambda-term? (caddr term))))

(define (is-lambda-term? term)
  (or (is-variable? term) (is-application? term) (is-abstraction? term)))

;; term -> (list var ..)
(define (free-vars t)
  (cond
    ((is-variable? t)    (list t))
    ((is-application? t) (append (free-vars (car t)) (free-vars (cadr t))))
    ((is-abstraction? t) (list-remove-item (caadr t) (free-vars (caddr t))))))

;; term var var -> term
(define (rename-var t x y)
  (cond
    ((is-variable? t)
     (if (eq? t x) y t))
    ((is-application? t)
     (list (rename-var (car t) x y) (rename-var (cadr t) x y)))
    ((is-abstraction? t)
     (if (eq? (caadr t) x)
         t
         (list 'lambda (cadr t) (rename-var (caddr t) x y))))))

;; term var term -> term
(define (substitute t x t-sub)
  (cond
    ((is-variable? t)
     (if (eq? t x) t-sub t))
    ((is-application? t)
     (list (substitute (car t) x t-sub) (substitute (cadr t) x t-sub)))
    ((is-abstraction? t)
     (if (eq? (caadr t) x)
       t
       ;; here we need to be careful to avoid variable capture
       (if (not (member (caadr t) (free-vars t-sub)))
           (list 'lambda (cadr t) (substitute (caddr t) x t-sub))
           ;; in this case, the bound variable (cadr t) occurs freely
           ;; in the term we are substituting. We need to rename (cadr t).
           (let* ((used-vars (append (free-vars (caddr t)) (free-vars t-sub)))
                  (new-var (gen-var "a" used-vars))
                  (renamed-term (rename-var (caddr t) (caadr t) new-var)))
             (list 'lambda new-var (substitute renamed-term x t-sub))))))))

;; term -> term
(define (eval-term t)
  (cond
    ((is-variable? t) t)
    ((is-application? t)
     (if (and (list? (car t)) (= (length (car t)) 3))
         ;; t of form '((lambda (x) M) N)
         (eval-term (substitute (caddr (car t)) (caadr (car t)) (cadr t)))
         ;; otherwise '(M N)
         (list (eval-term (car t)) (eval-term (cadr t)))))
    ((is-abstraction? t) (list 'lambda (cadr t) (eval-term (caddr t))))))


;; Implicational minimal logic & dervation terms ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (is-implication? formula)
  (and (list? formula)
       (= (length formula) 3)
       (eq? (car formula) '->)
       (is-formula? (cadr formula))
       (is-formula? (caddr formula))))

(define (is-formula? formula)
  (or (is-variable? formula) (is-implication? formula)))

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
      

;; proof search for implicational minimal logic ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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









  
;;-----------------------------------------------
;; Many-sorted quantifier logic
;; Extension to handle all-quantifier and algebraic data types

;; we now move to predicate logic, to allow reason about objects of various domains.
;; The extension introduces:

;; domains of quantification (algebraic data types) and a command to introduce them (by constructor expressions)

;; an algebra is a triple (name list-of-constructors
;(define ALGEBRAS '())

;(add-alg 'Nat '(Zero (Suc Nat)))

;; each newly defined algebraic data type yields two new domains of quantification:
;;     - its (co)total objects (adt=(co)inductive set)
;;     - its partial computation states (adt="Scott-Ershov Domain")
;; totality as extensionality for type 2 objects and higher?

;; object variables and constants to range over defined domains
;; variable types need to be declared before an (object) variable can be used.

;; terms
;; an all-quantifer





;; Extension to handle predicates
;; Extension to handle computation rules
;; totality


