(load "2-untyped-lambda-calculus.scm")

;; Propositional logic with inductively defined connectives ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (is-formula? formula)
  (or (is-variable? formula)
      (is-implication? formula)
      (is-defined-connective? formula)))

(define (is-implication? formula)
  (and (list? formula)
       (= (length formula) 3)
       (eq? (car formula) '->)
       (is-formula? (cadr formula))
       (is-formula? (caddr formula))))

;; Global variable for storing defined sentential connectives
(define CONNECTIVES '())
;; A defined connective is a triple
;;        (name-symbol arguments introduction-clauses)
;; consisting in the connectives <name-symbol> (e.g. '&), <arguments> (e.g. '(A B)),
;; and its <i-clauses>: a list of introduction-clauses, each of which is a chain of
;; implications with the new connective as consequent:
;;        ('-> some-formula (new-connective ..))
;; e.g. '((-> A (-> B (& A B))))
(define (_ARGUMENTS name)     (2nd (assoc name CONNECTIVES)))
(define (_I-CLAUSES name) (3rd (assoc name CONNECTIVES)))

;; Note that all connectives are used in Scheme prefix notation
(define (is-defined-connective? formula)
  (and (list? formula)
       ;; (1) is in CONNECTIVES?
       (member? (1st formula) (map car CONNECTIVES))
       ;; (2) has correct number of arguments?
       (= (length formula) (+ 1 (length (_ARGUMENTS (1st formula)))))
       ;; (3) each argument is a formula?
       (and (map is-formula? (cdr formula)))))


;; Extends the language with a defined connective.
;; For parameter info see comment above, near CONNECTIVES. Example use:
;;        (add-connective '& '(A B) '((-> A (-> B (& A B)))))
(define (define-connective name arguments i-clauses)
  (if (and (symbol? name)
           (list? arguments)
           (and (map symbol? arguments))
           (list? i-clauses)
           ;; check if i-clauses are chained implications ending with new connective formula:
           (letrec ((new-formula (cons name arguments))
                    (strip-antecedents
                      (lambda (formula) (if (is-implication? formula)
                                           (strip-antecedents (3rd formula)) formula))))
             (begin ;(and (map (lambda (i-clause) (equal? (strip-antecedents i-clause) new-formula))
                     ;  i-clauses))
                    (display new-formula)
                    (display i-clauses)
                    (display (map display i-clauses))
                    #t)
             )
           )
  (set! CONNECTIVES (cons (list name arguments i-clauses) CONNECTIVES))
  (error "ERROR: not a valid connective definition")))

;; Computes the inductive elimination clause for the given connective
(define (elimination-clause name arguments i-clauses)
  (let* ((elim-var (gen-var "C" arguments))
         (ind-clause (map (lambda (i-clause)
                            (list (1st i-clause)
                                  (2nd i-clause)
                                  (cons elim-var arguments)))
                          i-clauses)))
    (list '-> (cons name arguments)
          (list '-> ind-clause (cons elim-var arguments)))))


(define (display-connectives)
  (for-each (lambda (C) (display C) (newline)) CONNECTIVES))

;; Test: Define usual connectives
(define-connective 'neg  '(A)   '((-> (-> A bot) (neg A))))
(define-connective '&    '(A B) '((-> A (-> B (& A B)))))
(define-connective 'v    '(A B) '((-> A (v A B))
                                  (-> B (v A B))))
;(define-connective 'weak_v   '(A B) '((-> (neg (-> (neg A) (neg B))) (weak_v A B))))
;(define-connective 'weak_->  '(A B) '((-> (weak-v (neg A) B) (weak_-> A B))))
;(define-connective 'weak_neg '(A B) '((-> (neg (neg (neg A))) (weak_neg A))))
;(display-connectives)


;; For each defined connective 'name, we allow term constants 
;;    'name+_n' and 'name-'
;; in derivation terms. They express the n-th introduction rule (and the e-rule)
;; for the defined connective. Their (schematic) type is given by the i-clauses of 'name.

;; Takes information of a defined connective and returns the list
;; of associated term constants together with their parameters
;; and respective (schematic) types
(define (derivation-constants name arguments i-clauses)
  (letrec ((e-constant (list (symbol-append name '-)
                             (elimination-clause name arguments i-clauses)))
           (i-constants (lambda (i-clauses n)
                          (if (not (null? i-clauses))
                              (cons (list (symbol-append name '+_ (number->symbol n))
                                          arguments
                                          (1st i-clauses))
                                    (i-constants (cdr i-clauses) (+ 1 n)))
                               '()))))
    (append (i-constants i-clauses 0) (list e-constant))))
    
;; list of (implicitly) defined term constants, corresponding to current CONNECTIVES
(define (_IE-TERM-CONSTANTS)
  (apply append (map (lambda (C) (apply derivation-constants C)) CONNECTIVES)))

(define (display-ie-term-constants)
  (for-each (lambda (C) (display C) (newline)) (_IE-TERM-CONSTANTS)))

;(display-ie-term-constants)


;; when constants appear in derivations their arguments (for
;; example A,B in "A->B->A&B") have to be replaced with
;; concrete instances. We need some functions for doing so:

;; propositional substitution ("specialization"): replaces all
;; occurrences of <variable> with <instance-formula> in <formula>.
(define (specialize-formula formula variable instance-formula)
  '() ;; TODO
  )

;; checks if formula1 can be obtained from  formula2 via substitution.
;; returns #f if not; if yes, returns list of substitutions of form
;;     ((variable1 instance-formula1) ..)
(define (is-specialization-of? formula1 formula2)
  '() ;; TODO
  )

;; checks if <term> is (a specialization of) an i/e-constant for any defined
;; connective. If so, return a pair '(A B), with A being the constant and B
;; B it's (specialized) type.
(define (is-ie-constant-instance? term context)
  '() ;; TODO
  )

;; i/e-clauses contain schematic variables (A,B,C,..),
;; if <term> is a i/e-constant instance, this functions adds the
;; correctly specialised type of the constant to the context
(define (add-ie-rules-instances term context)
  (let ((inst-info (is-ie-constant-instance? term context)))
    (if (inst-info)
        (let ((ie-constant  (1st inst-info))
              (instant-type (2nd inst-info)))
          (cons (ie-constant instant-type) context)
          context))))


;; term (list (list var formula) ..) -> boole
(define (is-valid-derivation? term context)
  (let ((context (add-ie-rules-instances term context)))
    (and (is-lambda-term? term)
         (cond
           (is-variable? term)
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
  (let ((context (add-ie-rules-instances term context)))
    (cond
      ((is-variable? term)
       (cadr (assoc term context)))
      ((is-application? term)
       (caddr (infer-formula (car term) context)))
      ((is-abstraction? term)
       (let ((antecedent (infer-formula (caadr term) context))
             (consequent (infer-formula (caddr term) context)))
         (list '-> antecedent consequent))))))


;; TODO: extend as follows
;  if formulas do not match but the derived formula can be
;  specialized to target formula by instantiating propositional
;  variables that do not appear in the context, then it still
;  counts as a valid derivation
(define (is-derivation-of? term context formula)
  (and (is-valid-derivation? term context)
       (is-formula? formula)
       (equal? (infer-formula term context) formula)))
