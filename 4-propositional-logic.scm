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
       (member (1st formula) (map car CONNECTIVES))
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
                      (lambda (formula) (if (eq? '-> (1st formula))
                                            (strip-antecedents (3rd formula)) formula))))
             (and (map (lambda (i-clause) (equal? (strip-antecedents i-clause) new-formula))
                      i-clauses))))
  (set! CONNECTIVES (cons (list name arguments i-clauses) CONNECTIVES))
  (error "ERROR: not a valid connective definition")))

;; Computes the inductive elimination clause for the given connective
(define (elimination-clause name arguments i-clauses)
  (letrec ((elim-var (gen-var "C" arguments))
           (mk-ind-clause (lambda (i-clause)
                            (if (is-implication? i-clause)
                                (list '-> (2nd i-clause) (mk-ind-clause (3rd i-clause)))
                                elim-var))))
    (list '-> (cons name arguments)
          (fold-left (lambda (i-clause result-formula)
                       (list '-> (mk-ind-clause i-clause) result-formula))
                     elim-var i-clauses))))


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
(display-connectives)


;; For each defined connective 'name, we allow term constants 
;;    'name+_n' and 'name-'
;; in derivation terms. They express the n-th introduction rule (and the e-rule)
;; for the defined connective. Their (schematic) type is given by the i-clauses of 'name.

;; Takes information of a defined connective and returns the list
;; of associated term constants together with their arguments
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

(newline)
(display-ie-term-constants)


;; when constants appear in derivations their arguments (for
;; example A,B in "A->B->A&B") have to be replaced with
;; concrete instances. We need some functions for doing so:

;; propositional substitution ("specialization"): replaces all
;; occurrences of <variable> with <instance-formula> in <formula>.
(define (specialize-formula formula variable instance-formula)
  (cond
    ((is-variable? formula)
     (if (eq? formula variable) instance-formula formula))
    ((is-implication? formula)
     (list '-> (specialize-formula (2nd formula) variable instance-formula)
               (specialize-formula (3rd formula) variable instance-formula)))
    ((is-defined-connective? formula)
     (list (car formula) (map (lambda (f) (specialize-formula f variable instance-formula)
                                (cdr formula)))))))

;(specialize-formula '(-> A B) 'B '(v X Y))

;; checks if formula2 can be obtained from  formula1 via substitution.
;; returns pair (<#t or #f> <var-specializations>), first component
;; is #t if specialization is possible, else #f; <var-specializations> is
;; list of necessary substitutions (in f1) of form (var subst-formula)
(define (is-specialization-of? f1 f2 . specializations)
  (let* ((specializations (if (null? specializations) '() (car specializations))))
    (cond
      ((equal? f1 f2) (list #t '()))
      ((is-variable? f1)
       (if (not (member f1 (map 1st specializations)))
           (list #t (cons (list f1 f2) specializations))
           (list (equal? f2 (2nd (assoc f1 specializations))) specializations)))
      ((and (is-implication? f1) (is-implication? f2))
       (let* ((result (is-specialization-of? (2nd f1) (2nd f2) specializations))
              (is-ok? (1st result))
              (antecedent-specializations (2nd result)))
         (if is-ok? 
             (is-specialization-of? (3rd f1) (3rd f2) antecedent-specializations)
             (list #f '()))))
      ((and (is-defined-connective? f1) (is-defined-connective? f2)
            (eq? (1st f1) (1st f2)))
       (fold2-left (lambda (sub-f1 sub-f2 acc)
                     (let ((result (is-specialization-of? sub-f1 sub-f2 (2nd acc))))
                       (list (and (1st acc) (1st result)) (2nd result))))
                   (#t specializations) (cdr f1) (cdr f2)))
      (else (list #f '())))))

(is-specialization-of? '(-> (-> a c) f) (specialize-formula '(-> A B) 'B '(v X Y)))

;; check if <term> (given <context>) is a type-correct application of <i-const-name>.
;; returns the list of required argument specializations ((A->f1) ..) of the instance, otherwise #f.
(define (valid-i-clause-instance? term context i-const-name i-clause connective . arg-specializations)
  (let* ((arg-specializations (if (null? arg-specializations) '() (car arg-specializations)))
         (args (_ARGUMENTS connective)))
    (cond ((and (is-implication? i-clause) (is-application? term))
           (let* ((premise-type           (infer-formula (2nd term) context)) ; '(t1 _t2_)
                  (premise-schema         (2nd i-clause))                     ; '(-> _F1_ F2)
                  (premise-specialization (is-specialization-of?
                                            premise-schema
                                            premise-type
                                            arg-specializations)))
             (if (1st premise-specialization)
                 (valid-i-clause-instance? (1st term) (3rd i-clause) (2nd premise-specialization))
                 #f)))
          ((and (eq? (1st i-clause) connective) (eq? i-const-name term))
           ; check if all required specializations are allowed.
           (if (fold-left (lambda (spec acc) (and (member (1st spec) args) acc)) #t arg-specializations)
               arg-specializations #f))
          (otherwise #f))))


;(valid-i-clause-instance? term context i-const-name i-clause connective)

(define (valid-e-clause-instance? term context e-const-name e-clause connective)
  '())
                                                      
;(valid-e-clause-instance? term context e-const-name e-clause connective)

                               


        
;; term (list (list var formula) ..) -> boole
(define (is-valid-derivation? term context)
  (and (is-lambda-term? term)
       (cond
         ((is-variable? term)
          (unique-assoc term context))
         ((ie-const-application? term)
            ;; deal with consts here
          )
         ((is-application? term)          
          (let ((f1 (infer-formula (car term) context))
                (f2 (infer-formula (cadr term) context)))
            (and (is-valid-derivation? (car term) context)
                 (is-valid-derivation? (cadr term) context)
                 (is-implication? f1)
                 (eq? (cadr f1) f2))))
         ((is-abstraction? term)
          (and (is-valid-derivation? (caddr term) context)
               (unique-assoc (caadr term) context))))))

;; term (list (list var formula) ..) -> formula
(define (infer-formula term context)
  (cond
    ((is-variable? term)
     (cadr (assoc term context)))
    ((ie-const-application? term)
       ;; deal with consts here
     )
    ((is-application? term)
     (caddr (infer-formula (car term) context)))
    ((is-abstraction? term)
     (let ((antecedent (infer-formula (caadr term) context))
           (consequent (infer-formula (caddr term) context)))
       (list '-> antecedent consequent)))))


(define (is-derivation-of? term context formula)
  (and (is-valid-derivation? term context)
       (is-formula? formula)
       (is-specialization-of? (infer-formula term context) formula)))
