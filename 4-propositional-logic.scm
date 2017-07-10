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
                             name
                             (elimination-clause name arguments i-clauses)))
           (i-constants (lambda (i-clauses n)
                          (if (not (null? i-clauses))
                              (cons (list (symbol-append name '+_ (number->symbol n))
                                          name
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



;; Note that when constants appear in derivations their arguments (for
;; example A,B in "A->B->A&B") are replaced with concrete instances.

;; term (list (list var formula) ..) -> boole
(define (is-valid-derivation? term context)
  (and (is-lambda-term? term)
       (cond
         ((is-variable? term)
          (unique-assoc term context))
         ((ie-const-application? term)
          (1st (valid-ie-clause-instance? term context)))
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
     (let* ((res (valid-ie-clause-instance? term context))
            (inferred-formula (2nd res)))
       inferred-formula))
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




;; propositional substitution ("specialization"): replaces all
;; occurrences of <variable> with <instance-formula> in <formula>.
(define (specialize formula variable instance-formula)
  (cond
    ((is-variable? formula)
     (if (eq? formula variable) instance-formula formula))
    ((is-implication? formula)
     (list '-> (specialize (2nd formula) variable instance-formula)
               (specialize (3rd formula) variable instance-formula)))
    ((is-defined-connective? formula)
     (cons (car formula) (map (lambda (f) (specialize f variable instance-formula))
                              (cdr formula))))))
;(specialize '(-> A B) 'B '(v X Y))

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
;(is-specialization-of? '(-> (-> a c) f) (specialize '(-> A B) 'B '(v X Y)))


;; Converts a (possibly left-nested) application term into a pair (t args),
;; where t is the innermost left applicant and args is the list of arguments of t.
;; Example: (((t0 t1) t2) t3) --> (t0 (t1 t2 t3))
(define (uncurry-term term)
  (if (is-application? term)
      (let ((lterm (uncurry-term (1st term))))
        (list (1st lterm) (append (2nd lterm) (list (2nd term)))))
      (list term '())))

;; Converts a (possibly right-nested) implication chain formula into a pair
;;      (premise-list conclusion).
;; Example: (-> p1 (-> p2 (-> p3 concl))) --> ((p1 p2 p3) concl)      
(define (list-premises formula)
  (if (is-implication? formula)
      (let ((rformula (list-premises (3rd formula))))
        (list (cons (2nd formula) (1st rformula))  (2nd rformula)))
      (list '() formula)))
;; The inverse: builds a nested implication from a premise-list and conclusion
(define (unlist-premises premise-list conclusion)
  (if (null? premise-list)
      conclusion
      (list '-> (car premise-list) (unlist-premises (cdr premise-list conclusion)))))
      

;; Checks if term is an introduction- or eliminiation-constant applied
;; to one or more terms. returns the constant name, otherwise #f.
(define (ie-const-application? term)
  (let* ((ucterm   (uncurry-term term))
         (const    (1st ucterm))
         (num-args (length (2nd ucterm))) ; # of subterms the constant is applied to
         (ie-const (assoc const (_IE-TERM-CONSTANTS))))
    (if (and ie-const
             (<= num-args
                 (length (1st (list-premises (3rd ie-const)))))) ; # of premises in i/e-clause
        const #f)))


;; check if <term> (given <context>) is a type-correct application of <ie-const>.
;; returns a triple:
;;    '(is-valid? type specializations)
;; e.g. (#t '(& A B) '()).
(define (valid-ie-clause-instance? term context)
  (let* ((uncurried-term  (uncurry-term term))
         (ie-const        (car uncurried-term))
         (connective      (2nd (assoc ie-const (_IE-TERM-CONSTANTS))))
         (ie-clause       (3rd (assoc ie-const (_IE-TERM-CONSTANTS))))
         (ie-premises     (1st (list-premises ie-clause)))
         (ie-conclusion   (2nd (list-premises ie-clause)))
         (app-terms       (2nd uncurried-term))
         (app-formulas    (map (lambda (t) (infer-formula t context)) app-terms))
         (args            (_ARGUMENTS connective))
         ; check-app determines for one premise(-schema) and one applied term
         ; whether it a valid instantiation. acc is a pair '(is-ok current-specializations).
         (check-app (lambda (applicatum-formula premise-schema acc)
                      (let* ((is-ok       (1st acc))
                             (specs       (2nd acc))
                             (spec-result (is-specialization-of? premise-schema applicatum-formula specs))
                             (new-specs   (2nd spec-result))
                             ; is-still-ok = is-ok and substitution for current term possible
                             ;                     and only schematic args subsituted
                             (is-still-ok (and is-ok
                                               (1st spec-result)  
                                               (subset? (map car new-specs) args)))
                             (new-acc (list is-still-ok new-specs)))
                        new-acc)))
         (result          (fold2-left check-app '(#t ()) app-formulas ie-premises))
         (is-valid        (1st result))
         (specializations (2nd result))
         ;; finally we also determine the formula inferred by the derivation term:
         (rest-clause     (unlist-premises (list-tail ie-premises (length app-terms))
                                           ie-conclusion))
         (rest-formula    (if is-valid
                              ; carry out all determined specializations
                              (fold-left (lambda (spec cur-formula)
                                           (specialize cur-formula (1st spec) (2nd spec)))
                                         rest-clause
                                         specializations)
                              '())))
      (if (1st result)
        (list #t rest-formula specializations)
        (list #f '() '()))))

(ie-const-application? '((&+_0 u) (v w)))

(valid-ie-clause-instance? '((&+_0 u) (v w)) '((u F1) (v (-> F2 F3) (w F3))))
;(infer-formula 'u '((u F1)))
