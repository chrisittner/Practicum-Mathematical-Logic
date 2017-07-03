(load "2-untyped-lambda-calculus.scm")

;; Minimal logic for implication and all-quantifier fragment ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

