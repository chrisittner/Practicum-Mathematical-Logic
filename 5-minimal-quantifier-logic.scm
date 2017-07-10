(load "2-untyped-lambda-calculus.scm")

;; Minimal logic for implication and all-quantifier fragment ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Formula: F  =  'v  |  '(-> F1 F2)  |  '(forall v1 F1)

(define (is-implication? formula)
  (and (list? formula)
       (= (length formula) 3)
       (eq? (car formula) '->)
       (is-formula? (2nd formula))
       (is-formula? (3rd formula))))

(define (is-forall? formula)
  (and (list? formula)
       (= (length formula) 3)
       (eq? (car formula) 'forall)
       (is-variable? (2nd formula))
       (is-formula? (3rd formula))))

(define (is-formula? formula)
  (or (is-variable? formula)
      (is-implication? formula)
      (is-forall? formula)))


(define (is-assumption-var? var context)
  (member var (map 1st context)))
(define (is-object-var? var context)
  (not (is-assumption-var? var context)))

; (lambda (x) t)
(define (is-->+-abstraction? term context)
  (and (is-abstraction? term)
       (is-assumption-var? (caadr term) context)))
(define (is-forall+-abstraction?)
  (and (is-abstraction? term)
       (is-object-var? (caadr term) context)))
; (M N)
(define (is-->--application? term context)
  (and (is-application? term)
       (is-assumption-var? (2nd term) context)))
(define (is-forall--application?)
  (and (is-application? term)
       (is-object-var? (2nd term) context)))

;; Derivation Rules: ->+, ->-, forall+, forall-
;; Derivation Terms:  'u  |  '(lambda (u) T1)  |  '(T1 T2)

(define (is-valid-derivation? term context)
  (and (is-lambda-term? term)
       (cond
         ((is-variable? term)
          (unique-assoc term context)
         ((is-->--application? term context)
          (let ((f1 (infer-formula (car term) context))
                (f2 (infer-formula (cadr term) context)))
            (and (is-valid-derivation? (car term) context)
                 (is-valid-derivation? (cadr term) context)
                 (is-implication? f1)
                 (eq? (cadr f1) f2))))
         ((is-forall--application? term context) ) ;TODO
         ((is-->-abstraction? term)
          (and (is-valid-derivation? (caddr term) context)
               (unique-assoc (caadr term) context)))
         ((is-forall-abstraction? term) ) ;TODO
         ))))

(define (infer-formula term context)
  (cond
    ((is-assumption-var? term context)
     (cadr (assoc term context)))
    ((is-->--application? term context)
     (3rd (infer-formula (1st term) context)))
    ((is-forall--application? term context)
     (let ((forall-formula (infer-formula (1st term))))
       (specialize-formula (3rd forall-formula) (2nd forall formula) (2nd term))))
    ((is-->+-abstraction? term context)
     (let ((antecedent (infer-formula (caadr term) context))
           (consequent (infer-formula (caddr term) context)))
       (list '-> antecedent consequent)))
    ((is-forall+-abstraction? term context)
     (list 'forall (caadr term) (infer-formula (3rd term))))))

(define (is-derivation-of? term context formula)
  (and (is-valid-derivation? term context)
       (is-formula? formula)
       (equal? (infer-formula term context) formula)))
      

;; Proof checking examples:
;(define proposition1 '(forall x (-> (-> A (-> B C)) (-> (-> A B) (-> A C)))))
;(define term1        '(lambda (x) (lambda (u) (lambda (w) (lambda (v) ((u v) (w v)))))))
;(define context1     '((u (-> A (-> B C))) (v A) (w (-> A B))))

;(is-formula? proposition1)
;(infer-formula term1 context1)
;(is-valid-derivation? term1 context1)
;(is-derivation-of? term1 context1 proposition1)

