;; Exercise 1.7.1
;; 1.7.1 (a)
(- (* 50 100) 4999)
(* 50 (- 100 4999))
;; 1.7.1 (b)
(define (f x y)
  (* (* x x) (* y y)))
(define (s x)
  (cond ((> x 0) 1)
        ((= x 0) 0)
        ((< x 0) -1)))
;; 1.7.1 (c)
(define (compose f g)
  (lambda (x) (f (g x))))



;; Exercise 1.7.2
;; 1.7.1 (a)
(define (pow x y)
  (if (= 0 y) 1 (* x (pow x (- y 1)))))
;(pow 2 10)

;; 1.7.1 (b)
(define (maximum l)
  (if (= (length l) 1)
      (car l)
      (let ((rest-maximum (maximum (cdr l))))
        (if (> (car l) rest-maximum)
            (car l)
            rest-maximum))))
;(maximum '(1 2 65 2 9))

;; 1.7.1 (c)
(define (rev l)
  (cond ((not (list? l))  #f)
        ((= (length l) 0) '())
        ((> (length l) 0) (append (rev (cdr l)) (list (car l))))))
(rev '(1 2 65 2 9))



;; Exercise 1.7.3
(define (tree-height L)
  (cond
    ;; Case 1: L is of form (x)
    ((and (= (length L) 1) (not (list? (car L))))
     0)
    ;; Case 2: L is of form (x L1 L2 .. Ln)
    ((and (> (length L) 1) (not (list? (car L))))
     (+ 1 (maximum (map tree-height (cdr L)))))))

; (define my-tree '("A" ("B" ("E") ("F")) ("C") ("D" ("G"))))
; (tree-height my-tree)


;; Exercise 1.7.4
;; 1.7.4 (a)
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

;; 1.7.4 (b)
;; For DrRacket+R5RS compatibility, because 'filter' not present in R5RS
(define (my-filter pred list)
  (cond ((null? list) '())
        ((pred (car list))
         (cons (car list) (my-filter pred (cdr list))))
        (else (my-filter pred (cdr list)))))

;; helper function to remove item from list
(define (list-remove-item item list)
  (my-filter (lambda (x) (not (equal? x item))) list))

(define (free-vars t)
  (cond
    ((is-variable? t)    (list t))
    ((is-application? t) (append (free-vars (car t)) (free-vars (cadr t))))
    ((is-abstraction? t) (list-remove-item (caadr t) (free-vars (caddr t))))))

 ;; 1.7.4 (c)
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

;; 1.7.4 (d)
;; helper function to find a symbol of form "a42" not in used-vars
(define (gen-var used-vars . counter)
  (let* ((counter (if (null? counter) 0 (car counter)))
        (candidate-var (string->symbol
                        (string-append "a" (number->string counter)))))
    (if (not (member candidate-var used-vars))
        candidate-var (gen-var used-vars (+ 1 counter)))))

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
                  (new-var (gen-var used-vars))
                  (renamed-term (rename-var (caddr t) (caadr t) new-var)))
             (list 'lambda new-var (substitute renamed-term x t-sub))))))))

;; 1.7.4 (e)
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


;; Example: arithmetic computations with (eval-term t) and Church numerals
(define (churchify n) (letrec
  ((nest-f (lambda (t n) (if (= 0 n) t (nest-f (list 'f t) (- n 1))))))
  (list 'lambda '(f) (list 'lambda '(x) (nest-f 'x n)))))
; (churchify 7) => '(lambda (f) (lambda (x) (f (f (f (f (f (f (f x)))))))))

(define (unchurchify t)
  (eval (list (list t '(lambda (x) (+ 1 x))) 0) (interaction-environment)))

(define plus '(lambda (m) (lambda (n)
    (lambda (f) (lambda (x) ((m f) ((n f) x)))))))
(define times '(lambda (m) (lambda (n)
    (lambda (f) (n (m f))))))

(define n (churchify 17))
(define m (churchify 42))
(define n+m (list (list plus n) m)) ;; => ((plus n) m)
(unchurchify (eval-term n+m))       ;; => 59

(define n*m (list (list times n) m))
(is-lambda-term? n*m)
(unchurchify (eval-term n*m))


;; Exercise 1.7.5

;; 1.7.5 (a)
(define (is-implication? formula)
  (and (list? formula)
       (= (length formula) 3)
       (eq? (car formula) '->)
       (is-formula? (cadr formula))
       (is-formula? (caddr formula))))

(define (is-formula? formula)
  (or (is-variable? formula) (is-implication? formula)))

;; 1.7.5 (b)
;; check if var is assigned a unique type in context
(define (unique-assoc var context)
  (= 1 (length (my-filter (lambda (p) (eq? var (car p))) context))))

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

;; 1.7.5 (c)
(define (infer-formula term context)
  (cond
    ((is-variable? term)
     (cadr (assq term context)))
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
      

;; Example: Derivation checking
(define proposition1 '(-> (-> A (-> B C)) (-> (-> A B) (-> A C))))
(define term1        '(lambda (u) (lambda (w) (lambda (v) ((u v) (w v))))))
(define context1     '((u (-> A (-> B C))) (v A) (w (-> A B))))

(is-formula? proposition1)
(infer-formula term1 context1)
(is-valid-derivation? term1 context1)

(is-derivation-of? term1 context1 proposition1)




