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
(pow 2 10)
;; 1.7.1 (b)
(define (maximum l)
  (if (= (length l) 1)
      (car l)
      (let ((rest-maximum (maximum (cdr l))))
        (if (> (car l) rest-maximum)
            (car l)
            rest-maximum))))
(maximum '(1 2 65 2 9))
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
(define (is-lambda-term? t)
  (cond
    ;; Case 1: t is a variable (=any quoted symbol)
    ((symbol? t) #t)
    ;; Case 2: t is of form '(M N)
    ((and (= (length t) 2)
          (is-lambda-term? (car t))
          (is-lambda-term? (cadr t)))
     #t)
    ;; Case 3: t is of form '(lambda (x) N)
    ((and (= (length t) 3)
          (eq? (car t) 'lambda)
          (list? (cadr t))
          (= (length (cadr t)) 1)
          (symbol? (caadr t))
          (is-lambda-term? (caddr t)))
     #t)
    ;; Nothing else is a lambda-term..
    (else #f)))

;; 1.7.4 (b)
(define (my-filter pred lst)
  (cond ((null? lst) '())
        ((pred (car lst))
         (cons (car lst) (my-filter pred (cdr lst))))
        (else (my-filter pred (cdr lst)))))

;; helper function to remove item from list
(define (list-remove-item item list)
  (my-filter (lambda (x) (not (equal? x item))) list))

(define (free-vars t)
  (cond
    ((symbol? t) ;; t is a variable
     (list t))
    ((= (length t) 2) ;; t is of form '(M N)
     (append (free-vars (car t)) (free-vars (cadr t))))
    ((= (length t) 3) ;; t is of form '(lambda x N)
     (list-remove-item (caadr t) (free-vars (caddr t))))))

 ;; 1.7.4 (c)
(define (rename-var t x y)
  (cond
    ((symbol? t)
     (if (eq? t x) y t))
    ((= (length t) 2)
     (list (rename-var (car t) x y) (rename-var (cadr t) x y)))
    ((= (length t) 3)
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
    ((symbol? t)
     (if (eq? t x) t-sub t))
    ((= (length t) 2)
     (list (substitute (car t) x t-sub) (substitute (cadr t) x t-sub)))
    ((= (length t) 3)
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
    ((symbol? t) t)
    ((= (length t) 2)
     (if (and (list? (car t)) (= (length (car t)) 3))
         ;; t of form '((lambda (x) M) N)
         (eval-term (substitute (caddr (car t)) (caadr (car t)) (cadr t)))
         ;; otherwise '(M N)
         (list (eval-term (car t)) (eval-term (cadr t)))))
    ((= (length t) 3) (list 'lambda (cadr t) (eval-term (caddr t))))))


;; Example: arithmetic computations with (eval-term t) and Church numerals
(define (churchify n) (letrec
  ((nest-f (lambda (t n) (if (= 0 n) t (nest-f (list 'f t) (- n 1))))))
  (list 'lambda '(f) (list 'lambda '(x) (nest-f 'x n)))))
; (churchify 7) => (lambda (f) (lambda (x) (f (f (f (f (f (f (f x)))))))))

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

(define 2*n (list (list times n) m))
(unchurchify (eval-term 2*n))
