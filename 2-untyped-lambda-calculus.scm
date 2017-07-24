(load "B1-helper-functions.scm")

;; Untyped Lambda Terms ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;

(define is-variable? symbol?)

(define (is-application? term)
  (and (list? term)
       (= (length term) 2)
       (is-lambda-term? (car term))
       (is-lambda-term? (cadr term))))

(define (is-abstraction? term)
  (and (list? term)
       (= (length term) 3)
       (eq? (car term) 'lambda)
       (list? (cadr term))
       (= (length (cadr term)) 1)
       (symbol? (caadr term))
       (is-lambda-term? (caddr term))))

(define (is-lambda-term? term)
  (or (is-variable? term) (is-application? term) (is-abstraction? term)))


(define (free-vars t)
  (cond
    ((is-variable? t)    (list t))
    ((is-application? t) (append (free-vars (car t)) (free-vars (cadr t))))
    ((is-abstraction? t) (list-remove-item (caadr t) (free-vars (caddr t))))))

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

;; Replace x by t-rep in t (without avoiding variable capture)
(define (replace t x t-rep)
  (cond
    ((is-variable? t)
     (if (eq? t x) t-rep t))
    ((is-application? t)
     (list (replace (car t) x t-rep) (replace (cadr t) x t-rep)))
    ((is-abstraction? t)
     (list 'lambda (2nd t) (replace (3rd t) x t-rep)))))

;; Substitute t-sub for x in t.
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


;; Example: Arithmetic in LC with Church numerals  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;(define n (churchify 17))
;(define m (churchify 42))
;(define n+m (list (list plus n) m))  ;; => ((plus n) m)
;(unchurchify (eval-term n+m))        ;; => 59

;(define n*m (list (list times n) m)) ;; => ((times n) m)
;(is-lambda-term? n*m)                ;; #t
;(unchurchify (eval-term n*m))        ;; => 714
