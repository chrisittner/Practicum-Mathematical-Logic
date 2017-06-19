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
