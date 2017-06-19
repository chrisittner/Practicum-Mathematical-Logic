;; Helper Functions ;;
;;;;;;;;;;;;;;;;;;;;;;

(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

;; For DrRacket+R5RS compatibility, because 'filter' not present in R5RS Scheme
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

;; check if key is assigned a unique value in association-list (=list of '(key value) pairs)
(define (unique-assoc key association-list)
  (= 1 (length (my-filter (lambda (p) (eq? key (car p))) association-list))))

;; concatenates two symbols. (symbol-append 'as 'df) => 'asdf
(define (symbol-append . symbols)
  (string->symbol (apply string-append (map symbol->string symbols))))

(define (number->symbol x) (string->symbol (number->string x)))