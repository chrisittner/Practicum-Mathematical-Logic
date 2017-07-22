(load "4-propositional-logic.scm")

;; This file defines export functions to convert derivation terms into
;; latex-compilable proof trees, using 'bussproofs'.

;; turns logical constant into latex symbol.
(define (symb2tex s)
  (string-append "\\" (2nd (assoc s symbol2tex-alist)) " "))
(define symbol2tex-alist
  '((->     "to")
    (F      "bot")
    (bot    "bot")
    (neg    "neg")
    (v      "lor")
    (&      "land")
    (forall "forall")
    (all    "forall")
    (ex     "exists")
    (exists "exists")))

;; turns formula into latex formula.
(define (formula2tex f . add-parentheses)
  (let ((tex (cond ((is-variable? f)
                    (symbol->string f))
                   ((or (is-implication? f) ;; make binary connectives infix
                        (and (is-defined-connective? f) (= (length f) 3)))
                    (string-append (formula2tex (2nd f) #t) (symb2tex (1st f)) (formula2tex (3rd f) #t)))
                   ((is-defined-connective? f)
                    (string-append (symb2tex (car f)) (apply string-append (map formula2tex (cdr f) #t)))))))
    (if (and (not (null? add-parentheses)) (1st add-parentheses) (not (is-variable? f)))
        (string-append "(" tex ")")
        tex)))

;; return bussproof latex commands for k-ary derivation steps.
(define (bussproof k) (string-append "\\" (list-ref bussproof-tree-commands k)))
(define bussproof-tree-commands
  '("AxiomC" "UnaryInfC" "BinaryInfC" "TrinaryInfC" "QuaternaryInfC" "QuinaryInfC"))

;; turns valid derivation (formula + term + context) into bussproofs string.
(define (term2tex formula term context)
  (cond
    ((is-variable? term)
     (string-append
      (bussproof 0) "{$" (symbol->string term) "\\colon " (formula2tex (2nd (assoc term context))) "$}\n"))
    ((is-abstraction? term)
     (string-append
      (term2tex (3rd formula) (3rd term) (cons (list (caadr term) (2nd formula)) context))
      (bussproof 1) "{$" (formula2tex formula) "$}\\RightLabel{$\\to^+" (symbol->string (caadr term)) "$}\n"))
    ((ie-const-application? term)
     (let* ((uncurried-term  (uncurry-term term))
            (ie-const        (1st uncurried-term))       
            (app-terms       (2nd uncurried-term)))
       (string-append
        (apply string-append (map (lambda (t) (term2tex (infer-formula t context) t context)) app-terms))
        (bussproof n) "{$" (formula2tex formula) "$}\\RightLabel{$" ie-const "$}\n")))
    ((is-application? term)
     (let ((premise (infer-formula (2nd term) context)))
       (string-append
        (term2tex (list '-> premise formula) (1st term) context)
        (term2tex premise (2nd term) context)
        (bussproof 2) "{$" (formula2tex formula) "$}\\RightLabel{$\\to^-$}\n")))
    (else (display (string-append "Error, " term " not a valid term")))))

;; wraps proof steps in latex document header+footer; returns compilable latex.
(define (add-latexheaderfooter s)
  (string-append latex-header
                 "\\begin{prooftree}\n" s "\\end{prooftree}\n"
                 latex-footer))
(define latex-header
  "\\documentclass{scrartcl}\n\\usepackage{amsmath, bussproofs}\n\\begin{document}\n\n")
(define latex-footer "\n\\end{document}\n")

;; writes <string> to file <filename> in the current folder.
(define (string2file string filename)
      (with-output-to-file filename (lambda () (display string))))


;; Examples         
(formula2tex '(-> (-> (-> a b) a) a))
(newline)
(display (term2tex '(-> (-> a (-> b c)) (-> (-> a b) (-> a c))) 
          '(lambda (a0) (lambda (a1) (lambda (a2) ((a0 a2) (a1 a2)))))
          '()))
(newline)

(define p2 (term2tex '(-> (-> a b) (-> (-> b c) (-> a c)))
           '(lambda (a0) (lambda (a1) (lambda (a2) (a1 (a0 a2)))))
           '()))
(display p2)
(newline)
(display "## Compilable example latex code:\n")
(display (add-latexheaderfooter p2))
; (string2file (add-latexheaderfooter p2) "prooftree.tex")
