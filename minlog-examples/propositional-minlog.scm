(load "../minlog/init.scm")  ;; INSERT PATH TO YOUR MINLOG INSTALLATION

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Propositional logic
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Implicational logic

;; Formulas (implication only)

(add-pvar-name "A" "B" "C" (make-arity))

(pf "A")
(pp (pf "A"))

(pf "A -> B")
(pp (pf "A -> B"))

(pp (pf "A -> B -> C"))


(pp (pf "(A -> B -> C) -> (A -> B) -> C"))

;; Proofs

(define avar1 (make-avar (pf "A -> B -> C") -1 "u"))
(define pf1 (make-proof-in-avar-form avar1))
(cdp pf1)

(define avar2 (make-avar (pf "A -> B") -1 "v"))
(define pf2 (make-proof-in-avar-form avar2))
(cdp pf2)

(define avar3 (make-avar (pf "A") -1 "w"))
(define pf3 (make-proof-in-avar-form avar3))
(cdp pf3)

(define pf4 (make-proof-in-imp-elim-form pf2 pf3))
(cdp pf4)
(proof-to-expr-with-formulas pf4)

(define pf5 (make-proof-in-imp-elim-form pf1 pf3))
(cdp pf5)

(define pf6 (make-proof-in-imp-elim-form pf5 pf4))
(cdp pf6)
(proof-to-expr-with-formulas pf6)

(define pf7 (make-proof-in-imp-intro-form avar3 pf6))
(cdp pf7)
(proof-to-expr-with-formulas pf7)

(define pf8 (make-proof-in-imp-intro-form avar2 pf7))
(cdp pf8)
(proof-to-expr-with-formulas pf8)

(define pf9 (make-proof-in-imp-intro-form avar1 pf8))
(cdp pf9)
(proof-to-expr-with-formulas pf9)



;; Partial proofs


(define (prop-set-goal string-or-formula)
  (let ((formula (if (string? string-or-formula)
		     (pf string-or-formula)
		     string-or-formula)))
    (if (not (formula-form? formula))
	(myerror "set-goal" "formula expected" formula))
    (let* ((avar (formula-to-new-avar formula DEFAULT-AVAR-NAME))
	   (goal (make-goal-in-avar-form avar))
	   (init-num-goal
	    (make-num-goal 1 goal empty-drop-info empty-hypname-info)))
      (set! PPROOF-STATE (make-pproof-state (list init-num-goal) goal 1))
      (pproof-state-history-clear)
      (pproof-state-history-push PPROOF-STATE)
      (display-num-goal init-num-goal fold-formula))))

(define (prop-assume . x-list)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal)))
    (set! PPROOF-STATE
	  (apply prop-assume-intern num-goals proof maxgoal x-list))
    (pproof-state-history-push PPROOF-STATE)
    (display-comment "ok, we now have the new goal ")
    (if COMMENT-FLAG (newline))
    (display-num-goal (car (pproof-state-to-num-goals)))))

(define (prop-assume-intern num-goals proof maxgoal . x-list)
  (let* ((num-goal (car num-goals))
	 (number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (drop-info (num-goal-to-drop-info num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (context (goal-to-context goal))
	 (formula (goal-to-formula goal)))
    (do ((l x-list (cdr l))
	 (nc-and-np-and-ng-and-nh
	  (list '() goal goal hypname-info)
	  (let* ((x1 (car l))
		 (nc (car nc-and-np-and-ng-and-nh)) ;new context
		 (np (cadr nc-and-np-and-ng-and-nh)) ;new proof
		 (ng (caddr nc-and-np-and-ng-and-nh)) ;new goal
		 (nh (cadddr nc-and-np-and-ng-and-nh)) ;new hypname-info
		 (nf (proof-to-formula ng)))
	    (case (tag nf)
	      ((imp)
	       (let* ((premise (imp-form-to-premise nf))
		      (name (if (string? x1) x1 DEFAULT-AVAR-NAME))
		      (avar (formula-to-new-avar premise name))
		      (ng1 (make-goal-in-imp-elim-form ng avar))
		      (hypnumber (+ (length (context-to-avars context))
				    (length (context-to-avars nc))))
		      (nh1 (if (string? x1)
			       (add-hypname-info (+ 1 hypnumber) x1 nh)
			       nh)))
		 (list
		  (cons avar nc)
		  (goal-subst np ng (make-proof-in-imp-intro-form avar ng1))
		  ng1 nh1)))
	      (else (myerror "prop-assume" "formula"
			     nf "not of the appropriate form to assume"
			     x1))))))
	((null? l)
	 (let* ((np (cadr nc-and-np-and-ng-and-nh))
		(ng (caddr nc-and-np-and-ng-and-nh))
		(nh (cadddr nc-and-np-and-ng-and-nh))
		(new-num-goal (make-num-goal (+ 1 maxgoal) ng drop-info nh)))
	   (make-pproof-state (cons new-num-goal (cdr num-goals))
			      (goal-subst proof goal np)
			      (+ 1 maxgoal)))))))

(define (prop-use-with x . x-list)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (proof (pproof-state-to-proof))
	 (maxgoal (pproof-state-to-maxgoal))
	 (number (num-goal-to-number (car num-goals))))
    (set! PPROOF-STATE
	  (apply prop-use-with-intern num-goals proof maxgoal x x-list))
    (pproof-state-history-push PPROOF-STATE)
    (display-new-goals num-goals number)))

(define (prop-use-with-intern num-goals proof maxgoal x . x-list)
  (let* ((num-goal (car num-goals))
	 (goal (num-goal-to-goal num-goal))
	 (goal-formula (goal-to-formula goal))
	 (proof-and-new-num-goals-and-maxgoal
	  (apply prop-x-and-x-list-to-proof-and-new-num-goals-and-maxgoal
		 num-goal maxgoal x x-list))
	 (new-proof (car proof-and-new-num-goals-and-maxgoal))
	 (new-num-goals (cadr proof-and-new-num-goals-and-maxgoal))
	 (new-maxgoal (caddr proof-and-new-num-goals-and-maxgoal)))
    (if (not (classical-formula=? (proof-to-formula new-proof) goal-formula))
	(myerror "use-with-intern" "equal formulas expected"
		 (fold-formula (proof-to-formula new-proof))
		 goal-formula))
    (let ((final-proof (goal-subst proof goal new-proof)))
      (make-pproof-state
       (append (reverse new-num-goals) (cdr num-goals))
       final-proof
       new-maxgoal))))

(define (prop-x-and-x-list-to-proof-and-new-num-goals-and-maxgoal
	 num-goal maxgoal x . x-list)
  (let* ((number (num-goal-to-number num-goal))
	 (goal (num-goal-to-goal num-goal))
	 (drop-info (num-goal-to-drop-info num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (context (goal-to-context goal))
	 (avars (context-to-avars context))
	 (maxhyp (length avars))
	 (cterms (list-transform-positive x-list cterm-form?))
	 (rest-x-list (list-transform-positive x-list
			(lambda (y) (not (cterm-form? y)))))
	 (x-for-cterms
	  (if
	   (pair? cterms) ;else x
	   (let* ((proof (if (proof-form? x) x (thm-or-ga-name-to-proof x)))
		  (pvars (proof-to-pvars proof))
		  (l (min (length pvars) (length cterms)))
		  (psubst (map list (list-head pvars l) (list-head cterms l))))
	     (proof-substitute proof psubst))
	   x))
	 (leaf (hyp-info-to-leaf num-goal x-for-cterms))
	 (leaf-and-new-num-goals-and-maxgoal (list leaf '() maxgoal)))
    (do ((l rest-x-list (cdr l))
	 (proof-and-new-num-goals-and-maxgoal
	  leaf-and-new-num-goals-and-maxgoal
	  (let* ((proof (car proof-and-new-num-goals-and-maxgoal))
		 (used-formula (unfold-formula (proof-to-formula proof)))
		 (new-num-goals (cadr proof-and-new-num-goals-and-maxgoal))
		 (maxgoal (caddr proof-and-new-num-goals-and-maxgoal))
		 (x1 (car l)))
	    (if (not (imp-form? used-formula))
		(myerror
		 "prop-x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
		 "imp-form expected" used-formula))
	    (if
	     (equal? x1 DEFAULT-GOAL-NAME) ;a new goal is created
	     (let* ((prem (imp-form-to-premise used-formula))
		    (goalvarformula
		     (apply mk-imp (append (map avar-to-formula avars)
					   (list prem))))
		    (goalvar (formula-to-new-avar goalvarformula
						  DEFAULT-AVAR-NAME))
		    (goal (apply mk-goal-in-elim-form
				 (make-goal-in-avar-form goalvar)
				 context))
		    (new-num-goal (make-num-goal
				   (+ 1 maxgoal) goal drop-info hypname-info)))
	       (list (make-proof-in-imp-elim-form proof goal)
		     (cons new-num-goal new-num-goals)
		     (+ 1 maxgoal)))
	     (let ((arg (cond
			 ((and (integer? x1) (positive? x1))
			  (if (<= x1 maxhyp)
			      (make-proof-in-avar-form
			       (list-ref avars (- x1 1)))
			      (myerror "prop-x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
				       "assumption number expected" x1)))
			 ((and (string? x1)
			       (member x1 (hypname-info-to-names
					   hypname-info)))
			  (let ((i (name-and-hypname-info-to-index
				    x1 hypname-info)))
			    (if (<= i maxhyp)
				(make-proof-in-avar-form
				 (list-ref avars (- i 1)))
				(myerror "prop-x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
					 "assumption number expected" i))))
			 ((and (string? x1) (assoc x1 THEOREMS))
			  (make-proof-in-aconst-form
			   (cadr (assoc x1 THEOREMS)))))))
	       (if (formula=? (imp-form-to-premise used-formula)
			      (proof-to-formula arg))
		   (list (make-proof-in-imp-elim-form proof arg)
			 new-num-goals maxgoal)
		   (myerror
		    "prop-x-and-x-list-to-proof-and-new-num-goals-and-maxgoal"
		    "formulas do not fit"
		    used-formula
		    (proof-to-formula arg))))))))
	((null? l) proof-and-new-num-goals-and-maxgoal))))




(prop-set-goal "A -> (A -> B) -> B")
(prop-assume "u" "v")
(prop-use-with "v" "u")

(prop-set-goal "(A -> B -> C) -> (A -> B) -> A -> C")
(prop-assume "u" "v" "w")
(prop-use-with "u" "w" "?")
(prop-use-with "v" "w")
;; Proof finished.
(save "SThm")

;; (set-goal "(A -> B -> C) -> (A -> B) -> A -> C")
;; (assume "u")
;; (assume "v")
;; (assume "w")
;; (use-with "u" "?" "?")
;; (use-with "w")
;; (use-with "v" "w")
;; ;; Proof finished.
;; (save "SThm")

(cdp "SThm")
(proof-to-expr-with-formulas "SThm")

(current-proof)
(current-goal)


;; Here we prove the introduction and elimination axioms using
;; commands intro and elim form a general treatment of inductive
;; predicates, which is postponed.  The reader may view AndDIntro and
;; AndDElim as axioms.

;; AndDIntro
(prop-set-goal "A -> B -> A andd B")
(prop-assume "u" "v")
(intro 0)
(use "u")
(use "v")
;; Proof finished.
(save "AndDIntro")

;; AndDElim
(prop-set-goal "A andd B -> (A -> B -> Pvar) -> Pvar")
(prop-assume "Conj")
(elim "Conj")
(prop-assume "u" "v" "w")
(prop-use-with "w" "u" "v")
;; Proof finished.
(save "AndDElim")

;; OrDIntroZero
(prop-set-goal "A -> A ord B")
(prop-assume "u")
(intro 0)
(prop-use-with "u")
;; Proof finished.
(save "OrDIntroZero")

;; OrDIntroOne
(prop-set-goal "B -> A ord B")
(prop-assume "u")
(intro 1)
(prop-use-with "u")
;; Proof finished.
(save "OrDIntroOne")

;; OrDElim
(prop-set-goal "A ord B -> (A -> Pvar) -> (B -> Pvar) -> Pvar")
(prop-assume "Disj" "u" "v")
(elim "Disj")
(prop-use-with "u")
(prop-use-with "v")
;; Proof finished.
(save "OrDElim")

(prop-set-goal "(A -> B) ord (A -> Pvar) -> A -> B ord Pvar")
(prop-assume "Disj" "u")
(prop-use-with "OrDElim"
	       (make-cterm (pf "A -> B"))
	       (make-cterm (pf "A -> Pvar"))
	       (make-cterm (pf "B ord Pvar"))
	       "Disj" "?" "?")
;; 3
(prop-assume "v")
(prop-use-with "OrDIntroZero"
	       (make-cterm (pf "B"))
	       (make-cterm (pf "Pvar"))
	       "?")
(prop-use-with "v" "u")
;; 4
(prop-assume "v")
(prop-use-with "OrDIntroOne"
	       (make-cterm (pf "Pvar"))
	       (make-cterm (pf "B"))
	       "?")
(prop-use-with "v" "u")
;; Proof finished.

