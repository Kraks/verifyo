(load "../mk/mk.scm")
(load "../membero.scm")

#|
A formula is in CNF, i.e., a list of clauses.
A clauses is a disjunction of literals, i.e., a list of literals.
A literal is either a symbol, or a negation of a symbol (¬ x).
|#

(define (forall xs rel)
  (conde
   [(== xs '())]
   [(fresh (a d)
           (== xs `(,a . ,d))
           (rel a)
           (forall d rel))]))

(define-syntax ∀
  (syntax-rules (←)
    ((_ (x ← xs) rel ...)
     (forall xs (lambda (x) rel ...)))))

(define-syntax ∃
  (syntax-rules (←)
    ((_ (x = (f xs ...)) rel ...)
     (fresh (x) (f xs ... x) rel ...))
    ((_ (x ← xs) rel ...)
     (fresh (x) (∈ x xs) rel ...))
    ((_ (x ...) rel ...)
     (fresh (x ...) rel ...))))

(define-syntax ∧
  (syntax-rules ()
    ((_ rel ...)
     (fresh () rel ...))))

(define-syntax ∨
  (syntax-rules ()
    ((_ (rel ...) ...)
     (conde (rel ...) ...))))

(define (litᵒ l)
  (∨ [(symbolo l)]
     [(fresh (l^)
             (== l `(¬ ,l^))
             (symbolo l^))]))

(define (clauseᵒ c) (forall c litᵒ))

(define (formulaᵒ f) (forall f clauseᵒ))

(define (assignmentᵒ m) (forall m litᵒ))

(define (∩ x y z)
  (∨ [(== x '()) (== z '())]
     [(fresh (a d z^)
             (== `(,a . ,d) x)
             (∨ [(∈ a y)
                 (∩ d y z^)
                 (== z `(,a . ,z^))]
                [(∉ a y)
                 (∩ d y z)]))]))

(define (negᵒ p q)
  (∨ [(∃ (p^)
         (== p `(¬ ,p^))
         (symbolo p^)
         (== q p^))]
     [(symbolo p)
      (== q `(¬ ,p))]))

;; the model does not contain duplicates, or conflicted assignments.
(define (consistentᵒ m)
  (∨ [(== m '())]
     [(∃ (a d na)
         (== m `(,a . ,d))
         (negᵒ a na)
         (∉ na d)
         (∉  a d)
         (consistentᵒ d))]))

;; variable x is undefined in model m.
(define (↑ m x)
  (∃ (¬x = (negᵒ x)) (∉ ¬x m) (∉ x m)))

;; variable x is defined in model m.
(define (↓ m x)
  (∨ [(∈ x m)]
     [(∃ (¬x ← m) (negᵒ x ¬x))]))

(define (c/⊨ m c)
  (∃ (x ← c) (∈ x m)))

(define (c/⊭ m c)
  (∀ (x ← c) (∃ (¬x ← m) (negᵒ x ¬x))))

(define (f/⊨ m f)
  (∀ (c ← f) (c/⊨ m c)))

(define (f/⊭ m f)
  (∃ (c ← f) (c/⊭ m c)))

;; Split list pxq at the the first occorence of x.
(define (splitᵒ pxq p x q)
  (∃ (a d p^)
     (== pxq `(,a . ,d))
     (∨ [(== a x)
         (== p '())
         (== q d)]
        [(=/= a x)
         (splitᵒ d p^ x q)
         (== p `(,a . ,p^))])))

(define (rem-dupᵒ xs ys)
  (∨ [(== xs '()) (== ys '())]
     [(∃ (a d ys^)
         (== xs `(,a . ,d))
         (∨ [(∈ a d) (rem-dupᵒ d ys)]
            [(∉ a d)
             (rem-dupᵒ d ys^)
             (== ys `(,a . ,ys^))]))]))

(define (appendᵒ l s out)
  (∨ [(== '() l) (== s out)]
     [(∃ (a d res)
         (== `(,a . ,d) l)
         (== `(,a . ,res) out)
         (appendᵒ d s res))]))

(define (flattenᵒ xss xs)
  (∨ [(== xss '()) (== xs '())]
     [(∃ (a d res)
         (== xss `(,a . ,d))
         (flattenᵒ d res)
         (appendᵒ a res xs))]))

(define (⊆* ∈)
  (lambda (xs ys)
    (∨ [(== xs '())]
       [(∃ (a d)
           (== xs `(,a . ,d))
           (∈ a ys)
           ((⊆* ∈) d ys))])))

(define (⊆ xs ys) ((⊆* (lambda (a m) (↓ m a))) xs ys))

;; should be the final state: all the variables are assigned.
(define (finalo m f)
  (∃ (vars vars^ c cs)
     (flattenᵒ f vars^)
     (rem-dupᵒ vars^ vars)
     (⊆ m vars)
     (⊆ vars m)))

(define (removeᵒ xs x ys)
  (∨ [(== xs '()) (== ys '())]
     [(∃ (a d ys^)
         (== xs `(,a . ,d))
         (∨ [(== a x) (removeᵒ d x ys)]
            [(=/= a x)
             (removeᵒ d x ys^)
             (== ys `(,a . ,ys^))]))]))

(define (c/unitpropᵒ c x c^)
  (∨ [(∈ x c) (== c^ #t)]
     [(∃ (¬x ← c) (negᵒ x ¬x) (∉ x c) (removeᵒ c ¬x c^))]
     [(↑ c x) (== c c^)]))

(define (mapfilterᵒ xs p f ys)
  (∨ [(== xs '()) (== ys '())]
     [(∃ (a a^ d r ys^)
         (== xs `(,a . ,d))
         (f a a^)
         (p a^ r)
         (∨ [(== r #t)
             (mapfilterᵒ d p f ys^)
             (== ys `(,a^ . ,ys^))]
            [(== r #f)
             (mapfilterᵒ d p f ys)]))]))

;; Note: an empty disjunction is false; an empty conjunction is true

(define (unitpropᵒ f x f^)
  (∨ [(== f '()) (== f^ '())]
     [(mapfilterᵒ
       f
       (lambda (a r) (conde [(== a #t) (== r #f)] [(=/= a #t) (== r #t)]))
       (lambda (c c^) (c/unitpropᵒ c x c^))
       f^)]))

(define-syntax ∃/unit
  (syntax-rules (←)
    ((_ ((x) ← f) rel ...)
     (∃ (x c)
        (∈ c f)
        (== c `(,x))
        rel ...))))

(define (∄/mt-clause f)
  (∀ (c ← f) (=/= c '())))

(define (∄/unit f)
  (∀ (c ← f)
     (∨ [(== c '())]
        [(fresh (a d)
                (== c `(,a . ,d))
                (=/= d '()))])))

(define-syntax ∃/lit
  (syntax-rules (←)
    ((_ (x ← c ← f) rel ...)
     (fresh (x c)
            (∈ c f)
            (∈ x c)
            rel ...))))

(define-syntax ∃/clause
  (syntax-rules (← with)
    ((_ (c ← f) (with v ...) rel ...)
     (fresh (c v ...)
            (∈ c f)
            rel ...))))

(define-syntax ∃/mt-clause
  (syntax-rules (with)
    ((_ (f) (with v ...) rel ...)
     (∃/clause (c ← f) (with v ...) (== c '()) rel ...))))

(define (decisionᵒ d x f d^)
  (== d `((,x ,f) . ,d^)))

(define (push-decisionᵒ d x f d^)
  (decisionᵒ d^ x f d))

(define (pop-decisionᵒ d x f d^)
  (decisionᵒ d x f d^))

(define (substᵒ xs x y ys)
  (∨ [(== xs '()) (== ys '())]
     [(∃ (a d ys^)
         (== xs `(,a . ,d))
         (∨ [(== a x)
             (== ys `(,y . ,d))]
            [(=/= a x)
             (substᵒ d x y ys^)
             (== ys `(,a . ,ys^))]))]))

(define (step/unitᵒ f d m f^ d^ m^)
  (∧ (∄/mt-clause f)
     (∃/unit ((x) ← f)
             (↑ m x)
             (unitpropᵒ f x f^)
             (== d^ d)
             (== m^ `(,x . ,m)))))

(define (step/decideᵒ f d m f^ d^ m^)
  (∧ (∄/unit f)
     (∄/mt-clause f)
     (∃/lit (x ← c ← f)
            (↑ m x)
            (unitpropᵒ f x f^)
            (push-decisionᵒ d x f d^)
            (== m^ `(,x . ,m)))))

(define (step/backtrackᵒ f d m f^ d^ m^)
  (∧ (∄/unit f)
     (∃/mt-clause (f) (with x ¬x ^f)
                  (pop-decisionᵒ d x ^f d^)
                  (negᵒ x ¬x)
                  (unitpropᵒ ^f ¬x f^)
                  (substᵒ m x ¬x m^))))

#|
  (∃ (c x ¬x ^f)
     (∈ c f)
     (== c '())
     (pop-decisionᵒ x ^f d d^)
     (negᵒ x ¬x)
     (unitpropᵒ ^f ¬x f^)
     (substᵒ m x ¬x m^)))
|#

(define (stepᵒ f d m f^ d^ m^)
  (∨
   ;; Unit Propogate, only eliminates real unit clauses
   [(step/unitᵒ f d m f^ d^ m^)]
   ;; Decide
   [(step/decideᵒ f d m f^ d^ m^)]
   ;; Backtrack, just back jump to the most recent decision
   [(step/backtrackᵒ f d m f^ d^ m^)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; d is an auxiliary list that tracks decision literals (only added by Decide rule).
;; m is the model, i.e., the assignment.
;; ⟨d, m⟩ ↦ ⟨d^, m^⟩
;; TODO: make the step relation deterministic
(define (stepo d m f d^ m^)
  (conde
   ;; Unit Propagate
   [(fresh (x xs c)
           (∈ c f)
           (== c `(,x . ,xs))
           (c/⊭ m xs)
           (↑ m x)
           (== m^ `(,x . ,m))
           (== d^ d))]
   ;; Decide
   [(fresh (x c)
           ;; TODO: when do not have unit variable
           (∈ c f)
           (∈ x c)
           (↑ m x)
           (== d^ `(,x . ,d))
           (== m^ `(,x . ,m)))]
   ;; Fail
   [(fresh (c)
           (== m^ 'fail)
           (∈ c f)
           (c/⊭ m c)
           (== d '())
           (== d^ d))]
   ;; Backjump
   [(fresh (dl ds ndl m1 m2)
           ;; TODO: when reach a conflict
           (== d `(,dl . ,ds))
           (splitᵒ m m1 dl m2)
           (negᵒ dl ndl)
           (↑ m2 ndl)
           (== m^ `(,ndl ,m2))
           (== d^ d))]))

;; TODO: failed to disprove something
(define (dpllo d m f d^ m^)
  (fresh (d* m* x c)
         (formulaᵒ f)
         (assignmentᵒ m)
         (consistentᵒ m)
         (consistentᵒ m*)
         (stepo d m f d* m*)
         (conde
          [(== m* 'fail) (== m^ 'fail)]
          [(finalo m* f)
           (f/⊨ m^ f) ;;TODO: necessary?
           (consistentᵒ m*)
           (== m* m^)]
          [(=/= m* 'fail)
           (↑ m* x) (∈ x c) (∈ c f)
           (dpllo d* m* f d^ m^)])))
