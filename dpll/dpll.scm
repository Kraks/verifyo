(load "../mk/mk.scm")
(load "../membero.scm")

#|
A formula is in CNF, i.e., a list of clauses.
A clauses is a disjunction of literals, i.e., a list of literals.
A literal is either a symbol, or a negation of a symbol (¬ x).
|#

(define-syntax listᵒ
  (syntax-rules (← with)
    ((_ ((x . xs) ← lst) (with v ...) rel ...)
     (listᵒ ((x . xs) ← lst)
            (fresh (v ...) rel ...)))
    ((_ ((x . xs) ← lst) rel ...)
     (conde
      [(== lst '())]
      [(fresh (x xs)
              (== lst `(,x . ,xs))
              rel ...)]))))

(define (forall lst rel)
  (listᵒ ((x . xs) ← lst)
         (rel x)
         (forall xs rel)))

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

(define (emptyᵒ l) (== l '()))

(define (non-emptyᵒ l) (=/= l '()))

(define (symnumᵒ x)
  (∨ [(symbolo x)] [(numbero x)]))

(define (litᵒ l)
  (∨ [(symnumᵒ l)]
     [(fresh (l^)
             (== l `(¬ ,l^))
             (symnumᵒ l^))]))

(define (clauseᵒ c) (forall c litᵒ))

(define (formulaᵒ f) (forall f clauseᵒ))

(define (modelᵒ m) (forall m litᵒ))

(define (∩ x y z)
  (∨ [(emptyᵒ x) (emptyᵒ z)]
     [(emptyᵒ y) (emptyᵒ z)]
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
         (symnumᵒ p^)
         (== q p^))]
     [(symnumᵒ p)
      (== q `(¬ ,p))]))

;; the model does not contain duplicates, or conflicted assignments.
(define (consistentᵒ m)
  (listᵒ ((x . xs) ← m) (with ¬x)
         (negᵒ x ¬x)
         (∉  x xs)
         (∉ ¬x xs)
         (consistentᵒ xs)))

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
         (emptyᵒ p)
         (== q d)]
        [(=/= a x)
         (splitᵒ d p^ x q)
         (== p `(,a . ,p^))])))

(define (rem-dupᵒ xs ys)
  (∨ [(emptyᵒ xs) (emptyᵒ ys)]
     [(∃ (a d ys^)
         (== xs `(,a . ,d))
         (∨ [(∈ a d) (rem-dupᵒ d ys)]
            [(∉ a d)
             (rem-dupᵒ d ys^)
             (== ys `(,a . ,ys^))]))]))

(define (appendᵒ l s out)
  (∨ [(emptyᵒ l) (== s out)]
     [(∃ (a d res)
         (== `(,a . ,d) l)
         (== `(,a . ,res) out)
         (appendᵒ d s res))]))

(define (flattenᵒ xss xs)
  (∨ [(emptyᵒ xss) (emptyᵒ xs)]
     [(∃ (a d res)
         (== xss `(,a . ,d))
         (flattenᵒ d res)
         (appendᵒ a res xs))]))

(define (⊆* ∈)
  (lambda (xs ys)
    (∨ [(emptyᵒ xs)]
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
  (∨ [(emptyᵒ xs) (emptyᵒ ys)]
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
  (∨ [(emptyᵒ xs) (emptyᵒ ys)]
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
  (∨ [(emptyᵒ f) (emptyᵒ f^)]
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

(define (∄/mt-clause f) (∀ (c ← f) (non-emptyᵒ c)))

(define (∄/unit f)
  (∀ (c ← f)
     (∨ [(emptyᵒ c)]
        [(fresh (a d)
                (== c `(,a . ,d))
                (non-emptyᵒ d))])))

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
            rel ...))
    ((_ (c ← f) rel ...)
     (fresh (c)
            (∈ c f)
            rel ...))))

(define-syntax ∃/mt-clause
  (syntax-rules (with)
    ((_ (f) (with v ...) rel ...)
     (∃/clause (c ← f) (with v ...) (emptyᵒ c) rel ...))
    ((_ (f))
     (∃/clause (c ← f) (emptyᵒ c)))))

(define (decisionᵒ d x f d^)
  (== d `((,x ,f) . ,d^)))

(define (push-decisionᵒ d x f d^)
  (decisionᵒ d^ x f d))

(define (pop-decisionᵒ d x f d^)
  (decisionᵒ d x f d^))

(define (substᵒ xs x y ys)
  (∨ [(emptyᵒ xs) (emptyᵒ ys)]
     [(∃ (a d ys^)
         (== xs `(,a . ,d))
         (∨ [(== a x)
             (== ys `(,y . ,d))]
            [(=/= a x)
             (substᵒ d x y ys^)
             (== ys `(,a . ,ys^))]))]))

;; Unit Propogate, only eliminates real unit clauses
(define (step/unitᵒ f d m f^ d^ m^)
  (∃/unit ((x) ← f)
          (↑ m x)
          (unitpropᵒ f x f^)
          (== d^ d)
          (== m^ `(,x . ,m))))

(define (step/decideᵒ f d m f^ d^ m^)
  (∃/lit (x ← c ← f)
         (↑ m x)
         (unitpropᵒ f x f^)
         (push-decisionᵒ d x f d^)
         (== m^ `(,x . ,m))))

;; Backtrack, just back jump to the most recent decision
(define (step/backtrackᵒ f d m f^ d^ m^)
  (∃/mt-clause (f) (with x ¬x ^f)
               (pop-decisionᵒ d x ^f d^)
               (negᵒ x ¬x)
               (unitpropᵒ ^f ¬x f^)
               (substᵒ m x ¬x m^)))

(define (stepᵒ f d m f^ d^ m^ rule)
  (∨ [(∄/mt-clause f)
      (non-emptyᵒ f)
      (step/unitᵒ f d m f^ d^ m^)
      (== rule 'unit)]
     [(∄/unit f)
      (∄/mt-clause f)
      (non-emptyᵒ f)
      (step/decideᵒ f d m f^ d^ m^)
      (== rule 'decide)]
     [(∄/unit f)
      (non-emptyᵒ f)
      (step/backtrackᵒ f d m f^ d^ m^)
      (== rule 'backtrack)]))

(define (dpllᵒ f d m f^ d^ m^)
  (∨ [(emptyᵒ f)
      (modelᵒ m)
      (== f f^) (== d d^) (== m m^)]
     [(non-emptyᵒ f)
      (emptyᵒ d)
      (∃/mt-clause (f))
      (== m^ 'fail)
      (== d d^)
      (== f f^)]
     [(∃ (f* d* m* rule)
         (non-emptyᵒ m*)
         ;(formulaᵒ f*)
         ;(modelᵒ m*)
         (stepᵒ f  d  m  f* d* m* rule)
         (dpllᵒ f* d* m* f^ d^ m^))]))

(define (solveᵒ f m)
  (∃ (f^ d^)
     (dpllᵒ f '() '() f^ d^ m)))
