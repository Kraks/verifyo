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
  (syntax-rules (<- ∃)
    ((_ (x <- xs) (∃ (y <- ys) rel ...))
     (forall xs (lambda (x) (fresh (y) (∈ y ys) rel ...))))
    ((_ (x <- xs) (∃ y ...) rel ...)
     (forall xs (lambda (x) (fresh (y ...) rel ...))))
    ((_ (x <- xs) rel ...)
     (forall xs (lambda (x) rel ...)))))

(define-syntax ∃
  (syntax-rules (<-)
    ((_ (x <- xs) rel ...)
     (fresh (x) (∈ x xs) rel ...))))

(define (lito l)
  (conde
   [(symbolo l)]
   [(fresh (l^)
           (== l `(¬ ,l^))
           (symbolo l^))]))

(define (clauseo c) (forall c lito))

(define (formulao f) (forall f clauseo))

(define (assignmento m) (forall m lito))

(define (intersecto x y z)
  (conde
   [(== x '()) (== z '())]
   [(fresh (a d z^)
           (== `(,a . ,d) x)
           (conde
            [(∈ a y)
             (intersecto d y z^)
             (== z `(,a . ,z^))]
            [(∉ a y)
             (intersecto d y z)]))]))

(define (nego p q)
  (conde
   [(fresh (p^)
           (== p `(¬ ,p^))
           (symbolo p^)
           (== q p^))]
   [(symbolo p)
    (== q `(¬ ,p))]))

;; the model does not contain duplicates, or conflicted assignments.
(define (consistento m)
  (conde
   [(== m '())]
   [(fresh (a d na)
           (== m `(,a . ,d))
           (nego a na)
           (∉ na d)
           (∉  a d)
           (consistento d))]))

;; variable x is undefined in model m.
(define (↑ m x)
  (fresh (nx)
         (nego x nx)
         (∉ nx m)
         (∉ x m)))

;; variable x is defined in model m.
(define (↓ m x)
  (conde
   [(∈ x m)]
   [(fresh (nx) (nego x nx) (∈ nx m))]))

(define (c/⊨ m c)
  (∃ (x <- c) (∈ x m)))

(define (c/⊭ m c)
  (∀ (x <- c) (∃ (nx <- m) (nego x nx))))

(define (f/⊨ m f)
  (∀ (c <- f) (c/⊨ m c)))

(define (f/⊭ m f)
  (∃ (c <- f) (c/⊭ m c)))

(define (splito pxq p x q)
  (conde
   [(== pxq '())
    (== #t #f)]
   [(fresh (a d p^)
           (== pxq `(,a . ,d))
           (conde
            [(== a x)
             (== p '())
             (== q d)]
            [(=/= a x)
             (splito d p^ x q)
             (== p `(,a . ,p^))]))]))

(define (rem-dupo xs ys)
  (conde
   [(== xs '()) (== ys '())]
   [(fresh (a d ys^)
           (== xs `(,a . ,d))
           (conde
            [(∈ a d) (rem-dupo d ys)]
            [(∉ a d)
             (rem-dupo d ys^)
             (== ys `(,a . ,ys^))]))]))

(define (appendo l s out)
  (conde
   [(== '() l) (== s out)]
   [(fresh (a d res)
           (== `(,a . ,d) l)
           (== `(,a . ,res) out)
           (appendo d s res))]))

(define (flatteno xss xs)
  (conde
   [(== xss '()) (== xs '())]
   [(fresh (a d res)
           (== xss `(,a . ,d))
           (flatteno d res)
           (appendo a res xs))]))

(define (⊆* ∈)
  (lambda (xs ys)
    (conde
     [(== xs '())]
     [(fresh (a d)
             (== xs `(,a . ,d))
             (∈ a ys)
             ((⊆* ∈) d ys))])))

(define (⊆ xs ys) ((⊆* (lambda (a m) (↓ m a))) xs ys))

;; should be the final state: all the variables are assigned.
(define (finalo m f)
  (fresh (vars vars^ c cs)
         (flatteno f vars^)
         (rem-dupo vars^ vars)
         (⊆ m vars)
         (⊆ vars m)))

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
   [(fresh (x nx c)
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
           (splito m m1 dl m2)
           (nego dl ndl)
           (↑ m2 ndl)
           (== m^ `(,ndl ,m2))
           (== d^ d))]))

;; TODO: failed to disprove something
(define (dpllo d m f d^ m^)
  (fresh (d* m* x c)
         (formulao f)
         (assignmento m)
         (consistento m)
         (consistento m*)
         (stepo d m f d* m*)
         (conde
          [(== m* 'fail) (== m^ 'fail)]
          [(finalo m* f)
           (f/⊨ m^ f) ;;TODO: necessary?
           (consistento m*)
           (== m* m^)]
          [(=/= m* 'fail)
           (↑ m* x) (∈ x c) (∈ c f)
           (dpllo d* m* f d^ m^)])))
