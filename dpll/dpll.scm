(load "../mk/mk.scm")
(load "../membero.scm")

#|
A formula is in CNF, i.e., a list of clauses.
A clauses is a disjunction of literals, i.e., a list of literals.
A literal is either a symbol, or a negation of a symbol (¬ x).
|#

(define (lito l)
  (conde
   [(symbolo l)]
   [(fresh (l^)
           (== l `(¬ ,l^))
           (symbolo l^))]))

(define listofo
  (lambda (rel)
    (lambda (xs)
      (conde
       [(== xs '())]
       [(fresh (a d)
               (== `(,a . ,d) xs)
               (rel a)
               ((listofo rel) d))]))))

(define (clauseo c) ((listofo lito) c))

(define (formulao f) ((listofo clauseo) f))

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

;; TODO: where to add syntactic constraint?

(define (consistento m)
  (conde
   [(== m '())]
   [(fresh (a d na)
           (== m `(,a . ,d))
           (nego a na)
           (∉ na d)
           (consistento d))]))

(define (↑ m x)
  (fresh (nx)
         (nego x nx)
         (∉ nx n)
         (∉ x m)))

(define (c/⊨ m c)
  (fresh (r)
         ((listofo lito) m)
         (intersecto m c r)
         (=/= r '())))

(define (c/⊭ m c)
  (conde
   [(== c '())]
   [(fresh (a d na)
           (== c `(,a . ,d))
           (nego a na)
           (∈ na m)
           (c/⊭ m d))]))

(define (f/⊨ m f)
  (conde
   [(== f '())]
   [(fresh (a d)
           (== f `(,a . ,d))
           (c/⊨ m a)
           (f/⊨ m d))]))

(define (f/⊭ m f)
  (fresh (a d)
         (=/= f '())
         (== f `(,a . ,d))
         (conde
          [(c/⊭ m a)]
          [(f/⊭ m d)])))

;; m is the model, i.e., the assignment
;; f is the formula
;; d is an auxiliary list that tracks decision literals (only added by Decide rule)
;; r is the result
(define (dpllo m f d r)
  (conde
   ;; Succeed
   ;;[(f/⊨ m f) (== r #t)]
   ;; Unit Propagate
   [(fresh (x xs c m^)
           (∈ c f)
           (== c `(,x . ,xs))
           (c/⊭ m xs)
           (↑ m x)
           (== m^ `(,x . ,m))
           (dpllo m^ f d r))]
   ;; Decide
   [(fresh (x nx c m^ d^)
           (∈ c f)
           (∈ x c)
           (↑ m x)
           (== d^ `(,x . ,d))
           (== m^ `(,x . ,m))
           (dpllo m^ f d^ r))]
   ;; Fail
   [(fresh (c)
           (∈ c f)
           (c/⊭ m c)
           (== d '())
           (== r #f))]
   ;; Backjump
   ;; partition
   ))
