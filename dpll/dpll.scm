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

(define (consistento m)
  (conde
   [(== m '())]
   [(fresh (a d na)
           (== m `(,a . ,d))
           (nego a na)
           (∉ na d)
           (∉  a d)
           (consistento d))]))

(define (↑ m x)
  (fresh (nx)
         (nego x nx)
         (∉ nx m)
         (∉ x m)))

(define (↓ m x)
  (conde
   [(∈ x m)]
   [(fresh (nx) (nego x nx) (∈ nx m))]))

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

(define (finalo m f)
  (fresh (vars vars^ c cs)
         (flatteno f vars^)
         (rem-dupo vars^ vars)
         (⊆ m vars)
         (⊆ vars m)))

;; d is an auxiliary list that tracks decision literals (only added by Decide rule)
;; m is the model, i.e., the assignment
;; f is the formula
;; r is the result
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
           (== d `(,dl . ,ds))
           (splito m m1 dl m2)
           (nego dl ndl)
           (↑ m2 ndl)
           (== m^ `(,ndl ,m2))
           (== d^ d))]))

(define (dpllo d m f d^ m^)
  (fresh (d* m* x c)
         (formulao f)
         (consistento m)
         (consistento m*)
         (stepo d m f d* m*)
         (conde
          [(== m* 'fail) (== m^ 'fail)]
          [(finalo m* f)
           (f/⊨ m^ f)
           (consistento m*)
           (== m* m^)]
          [(=/= m* 'fail)
           (↑ m* x) (∈ x c) (∈ c f)
           (dpllo d* m* f d^ m^)])))

         #|
         (conde
         [(f/⊭ m^ f) ;; TODO
         (== m^ 'fail)]
         [(finalo m^ f)
         (f/⊨ m^ f) ;; TODO
         (consistento m^)]
         [(stepo d m f d* m*)
         (dpllo d* m* f d^ m^)])))
         |#
