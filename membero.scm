(define (membero x xs)
  (fresh (a d)
         (== `(,a . ,d) xs)
         (conde
           [(== a x)]
           [(membero x d)])))

(define (not-membero x xs)
  (conde
   [(== xs '())]
   [(fresh (a d)
           (== xs `(,a . ,d))
           (=/= a x)
           (not-membero x d))]))

(define (∈ x m) (membero x m))
(define (∉ x m) (not-membero x m))
