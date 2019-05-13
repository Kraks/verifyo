(define (membero x xs)
  (fresh (a d)
         (== `(,a . ,d) xs)
         (conde
           [(== a x)]
           [(membero x d)])))
