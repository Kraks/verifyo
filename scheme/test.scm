(load "dmatch.scm")

(define a 1)
(define b 
  (dmatch a
   [,x number? 2]))

(define s 'false)

(define c
  (dmatch s
    [true 1]
    [false 2]))

(define p '(1 + 2))
(define d
  (dmatch p
    [(,a + ,b) (+ a b)]))

(define e (dmatch 'a
  [,n (guard (number? n))
   n]
  [,x (guard (symbol? x))
   x]
  [(,a + ,b)
   (a + b)]))
