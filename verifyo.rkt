#lang racket

(require rackunit)
(require minikanren)
(require minikanren/numbers)

(require "while.rkt")
(require "smt.rkt")

;; Idea 1: relation verification condition generator

; Substitution for expressions
; e[x -> t] = res
(define substo/exp
  (lambda (e x t res)
    (conde
     [(numbero e)
      (== res e)]
     [(symbolo e)
      (== e x)
      (== t res)]
     [(symbolo e)
      (=/= e x)
      (== e res)]
     [(fresh (e1 e2 s1 s2)
             (== e `(,e1 + ,e2))
             (substo/exp e1 x t s1)
             (substo/exp e2 x t s2)
             (== res `(,s1 + ,s2)))]
     [(fresh (e1 e2 s1 s2)
             (== e `(,e1 - ,e2))
             (substo/exp e1 x t s1)
             (substo/exp e2 x t s2)
             (== res `(,s1 - ,s2)))]
     [(fresh (e1 e2 s1 s2)
             (== e `(,e1 * ,e2))
             (substo/exp e1 x t s1)
             (substo/exp e2 x t s2)
             (== res `(,s1 * ,s2)))]
     [(fresh (e1 e2 s1 s2)
             (== e `(,e1 / ,e2))
             (substo/exp e1 x t s1)
             (substo/exp e2 x t s2)
             (== res `(,s1 / ,s2)))]
     )))

(check-equal?
 (run 1 (q) (substo/exp 1 'a 'b q)) '(1))

(check-equal?
 (run 1 (q) (substo/exp 'c 'a 'b q)) '(c))

(check-equal?
 (run 1 (q) (substo/exp 'a 'a 'b q)) '(b))

(check-equal?
 (run 1 (q) (substo/exp '(a + b) 'a 'c q)) '((c + b)))

(check-equal?
 (run 1 (q) (substo/exp q 'a 'c '(c + b))) '((a + b)))

; Substitution for predicates
; p[x -> t] = res
(define substo
  (lambda (p x t res)
    (conde
     [(== p 'true) (== p res)]
     [(== p 'false) (== p res)]
     [(fresh (e1 e2 s1 s2)
             (== p `(,e1 = ,e2))
             (== res `(,s1 = ,s2))
             (substo/exp e1 x t s1)
             (substo/exp e2 x t s2))]
     [(fresh (e1 e2 s1 s2)
             (== p `(,e1 < ,e2))
             (== res `(,s1 < ,s2))
             (substo/exp e1 x t s1)
             (substo/exp e2 x t s2))]
     [(fresh (e1 e2 s1 s2)
             (== p `(,e1 ≤ ,e2))
             (== res `(,s1 ≤ ,s2))
             (substo/exp e1 x t s1)
             (substo/exp e2 x t s2))]
     [(fresh (e1 e2 s1 s2)
             (== p `(,e1 > ,e2))
             (== res `(,s1 > ,s2))
             (substo/exp e1 x t s1)
             (substo/exp e2 x t s2))]
     [(fresh (e1 e2 s1 s2)
             (== p `(,e1 ≥ ,e2))
             (== res `(,s1 ≥ ,s2))
             (substo/exp e1 x t s1)
             (substo/exp e2 x t s2))]
     [(fresh (p1 p2 s1 s2)
             (== p `(,p1 ∧ ,p2))
             (== res `(,s1 ∧ ,s2))
             (substo p1 x t s1)
             (substo p2 x t s2))]
     [(fresh (p1 p2 s1 s2)
             (== p `(,p1 ∨ ,p2))
             (== res `(,s1 ∨ ,s2))
             (substo p1 x t s1)
             (substo p2 x t s2))]
     [(fresh (p1 p2 s1 s2)
             (== p `(,p1 ⇒ ,p2))
             (== res `(,s1 ⇒ ,s2))
             (substo p1 x t s1)
             (substo p2 x t s2))]
     [(fresh (p1 s1)
             (== p `(¬ ,p1))
             (== res `(¬ ,p1))
             (substo p1 x t s1))])))

(check-equal?
 (run 1 (q) (substo '((a + b) = (b + c)) 'b 1 q))
 '(((a + 1) = (1 + c))))

(check-equal?
 (run 1 (q) (substo q 'b 'c '((a + 1) = (d + c))))
 '(((a + 1) = (d + b))))

(check-equal?
 (run 1 (q) (substo q 'b 'c '((a + 1) = (d + c))))
 '(((a + 1) = (d + b))))

(check-equal?
 (run 1 (q) (substo q 'b 'c '((a + c) = (d + c))))
 '(((a + b) = (d + b))))

(define wpo
  (lambda (com post wp sc)
    (conde
     [(fresh (x e v)
             (== com `(,x := ,e))
             (substo post x e wp))]
     [(fresh (c1 c2)
             (== com `(seq ,c1 ,c2))
             )]
     [(fresh (c cv t e)
             (== com `(if ,c ,t ,e))
             )]
     [(fresh (c cv i body σ*)
             (== com `(while ,c ,i ,body))
             )]
     [(== com `(skip))])))
