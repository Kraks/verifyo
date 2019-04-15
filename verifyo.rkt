#lang racket

(require rackunit)
(require minikanren)
(require minikanren/numbers)

(require "while.rkt")
(require "while-evalo.rkt")
(require "smt.rkt")

(provide (all-defined-out))

;; Idea 1: relation verification condition generator

; Substitution for expressions
; e[x -> t] = res
(define substo/exp
  (lambda (e x t res)
    (conde
     [(fresh (n)
             (== `(int ,n) e)
             (== e res))]
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
