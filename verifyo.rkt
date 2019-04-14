#lang racket

(require rackunit)
(require minikanren)
(require minikanren/numbers)

(require "while.rkt")
(require "smt.rkt")

;; Idea 1: relation verification condition generator

; e[x -> t] = res
(define substo
  (lambda (e x t res)
    (conde
     [(== 

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
