#lang racket

(require rackunit)
(require minikanren)
(require minikanren/numbers)

(require "while.rkt")
(require "smt.rkt")

(define verifyo
  (lambda (P com Q)
    (conde
     [(fresh (x e v)
             (== com `(,x := ,e))
            )]
     [(fresh (c1 c2 σ*)
             (== com `(seq ,c1 ,c2))
             )]
     [(fresh (c cv t e)
             (== com `(if ,c ,t ,e))
             )]
     [(fresh (c cv i body σ*)
             (== com `(while ,c ,i ,body))
             )]
     [(== com `(skip))])))
