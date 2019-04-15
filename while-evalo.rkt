#lang racket

(require rackunit)
(require minikanren)
(require minikanren/numbers)

(provide (all-defined-out))

(define succeed (== #f #f))

(define int
  (λ (x) `(int ,(build-num x))))

(define lookupo
  (λ (σ x v)
    (conde
     [(fresh (x^ v^ rest)
             (== x x^)
             (== v v^)
             (== `((,x^ ↦ ,v^) . ,rest) σ))]
     [(fresh (x^ v^ rest)
             (=/= x x^)
             (== `((,x^ ↦ ,v^) . ,rest) σ)
             (lookupo rest x v))])))

(define updateo
  (λ (σ x v σ^)
    (conde
     [(== '() σ)
      (== `((,x ↦ ,v)) σ^)]
     [(fresh (x^ v^ rest)
             (== x x^)
             (== `((,x^ ↦ ,v^) . ,rest) σ)
             (== `((,x ↦ ,v) . ,rest) σ^))]
     [(fresh (x^ v^ rest σ*)
             (=/= x x^)
             (== `((,x^ ↦ ,v^) . ,rest) σ)
             (updateo rest x v σ*)
             (== `((,x^ ↦ ,v^) . ,σ*) σ^))])))

(define eval/predo
  (λ (p σ v)
    (conde
     [(== p 'true) (== v #t)]
     [(== p 'false) (== v #f)]
     [(fresh (e1 e2 v1 v2)
             (== p `(,e1 = ,e2))
             (conde
              [(== v1 v2) (== v #t)]
              [(=/= v1 v2) (== v #f)])
             (eval/expo e1 σ v1)
             (eval/expo e2 σ v2))]
     [(fresh (e1 e2)
             (== p `(,e1 > ,e2))
             (eval/predo `(,e2 <= ,e1) σ v))]
     [(fresh (e1 e2)
             (== p `(,e1 >= ,e2))
             (eval/predo `(,e2 < ,e2) σ v))]
     [(fresh (e1 e2 v1 v2)
             (== p `(,e1 < ,e2))
             (conde
              [(<o v1 v2) (== v #t)]
              [(<=o v2 v1) (== v #f)])
             (eval/expo e1 σ `(int ,v1))
             (eval/expo e2 σ `(int ,v2)))]
     [(fresh (e1 e2 v1 v2)
             (== p `(,e1 <= ,e2))
             (conde
              [(<=o v1 v2) (== v #t)]
              [(<o v2 v1) (== v #f)])
             (eval/expo e1 σ `(int ,v1))
             (eval/expo e2 σ `(int ,v2)))]
     [(fresh (p1 p2 v1 v2)
             (== p `(,p1 ∧ ,p2))
             (conde
              [(== v1 #t) (== v2 #t) (== v #t)]
              [(== v1 #f) (== v2 #t) (== v #f)]
              [(== v1 #t) (== v2 #f) (== v #f)]
              [(== v1 #f) (== v2 #f) (== v #f)])
             (eval/predo p1 σ v1)
             (eval/predo p2 σ v2))]
     [(fresh (p1 p2 v1 v2)
             (== p `(,p1 ∨ ,p2))
             (conde
              [(== v1 #t) (== v2 #t) (== v #t)]
              [(== v1 #t) (== v2 #f) (== v #t)]
              [(== v1 #f) (== v2 #t) (== v #t)]
              [(== v1 #f) (== v2 #f) (== v #f)])
             (eval/predo p1 σ v1)
             (eval/predo p2 σ v2))];;TODO: could be optimized by shortcut
     [(fresh (p1 p2 v1 v2)
             (== p `(,p1 ⇒ ,p2))
             (conde
              [(== v1 #t) (== v2 #f) (== v #f)]
              [(== v1 #t) (== v2 #t) (== v #t)]
              [(== v1 #f) (== v2 #t) (== v #t)]
              [(== v1 #f) (== v2 #f) (== v #t)])
             (eval/predo p1 σ v1)
             (eval/predo p2 σ v2))]
     [(fresh (np pv)
             (== p `(¬ ,np))
             (conde
              [(== pv #t) (== v #f)]
              [(== pv #f) (== v #t)])
             (eval/predo np σ pv))])))

(define eval/expo
  (λ (e σ v)
    (conde
     [(fresh (n)
             (== `(int ,n) e)
             (== e v))]
     [(symbolo e) (lookupo σ e v)]
     ;[(numbero e) (== v e)]
     [(fresh (e1 e2 v1 v2 ans)
             (== e `(,e1 + ,e2))
             (== v `(int ,ans))
             (eval/expo e1 σ `(int ,v1))
             (eval/expo e2 σ `(int ,v2))
             (pluso v1 v2 ans))]
     [(fresh (e1 e2 v1 v2 ans)
             (== e `(,e1 - ,e2))
             (== v `(int ,ans))
             (eval/expo e1 σ `(int ,v1))
             (eval/expo e2 σ `(int ,v2))
             (minuso v1 v2 ans))]
     [(fresh (e1 e2 v1 v2 ans)
             (== e `(,e1 * ,e2))
             (== v `(int ,ans))
             (eval/expo e1 σ `(int ,v1))
             (eval/expo e2 σ `(int ,v2))
             (*o v1 v2 ans))]
     [(fresh (e1 e2 v1 v2 ans)
             (== e `(,e1 / ,e2))
             (== v `(int ,ans))
             (eval/expo e1 σ `(int ,v1))
             (eval/expo e2 σ `(int ,v2))
             (/o v1 v2 v ans))])))
            
(define execo
  (λ (com σ σ^)
    (conde
     [(fresh (x e v)
             (== com `(,x := ,e))
             (eval/expo e σ v)
             (updateo σ x v σ^))]
     [(fresh (c1 c2 σ*)
             (== com `(seq ,c1 ,c2))
             (execo c1 σ σ*)
             (execo c2 σ* σ^))]
     [(fresh (c cv t e)
             (== com `(if ,c ,t ,e))
             (conde
              [(== cv #t) (execo t σ σ^)]
              [(== cv #f) (execo e σ σ^)])
             (eval/predo c σ cv))]
     [(fresh (c cv i body σ*)
             (== com `(while ,c ,i ,body))
             (conde
              [(== cv #t)
               (execo body σ σ*)
               (execo com σ* σ^)]
              [(== cv #f) (== σ σ^)])
             (eval/predo c σ cv))]
     [(== com `(skip)) (== σ σ^)])))

