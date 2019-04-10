#lang racket

(require rackunit)
(require minikanren)
(require minikanren/numbers)

(define succeed (== #f #f))
(define fail (== #f #t))

(define lookupo
  (λ (σ x v)
    (conde
     [(fresh (x^ v^ rest)
             (== `((,x^ . ,v^) . ,rest) σ)
             (== x x^)
             (== v v^))]
     [(fresh (x^ v^ rest)
             (== `((,x^ . ,v^) . ,rest) σ)
             (=/= x x^)
             (lookupo rest x v))])))

(define updateo
  (λ (σ x v σ^)
    (conde
     [(== '() σ)
      (== `((,x . ,v)) σ^)]
     [(fresh (x^ v^ rest)
             (== `((,x^ . ,v^) . ,rest) σ)
             (== x x^)
             (== `((,x . ,v) . ,rest) σ^))]
     [(fresh (x^ v^ rest σ*)
             (== `((,x^ . ,v^) . ,rest) σ)
             (=/= x x^)
             (updateo rest x v σ*)
             (== `((,x^ . ,v^) . ,σ*) σ^))])))

(check-equal?
 (run 1 (q)
      (lookupo '((a . 1)) 'a q))
 '(1))
(check-equal?
 (run 1 (q)
      (lookupo '((b . 2) (a . 1)) 'a q))
 '(1))
(check-equal?
 (run 1 (q)
      (lookupo '((a . 1)) 'b q))
 '())
(check-equal?
 (run 1 (q)
      (updateo '() 'a 1 q))
 '(((a . 1))))
(check-equal?
 (run 1 (q)
      (updateo '((a . 2)) 'a 2 q))
 '(((a . 2))))
(check-equal?
 (run 1 (q)
      (updateo '((a . 1)) 'b 2 q))
 '(((a . 1) (b . 2))))

(define eval/predo
  (λ (p σ v)
    (conde
     [(== p 'true) (== v #t)]
     [(== p 'false) (== v #f)]
     [(fresh (e1 e2 v1 v2)
             (== p `(,e1 = ,e2))
             (eval/expo e1 σ v1)
             (eval/expo e2 σ v2)
             (conde
              [(== v1 v2) (== v #t)]
              [(=/= v1 v2) (== v #f)]))]
     [(fresh (e1 e2)
             (== p `(,e1 > ,e2))
             (eval/predo `(,e2 <= ,e1) σ v))]
     [(fresh (e1 e2)
             (== p `(,e1 >= ,e2))
             (eval/predo `(,e2 < ,e2) σ v))]
     [(fresh (e1 e2 v1 v2)
             (== p `(,e1 < ,e2))
             (eval/expo e1 σ `(int ,v1))
             (eval/expo e2 σ `(int ,v2))
             (conde
              [(<o v1 v2) (== v #t)]
              [(<=o v2 v1) (== v #f)]))]
     [(fresh (e1 e2 v1 v2)
             (== p `(,e1 <= ,e2))
             (eval/expo e1 σ `(int ,v1))
             (eval/expo e2 σ `(int ,v2))
             (conde
              [(<=o v1 v2) (== v #t)]
              [(<o v2 v1) (== v #f)]))]
     [(fresh (p1 p2 v1 v2)
             (== p `(,p1 ∧ ,p2))
             (eval/predo p1 σ v1)
             (eval/predo p2 σ v2)
             (conde
              [(== v1 #t) (== v2 #t) (== v #t)]
              [(== v1 #f) (== v2 #t) (== v #f)]
              [(== v1 #t) (== v2 #f) (== v #f)]
              [(== v1 #f) (== v2 #f) (== v #f)]))]
     [(fresh (p1 p2 v1 v2)
             (== p `(,p1 ∨ ,p2))
             (eval/predo p1 σ v1)
             (eval/predo p2 σ v2) ;;TODO: could be optimized by shortcut
             (conde
              [(== v1 #t) (== v2 #t) (== v #t)]
              [(== v1 #t) (== v2 #f) (== v #t)]
              [(== v1 #f) (== v2 #t) (== v #t)]
              [(== v1 #f) (== v2 #f) (== v #f)]))]
     [(fresh (p1 p2 v1 v2)
             (== p `(,p1 ⇒ ,p2))
             (eval/predo p1 σ v1)
             (eval/predo p2 σ v2)
             (conde
              [(== v1 #t) (== v2 #f) (== v #f)]
              [(== v1 #t) (== v2 #t) (== v #t)]
              [(== v1 #f) (== v2 #t) (== v #t)]
              [(== v1 #f) (== v2 #f) (== v #t)]))]
     [(fresh (np pv)
             (== p `(¬ ,np))
             (eval/predo np σ pv)
             (conde
              [(== pv #t) (== v #f)]
              [(== pv #f) (== v #t)]))])))

(define eval/expo
  (λ (e σ v)
    (conde
     [(fresh (n)
             (== `(int ,n) e)
             (== e v))]
     [(symbolo e) (lookupo σ e v)]
     [(numbero e) (== v e)]
     [(fresh (e1 e2 v1 v2 ans)
             (== e `(,e1 + ,e2))
             (eval/expo e1 σ `(int ,v1))
             (eval/expo e2 σ `(int ,v2))
             (pluso v1 v2 ans)
             (== v `(int ,ans)))]
     [(fresh (e1 e2 v1 v2 ans)
             (== e `(,e1 - ,e2))
             (eval/expo e1 σ `(int ,v1))
             (eval/expo e2 σ `(int ,v2))
             (minuso v1 v2 ans)
             (== v `(int ,ans)))]
     [(fresh (e1 e2 v1 v2 ans)
             (== e `(,e1 * ,e2))
             (eval/expo e1 σ `(int ,v1))
             (eval/expo e2 σ `(int ,v2))
             (*o v1 v2 ans)
             (== v `(int ,ans)))]
     [(fresh (e1 e2 v1 v2 ans)
             (== e `(,e1 / ,e2))
             (eval/expo e1 σ `(int ,v1))
             (eval/expo e2 σ `(int ,v2))
             (/o v1 v2 v ans)
             (== v `(int ,ans)))])))

(define int
  (λ (x) `(int ,(build-num x))))

(check-equal?
 (run 1 (q) (eval/expo (int 1) '() q))
 '((int (1)))
 )
(check-equal?
 (run 1 (q)
      (eval/expo 'a '((a . 1)) q))
 '(1))
(check-equal?
 (run 1 (q)
      (eval/expo 'b '((a . 1) (b . 2)) q))
 '(2))
(check-equal?
 (run 1 (q)
      (eval/expo '(a + b) `((a . ,(int 3)) (b . ,(int 3))) q))
 '((int (0 1 1)))
 )
(check-equal?
 (run 1 (q)
      (eval/expo '(a + b) `((a . ,q) (b . ,(int 3))) (int 6)))
 '((int (1 1)))
 )
(check-equal?
 (run 1 (q)
      (eval/expo `(,q + b) `((b . ,(int 3))) (int 6)))
 '((int (1 1)))
 )
(check-equal?
 (run 1 (q)
      (eval/predo 'true '() q))
 '(#t))
(check-equal?
 (run 1 (q)
      (eval/predo 'false '() q))
 '(#f))
(check-equal?
 (run 1 (q)
      (eval/predo '(¬ true) '() q))
 '(#f))
(check-equal?
 (run 1 (q)
      (eval/predo '(1 = 2) '() q))
 '(#f))
(check-equal?
 (run 1 (q) (eval/predo '(3 = 3) '() q))
 '(#t))
(check-equal?
 (run 1 (q)
      (eval/predo `((,(int 1) + ,(int 2)) = ,(int 3)) '() q))
 '(#t))

(define execo
  (λ (com σ σ^)
    (conde
     [(fresh (x e v)
             (== com `(,x := ,e))
             (eval/expo e σ v)
             (updateo σ x v σ^))]
     [(fresh (c1 c2 σ*)
             (== com `(seq ,c1 ,c2))
             (== execo c1 σ σ*)
             (== execo c2 σ* σ^))]
     [(fresh (c cv t e)
             (== com `(if ,c ,t ,e))
             (eval/predo c σ cv)
             (conde
              [(== cv #t) (execo t σ σ^)]
              [(== cv #f) (execo e σ σ^)]))]
     [(fresh (c cv i body σ*)
             (== com `(while ,c ,i ,body))
             (== eval/predo c σ cv)
             (conde
              [(== cv #t)
               (execo body σ σ*)
               (execo com σ* σ^)]
              [(== cv #f) (== σ σ^)]))]
     [(== com `(skip))
      (== σ σ^)])))