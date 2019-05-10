;;(load "mk/test-check.scm")
;;(load "evalo-optimized.scm")
(load "mk/mk.scm")
(set! allow-incomplete-search? #t)

;; TODO
(define (normo p q)
  (conde
   [(fresh (r)
           (rewriteo p r)
           (normo r q))]
   [(== p q)]))

;; TODO
(define (implieso p q)
  (== p q))

;; TODO
(define (substo* p x t q)
  (== p q))

(define (equivo p q)
  (fresh (r)
         (normo p r)
         (normo r q)))

;; p[x -> t] = q
(define (substo p x t q)
  (fresh (r)
         (substo* p x t r)
         (equivo r q)))

(define (provero p com q)
  (conde
   [(fresh (x e)
           (== com `(,x := ,e))
           (substo q x e p))]
   [(fresh (c1 r c2)
           (== com `(seq ,c1 ,c2))
           (provero p c1 r)
           (provero r c2 q))]
   [(fresh (cnd thn els)
           (== com `(if ,cnd ,thn ,els))
           (provero `(and ,p ,cnd) thn q)
           (provero `(and ,p (not ,cnd)) els q))]
   [(fresh (cnd body)
           (== com `(while ,cnd ,body))
           (equivo `(and ,p (not ,cnd)) q)
           (provero `(and ,p ,cnd) body p))]
   [(fresh (r com^)
           (== com `(pre ,r ,com^))
           (implieso p r)
           (provero r com^ Q))]
   [(fresh (r com^)
           (== com `(post ,r ,com^))
           (implieso r q)
           (provero p com^ r))]
   [(== com `(skip))
    (equivo p q)]))
