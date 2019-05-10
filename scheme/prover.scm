;;(load "mk/test-check.scm")
;;(load "evalo-optimized.scm")
(load "mk/mk.scm")
(load "arithmetic.scm")
(set! allow-incomplete-search? #t)

;; TODO: We need it to be pure
(define (normo p q)
  (conde
   [(fresh (r)
           (rewriteo p r)
           (normo r q))]
   [(== p q)]))

;; TODO
(define (rewriteo p q)
  (== p q))

;; TODO
(define (substo* p x t q)
  (conde
   [(== p q) (numbero p)]
   [(symbolo p)
    (== p x)
    (== t q)]
   [(symbolo p)
    (=/= p x)
    (== p q)]))

(define (implieso* p q)
  (conde
   [(== p q)]
   [(== q 'true)]
   [(== p 'false)]
   [(fresh (r s w v)
           (== p `(and ,r ,s))
           (== q `(and ,w ,v))
           (implieso* r w)
           (implieso* s v))]
   [(fresh (r s)
           (== p `(or ,r ,s))
           (conde
            [(implieso r q)]
            [(implieso s q)]))]
   [(fresh (x n m)
           (symbolo x)
           (== p `(< ,x (int ,n)))
           (== q `(< ,x (int ,m)))
           (<o n m))]
   [(fresh (x n m)
           (symbolo x)
           (== p `(<= ,x (int ,n)))
           (== q `(<= ,x (int ,m)))
           (<=o n m))]
   [(fresh (x n m)
           (symbolo x)
           (== p `(> ,x (int ,n)))
           (== q `(> ,x (int ,m)))
           (<o m n))]
   [(fresh (x n m)
           (symbolo x)
           (== p `(>= ,x (int ,n)))
           (== q `(>= ,x (int ,m)))
           (<=o m n))]))

(define (implieso p q)
  (fresh (r t)
         (normo p r)
         (normo q t)
         (implieso* r t)))

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
