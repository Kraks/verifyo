(load "mk/mk.scm")
(load "arithmetic.scm")
(load "membero.scm")
(load "mk/test-check.scm")
(set! allow-incomplete-search? #t)

#| Grammar:
com := (skip)                   skip
     | (x := aexp)              assignment
     | (if bexp com com)        conditional
     | (seq com com)            sequence
     | (while bexp com)         loop
     | (pre bexp com)           strenthen the pre-condition
     | (post bexp com)          weaken the post-condition

aexp := ℕ | x
      | (+ aexp aexp)
      | (- aexp aexp)
      | (* aexp aexp)

bexp := true | false
      | (and bexp bexp)
      | (>= aexp aexp)          greater or equal than
      | (>  aexp aexp)          greater than
|#

(define op1 '(not))
(define op2 '(= >= > < <= + - * and or))

;; Reflexive, symmetric, transitive closure of rewriteo
(define (normo p q)
  (conde
   [(fresh (r)
           (=/= p q)
           (rewriteo p r)
           (normo r q))]
   [(== p q)]))

;; TODO: why such rewrite rules are adequate?
;; TODO: consider divide rewrite to rewrite/pred rewrite/exp?
;; Such rewriteo is essentially a partial evaluator on logic terms.

;; Single-step rewrite rules
(define (rewriteo p q)
  (conde
   ;; Reflexivity
   [(fresh (x)
           (== p `(= ,x ,x))
           (== q 'true))]
   [(fresh (x)
           (== p `(>= ,x ,x))
           (== q 'true))]
   #|
   [(fresh (x)
           (== p `(<= ,x ,x))
           (== q 'true))]
   |#
   ;; Congruence of unary operators
   [(fresh (op p^ q^)
           (== p `(,op ,p^))
           (== q `(,op ,q^))
           (membero op op1)
           (rewriteo p^ q^))]
   ;; Congruence of binary operators
   [(fresh (op p1 p2 q1 q2)
           (== p `(,op ,p1 ,p2))
           (== q `(,op ,q1 ,q2))
           (membero op op2)
           (rewriteo p1 q1)
           (rewriteo p2 q2))]
   ;; Prefer right-associativity over left-associativity
   [(fresh (p1 p2 p3)
           (== p `(and (and ,p1 ,p2) ,p3))
           (== q `(and ,p1 (and ,p2 ,p3))))]
   [(fresh (p1 p2 p3)
           (== p `(or (or ,p1 ,p2) ,p3))
           (== q `(or ,p1 (or ,p2 ,p3))))]
   ;; Unit laws
   [(fresh (p^)
           (conde
            [(== p `(and true ,p^))
             (== q p^)]
            [(== p `(and ,p^ true))
             (== q p^)]))]
   [(fresh (p^)
           (conde
            [(== p `(or false ,p^))
             (== q p^)]
            [(== p `(or ,p^ false))
             (== q p^)]))]
   [(fresh (x)
           (conde
            [(== p `(+ (int ()) (int ,x)))
             (== q `(int ,x))]
            [(== p `(+ (int ,x) (int ())))
             (== q `(int ,x))]))]
   [(fresh (x)
           (== p `(- (int ,x) (int ())))
           (== q `(int ,x)))]
   [(fresh (x)
           (conde
            [(== p `(* (int (1)) (int ,x)))
             (== q `(int ,x))]
            [(== p `(* (int ,x) (int (1))))
             (== q `(int ,x))]))]
   ;; Zero laws
   [(fresh (p^)
           (conde
            [(== p `(and false ,p^))
             (== q 'false)]
            [(== p `(and ,p^ false))
             (== q 'false)]))]
   [(fresh (p^)
           (conde
            [(== p `(or true ,p^))
             (== q 'true)]
            [(== p `(or ,p^ true))
             (== q 'true)]))]
   [(fresh (p^)
           (conde
            [(== p `(* (int ()) (int ,p^)))
             (== q (int 0))]
            [(== p `(* (int ,p^) (int ())))
             (== q (int 0))]))]
   ;; Prefer greater over geq
   [(fresh (x n1 n2)
           (== p `(>= (int ,x) (int ,n1)))
           (== q `(>  (int ,x) (int ,n2)))
           (minuso n1 (build-num 1) n2))]
   ;; Simplify conjunctions of comparisons
   ;; TODO: Obviously, there can be more such rules, do we need them?
   ;; TODO: Do we need both >=/> and <=/<?
   ;;       If we enforce that variables must appear on the lhs, then seems yes.
   ;;       But if we relax that (x > 1 or 1 > x are both valid), then we need more rewrite rules to handle the later cases.
   [(fresh (x y)
           (== p `(and (>= ,x ,y) (> ,x ,y)))  ;; Note: this assumes > appears before >=!
           (== q `(> ,x ,y)))]
   [(fresh (x y)
           (== p `(and (>= ,x ,y) (not (> ,x ,y))))
           (== q `(= ,x ,y)))]
   #|
   [(fresh (x y)
           (== p `(and (< ,x ,y) (<= ,x ,y)))
           (== q `(< ,x ,y)))]
   [(fresh (x y)
           (== p `(and (<= ,x ,y) (not (< ,x ,y))))
           (== q `(= ,x ,y)))]
   |#
   ;; Constant folding
   [(fresh (x y)
           (== p `(> (int ,x) (int ,y)))
           (conde
            [(<o y x) (== q 'true)]
            [(<=o x y) (== q 'false)]))]
   [(fresh (x y)
           (== p `(>= (int ,x) (int ,y)))
           (conde
            [(<=o y x) (== q 'true)]
            [(<o x y) (== q 'false)]))]
   [(fresh (x n1 n2 n3)
           (== p `(> (- (int ,x) (int n1)) (int ,n2)))
           (== q `(> (int ,x) (int ,n3)))
           (== n3 (pluso n1 n2)))]
   [(fresh (x n1 n2)
           (== p `(and (> (int ,x) (int ,n1) (not (> (int ,x) (int ,n2))))))
           (== q `(= (int ,x) (int ,n2)))
           (pluso n1 (build-num 1) n2))]
   [(fresh (x n1 n2 n3)
           (== p `(and (> (int ,x) (int ,n1)) (> (int ,x) (int ,n2))))
           (== q `(> (int ,x) (int ,n3)))
           (maxo n1 n2 n3))]
   [(fresh (x n1 n2 n3)
           (== p `(> (+ (int ,x) (int ,n1)) (int ,n2)))
           (== q `(> (int ,x) (int ,n3)))
           (minuso n2 n1 n3))]
   [(fresh (x y)
           (== p `(>= (- (int ,x) (int ,y)) ,(int 0)))
           (== q `(>= (int ,x) (int ,y))))]
   #| -1 is not expressible
   [(fresh (x y)
           (== p `(> (- ,x ,y) (int -1)))
           (== q `(>= ,x ,y)))]
   |#
   [(fresh (x y z)
           (== p `(+ (* (+ (int ,x) ,(int 1)) (int ,y)) (- (int ,z) (int ,y))))
           (== q `(+ (* (int ,x) (int ,y)) (int ,z))))]))

(define (substo* p x t q)
  (conde
   ;;[(== p q) (numbero p)]
   [(fresh (n)
           (== p `(int ,n))
           (== q p))]
   [(symbolo p)
    (== p x)
    (== t q)]
   [(symbolo p)
    (=/= p x)
    (== p q)]
   [(fresh (op p^ q^)
           (== p `(,op ,p^))
           (== q `(,op ,q^))
           (membero op op1)
           (substo* p^ x t q^))]
   [(fresh (op p1 p2 q1 q2)
           (== p `(,op ,p1 ,p2))
           (== q `(,op ,q1 ,q2))
           (membero op op2)
           (substo* p1 x t q1)
           (substo* p2 x t q2))]))

(define (implieso* p q)
  (conde
   [(== p q)]
   [(== q 'true)]
   [(== p 'false)]
   ;; TODO: is it sound? under what condition?
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

;; Equivalent up to normalization
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

