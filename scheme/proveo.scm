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
      | (∧ bexp bexp)
      | (>= aexp aexp)          greater or equal than
      | (>  aexp aexp)          greater than
|#

(define op1 '(¬))
(define op2 `(+ - * = >= > < <= ∧ ∨))

(define arithop '(+ - *))
(define boolop_num '(= >= > < <=))
(define boolop_bool '(∧ ∨))
(define boolop `(,@op1 ,@boolop_bool ,@boolop_bool))


;; Reflexive, symmetric, transitive closure of rewriteo
(define (⇓o p q)
  (conde
   [(fresh (r)
           (=/= p q)
           (rewriteo p r)
           (⇓o r q))]
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
           (== p `(∧ (∧ ,p1 ,p2) ,p3))
           (== q `(∧ ,p1 (∧ ,p2 ,p3))))]
   [(fresh (p1 p2 p3)
           (== p `(∨ (∨ ,p1 ,p2) ,p3))
           (== q `(∨ ,p1 (∨ ,p2 ,p3))))]
   ;; Unit laws
   [(fresh (p^)
           (conde
            [(== p `(∧ true ,p^))
             (== q p^)]
            [(== p `(∧ ,p^ true))
             (== q p^)]))]
   [(fresh (p^)
           (conde
            [(== p `(∨ false ,p^))
             (== q p^)]
            [(== p `(∨ ,p^ false))
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
            [(== p `(∧ false ,p^))
             (== q 'false)]
            [(== p `(∧ ,p^ false))
             (== q 'false)]))]
   [(fresh (p^)
           (conde
            [(== p `(∨ true ,p^))
             (== q 'true)]
            [(== p `(∨ ,p^ true))
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
           (== p `(∧ (>= ,x ,y) (> ,x ,y)))  ;; Note: this assumes > appears before >=!
           (== q `(> ,x ,y)))]
   [(fresh (x y)
           (== p `(∧ (>= ,x ,y) (¬ (> ,x ,y))))
           (== q `(= ,x ,y)))]
   #|
   [(fresh (x y)
           (== p `(∧ (< ,x ,y) (<= ,x ,y)))
           (== q `(< ,x ,y)))]
   [(fresh (x y)
           (== p `(∧ (<= ,x ,y) (¬ (< ,x ,y))))
           (== q `(= ,x ,y)))]
   |#
   ;; Constant folding
   [(fresh (x y)
           (== p `(= (int ,x) (int ,y)))
           (conde
            [(== x y) (== q 'true)]
            [(=/= x y) (== q 'false)]))]
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
           (== p `(∧ (> (int ,x) (int ,n1) (¬ (> (int ,x) (int ,n2))))))
           (== q `(= (int ,x) (int ,n2)))
           (pluso n1 (build-num 1) n2))]
   [(fresh (x n1 n2 n3)
           (== p `(∧ (> (int ,x) (int ,n1)) (> (int ,x) (int ,n2))))
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
           (== p `(∧ ,r ,s))
           (== q `(∧ ,w ,v))
           (implieso* r w)
           (implieso* s v))]
   [(fresh (r s)
           (== p `(∨ ,r ,s))
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
         (⇓o p r)
         (⇓o q t)
         (implieso* r t)))

;; Equivalent up to normalization
(define (equivo p q) (⇓o p q))

;; p[x -> t] = q
(define (substo p x t q)
  (fresh (r)
         (substo* p x t r)
         (equivo r q)))

(define (listof01o x)
  (conde
   [(== x '())]
   [(fresh (a d)
           (== `(,a . ,d) x)
           (membero a '(0 1))
           (listof01o d))]))

(define (into e)
  (fresh (x)
         (== e `(int ,x))
         (listof01o x)))

(define (aexpo e)
  (conde
   [(into e)]
   [(symbolo e)]
   [(fresh (op e1 e2)
           (== e `(,op ,e1 ,e2))
           (membero op arithop)
           (aexpo e1)
           (aexpo e2))]))

(define (bexpo e)
  (conde
   [(== e 'true)]
   [(== e 'false)]
   [(fresh (op e1)
           (== e `(,op ,e1))
           (membero op op1)
           (bexpo e1))]
   [(fresh (op e1 e2)
           (== e `(,op ,e1 ,e2))
           (membero op boolop_num)
           (aexpo e1)
           (aexpo e2))]
   [(fresh (op e1 e2)
           (== e `(,op ,e1 ,e2))
           (membero op boolop_bool)
           (bexpo e1)
           (bexpo e2))]))

(define (varo x) (symbolo x))

(define (proveo p com q)
  ;; TODO: bexpo p and q
  (conde
   [(fresh (x e)
           (== com `(,x := ,e))
           (varo x)
           (aexpo e)
           (substo q x e p))]
   [(fresh (c1 r c2)
           (== com `(seq ,c1 ,c2))
           (proveo p c1 r)
           (proveo r c2 q))]
   [(fresh (cnd thn els)
           (== com `(if ,cnd ,thn ,els))
           (proveo `(∧ ,p ,cnd) thn q)
           (proveo `(∧ ,p (¬ ,cnd)) els q))]
   [(fresh (cnd body)
           (== com `(while ,cnd ,body))
           (equivo `(∧ ,p (¬ ,cnd)) q)
           (proveo `(∧ ,p ,cnd) body p))]
   [(fresh (r com^)
           (== com `(pre ,r ,com^))
           (implieso p r)
           (proveo r com^ Q))]
   [(fresh (r com^)
           (== com `(post ,r ,com^))
           (implieso r q)
           (proveo p com^ r))]
   [(== com `(skip))
    (equivo p q)]))
