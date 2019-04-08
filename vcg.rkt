#lang racket

(require "while.rkt")

;; TODO: logical variables

;; e[x → t]
(define (subst/exp e x t)
  (match e
    [(? number? n) n]
    [(? symbol? v)
     (if (eq? v x)
         t
         v)]
    [`(,e1 + ,e2) `(,(subst/exp e1 x t) + ,(subst/exp e2 x t))]
    [`(,e1 - ,e2) `(,(subst/exp e1 x t) - ,(subst/exp e2 x t))]
    [`(,e1 * ,e2) `(,(subst/exp e1 x t) * ,(subst/exp e2 x t))]
    [`(,e1 / ,e2) `(,(subst/exp e1 x t) / ,(subst/exp e2 x t))]))

;; pred[x → e]
(define (subst pred x e)
  (match pred
    ['true 'true]
    ['false 'false]
    [`(,e1 = ,e2) `(,(subst/exp e1 x e) = ,(subst/exp e2 x e))]
    [`(,e1 < ,e2) `(,(subst/exp e1 x e) < ,(subst/exp e2 x e))]
    [`(,e1 ≤ ,e2) `(,(subst/exp e1 x e) ≤ ,(subst/exp e2 x e))]
    [`(,e1 > ,e2) `(,(subst/exp e1 x e) > ,(subst/exp e2 x e))]
    [`(,e1 ≥ ,e2) `(,(subst/exp e1 x e) ≥ ,(subst/exp e2 x e))]
    [`(,p1 ∧ ,p2) `(,(subst p1 x e) ∧ ,(subst p2 x e))]
    [`(,p1 ∨ ,p2) `(,(subst p1 x e) ∨ ,(subst p2 x e))]
    [`(,p1 ⇒ ,p2) `(,(subst p1 x e) ⇒ ,(subst p2 x e))]
    [`(¬ ,p) `(¬ (substs p x e))]))

(define (get-pred annotation)
  (match annotation
    [`(assume ,p) p]
    [`(invariant ,p) p]
    [`(assert ,p) p]))

;; Generate weakeat preconditions and side conditions
(define (wp com post sc)
  (match com
    [`(,x := ,e)
     (values (subst post x e) sc)]
    [`(seq ,c1 ,c2)
     (define-values (pre-c2 sc1) (wp c2 post sc))
     (wp c1 pre-c2 sc1)]
    [`(if ,cnd ,thn ,els)
     (define-values (pre-t sc1) (wp thn post sc))
     (define-values (pre-e sc2) (wp els post sc1))
     (values `((,cnd ⇒ ,pre-t) ∧ ((¬ ,cnd) ⇒ ,pre-e))
             sc2)]
    [`(while ,b ,i ,c)
     (define inv (get-pred i))
     (define-values (pre-c sc1) (wp c inv sc))
     (values inv
             (cons `((,inv ∧ ,b) ⇒ ,pre-c)
                   (cons `((,inv ∧ (¬ ,b)) ⇒ ,post)
                         sc1)))]
    [`(skip)
     (values post sc)]))

(define (vcg/helper pre com post)
  (define-values (pre* sc) (wp com post '()))
  (define query (cons `(,pre ⇒ ,pre*) sc))
  query)

(define (vcg prog)
  (vcg/helper (get-pred (first prog))
              (second prog)
              (get-pred (third prog))))

(define (to-smt/expr e)
  (match e
    [(? number? n) n]
    [(? symbol? v) v]
    [`(,e1 + ,e2) `(+ ,(to-smt/expr e1) ,(to-smt/expr e2))]
    [`(,e1 - ,e2) `(- ,(to-smt/expr e1) ,(to-smt/expr e2))]
    [`(,e1 * ,e2) `(* ,(to-smt/expr e1) ,(to-smt/expr e2))]
    [`(,e1 / ,e2) `(/ ,(to-smt/expr e1) ,(to-smt/expr e2))]))

(define (to-smt pred)
  (match pred
    ['true 'true]
    ['false 'false]
    [`(,e1 = ,e2) `(= ,(to-smt/expr e1) ,(to-smt/expr e2))]
    [`(,e1 < ,e2) `(< ,(to-smt/expr e1) < ,(to-smt/expr e2))]
    [`(,e1 ≤ ,e2) `(<= ,(to-smt/expr e1) ,(to-smt/expr e2))]
    [`(,e1 > ,e2) `(> ,(to-smt/expr e1) ,(to-smt/expr e2))]
    [`(,e1 ≥ ,e2) `(>= ,(to-smt/expr e1) ,(to-smt/expr e2))]
    [`(,p1 ∧ ,p2) `(and ,(to-smt p1) ,(to-smt p2))]
    [`(,p1 ∨ ,p2) `(or ,(to-smt p1) ,(to-smt p2))]
    [`(,p1 ⇒ ,p2) `(=> ,(to-smt p1) ,(to-smt p2))]
    [`(¬ ,p) `(not ,(to-smt p))]))

(define (variables/com c)
  (match c
    [`(,x := ,e) (set-union (set x) (variables/exp e))]
    [`(seq ,c1 ,c2)
     (set-union (variables/com c1) (variables/com c2))]
    [`(if ,cnd ,thn ,els)
     (set-union (variables/pred cnd)
                (variables/com thn)
                (variables/com els))]
    [`(while ,b ,i ,c)
     (set-union (variables/pred b)
                (variables/pred (get-pred i))
                (variables/com c))]
    [`(skip) (set)]))

(define (variables/exp e)
  (match e
    [(? number? n) (set)]
    [(? symbol? v) (set v)]
    [`(,e1 + ,e2) (set-union (variables/exp e1) (variables/exp e2))]
    [`(,e1 - ,e2) (set-union (variables/exp e1) (variables/exp e2))]
    [`(,e1 * ,e2) (set-union (variables/exp e1) (variables/exp e2))]
    [`(,e1 / ,e2) (set-union (variables/exp e1) (variables/exp e2))]))

(define (variables/pred p)
  (match p
    ['true (set)]
    ['false (set)]
    [`(,e1 = ,e2) (set-union (variables/exp e1) (variables/exp e2))]
    [`(,e1 < ,e2) (set-union (variables/exp e1) (variables/exp e2))]
    [`(,e1 ≤ ,e2) (set-union (variables/exp e1) (variables/exp e2))]
    [`(,e1 > ,e2) (set-union (variables/exp e1) (variables/exp e2))]
    [`(,e1 ≥ ,e2) (set-union (variables/exp e1) (variables/exp e2))]
    [`(,p1 ∧ ,p2) (set-union (variables/pred p1) (variables/pred p2))]
    [`(,p1 ∨ ,p2) (set-union (variables/pred p1) (variables/pred p2))]
    [`(,p1 ⇒ ,p2) (set-union (variables/pred p1) (variables/pred p2))]
    [`(¬ ,p) (variables/pred p)]))

(define (variables prog)
  (set-union
   (variables/pred (get-pred (first prog)))
   (variables/com (second prog))
   (variables/pred (get-pred (third prog)))))

(define (declare v ty) `(declare-const ,v ,ty))
(define (declare/int v) (declare v 'Int))

(define (assert-valid p)
  `((push)
    (assert (not ,(to-smt p)))
    (check-sat)
    (pop)))

(define (verify/smt prog)
  (define queries (vcg prog))
  (define vars (variables prog))
  (define declares (map declare/int (set->list vars)))
  (define asserts (map assert-valid queries))
  (append declares (foldl append '() asserts)))

(verify/smt example1)