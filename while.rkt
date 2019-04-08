#lang racket

;; A simple interpreter for While
;; Author: Guannan Wei

#| The While language

<exp> ::= <number>
        | <symbol>
        | (<exp> + <exp>) | (<exp> - <exp>)
        | (<exp> * <exp>) | (<exp> / <exp>)

<pred> ::= true | false
         | (<exp> = <exp>)
         | (<exp> ≤ <exp>) | (<exp> < <exp>)
         | (<exp> ≥ <exp>) | (<exp> > <exp>)
         | (<pred> ∧ <pred>)  | (<pred> ∨ <pred>)
         | (¬ <pred>) | (<pred> ⇒ <pred>)

<annotation> ::= (assume <pred>)
               | (assert <pred>)
               | (invariant <pred>)

<command> ::= (<symbol> := <exp>)
            | (seq <command> <command>)
            | (if <pred> <command> <command>)
            | (while <pred> <annotation> <command>)
            | (skip)
|#

(define lookup
  (λ (σ x)
    (match σ
      ['() (error 'lookup "undefined variable ~a" x)]
      [`((,y . ,v) . ,rest)
       (if (eq? x y) v
           (lookup rest x))])))

(define update
  (λ (σ x v)
    (match σ
      ['() `((,x . ,v))]
      [`((,y . ,w) . ,rest)
       (if (eq? x y)
           `((,x . ,v) . ,rest)
           `((,y . ,w) . ,(update rest x v)))])))

;; eval/exp : exp σ -> value
(define eval/exp
  (λ (exp σ)
    (match exp
      [(? number? n) n]
      [(? symbol? x) (lookup σ x)]
      [`(,e1 + ,e2)
       (+ (eval/exp e1 σ)
          (eval/exp e2 σ))]
      [`(,e1 - ,e2)
       (- (eval/exp e1 σ)
          (eval/exp e2 σ))]
      [`(,e1 * ,e2)
       (* (eval/exp e1 σ)
          (eval/exp e2 σ))]
      [`(,e1 / ,e2)
       (/ (eval/exp e1 σ)
          (eval/exp e2 σ))])))

(define eval/pred
  (λ (pred σ)
    (match pred
      ['true #t]
      ['false #f]
      [`(,e1 = ,e2)
       (eq? (eval/exp e1 σ)
            (eval/exp e2 σ))]
      [`(,e1 < ,e2)
       (< (eval/exp e1 σ)
          (eval/exp e2 σ))]
      [`(,e1 ≤ ,e2)
       (<= (eval/exp e1 σ)
           (eval/exp e2 σ))]
      [`(,e1 > ,e2)
       (> (eval/exp e1 σ)
          (eval/exp e2 σ))]
      [`(,e1 ≥ ,e2)
       (>= (eval/exp e1 σ)
           (eval/exp e2 σ))]
      [`(,p1 ∧ ,p2)
       (and (eval/pred p1 σ)
            (eval/pred p2 σ))]
      [`(,p1 ∨ ,p2)
       (or (eval/pred p1 σ)
           (eval/pred p2 σ))]
      [`(¬ ,p)
       (not (eval/pred p σ))]
      [`(,p1 ⇒ ,p2)
       (or (not (eval/pred p1 σ))
           (eval/pred p2 σ))])))
  
;; exec/com : command state -> state
(define exec/com
  (λ (com σ)
    (match com
      [`(,x := ,e)
       (update σ x (eval/exp e σ))]
      [`(seq ,c1 ,c2)
       (exec/com c2 (exec/com c1 σ))]
      [`(if ,c ,t ,e)
       (if (eval/pred c)
           (exec/com t σ)
           (exec/com e σ))]
      [`(while ,cnd ,inv ,body)
       (let loop ([σ σ])
         (if (eval/pred cnd σ)
             (loop (exec/com body σ))
             σ))]
      [`(skip) σ])))

(define interp
  (λ (acom σ)
    (match acom
      [`(,P ,C ,Q) (exec/com C σ)])))

(define example1
  '({assume ((x = 8) ∧ (y = 16))}
    (while (x > 0)
           {invariant ((y = (2 * x)) ∧ (x ≥ 0))}
           (seq (x := (x - 1))
                (y := (y - 2))))
    {assert (y = 0)}))

(interp example1 '((x . 8) (y . 16)))