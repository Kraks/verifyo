(load "dmatch.scm")

;; A simple interpreter for While
;; Author: Guannan Wei

#| The While language

<exp> ::= <number>
        | <symbol>
        | (<exp> + <exp>) | (<exp> - <exp>)
        | (<exp> * <exp>) | (<exp> / <exp>)

<bval> ::= true | false

<pred> ::= <bval>
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
  (lambda (σ x)
    (dmatch σ
      [() (error 'lookup "undefined variable ~a" x)]
      [((,y . ,v) . ,rest)
       (if (eq? x y) v
           (lookup rest x))])))

(define update
  (lambda (σ x v)
    (dmatch σ
      [() `((,x . ,v))]
      [((,y . ,w) . ,rest)
       (if (eq? x y)
           `((,x . ,v) . ,rest)
           `((,y . ,w) . ,(update rest x v)))])))

;; eval/exp : exp σ -> value
(define eval/exp
  (lambda (exp σ)
    (dmatch exp
      [,n (guard (number? n)) n]
      [,x (guard (symbol? x)) (lookup σ x)]
      [(,e1 + ,e2)
       (+ (eval/exp e1 σ)
          (eval/exp e2 σ))]
      [(,e1 - ,e2)
       (- (eval/exp e1 σ)
          (eval/exp e2 σ))]
      [(,e1 * ,e2)
       (* (eval/exp e1 σ)
          (eval/exp e2 σ))]
      [(,e1 / ,e2)
       (/ (eval/exp e1 σ)
          (eval/exp e2 σ))])))

; eval/pred : pred σ -> bval
(define eval/pred
  (lambda (pred σ)
    (dmatch pred
      [true #t]
      [false #f]
      [(,e1 = ,e2)
       (eq? (eval/exp e1 σ)
            (eval/exp e2 σ))]
      [(,e1 < ,e2)
       (< (eval/exp e1 σ)
          (eval/exp e2 σ))]
      [(,e1 ≤ ,e2)
       (<= (eval/exp e1 σ)
           (eval/exp e2 σ))]
      [(,e1 > ,e2)
       (> (eval/exp e1 σ)
          (eval/exp e2 σ))]
      [(,e1 ≥ ,e2)
       (>= (eval/exp e1 σ)
           (eval/exp e2 σ))]
      [(,p1 ∧ ,p2)
       (and (eval/pred p1 σ)
            (eval/pred p2 σ))]
      [(,p1 ∨ ,p2)
       (or (eval/pred p1 σ)
           (eval/pred p2 σ))]
      [(¬ ,p)
       (not (eval/pred p σ))]
      [(,p1 ⇒ ,p2)
       (or (not (eval/pred p1 σ))
           (eval/pred p2 σ))])))

;; exec/com : command state -> state
(define exec/com
  (lambda (com σ)
    (dmatch com
      [(,x := ,e)
       (update σ x (eval/exp e σ))]
      [(seq ,c1 ,c2)
       (exec/com c2 (exec/com c1 σ))]
      [(if ,c ,t ,e)
       (if (eval/pred c)
           (exec/com t σ)
           (exec/com e σ))]
      [(while ,cnd ,inv ,body)
       (let loop ([σ σ])
         (if (eval/pred cnd σ)
             (loop (exec/com body σ))
             σ))]
      [(skip) σ])))

(define interp
  (lambda (acom σ)
    (dmatch acom
      [(,P ,C ,Q) (exec/com C σ)])))

(define example1
  '([assume ((x = 8) ∧ (y = 16))]
    (while (x > 0)
           [invariant ((y = (2 * x)) ∧ (x ≥ 0))]
           (seq (x := (x - 1))
                (y := (y - 2))))
    [assert (y = 0)]))

(define fact
  '([assume]
    (seq (y := 1)
         (while (¬ (x = 1))
                [invariant]
                (seq (y := (y * x))
                     (x := (x - 1)))))
    [assert]))

;(interp example1 '[(x . 8) (y . 16)])
(interp fact '[(x . 5)])
