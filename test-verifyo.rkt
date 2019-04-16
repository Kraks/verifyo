#lang racket

(require rackunit)
(require minikanren)
(require minikanren/numbers)

(require "verifyo.rkt")
(require "while.rkt")
(require "while-evalo.rkt")
(require "smt.rkt")

(check-equal?
 (run 1 (q) (substo/exp (int 1) 'a 'b q)) (list (int 1)))

(check-equal?
 (run 1 (q) (substo/exp 'c 'a 'b q)) '(c))

(check-equal?
 (run 1 (q) (substo/exp 'a 'a 'b q)) '(b))

(check-equal?
 (run 1 (q) (substo/exp '(a + b) 'a 'c q)) '((c + b)))

(check-equal?
 (run 1 (q) (substo/exp q 'a 'c '(c + b))) '((a + b)))

(check-equal?
 (run 1 (q)
      (substo `(x = ,(int 5)) 'x (int 5) q))
 '(((int (1 0 1)) = (int (1 0 1)))))

(check-equal?
 (run 1 (q) (substo '((a + b) = (b + c)) 'b (int 1) q))
 `(((a + ,(int 1)) = (,(int 1) + c))))

(check-equal?
 (run 1 (q) (substo q 'b 'c `((a + ,(int 1)) = (d + c))))
 `(((a + ,(int 1)) = (d + b))))

(check-equal?
 (run 1 (q) (substo q 'b 'c `((a + ,(int 1)) = (d + c))))
 `(((a + ,(int 1)) = (d + b))))

(check-equal?
 (run 1 (q) (substo q 'b 'c '((a + c) = (d + c))))
 '(((a + b) = (d + b))))

;; WP is 3 = 3, SC is unbounded
(check-equal?
 (run 1 (wp sc) (wpo `(x := ,(int 3)) `(x = ,(int 3)) wp sc))
 '((((int (1 1)) = (int (1 1))) _.0)))

(check-equal?
 (run 1 (wp sc)
      (wpo `(seq (x := ,(int 2))
                 (y := (x + ,(int 1))))
           `(y = ,(int 3))
           wp
           sc))
 '(((((int (0 1)) + (int (1))) = (int (1 1))) _.0)))

(check-equal?
 (run 1 (wp sc)
      (wpo `(seq (x := (x + ,(int 1)))
                 (y := (x + ,(int 1))))
           `(y = ,(int 5))
           wp
           sc))
 '(((((x + (int (1))) + (int (1))) = (int (1 0 1))) _.0)))

(check-equal?
 (run 1 (wp sc)
      (wpo `(seq (z := (x + ,(int 1)))
                 (seq (x := (x + ,(int 1)))
                      (y := (x + ,(int 1)))))
           `(y = ,(int 5))
           wp
           sc))
 '(((((x + (int (1))) + (int (1))) = (int (1 0 1))) _.0)))

(check-equal?
 (run 1 (wp sc)
      (wpo `(if (a = b) (a := ,(int 3)) (b := ,(int 4)))
           `((a = ,(int 3)) ∨ (b = ,(int 4)))
           wp sc))
 '(((((a = b) ⇒ (((int (1 1)) = (int (1 1))) ∨ (b = (int (0 0 1)))))
     ∧
     ((¬ (a = b)) ⇒ ((a = (int (1 1))) ∨ ((int (0 0 1)) = (int (0 0 1))))))
    _.0)))

(check-equal?
 (run 1 (wp sc)
      (wpo `(while (x > ,(int 0))
                   {invariant ((y = (,(int 2) * x)) ∧ (x ≥ ,(int 0)))}
                   (seq (x := (x - ,(int 1)))
                        (y := (y - ,(int 2)))))
           `(y = ,(int 0))
           wp
           sc))
 '((((y = ((int (0 1)) * x)) ∧ (x ≥ (int ())))
    (((((y = ((int (0 1)) * x)) ∧ (x ≥ (int ()))) ∧ (x > (int ())))
      ⇒
      (((y - (int (0 1))) = ((int (0 1)) * (x - (int (1))))) ∧ ((x - (int (1))) ≥ (int ()))))
     ((((y = ((int (0 1)) * x)) ∧ (x ≥ (int ()))) ∧ (¬ (x > (int ())))) ⇒ (y = (int ())))))))