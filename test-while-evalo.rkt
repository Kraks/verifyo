#lang racket

(require rackunit)
(require minikanren)
(require minikanren/numbers)

(require "while-evalo.rkt")

;; lookupo tests

(check-equal?
 (run 1 (q)
      (lookupo '((a ↦ 1)) 'a q))
 '(1))
(check-equal?
 (run 1 (q)
      (lookupo '((b ↦ 2) (a ↦ 1)) 'a q))
 '(1))
(check-equal?
 (run 1 (q)
      (lookupo '((a ↦ 1)) 'b q))
 '())

;; updateo tests

(check-equal?
 (run 1 (q)
      (updateo '() 'a 1 q))
 '(((a ↦ 1))))
(check-equal?
 (run 1 (q)
      (updateo '((a ↦ 2)) 'a 2 q))
 '(((a ↦ 2))))
(check-equal?
 (run 1 (q)
      (updateo '((a ↦ 1)) 'b 2 q))
 '(((a ↦ 1) (b ↦ 2))))
(check-equal?
 (run 1 (q)
      (updateo '() 'a (int 2) q))
 '(((a ↦ (int (0 1))))))

;; eval/expo tests

(check-equal?
 (run 1 (q) (eval/expo (int 1) '() q))
 '((int (1)))
 )
(check-equal?
 (run 1 (q)
      (eval/expo 'a '((a ↦ 1)) q))
 '(1))
(check-equal?
 (run 1 (q)
      (eval/expo 'b '((a ↦ 1) (b ↦ 2)) q))
 '(2))
(check-equal?
 (run 1 (q)
      (eval/expo '(a + b) `((a ↦ ,(int 3)) (b ↦ ,(int 3))) q))
 '((int (0 1 1)))
 )
(check-equal?
 (run 1 (q)
      (eval/expo '(a + b) `((a ↦ ,q) (b ↦ ,(int 3))) (int 6)))
 '((int (1 1)))
 )
(check-equal?
 (run 1 (q)
      (eval/expo `(,q + b) `((b ↦ ,(int 3))) (int 6)))
 '((int (1 1)))
 )


;; eval/predo tests

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
(check-equal?
 (run 1 (q)
      (eval/predo `((,(int 1) + ,q) = ,(int 3)) '() #t))
 '((int (0 1))))
(check-equal?
 (run 1 (q)
      (eval/predo `((,(int 1) + ,(int 4)) = (,(int 2) + ,(int 3))) '() q))
 '(#t))
(check-equal?
 (run 1 (q)
      (fresh (a b)
             (eval/predo `((,(int 1) + ,a) = (,b + ,(int 3))) '() #t)
             (== `(,a . ,b) q)))
 '(((int (0 1)) int ())))
(check-equal?
 (run 1 (q)
      (eval/predo `((true ∧ false) ∨ (false ∨ (true ∧ true))) '() q))
 '(#t))

(check-equal?
 (run 1 (q)
      (eval/predo `((true ∧ false) ∨ (false ∨ (,q ∧ true))) '() #t))
 '(true))

;; execo test

(check-equal?
 (run 1 (q) (eval/expo (int 2) '() q))
 '((int (0 1))))
(check-equal?
 (run 1 (q)
      (fresh (v)
             (eval/expo (int 2) '() v)
             (updateo '() 'x v q)))
 '(((x ↦ (int (0 1))))))

(check-equal?
 (run 1 (q)
      (execo `(x := ,(int 2))
             '()
             q))
 '(((x ↦ (int (0 1))))))

;; (x + 1) * (x + 1) under (x ↦ 1)
(check-equal?
 (run 1 (q)
      (execo `(seq (x := (x + ,(int 1)))
                   (x := (x * x)))
             `((x ↦ ,(int 1)))
             q))
 '(((x ↦ (int (0 0 1))))))

;; (x + 1) * (x + 1) under (x ↦ 2)
(check-equal?
 (run 1 (q)
      (execo `(seq (x := (x + ,(int 1)))
                   (x := (x * x)))
             `((x ↦ ,(int 2)))
             q))
 '(((x ↦ (int (1 0 0 1))))))

;; Note: if we reorder the absento constraint,
;; we will obtain different q.

(check-equal?
 (run 1 (q)
      (absento 'int q)
      (execo `(seq (x := (x + ,(int 1)))
                   (x := ,q))
             `((x ↦ ,(int 2)))
             `((x ↦ ,(int 9)))))
 '((x + (x + x))))

(check-equal?
 (run 1 (q)
      (execo `(seq (x := (x + ,(int 1)))
                   (x := ,q))
             `((x ↦ ,(int 2)))
             `((x ↦ ,(int 9))))
      (absento 'int q))
 '((x * x)))

;; We can also synthesize with two input/output examples.
(check-equal?
 (run 1 (q)
      (execo `(seq (x := (x + ,(int 1)))
                   (x := ,q))
             `((x ↦ ,(int 2)))
             `((x ↦ ,(int 9))))
      (execo `(seq (x := (x + ,(int 1)))
                   (x := ,q))
             `((x ↦ ,(int 3)))
             `((x ↦ ,(int 16))))
      (absento 'int q))
 '((x * x)))

;; TODO: now get into trouble!
;; Random ideas: improve the relation arithmetic system
;;               SMT solver to discharge the arithmetic constraints
(run 1 (q)
      (execo `(seq (x := ,q)
                   (x := (x * x)))
             `((x ↦ ,(int 2)))
             `((x ↦ ,(int 9))))
      #|
      (execo `(seq (x := ,q)
                   (x := (x * x)))
             `((x ↦ ,(int 3)))
             `((x ↦ ,(int 16))))
      (execo `(seq (x := ,q)
                   (x := (x * x)))
             `((x ↦ ,(int 1)))
             `((x ↦ ,(int 4))))
      |#
      (absento 'int q))