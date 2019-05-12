(load "mk/test-check.scm")
(load "provero.scm")

(test "(and (and true true) true) ≡ true"
      (run 1 (q) (normo '(and (and true true) true) 'true))
      '((_.0)))

(test "(> (+ 2 1) 2) ≡ true"
      (run 1 (q) (normo `(> (+ ,(int 2) ,(int 1)) ,(int 2)) 'true))
      '((_.0)))
