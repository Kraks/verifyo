(load "mk/test-check.scm")
(load "provero.scm")

(test "(and (and true true) true) ≡ true"
      (run 1 (q) (normo '(and (and true true) true) 'true))
      '((_.0)))
