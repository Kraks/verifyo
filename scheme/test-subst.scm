(load "mk/test-check.scm")
(load "prover.scm")

(test "x[x ↦ 1] ≡ 1"
      (run 1 (q) (substo* 'x 'x 1 1))
      '((_.0)))

(test "x[y ↦ 1] ≡ x"
      (run 1 (q) (substo* 'x 'y 1 'x))
      '((_.0)))

(test "(and x y)[x ↦ 2] ≡ (and 2 y)"
      (run 1 (q) (substo* '(and x y) 'x 2 '(and 2 y)))
      '((_.0)))

(test "(and x y)[{?} ↦ 2] ≡ (and 2 y)"
      (run 1 (q) (substo* '(and x y) q 2 '(and 2 y)))
      '((x)))
