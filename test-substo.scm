(load "mk/test-check.scm")
(load "arithmetic.scm")
(load "proveo.scm")

(test "x[x ↦ 1] ≡ 1"
      (run 1 (q) (substo* 'x 'x 1 1))
      '((_.0)))

(test "x[y ↦ 1] ≡ x"
      (run 1 (q) (substo* 'x 'y 1 'x))
      '((_.0)))

(test "(∧ x y)[x ↦ 2] ≡ (∧ 2 y)"
      (run 1 (q) (substo* '(∧ x y) 'x 2 '(∧ 2 y)))
      '((_.0)))

(test "(∧ x y)[{?} ↦ 2] ≡ (∧ 2 y)"
      (run 1 (q) (substo* '(∧ x y) q 2 '(∧ 2 y)))
      '((x)))

(test "(int 3)[y ↦ z] ≡ (int 3)"
      (run 1 (q) (substo* (int 3) 'y 'z (int 3)))
      '((_.0)))

(test "(= z (int 3))[z ↦ (int 3)] ≡ (= (int 3) (int 3))"
      (run 1 (q) (substo* `(= z ,(int 3)) 'z (int 3) `(= ,(int 3) ,(int 3))))
      '((_.0)))

(test "(= z (int 3))[{?} ↦ (int 3)] ≡ (= (int 3) (int 3))"
      (run 1 (q) (substo* `(= z ,(int 3)) q (int 3) `(= ,(int 3) ,(int 3))))
      '((z)))

(test "(= z (int 3))[z ↦ {?}] ≡ (= (int 3) (int 3))"
      (run 1 (q) (substo* `(= z ,(int 3)) 'z q `(= ,(int 3) ,(int 3))))
      `((,(int 3))))

