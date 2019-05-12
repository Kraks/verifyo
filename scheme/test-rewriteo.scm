(load "mk/test-check.scm")
(load "provero.scm")

(test "x = x ≡ true"
      (run 1 (q) (rewriteo '(= x x) 'true))
      '((_.0)))

(test "x ≥ x ≡ true"
      (run 1 (q) (rewriteo '(>= x x) 'true))
      '((_.0)))

(test "(and true true) ≡ true"
      (run 1 (q) (rewriteo '(and true true) 'true))
      '((_.0)))

(test "(and false true) ≡ true"
      (run 1 (q) (rewriteo '(and false true) 'false))
      '((_.0)))

(test "(and false true) ≡ {q} "
      (run 1 (q) (rewriteo '(and false true) q))
      '((false)))

(test "(and (and true true) true) ≡ true"
      (run 1 (q) (rewriteo '(and (and true true) true) '(and true (and true true))))
      '((_.0)))

(test "(> (+ 2 1) 2) ≡ (> 2 1)"
      (run 1 (q) (rewriteo `(> (+ ,(int 2) ,(int 1)) ,(int 2))
                           `(> ,(int 2) ,(int 1))))
      '((_.0)))

;; compute 100 valid terms
;; (run 100 (q) (rewriteo q 'true))

