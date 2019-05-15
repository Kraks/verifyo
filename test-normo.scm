(load "mk/test-check.scm")
(load "hoare.scm")

(test "x = x ≡ true"
      (run 1 (q) (rewriteo '(= x x) 'true))
      '((_.0)))

(test "x ≥ x ≡ true"
      (run 1 (q) (rewriteo '(>= x x) 'true))
      '((_.0)))

(test "(∧ true true) ≡ true"
      (run 1 (q) (rewriteo '(∧ true true) 'true))
      '((_.0)))

(test "(∧ false true) ≡ true"
      (run 1 (q) (rewriteo '(∧ false true) 'false))
      '((_.0)))

(test "(∧ false true) ≡ {q} "
      (run 1 (q) (rewriteo '(∧ false true) q))
      '((false)))

(test "(∧ (∧ true true) true) ≡ (∧ true (∧ true true))"
      (run 1 (q) (rewriteo '(∧ (∧ true true) true) '(∧ true (∧ true true))))
      '((_.0)))

(test "(> (+ 2 1) 2) ≡ (> 2 1)"
      (run 1 (q) (rewriteo `(> (+ ,(int 2) ,(int 1)) ,(int 2))
                           `(> ,(int 2) ,(int 1))))
      '((_.0)))

(test "(> (+ 2 1) 2) ≡ {q}"
      (run 1 (q) (rewriteo `(> (+ ,(int 2) ,(int 1)) ,(int 2)) q))
      '(((> (int (0 1)) (int (1))))))

(test "(> 2 1) ≡ {q}"
      (run 1 (q) (rewriteo `(> ,(int 2) ,(int 1)) q))
      '((true)))

(test "(∧ (>= 1 2) (¬ (> 1 2))) ≡ (= 1 2)"
      (run 1 (q) (rewriteo `(∧ (>= ,(int 1) ,(int 2)) (¬ (> ,(int 1) ,(int 2))))
                           `(= ,(int 1) ,(int 2))))
      '((_.0)))

(test "(= 1 2) ≡ false"
      (run 1 (q) (rewriteo `(= ,(int 1) ,(int 2)) 'false))
      '((_.0)))

;; compute 100 valid terms
;; (run 100 (q) (rewriteo q 'true))

(test "(∧ (∧ true true) true) ⇓ true"
      (run 1 (q) (⇓o '(∧ (∧ true true) true) 'true))
      '((_.0)))

(test "(> (+ 2 1) 2) ⇓ true"
      (run 1 (q) (⇓o `(> (+ ,(int 2) ,(int 1)) ,(int 2)) 'true))
      '((_.0)))

(test "(∧ (>= 1 2) (¬ (> 1 2))) ⇓ false"
      (run 1 (q) (⇓o `(∧ (>= ,(int 1) ,(int 2)) (¬ (> ,(int 1) ,(int 2))))
                     'false))
      '((_.0)))

(test "(∧ (>= 1 2) (¬ (> 1 2))) ⇓ {q}"
      (run 3 (q) (⇓o `(∧ (>= ,(int 1) ,(int 2)) (¬ (> ,(int 1) ,(int 2)))) q))
      '(((∧ (>= (int (1)) (int (0 1))) (¬ (> (int (1)) (int (0 1)))))) ;; reflexivity
        ((= (int (1)) (int (0 1))))                                     ;; one step
        (false)))                                                       ;; two steps, we may even ask answers more than 3.

