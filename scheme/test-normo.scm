(load "mk/test-check.scm")
(load "provero.scm")

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

