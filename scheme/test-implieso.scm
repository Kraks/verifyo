(load "mk/test-check.scm")
(load "prover.scm")

(test "true => true"
      (run 1 (q) (implieso* 'true 'true))
      '((_.0)))

(test "true => false"
      (run 1 (q) (implieso* 'true 'false))
      '())

(test "false => true"
      (run 1 (q) (implieso* 'false 'true))
      '((_.0)))

(test "false => false"
      (run 1 (q) (implieso* 'false 'false))
      '((_.0)))

(test "(<= x 5) => (<= x 5)"
      (run 1 (q) (implieso* `(<= x ,(int 5)) `(<= x ,(int 10))))
      '((_.0)))

(test "(<= x 5) => (<= x 10)"
      (run 1 (q) (implieso* `(<= x ,(int 5)) `(<= x ,(int 10))))
      '((_.0)))

(test "(<= x 11) =/=> (<= x 10)"
      (run 1 (q) (implieso* `(<= x ,(int 11)) `(<= x ,(int 10))))
      '())

(test "(> x 1) => (> x 0)"
      (run 1 (q) (implieso* `(> x ,(int 1)) `(> x ,(int 0))))
      '((_.0)))

(test "(> x 0) =/=> (> x 1)"
      (run 1 (q) (implieso* `(> x ,(int 0)) `(> x ,(int 1))))
      '())

(test "q => (> x 1)"
      (run 1 (q) (implieso* q `(> x ,(int 1))))
      '(((> x (int (1))))))

(test "q => (> x 1), q =/= (> x 1)"
      (run 1 (q)
           (implieso* q `(> x ,(int 1)))
           (=/= q `(> x ,(int 1))))
      '((false)))

(test "q => (> x 1), q =/= (> x 1), q =/= false"
      (run 1 (q)
           (implieso* q `(> x ,(int 1)))
           (=/= q `(> x ,(int 1)))
           (=/= q 'false))
      '(((> x (int (_.0 _.1 . _.2))))))
