(load "hoare.scm")

(test "[true] (skip) [true]"
      (run 1 (q) (proveo 'true '(skip) 'true))
      '((_.0)))

(test "[true] {q} [true]"
      (run 1 (q) (proveo 'true q 'true))
      '(((skip))))

(test "[2 = 2] (x := 2) [x = 2]"
      (run 1 (q) (proveo `(= ,(int 2) ,(int 2)) `(x := ,(int 2)) `(= x ,(int 2))))
      '((_.0)))

(test "[true] (x := 2) [x = 2]"
      (run 1 (q) (proveo 'true `(x := ,(int 2)) `(= x ,(int 2))))
      '((_.0)))

(test "[true] {q} [x = 2]"
      (run 1 (q) (proveo 'true q `(= x ,(int 2))))
      `(((x := ,(int 2)))))

(test "[(+ x 1) = 2] (x := (+ x 1)) [x = 2]"
      (run 1 (q) (proveo `(= (+ x ,(int 1)) ,(int 2))
                         `(x := (+ x ,(int 1)))
                         `(= x ,(int 2))))
      '((_.0)))

(test "[x = 1] (x := (+ x 1)) [x = 2]"
      (run 1 (q) (proveo `(= x ,(int 1))
                         `(x := (+ x ,(int 1)))
                         `(= x ,(int 2))))
      '((_.0)))

(test "[x = 1] {q} [x = 2]"
      (run 1 (q) (proveo `(= x ,(int 1))
                         q
                         `(= x ,(int 2))))
      '(((x := (+ x (int (1)))))))

(test "[x = 1] (seq (x := (+ x 1)) (x := (+ x 1))) [x = 3]"
      (run 1 (q) (proveo `(= x ,(int 1))
                         `(seq (x := (+ x ,(int 1)))
                               (x := (+ x ,(int 1))))
                         `(= x ,(int 3))))
      '((_.0)))

;; FIXME: prove this is invalid.
;;        In pure relational programming, the way to disprove something is 
;;        by failing to unifiy. But for `seq`, it tries to come up with an `r`
;;        that can be unified with other terms, however there are infinite `r` 
;;        can be exist. Need some way to cut the intermediate predicate of `seq`.
(test "[x = 1] (seq (x := (+ x 1)) (x := (+ x 1))) [x = 100]"
      (run 1 (q) (proveo `(= x ,(int 1))
                         `(seq (x := (+ x ,(int 1)))
                               (x := (+ x ,(int 1))))
                         `(= x ,(int 100))))
      '())

;; FIXME
#|
(test "[x = 1] (seq {p} {q}) [x = 3]"
      (run 1 (p q) (proveo `(= x ,(int 1))
                           `(seq ,p ,q)
                           `(= x ,(int 3))))
      '((_.0)))


(test "[x = 1] (seq (x := (+ {q} 1)) (x := (+ x 1))) [x = 3]"
      (run 1 (q) (proveo `(= x ,(int 1))
                         `(seq (x := (+ ,q ,(int 1)))
                               (x := (+ x ,(int 1))))
                         `(= x ,(int 3))))
      '((_.0)))
|#
