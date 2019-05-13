(load "proveo.scm")

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
