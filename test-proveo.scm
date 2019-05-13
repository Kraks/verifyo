(load "proveo.scm")

(test "[true] skip [true]"
      (run 1 (q) (proveo 'true '(skip) 'true))
      '((_.0)))

(test "[true] {q} [true]"
      (run 1 (q) (proveo 'true q 'true))
      '(((skip))))
