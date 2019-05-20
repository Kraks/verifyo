(load "../mk/mk.scm")
(load "../mk/test-check.scm")
(load "dpll.scm")
(load "parse-cnf.scm")

(define uf20-01 (parse-dimacs-file "uf20-91/uf20-01.cnf"))
(define uf20-02 (parse-dimacs-file "uf20-91/uf20-02.cnf"))
(define uf20-03 (parse-dimacs-file "uf20-91/uf20-03.cnf"))

(time (run 1 (m) (solveᵒ uf20-01 m))) ;; ~89s

(time (run 1 (m) (solveᵒ uf20-02 m))) ;; ~12s
;(time (run 1 (m) (f/⊨ m uf20-02)))   ;; ...

(time (run 1 (m) (solveᵒ uf20-03 m))) ;; ~512s
