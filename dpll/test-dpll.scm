(load "../mk/mk.scm")
(load "../mk/test-check.scm")
(load "dpll.scm")

(test "(∨ [(== q 1)] [(== q 2)]"
      (run* (q) (∨ [(== q 1)] [(== q 2)]))
      '((1) (2)))

(test "a is a literal"
      (run 1 (q) (litᵒ 'a))
      '((_.0)))

(test "1 is not a literal"
      (run 1 (q) (litᵒ 1))
      '())

(test "() is not a literal"
      (run 1 (q) (litᵒ '()))
      '())

(test "(a) is not a literal"
      (run 1 (q) (litᵒ '(a)))
      '())

(test "(¬ a) is a literal"
      (run 1 (q) (litᵒ '(¬ a)))
      '((_.0)))

(test "(¬ 1) is not a literal"
      (run 1 (q) (litᵒ '(¬ 1)))
      '())

(test "(¬ (a)) is not a literal"
      (run 1 (q) (litᵒ '(¬ (a))))
      '())

(test "(a b c) is a clause"
      (run 1 (q) (clauseᵒ '(a b c)))
      '((_.0)))

(test "(a b c (¬ d)) is a clause"
      (run 1 (q) (clauseᵒ '(a b c (¬ d))))
      '((_.0)))

(test "(a b (c)) is not a clause"
      (run 1 (q) (clauseᵒ '(a b (c))))
      '())

(test "((a b c) (d e f)) is a CNF formula"
      (run 1 (q) (formulaᵒ '((a b c) (d e f))))
      '((_.0)))

(test "((a b c) (d e f) ((¬ a))) is a CNF formula"
      (run 1 (q) (formulaᵒ '((a b c) (d e f) ((¬ a)))))
      '((_.0)))

(test "((a b c) (d e f) ((¬ a)) a) is not a CNF formula"
      (run 1 (q) (formulaᵒ '((a b c) (d e f) ((¬ a)) a)))
      '())

;======================================================

(test "'(a b c) ∩ '(a b c) ≡ '(a b c)"
      (run 1 (q) (∩ '(a b c) '(a b c) '(a b c)))
      '((_.0)))

(test "'(a) ∩ '(a b c) ≡ '(a)"
      (run 1 (q) (∩ '(a) '(a b c) '(a)))
      '((_.0)))

(test "'(a) ∩ '() ≡ '()"
      (run 1 (q) (∩ '(a) '() '()))
      '((_.0)))

(test "'() ∩ '(a) ≡ '()"
      (run 1 (q) (∩ '() '(a) '()))
      '((_.0)))

(test "'(a b) ∩ '(a b c) ≡ '(a b)"
      (run 1 (q) (∩ '(a b) '(a b c) '(a b)))
      '((_.0)))

(test "'(a b) ∩ '(a b c) ≡ {q}"
      (run* (q) (∩'(a b) '(a b c) q))
      '(((a b))))

;======================================================

(test "(negᵒ p (¬ p))"
      (run 1 (q) (negᵒ 'p '(¬ p)))
      '((_.0)))

(test "reverse negᵒ identity"
      (run 1 (q1 q2)
           (negᵒ 'p q1)
           (negᵒ q1 q2)
           (== q2 'p))
      '((((¬ p) p))))

;======================================================

(test "(splitᵒ '(a b c) '() 'a '(b c)"
      (run 1 (q) (splitᵒ '(a b c) '() 'a '(b c)))
      '((_.0)))

(test "(splitᵒ '(a b c) '(a) 'b '(c)"
      (run 1 (q) (splitᵒ '(a b c) '(a) 'b '(c)))
      '((_.0)))

(test "(splitᵒ '(a b c d e) '(a b c d) 'e '()"
      (run 1 (q) (splitᵒ '(a b c d e) '(a b c d) 'e '()))
      '((_.0)))

(test "(splitᵒ '(a b c d e) '(a b c d) 'e '()"
      (run 1 (q) (splitᵒ '(a b c d e) '(a b c d) 'g q))
      '())

;======================================================

(test "(rem-dupᵒ '(a b c a) '(b c a))"
      (run 1 (q) (rem-dupᵒ '(a b c a) '(b c a)))
      '((_.0)))

(test "(rem-dupᵒ '(a b c b a) '(c b a))"
      (run 1 (q) (rem-dupᵒ '(a b c b a) '(c b a)))
      '((_.0)))

(test "(rem-dupᵒ '() '())"
      (run 1 (q) (rem-dupᵒ '() '()))
      '((_.0)))

(test "(rem-dupᵒ '(a a a) '(a))"
      (run 1 (q) (rem-dupᵒ '(a a a) '(a)))
      '((_.0)))

(test "(flattenᵒ '((a b c) (d e f)) '(a b c d e f))"
      (run 1 (q) (flattenᵒ '((a b c) (d e f)) '(a b c d e f)))
      '((_.0)))

(test "(flattenᵒ '((a b c) ()) '(a b c))"
      (run 1 (q) (flattenᵒ '((a b c) ()) '(a b c)))
      '((_.0)))

(test "(flattenᵒ '(((¬ a) b c) ((¬ d))) '((¬ a) b c (¬ d)))"
      (run 1 (q) (flattenᵒ '(((¬ a) b c) ((¬ d))) '((¬ a) b c (¬ d))))
      '((_.0)))

(test "(removeᵒ '() 'a '())"
      (run 1 (q) (removeᵒ '() 'a '()))
      '((_.0)))

(test "(removeᵒ '(a) 'a '())"
      (run 1 (q) (removeᵒ '(a) 'a '()))
      '((_.0)))

(test "(removeᵒ '(a a a) 'a '())"
      (run 1 (q) (removeᵒ '(a a a) 'a '()))
      '((_.0)))

(test "(removeᵒ '(a b a c a) 'a '(b c))"
      (run 1 (q) (removeᵒ '(a b a c a) 'a '(b c)))
      '((_.0)))

(test "(removeᵒ '(b c) 'a '(b c))"
      (run 1 (q) (removeᵒ '(b c) 'a '(b c)))
      '((_.0)))

(test "(⊆ '(a b c) '(c b a))"
      (run 1 (q) (⊆ '(a b c) '(c b a)))
      '((_.0)))

(test "(⊆ '(a b c) '(c b))"
      (run 1 (q) (⊆ '(a b c) '(c b)))
      '())

;======================================================

(test "(c/unitpropᵒ '(a b c) 'b #t)"
      (run 1 (q) (c/unitpropᵒ '(a b c) 'b #t))
      '((_.0)))

(test "(c/unitpropᵒ '(b) '(¬ b) '())"
      (run 1 (q) (c/unitpropᵒ '(b) '(¬ b) '()))
      '((_.0)))

(test "(c/unitpropᵒ '(a (¬ b) c) '(¬ b) #t)"
      (run 1 (q) (c/unitpropᵒ '(a (¬ b) c) '(¬ b) #t))
      '((_.0)))

(test "(c/unitpropᵒ '(a b c) 'd '(a b c))"
      (run 1 (q) (c/unitpropᵒ '(a b c) 'd '(a b c)))
      '((_.0)))

(test "(c/unitpropᵒ '(a b c b) 'b #t)"
      (run 1 (q) (c/unitpropᵒ '(a b c b) 'b #t))
      '((_.0)))

(test "(c/unitpropᵒ '(a b c (¬ b) b) 'b #t)"
      (run 1 (q) (c/unitpropᵒ '(a b c (¬ b) b) 'b #t))
      '((_.0)))

(test "(c/unitpropᵒ '(a c (¬ b)) 'b '(a c))"
      (run 1 (q) (c/unitpropᵒ '(a c (¬ b)) 'b '(a c)))
      '((_.0)))

(test "(c/unitpropᵒ '(a c (¬ b) b) 'b '(a c))"
      (run 1 (q) (c/unitpropᵒ '(a c (¬ b) b) 'b '(a c)))
      '())

(test "(mapfilterᵒ '(a b) (λ (_ r) (== r #t)) (λ (x x^) (== x^ `(,x))) '((a) (b)))"
      (run 1 (q)
           (mapfilterᵒ '(a b)
                       (lambda (_ r) (== r #t))
                       (lambda (x x^) (== x^ `(,x)))
                       '((a) (b))))
      '((_.0)))

(test "(mapfilterᵒ '(a b) (λ (_ r) (== r #t)) (λ (x x^) (== x^ `(,x))) {q})"
      (run 1 (q)
           (mapfilterᵒ '(a b)
                       (lambda (_ r) (== r #t))
                       (lambda (x x^) (== x^ `(,x)))
                       q))
      '((((a) (b)))))

(test "(mapfilterᵒ {q} (λ (_ r) (== r #t)) (λ (x x^) (== x^ `(,x))) '((a) (b)))"
      (run 1 (q)
           (mapfilterᵒ q
                       (lambda (_ r) (== r #t))
                       (lambda (x x^) (== x^ `(,x)))
                       '((a) (b))))
      '(((a b))))

(test "(unitpropᵒ '((a b) (c d)) 'b '((c d)))"
      (run 1 (q)
           (unitpropᵒ '((a b) (c d)) 'b q))
      '((((c d)))))

(test "(unitpropᵒ '((a b) (b c d)) 'b '())"
      (run 1 (q)
           (unitpropᵒ '((a b) (b c d)) 'b q))
      '((())))

(test "(unitpropᵒ '() 'b '())"
      (run 1 (q)
           (unitpropᵒ '() 'b q))
      '((())))

(test "(unitpropᵒ '((a b) (c d) (d (¬ b))) 'b '((c d) (d)))"
      (run 1 (q)
           (unitpropᵒ '((a b) (c d) (d (¬ b))) 'b q))
      '((((c d) (d)))))

(test "(step/unitᵒ '((a b) (c)) '() '(c) {f} {d} {m})"
      (run 1 (f d m) (step/unitᵒ '((a b) (c)) '() '(c) f d m))
      ; an ill-state, an assignment is made, but not boolean propagated
      '())

(test "(step/unitᵒ '((a b) (c)) '() '() {f} {d} {m})"
      (run 1 (f d m)
           (step/unitᵒ '((a b) (c)) '() '() f d m))
      '(((((a b)) () (c)))))

(test "(step/unitᵒ '((a b) (c)) '() '() {f} {d} {m})"
      (run* (f d m)
           (step/unitᵒ '((a b) (c)) '() '() f d m))
      '(((((a b)) () (c)))))

(test "(step/unitᵒ '((a b) (c) (d) (e f)) '() '() {f} {d} {m})"
      (run* (f d m)
            (step/unitᵒ '((a b) (c) (d) (e f)) '() '() f d m))
      '(((((a b) (d) (e f)) () (c))) ((((a b) (c) (e f)) () (d)))))

(test "(∄/unit '((a b) (c d)))"
      (run 1 (q) (∄/unit '((a b) (c d))))
      '((_.0)))

(test "(∄/unit '())"
      (run 1 (q) (∄/unit '()))
      '((_.0)))

(test "(∄/unit '((a)))"
      (run 1 (q) (∄/unit '((a))))
      '())

(test "(∄/unit '((a) (b)))"
      (run 1 (q) (∄/unit '((a) (b))))
      '())

(test "(∄/unit '((a) (b) (d c)))"
      (run 1 (q) (∄/unit '((a) (b) (d c))))
      '())

(test "(∄/unit '((a e) (b) (d c)))"
      (run 1 (q) (∄/unit '((a e) (b) (d c))))
      '())

(test "(step/decideᵒ '((a b c) (a e)) '() '() {f} {d} {m})"
      (run 1 (f d m)
           (step/decideᵒ '((a b c) (a e)) '() '() f d m))
      '(((()                    ; f is reduced to empty (ie true)
          ((a ((a b c) (a e)))) ; the decision stack contains a ↦ true, and the formula before decision
          (a)                   ; the (partial) model
          ))))

(test "(step/decideᵒ '((a b c) (f e)) '() '() {f} {d} {m})"
      (run 1 (f d m)
           (step/decideᵒ '((a b c) (f e)) '() '() f d m))
      '(((((f e)) ((a ((a b c) (f e)))) (a)))))

(test "(step/decideᵒ '((f e)) '((a ((a b c) (f e)))) '(a) {f} {d} {m})"
      (run 1 (f d m)
           (step/decideᵒ '((f e)) '((a ((a b c) (f e)))) '(a) f d m))
      '(((() ((f ((f e))) (a ((a b c) (f e)))) (f a)))))

(test "(step/decideᵒ '((f e) ((¬ f) g)) '((a ((a b c) (f e)))) '(a) {f} {d} {m})"
      (run 1 (f d m)
           (step/decideᵒ '((f e) ((¬ f) g)) '((a ((a b c) (f e)))) '(a) f d m))
      '(((((g)) ((f ((f e) ((¬ f) g))) (a ((a b c) (f e)))) (f a)))))

(test "(substᵒ '(a b c) 'a '(¬ a) '((¬ a) b c))"
      (run 1 (q) (substᵒ '(a b c) 'a '(¬ a) '((¬ a) b c)))
      '((_.0)))

(test "(substᵒ '() 'a '(¬ a) '((¬ a) b c))"
      (run 1 (q) (substᵒ '() 'a '(¬ a) '()))
      '((_.0)))

(test "(substᵒ '(b c (¬ a)) '(¬ a) 'a '(b c a))"
      (run 1 (q) (substᵒ '(b c (¬ a)) '(¬ a) 'a q))
      '(((b c a))))

(test "(step/unitᵒ '((a b) ((¬ a) (¬ b)) (b)) '() '() {f} {d} {m})"
      (run 1 (f d m) (step/unitᵒ '((a b) ((¬ a) (¬ b)) (b)) '() '() f d m))
      '((((((¬ a))) () (b)))))

(test "(step/unitᵒ '(((¬ a))) '() '(b) f d m)"
      (run 1 (f d m) (step/unitᵒ '(((¬ a))) '() '(b) f d m))
      '(((() () ((¬ a) b)))))

;; can not decide, since there is a unit clause
(test "(step/decideᵒ '(((¬ a))) '() '(b) f d m)"
      (run 1 (f d m) (step/decideᵒ '(((¬ a))) '() '(b) f d m))
      '())

;======================================================

(test "(a b) ⊨ (a b)"
      (run 1 (q) (c/⊨ '(a b) '(a b)))
      '((_.0)))

(test "(a) ⊨ (a b)"
      (run 1 (q) (c/⊨ '(a) '(a b)))
      '((_.0)))

(test "(a (¬ b)) ⊨ (a b)"
      (run 1 (q) (c/⊨ '(a (¬ b)) '(a b)))
      '((_.0)))

(test "((¬ b)) ⊨ (a (¬ b))"
      (run 1 (q) (c/⊨ '((¬ b)) '(a (¬ b))))
      '((_.0)))

(test "(a ⊨ (a (¬ b))"
      (run 1 (q) (c/⊨ '(a) '(a (¬ b))))
      '((_.0)))

(test "(b) ⊨ (a (¬ b)) ;; undefined, since a is unspecified"
      (run 1 (q) (c/⊨ '(b) '(a (¬ b))))
      '())

(test "((¬ a)) ⊨ (a (¬ b)) ;; undefined, since b is unspecified"
      (run 1 (q) (c/⊨ '((¬ a)) '(a (¬ b))))
      '())

;======================================================

(test "((¬ a) b) ⊭ (a (¬ b))"
      (run 1 (q) (c/⊭ '((¬ a) b) '(a (¬ b))))
      '((_.0)))

(test "(b) ⊭ (a (¬ b)) ;; undefined"
      (run 1 (q) (c/⊭ '(b) '(a (¬ b))))
      '())

(test "{q} ⊭ (a (¬ b))"
      (run 1 (q) (c/⊭ q '(a (¬ b))))
      '((((¬ a) b . _.0))))

;======================================================

(test "(a b) ⊨ ((a) (b))"
      (run 1 (q) (f/⊨ '(a b) '((a) (b))))
      '((_.0)))

(test "(a) ⊨ ((a) (b)) ;; undefined"
      (run 1 (q) (f/⊨ '(a) '((a) (b))))
      '())

(test "{q} ⊨ ((a) (b c e) ((¬ b)) ((¬ c)))"
      (run 1 (q)
           (consistentᵒ q)
           (f/⊨ q '((a) (b c e) ((¬ b)) ((¬ c)))))
      '(((a (¬ b) (¬ c) e))))

;======================================================

(test "((¬ a)) ⊭ ((a) (b))"
      (run 1 (q) (f/⊭ '((¬ a)) '((a) (b))))
      '((_.0)))

;======================================================

(test "(finalo '(a b c) '((a) (b) (c a) (b c)))"
      (run 1 (q) (finalo '(a b c) '((a) (b) (c a) (b c))))
      '((_.0)))

(test "(finalo '((¬ a) (¬ b) c) '((a) (b) (c a) (b c)))"
      (run 1 (q) (finalo '((¬ a) (¬ b) c) '((a) (b) (c a) (b c))))
      '((_.0)))

(test "solve '((a b))"
      (run 1 (d m) (dpllo '() '() '((a b)) d m))
      '(((_.0 (b a)))))

(test "solve '((a b) ((¬ b)))"
      (run 1 (d m) (dpllo '() '() '((a b) ((¬ b))) d m))
      '(((_.0 ((¬ b) a)))))


#|
(test "solve '((a b) (c d) ((¬ c)) ((¬ b)))"
(run 1 (d m) (dpllo '() '() '((a b) (c d) ((¬ c)) ((¬ b))) d m))
'())

(test "disprove '((a) ((¬ a)))"
      (run 1 (d m) (dpllo '() '() '((a) ((¬ a))) d 'fail))
      '())

(test "disprove '((a b) ((¬ a)) ((¬ b)))"
      (run 1 (d m) (dpllo '() '() '((a b) ((¬ a)) ((¬ b))) d 'fail))
      '())
|#

(define f1
  '((a b c) (d e f) (g h i)
    ((¬ a) (¬ c))
    (b)
    ((¬ d))
    ((¬ f))
    (e)
    (g)
    (h)
    ((¬ i))))

;(time (run 1 (d m) (dpllo '() '() f1 d m)))
;(time (run 1 (m) (f/⊨ m f1)))


