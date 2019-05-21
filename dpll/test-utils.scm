(load "../mk/mk.scm")
(load "../mk/test-check.scm")
(load "utils.scm")

(test "(∨ [(== q 1)] [(== q 2)]"
      (run* (q) (∨ [(== q 1)] [(== q 2)]))
      '((1) (2)))

(test "match list '(1 2 3)"
      (run 1 (q) (listᵒ ((x . xs) ← '(1 2 3))
                        (== x '1)
                        (== xs '(2 3))))
      '((_.0)))

(test "match list '(1 2 3)"
      (run 1 (q) (listᵒ ((x . xs) ← '(1 2 3))
                        (== x q)
                        (== xs '(2 3))))
      '((1)))

(test "match list '(1 2 3)"
      (run 1 (q) (listᵒ ((x . xs) ← '(1 2 3))
                        (== x '1)
                        (== xs q)))
      '(((2 3))))

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

(test "'(a b) ∪ '(a b c d) ≡ {q}"
      (run* (q) (∪ '(a b) '(a b c d) q))
      '(((a b c d))))

(test "'(e f) ∪ '(a b c d) ≡ {q}"
      (run* (q) (∪ '(e f) '(a b c d) q))
      '(((e f a b c d))))

(test "'() ∪ '(a b c d) ≡ {q}"
      (run* (q) (∪ '() '(a b c d) q))
      '(((a b c d))))

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

(test "(foldᵒ '((a b c) (d e f)) '() appendᵒ q)"
      (run 1 (q) (foldᵒ '((a b c) (d e f)) '() appendᵒ q))
      '(((a b c d e f))))

(test "(foldᵒ '((a b c) {q}) '() appendᵒ '(a b c d e f))"
      (run 1 (q) (foldᵒ `((a b c) ,q) '() appendᵒ '(a b c d e f)))
      '(((d e f))))

(test "(foldᵒ {q} '() appendᵒ '(a b c d e f))"
      (run 3 (q) (foldᵒ q '() appendᵒ '(a b c d e f)))
      '((((a b c d e f)))
        ((() (a b c d e f)))
        (((a) (b c d e f)))))
