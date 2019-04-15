#lang racket

(require minikanren)

(provide (all-defined-out))

(define N 0)

(define (fresh-number)
  (let ([t N])
    (set! N (+ N 1))
    t))

(define (fresh-smt-filename)
  (string-append "smt-"
                 (number->string (fresh-number))
                 ".z3"))

(define (valid? query)
  (define filename (fresh-smt-filename))
  (call-with-output-file filename
    #:mode 'text
    #:exists 'replace
    (lambda (out)
      (for ([q query])
        (write q out)
        (write-char #\newline out))))
  (define output
    (string-split
     (with-output-to-string (λ () (system (string-append "z3 " filename)))) "\n"))
  (equal? (car output) "unsat"))

(define (valido query)
  (== #t (valid? query)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define query
  '((declare-const x Int)
    (declare-const y Int)
    (assert (not (= x y)))
    (assert (= x y))
    (check-sat)))