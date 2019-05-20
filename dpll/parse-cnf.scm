;; string-split is adapted from https://gist.github.com/matthewp/2324447
(define (string-split str ch)
  (letrec ([len (string-length str)]
           [split (lambda (a b)
                    (cond
                     [(>= b len) (if (= a b) '() (cons (substring str a b) '()))]
                     [(char=? ch (string-ref str b)) (if (= a b)
                                                         (split (+ 1 a) (+ 1 b))
                                                         (cons (substring str a b) (split b b)))]
                     [else (split a (+ 1 b))]))])
    (split 0 0)))

(define (string->lit x)
  (let ([n (string->number x)])
    (if (< n 0) `(¬ ,(abs n)) n)))

(define (discard-last xs)
  (cond [(null? xs) '()]
        [(null? (cdr xs)) '()]
        [else (cons (car xs) (discard-last (cdr xs)))]))

(define (line->clause line)
  (discard-last (map string->lit (string-split line #\space))))

(define (parse in-port)
  (let loop ([formula '()]
             [line (get-line in-port)])
    (cond [(eof-object? line) formula]
          [(= (string-length line) 0) formula]
          [else (cond [(char=? (string-ref line 0) #\c) (loop formula (get-line in-port))]
                      [(char=? (string-ref line 0) #\p) (loop formula (get-line in-port))]
                      [(char=? (string-ref line 0) #\%) (loop formula (get-line in-port))]
                      [(char=? (string-ref line 0) #\0) (loop formula (get-line in-port))]
                      [else (loop (append formula (list (line->clause line)))
                                  (get-line in-port))])])))

(define (parse-dimacs-file filepath)
  (call-with-input-file filepath parse))
