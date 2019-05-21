(load "../mk/mk.scm")

(define (membero x xs)
  (fresh (a d)
         (== `(,a . ,d) xs)
         (conde
           [(== a x)]
           [(membero x d)])))

(define (not-membero x xs)
  (conde
   [(== xs '())]
   [(fresh (a d)
           (== xs `(,a . ,d))
           (=/= a x)
           (not-membero x d))]))

(define ∈ membero)
(define ∉ not-membero)

(define-syntax listᵒ
  (syntax-rules (← with)
    ((_ ((x . xs) ← lst) (with v ...) rel ...)
     (listᵒ ((x . xs) ← lst)
            (fresh (v ...) rel ...)))
    ((_ ((x . xs) ← lst) rel ...)
     (conde
      [(== lst '())]
      [(fresh (x xs)
              (== lst `(,x . ,xs))
              rel ...)]))))

(define (forall lst rel)
  (listᵒ ((x . xs) ← lst)
         (rel x)
         (forall xs rel)))

(define-syntax ∀
  (syntax-rules (←)
    ((_ (x ← xs) rel ...)
     (forall xs (lambda (x) rel ...)))))

(define-syntax ∃
  (syntax-rules (←)
    ((_ (x = (f xs ...)) rel ...)
     (fresh (x) (f xs ... x) rel ...))
    ((_ (x ← xs) rel ...)
     (fresh (x) (∈ x xs) rel ...))
    ((_ (x ...) rel ...)
     (fresh (x ...) rel ...))))

(define-syntax ∧
  (syntax-rules ()
    ((_ rel ...)
     (fresh () rel ...))))

(define-syntax ∨
  (syntax-rules ()
    ((_ (rel ...) ...)
     (conde (rel ...) ...))))

(define (∩ x y z)
  (∨ [(emptyᵒ x) (emptyᵒ z)]
     [(emptyᵒ y) (emptyᵒ z)]
     [(fresh (a d z^)
             (== `(,a . ,d) x)
             (∨ [(∈ a y)
                 (∩ d y z^)
                 (== z `(,a . ,z^))]
                [(∉ a y)
                 (∩ d y z)]))]))

(define (∪ x y z)
  (∨ [(emptyᵒ x) (== y z)]
     [(emptyᵒ y) (== x z)]
     [(fresh (a d z^)
             (== x `(,a . ,d))
             (conde
              [(∈ a y) (∪ d y z)]
              [(∉ a y)
               (∪ d y z^)
               (== z `(,a . ,z^))]))]))

;; Split list pxq at the the first occorence of x.
(define (splitᵒ pxq p x q)
  (∃ (a d p^)
     (== pxq `(,a . ,d))
     (∨ [(== a x)
         (emptyᵒ p)
         (== q d)]
        [(=/= a x)
         (splitᵒ d p^ x q)
         (== p `(,a . ,p^))])))

(define (rem-dupᵒ xs ys)
  (∨ [(emptyᵒ xs) (emptyᵒ ys)]
     [(∃ (a d ys^)
         (== xs `(,a . ,d))
         (∨ [(∈ a d) (rem-dupᵒ d ys)]
            [(∉ a d)
             (rem-dupᵒ d ys^)
             (== ys `(,a . ,ys^))]))]))

(define (appendᵒ l s out)
  (∨ [(emptyᵒ l) (== s out)]
     [(∃ (a d res)
         (== `(,a . ,d) l)
         (== `(,a . ,res) out)
         (appendᵒ d s res))]))

(define (flattenᵒ xss xs)
  (∨ [(emptyᵒ xss) (emptyᵒ xs)]
     [(∃ (a d res)
         (== xss `(,a . ,d))
         (flattenᵒ d res)
         (appendᵒ a res xs))]))

(define (⊆* ∈)
  (lambda (xs ys)
    (∨ [(emptyᵒ xs)]
       [(∃ (a d)
           (== xs `(,a . ,d))
           (∈ a ys)
           ((⊆* ∈) d ys))])))

(define ⊆ (⊆* ∈))

(define (removeᵒ xs x ys)
  (∨ [(emptyᵒ xs) (emptyᵒ ys)]
     [(∃ (a d ys^)
         (== xs `(,a . ,d))
         (∨ [(== a x) (removeᵒ d x ys)]
            [(=/= a x)
             (removeᵒ d x ys^)
             (== ys `(,a . ,ys^))]))]))

;; mapfilter takes a list `xs`, a predicate relation `p`, and transformer relation `f`,
;; then transforms every element `x` in `xs`, and only keeps those transformed values who
;; satifies `p`.
(define (mapfilterᵒ xs p f ys)
  (∨ [(emptyᵒ xs) (emptyᵒ ys)]
     [(∃ (a a^ d r ys^)
         (== xs `(,a . ,d))
         (f a a^)
         (p a^ r)
         (∨ [(== r #t)
             (mapfilterᵒ d p f ys^)
             (== ys `(,a^ . ,ys^))]
            [(== r #f)
             (mapfilterᵒ d p f ys)]))]))

