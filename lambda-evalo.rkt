#lang racket

(require minikanren)
(require minikanren/numbers)

;; A relational interpreter for simplest λ-calculus
;; From "miniKanren, Live and Untagged"

(define ρ0 '())

(define evalo
  (λ (expr val)
    (eval-expro expr ρ0 val)))

(define eval-expro
  (λ (expr env val)
    (conde
     [(fresh (rator rand x body env* arg)
             (== `(,rator ,rand) expr)
             (eval-expro rator env `(closure ,x ,body ,env*))
             (eval-expro rand env arg)
             (eval-expro body `((,x . ,arg) . ,env*) val))]
     [(fresh (x body)
             (== `(λ (,x) ,body) expr)
             (symbolo x)
             (== `(closure ,x ,body ,env) val)
             (not-in-envo 'λ env))]
     [(symbolo expr) (lookupo expr env val)])))

(define not-in-envo
  (λ (x env)
    (conde
     [(== '() env)]
     [(fresh (y v rest)
             (== `((,y . ,v) . ,rest) env)
             (=/= y x)
             (not-in-envo x rest))])))

(define lookupo
  (λ (x env t)
    (conde
     [(fresh (y v rest)
             (== `((,y . ,v) . ,rest) env)
             (== y x)
             (== v t))]
     [(fresh (y v rest)
             (== `((,y . ,v) . ,rest) env)
             (=/= y x)
             (lookupo x rest t))])))
