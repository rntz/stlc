#lang racket

;; Intensional normalisation by evaluation for the simply-typed lambda calculus.
;; Based on http://homepages.inf.ed.ac.uk/slindley/nbe/nbe-cambridge2016.pdf

(provide define-flat-contract)
(define-syntax-rule (define-flat-contract name branches ...)
  (define name (opt/c (flat-rec-contract name branches ...))))

(define name? (and/c symbol? (not/c 'lambda)))

(define-flat-contract term?
  name?
  (list/c term? term?)
  (list/c 'lambda name? term?))

;; Normal here means β-short, but not necessarily η-long.
(define-values (nf? ne?)
  (flat-murec-contract
   ([nf? ne? (list/c 'lambda name? nf?)]
    [ne? name? (list/c ne? nf?)])
   (values nf? ne?)))

;; Semantic terms: either neutral terms or functions on semantic terms.
(define sem/c (recursive-contract (or/c ne? (-> sem/c sem/c)) #:chaperone))
(define env? (hash/c name? sem/c #:immutable #t))

(define/contract (den term env)
  (-> term? env? sem/c)
  (match term
    ;; if x is bound, return its denotation; otherwise, return it as syntax.
    [(? name? x) (hash-ref env x x)]
    [`(lambda ,x ,M) (lambda (v) (den M (hash-set env x v)))]
    [`(,M ,N) (app (den M env) (den N env))]))

(define/contract (app f a)
  (-> sem/c sem/c sem/c)
  (if (procedure? f) (f a) `(,f ,(reify a))))

(define/contract (reify v)
  (-> sem/c nf?)
  (if (not (procedure? v)) v
      (let ((x (gensym)))
        `(lambda ,x ,(reify (v (reflect x)))))))

;; we're intensional, so this is easy.
(define/contract (reflect N) (-> ne? sem/c) N)

(define (normalize M)
  (reify (den M (hash))))
