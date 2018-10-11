#lang racket

;; Intensional normalisation by evaluation for the untyped λ-calculus.
;; Based on http://homepages.inf.ed.ac.uk/slindley/nbe/nbe-cambridge2016.pdf
;;
;; Just for kicks, the s-expressions we use to represent λ-calculus terms are a
;; subset of valid Racket expressions. This means you can (eval) them.

(define-syntax-rule (define-flat-contract name branches ...)
  (define name (opt/c (flat-rec-contract name branches ...))))

(define name? (and/c symbol? (not/c 'lambda)))

(define-flat-contract term?
  name?
  (list/c term? term?)
  (list/c 'lambda (list/c name?) term?))

;; Normal here means β-short, but not necessarily η-long.
(define-values (nf? ne?)
  (flat-murec-contract
   ([nf? ne? (list/c 'lambda (list/c name?) nf?)]
    [ne? name? (list/c ne? nf?)])
   (values nf? ne?)))

;; Semantic terms: either neutral terms or functions on semantic terms.
(define sem/c (recursive-contract (or/c ne? (-> sem/c sem/c)) #:chaperone))
(define env/c (hash/c name? sem/c #:immutable #t))

(define/contract (den term [env (hash)])
  (->* (term?) (env/c) sem/c)
  (match term
    ;; if x is bound, return its denotation; otherwise, return it as syntax.
    [(? name? x) (hash-ref env x x)]
    [`(lambda (,x) ,M)
     ;; procedure-rename is a terrible hack to attach the parameter's name to
     ;; the function so we can recover it later in reify.
     (procedure-rename (lambda (v) (den M (hash-set env x v))) x)]
    [`(,M ,N) (app (den M env) (den N env))]))

(define/contract (app f a)
  (-> sem/c sem/c sem/c)
  (if (procedure? f) (f a) `(,f ,(reify a))))

(define/contract (reify v)
  (-> sem/c nf?)
  (if (not (procedure? v)) v
      ;; terrible hack: use object-name to get the original parameter's name.
      (let ((x (gensym (object-name v))))
        `(lambda (,x) ,(reify (v (reflect x)))))))

;; we're intensional, so this is easy.
(define/contract (reflect N) (-> ne? sem/c) N)

(define/contract (norm M)
  (-> term? nf?)
  (reify (den M (hash))))

;; (norm '((lambda (x) (x x)) (lambda (s) (lambda (f) (f ((s s) f))))))
