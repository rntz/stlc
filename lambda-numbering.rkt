;; Michael Arntzenius, daekharel@gmail.com, October 2018
;;
;; This file gives a program that renames the variables in a λ-term M such that
;; if two subterms N1, N2 are α-equivalent, they are syntactically _equal_ after
;; renaming. (Note that the reverse implication does not hold; subterms might be
;; syntactically equal without being α-equivalent.)
;;
;; I am using an unusual "contextual" definition of α-equivalence, as a relation
;; between _subterms_ of a term M, rather than two terms. For example, typically
;; we'd say (λx.y ≡α λx.y). However, consider:
;;
;;     let y = 1 in f = (λx.y) in let y = 2 in (λx.y)
;;                      ^ N1 ^                 ^ N2 ^
;;
;; There is a clear sense in which N1 ≢α N2. The "y" in N1 and in N2 are
;; distinct variables that merely happen to share a name.
;;
;; Normal α-equivalence is solved by deBruijn indexing. But not contextual
;; α-equivalence. Under deBruijn indexing,
;;
;;     λy.(λx.y)(λz.λx.y)  becomes  λ.(λ1)(λ(λ2))
;;        ^N1       ^N2                ^N1   ^N2
;;
;; Here, N1 ≡α N2 becomes λ1 ≠ λ2.
;;
;; Instead, my approach uses what I call "minimal deBruijn levels". Reusing the
;; prior example,
;;
;;     λy.(λx.y)(λz.λx.y)  becomes  λa.(λ_.a)(λ_.λ_.a)
;;
;; where "_" is a dummy variable used when a bound variable is never referred to
;; within its scope. So, what are minimal deBruijn levels?
;;
;; Let fv(X) be the set of free variables of the term X. Fix a term M. Consider
;; a subterm N = (λy.O) of M. Then the minimal deBruijn level mdb(y) of y is:
;;
;;     mdb(y) = 0                               if fv(N) = ∅
;;     mdb(y) = 1 + max {mdb(x) | x ∈ fv(N)}    otherwise
;;
;; This seemingly recursive definition is inductive: the minimal deBruijn level
;; of a binding depends only on the minimal deBruijn levels of bindings with
;; strictly wider scopes.
;;
;; Now, fix an infinite sequence of distinct concrete variables xᵢ, and a
;; distinct variable "_". My approach is to rename every λ-binding N = λy.O in M
;; as follows:
;;
;;     newname(y) = "_"     if y ∉ fv(O), i.e. N does not refer to its argument
;;     newname(y) = xᵢ      otherwise
;;        where i = mdb(y)
;;
;; I conjecture the following:
;; 1. M is α-equivalent (in the normal sense) to its renaming described above.
;; 2. For subterms N1, N2 of M, if N1 ≡α N2 (contextually), their renamings will be
;;    syntactically equal.

;; TODO:
;; - simplify the nfv/ann-term->term code.
;;   - is there a better way to store the nfv for each term?
;;   - is it possible to fuse these passes somehow?
;;     maybe something NBE/HOAS style?

#lang racket

(require syntax/parse/define)
(define-syntax-parser TODO [_ #'(error "TODO")])
(define-syntax-rule (define-flat-contract name branch ...)
  (define name (flat-rec-contract name branch ...)))


;; ========== PAIRING HEAPS ==========
;;
;; I find a renaming in O(n log n) time, where n is the size of M. To do this, I
;; need a priority queue data structure where findMax, deleteMax, and union each
;; take amortized O(log n) time.
;;
;; I use pairing heaps. They are remarkably simple to implement, with very nice
;; time bounds (whose proofs I do not yet understand):
;;
;; insert     O(1)     amortized & worst-case
;; union      O(1)     amortized & worst-case
;; findMax    O(1)     amortized & worst-case
;; deleteMax  O(log n) amortized, O(n) worst-case
;;
;; For details consult Wikipedia or the Monad Reader, issue 16.
;; https://en.m.wikipedia.org/wiki/Pairing_heap
;; https://themonadreader.files.wordpress.com/2010/05/issue16.pdf
;;
;; I've implemented a small variation which automatically eliminates duplicate
;; entries. I hope and conjecture, but have NOT proven, that this has the same
;; amortized time bounds.

;; A heap is either empty or a node.
;; A node has a max element and a list of child nodes.
(struct node (max kids) #:transparent)
(define heap? (or/c null? node?))

(define (heap-singleton x) (node x '()))
;; Returns #f if the heap is empty.
(define (heap-max x) (and (node? x) (node-max x)))
;; Drops the maximum element, if present.
(define (heap-drop h)
  (if (null? h) h (heap-union* (node-kids h))))

(define/match (heap-union a b)
  [('() b) b]
  [(a '()) a]
  [((node x xs) (node y ys))
   (cond
     [(> x y) (node x (cons b xs))]
     [(< x y) (node y (cons a ys))]
     ;; This is the case I've added to avoid duplicates.
     [(= x y)
      (node x (match (heap-union* ys)
                ['() xs]
                [y (cons y xs)]))])])

;; Unions a list of heaps.
(define/match (heap-union* l)
  [('()) '()]
  [(`(,x)) x]
  [(`(,x ,y)) (heap-union x y)]
  [(`(,x ,y ,@z)) (heap-union (heap-union x y) (heap-union* z))])

;; TODO: implement an invariant checking routine & use it to test my heap
;; implementation.


;; ========== λ-CALCULUS SYNTAX ==========
;; TODO: explain this
(define name? (and/c symbol? (not/c 'lambda)))
;; TODO: explain this
(define-flat-contract term?
  name?
  (list/c 'lambda (list/c name?) term?)
  (list/c term? term?))

;; Terms w/ deBruijn levels for variables, annotated with their NFVs.
;; TODO: explain this
(define-flat-contract ann-term?
  (list/c (or/c natural? #f)
          (or/c natural?
                (list/c 'lambda ann-term?)
                (list/c ann-term? ann-term?))))

;; TODO: explain this
(define cx? (hash/c name? natural? #:immutable #t))


;; ========== THE CORE ALGORITHM ==========

;; The definition of minimal deBruijn levels uses the free variables of each
;; subterm. However, computing the free variable set for every subterm seems
;; prohibitive: in the worst case, O(n) subterms might each have O(n) free
;; variables, using O(n^2) space. Possibly structural sharing would save us from
;; this quadratic hell, but there is another option.
;;
;; If we're careful, we only need the "nearest free variable" of each subterm N:
;; among the free variables of N, the one most recently bound. For example:
;;
;;     λa.λb.λc.(λd. abd)
;;              ^---N---^
;;
;; Here,
;;
;;     fv(N) = {a,b}        because in N, d is bound and c doesn't occur
;;     nfv(N) = b           because b is bound more recently than a
;;
(define/contract (nfv term depth cx)
  (-> term? natural? cx? (values heap? ann-term?))
  ;; invariant check
  (unless (= depth (+ 1 (apply max -1 (hash-values cx))))
    (error 'nfv "oops ~a ~a" depth cx))
  (match term
    [(? name? x)
     (define n (hash-ref cx x))
     (values (heap-singleton n) (list n n))]
    [`(lambda (,x) ,body)
     (define-values (heap ann-body)
       (nfv body (+ depth 1) (hash-set cx x depth)))
     ;; If body's NFV is x, drop it.
     (when (eq? depth (heap-max heap))
       ;; (printf "here ~a ~a\n" depth term)
       (set! heap (heap-drop heap)))
     (values heap `(,(heap-max heap) (lambda ,ann-body)))]
    [`(,fnc ,arg)
     (define-values (fheap fncx) (nfv fnc depth cx))
     (define-values (aheap argx) (nfv arg depth cx))
     (define heap (heap-union fheap aheap))
     (values heap `(,(heap-max heap) (,fncx ,argx)))]))

(define (term->ann-term term [vars '()])
  (define depth (length vars))
  (define cx (for/hash ([x vars] [i (in-naturals)]) (values x i)))
  (define-values (_ x) (nfv term depth cx))
  x)

;; What do these extra parameters do? Are they useful to the outside world?
(define/contract (ann-term->term ann-term [depth 0] [cx (hash)])
  (-> ann-term? term?)
  (match-define `(,nfv ,term) ann-term)
  (match term
    [(? natural? n) (hash-ref cx n)]
    [`(lambda ,(and body (list body-nfv _)))
     ;; If the lambda variable is used in the body, generate a new name for it
     ;; using the lowest variable index not already present in body.
     (define x (and (eqv? depth body-nfv)
                   (nat->symbol (+ 1 (or nfv -1)))))
     `(lambda (,(or x '_))
        ,(ann-term->term body (+ 1 depth) (if x (hash-set cx depth x) cx)))]
    [`(,fnc ,arg)
     `(,(ann-term->term fnc depth cx)
       ,(ann-term->term arg depth cx))]))

(define (rename term) (ann-term->term (term->ann-term term)))


;; ========== GENERATING VARIABLE NAMES ==========
;; Deterministically generating reasonable variable names given DeBruijn levels.
;; This makes the output of ann-term->term much prettier.
(define chars "abcdefghijklmnopqrstuvwxyz")
(define nchars (string-length chars))
(define chartbl (for/hash ([i (in-naturals)] [c chars])
                  (values i (string->symbol (string c)))))
(define nametbl (make-weak-hasheqv)) ;; memo table.
(define (nat->symbol d)
  (define (make)
    (define-values (lvl idx) (quotient/remainder d nchars))
    (string->symbol
     (format "~a~a" (hash-ref chartbl idx) (if (> lvl 0) lvl ""))))
  (hash-ref! nametbl d make))


;; ========== TESTS ==========
(module+ test
  (define example '(lambda (x) ((lambda (y) y) (lambda (z) (x z)))))
  (define-values (hp aterm) (nfv example 0 (hash)))

  (define example2 '(lambda (x)
                      ((lambda (y) x)
                       (lambda (y) (lambda (z) x)))))
  (rename example2)

  (define example3 '((lambda (x) x) (lambda (y) (lambda (x) x))))
  (rename example3)

  (define example4 '(lambda (x)
                      ((lambda (y) (y (lambda (z) (x z))))
                       (lambda (y) (lambda (z) (x z))))))
  (rename example4))
