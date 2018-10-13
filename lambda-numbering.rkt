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
;; Normal α-equivalence is solved by de Bruijn indexing. But not contextual
;; α-equivalence. Under de Bruijn indexing,
;;
;;     λy.(λx.y)(λz.λx.y)  becomes  λ.(λ1)(λ(λ2))
;;        ^N1       ^N2                ^N1   ^N2
;;
;; Here, N1 ≡α N2 becomes λ1 ≠ λ2.
;;
;; Instead, my approach uses what I call "minimal de Bruijn levels". Reusing the
;; prior example,
;;
;;     λy.(λx.y)(λz.λx.y)  becomes  λa.(λ_.a)(λ_.λ_.a)
;;
;; where "_" is a dummy variable used when a bound variable is never referred to
;; within its scope. So, what are minimal de Bruijn levels?
;;
;; Let fv(X) be the set of free variables of the term X. Fix a term M. Consider
;; a subterm N = (λy.O) of M. Then the minimal de Bruijn level mdb(y) of y is:
;;
;;     mdb(y) = 0                               if fv(N) = ∅
;;     mdb(y) = 1 + max {mdb(x) | x ∈ fv(N)}    otherwise
;;
;; This seemingly recursive definition is inductive: the minimal de Bruijn level
;; of a binding depends only on the minimal de Bruijn levels of bindings with
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

#lang racket

(require syntax/parse/define)
(define-syntax-rule (define-flat-contract name branch ...)
  (define name (flat-rec-contract name branch ...)))


;; ========== PAIRING HEAPS ==========
;;
;; I find a renaming in O(n log n) time, where n is the size of M. To do this, I
;; need a priority queue structure where findMax, deleteMax, and union each take
;; amortized O(log n) time. I use pairing heaps. They are remarkably simple to
;; implement, with very nice time bounds (whose proofs I do not yet understand):
;;
;; insert     O(1)     amortized & worst-case
;; union      O(1)     amortized & worst-case
;; findMax    O(1)     amortized & worst-case
;; deleteMax  O(log n) amortized, O(n) worst-case
;;
;; For details consult Wikipedia or the Monad Reader, issue 16.
;; https://en.wikipedia.org/wiki/Pairing_heap
;; https://themonadreader.files.wordpress.com/2010/05/issue16.pdf
;;
;; I've implemented a small variation that automatically eliminates duplicate
;; entries. I hope and conjecture, but have not proven, that this has the same
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


;; ========== THE CORE ALGORITHM ==========

;; The definition of minimal de Bruijn levels uses the free variables of each
;; subterm. However, computing the free variable set for every subterm seems
;; prohibitive: in the worst case, O(n) subterms might each have O(n) free
;; variables, using O(n^2) space!
;;
;; Possibly structural sharing would save us from this quadratic hell, but there
;; is another option. If we're careful, we only need the "nearest free variable"
;; of each subterm N: among the free variables of N, the one most recently
;; bound. For example:
;;
;;     λa.λb.λc.(λd. abd)
;;              ^---N---^
;;
;; Here,
;;
;;     fv(N) = {a,b}        because in N, d is bound and c doesn't occur
;;     nfv(N) = b           because b is bound more recently than a
;;
;; We can compute the nfv for each subterm by keeping a heap of free variables,
;; where "nearer" variables (with smaller scopes) have higher priority.
;; Concretely, we use their de Bruijn levels. A variables' de Bruijn level is
;; the number of binders enclosing its binder. For example,
;;
;;     λx.x(λy.y)(λz.xz)  becomes  λ0.0(λ1.1)(λ1.01)
;;
;; NB. DeBruijn levels and indices are very different. With de Bruijn levels,
;; the same variable always has the same number; unlike de Bruijn indices, where
;; a variable occurrence gets a number that depends on the number of binders
;; between the occurrence & its binder. On the other hand, with de Bruijn
;; levels, the subterm (λx.x) may become (λ0.0) or (λ1.1) or (λ2.2), etc.
;; depending on where it occurs; with de Bruijn indexes it is always (λ.0).
;;
;; TODO: explain why we only need nfv(). Can we reformulate mdb() in terms of
;; nfv()? Yes! mdb(y) = 1 + mdb(nfv(λy.O)) when fv(O) ≠ ∅.

;; λ-calculus terms are given by this grammar:
;;
;;     M, N ::= x | (lambda (x) M) | (M N)
;;
;; This is very easy to encode as a Racket contract.
(define-flat-contract term?
  symbol?
  (list/c 'lambda (list/c symbol?) term?)
  (list/c term? term?))

;; As mentioned, we first compute the nfv for each subterm. We represent this
;; using an "annotated term" where:
;; 1. Every subterm comes with an nfv (or #f, if it has no free variables).
;; 2. All variables are replaced by natural numbers (de Bruijn levels).
(define-flat-contract ann-term?
  (list/c (or/c natural? #f)
          (or/c natural?
                (list/c 'lambda ann-term?)
                (list/c ann-term? ann-term?))))

;; Given a subterm, its depth (number of binders it is under), and a context
;; mapping free variables to their de Bruijn levels, produces the free variable
;; heap and version of the subterm where every node is annotated with its nfv
;; and all variables replaced by their de Bruijn levels.
(define/contract (compute-nfvs term depth cx)
  (-> term? natural? (hash/c symbol? natural? #:immutable #t)
      (values heap? ann-term?))
  ;; Invariant check.
  (unless (= depth (+ 1 (apply max -1 (hash-values cx))))
    (error 'compute-nfvs "oops ~a ~a" depth cx))
  (match term
    [(? symbol? x)
     (define n (hash-ref cx x))
     (values (heap-singleton n) (list n n))]
    [`(lambda (,x) ,body)
     (define-values (heap ann-body)
       (compute-nfvs body (+ depth 1) (hash-set cx x depth)))
     ;; If body's NFV is x, drop it.
     (when (eq? depth (heap-max heap))
       ;; (printf "here ~a ~a\n" depth term)
       (set! heap (heap-drop heap)))
     (values heap `(,(heap-max heap) (lambda ,ann-body)))]
    [`(,f ,a)
     (define-values (fheap fx) (compute-nfvs f depth cx))
     (define-values (aheap ax) (compute-nfvs a depth cx))
     (define heap (heap-union fheap aheap))
     (values heap `(,(heap-max heap) (,fx ,ax)))]))

;; Now that we have an term annotated with nfvs, we can rename it in such a way
;; that subterms N1, N2 that are contextually α-equivalent become syntactically
;; equal.

;; Takes an nfv-annotated term, a depth (number of enclosing binders), and a
;; context mapping variables (de Bruijn levels) to their replacements (minimal
;; de Bruijn levels).
(define/contract (deannotate ann-term [depth 0] [cx (hash)])
  (-> ann-term? term?)
  (match-define `(,nfv ,term) ann-term)
  (match term
    [(? natural? n)
     (nat->symbol (hash-ref cx n))]
    [`(lambda ,(and body (list body-nfv _)))
     ;; Compute the variable's mdb. Here we use the fact that mdb(y) = 1 +
     ;; mdb(nfv(λy.O)) when fv(λy.O) ≠ ∅. TODO: justify this fact.
     (define mdb (if nfv (+ 1 (hash-ref cx nfv)) 0))
     ;; If the variable is used in the body, generate a name for it based on mdb.
     (define x (if (eqv? depth body-nfv) (nat->symbol mdb) '_))
     `(lambda (,x)
        ,(deannotate body (+ 1 depth) (if mdb (hash-set cx depth mdb) cx)))]
    [`(,f ,a)
     `(,(deannotate f depth cx)
       ,(deannotate a depth cx))]))

;; Annotates a closed term with nfvs for each subterm.
(define (annotate term)
  (define-values (_ x) (compute-nfvs term 0 (hash)))
  x)

;; Renames a term so that two contextually α-equivalent subterms become
;; syntactically equal.
(define (rename term) (deannotate (annotate term)))


;; ========== GENERATING VARIABLE NAMES ==========
;; Deterministically generating reasonable variable names given DeBruijn levels.
;; This makes the output of deannotate much prettier.
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
;;
;; TODO: make these actual tests which check equality or something.
;;
;; could I test this by randomly renaming things and checking that their
;; renamings are equal?
(module+ test
  (rename '(lambda (x) ((lambda (y) y) (lambda (z) (x z)))))
  (rename '(lambda (x) ((lambda (y) x) (lambda (y) (lambda (z) x)))))
  (rename '((lambda (x) x) (lambda (y) (lambda (x) x))))
  (rename '(lambda (x) ((lambda (y) (y (lambda (z) (x z))))
                   (lambda (y) (lambda (z) (x z))))))
  (rename '(lambda (a) (lambda (b) (lambda (c) (a c)))))
  (rename '(lambda (a) (lambda (b) (lambda (c) (lambda (d) (b d)))))))
