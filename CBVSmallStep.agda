module CBVSmallStep where

open import Level renaming (zero to lzero; suc to lsuc)

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum hiding (map)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import STLC

Term : Type -> Set
Term a = ∅ ⊢ a

-- A value judgment
data value : ∀{a} -> Term a -> Set where
  lam-value : ∀{a b} {M} -> value (lam {a = a}{b = b} M)
  -- hm. not sure about this.

-- A call-by-value small-step evaluation relation
infix 4 _↦_
data _↦_ : ∀{a} (M N : Term a) -> Set where
  β : ∀{a b} {M : a ∷ ∅ ⊢ b} {N} ->
      value N ->
      app (lam M) N ↦ sub⊢ (cons⊢* N) M
  app1 : ∀{a b M M' N}
       -> M ↦ M'
       -> app {∅}{a}{b} M N ↦ app M' N
  app2 : ∀{a b M N N'}
       -> value M
       -> N ↦ N'
       -> app {∅}{a}{b} M N ↦ app M N'

infix 4 _↦*_
data _↦*_ {a} : (M N : Term a) -> Set where
  nil : ∀ {M} -> M ↦* M
  _∙_ : ∀ {M N O} -> M ↦* N -> N ↦* O -> M ↦* O
  step : ∀ {M N} -> M ↦ N -> M ↦* N


-- Termination
terminates : ∀{a} -> Term a -> Set
terminates M = ∃ λ v -> value v × M ↦* v

terminates↦ : ∀{a M N} -> M ↦* N -> terminates {a} N -> terminates M
terminates↦ M↦*N (v , is-val , N↦*v) = v , is-val , M↦*N ∙ N↦*v

-- Hereditary termination
HT : ∀ a -> Term a -> Set
hered : ∀ a -> Term a -> Set
HT a M = terminates M × hered a M
hered base _ = ⊤
hered (a ⊃ b) M = ∀ N -> HT a N -> HT b (app M N)

-- HT base M = terminates M
-- HT (a ⊃ b) M = terminates M × (∀ N -> HT _ N -> HT _ (app M N))

HT* : ∀ {X} -> ∅ ⊢* X -> Set
HT* {X} σ = ∀ {a} (x : a ∈ X) -> HT _ (σ x)

-- extending to open terms
HT⊢ : ∀ X a -> X ⊢ a -> Set
HT⊢ X _ M = (σ : ∅ ⊢* X) -> HT* σ -> HT _ (sub⊢ σ M)

-- Showing HT is closed under ↦*:
app1* : ∀{a b} {M N : Term (a ⊃ b)} {O} -> M ↦* N -> app M O ↦* app N O
app1* nil = nil
app1* (M↦*N ∙ M↦*N₁) = app1* M↦*N ∙ app1* M↦*N₁
app1* (step x) = step (app1 x)

HT↦ : ∀{a M N} -> M ↦* N -> HT a N -> HT a M
hered↦ : ∀ a {M N} -> M ↦* N -> hered a N -> hered a M
HT↦ M↦*N (tM , hM) = terminates↦ M↦*N tM , hered↦ _ M↦*N hM
hered↦ base M↦*N = id
hered↦ (_ ⊃ _) M↦*N p O x = HT↦ (app1* M↦*N) (p O x)

-- All open terms are hereditarily terminating
ht : ∀ {X a} (M : X ⊢ a) -> HT⊢ X a M
ht (var v) σ x = x v
ht (app M N) σ x with ht M σ x | ht N σ x
ht (app M N) σ x | _ , hM | tN , hN = hM _ (tN , hN)
-- the tough case
ht (lam M) σ x = (lam (sub⊢ (∷/⊢* σ) M) , lam-value , nil) , foo
  where foo : (N : ∅ ⊢ _) -> HT _ N -> HT _ (app _ N)
        foo N (tN , hN) = {!!} , {!!}

-- ht (var ())
-- ht (app M N) = proj₂ (ht M N (ht N))
-- -- uh-oh, I need an inductive hypothesis for the (lam M) case!
-- ht (lam M) N x = (lam M , lam-value , nil) , {!!}


-- All closed terms terminate!
terminates! : ∀ {a} (M : ∅ ⊢ a) -> terminates M
terminates! M = {!proj₁ (ht M ? ?)!}

