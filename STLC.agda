module STLC where

open import Level renaming (zero to lzero; suc to lsuc)

open import Data.Empty
open import Data.Sum hiding (map)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

infixr 6 _⊃_
data Type : Set where
  base : Type
  _⊃_ : Type -> Type -> Type


---------- Contexts ----------
Cx : Set1
Cx = Type -> Set

∅ : Cx
∅ _ = ⊥

infix 4 _∈_
_∈_ : Type -> Cx -> Set
a ∈ X = X a

hyp : Type -> Cx
hyp = _≡_

infixr 4 _∪_
_∪_ : Cx -> Cx -> Cx
(X ∪ Y) a = X a ⊎ Y a

infixr 4 _∷_
_∷_ : Type -> Cx -> Cx
a ∷ X = hyp a ∪ X

pattern here = inj₁ refl
pattern next x = inj₂ x


---------- Context renamings ----------
infix 1 _⊆_
_⊆_ : Cx -> Cx -> Set
X ⊆ Y = ∀ {a} -> X a -> Y a

∪/⊆ : ∀ X L {R} -> L ⊆ R -> X ∪ L ⊆ X ∪ R
∪/⊆ _ _ f = Data.Sum.map id f

∷/⊆ : ∀ L {R a} -> L ⊆ R -> a ∷ L ⊆ a ∷ R
∷/⊆ _ = ∪/⊆ _ _

dedup : ∀ X -> X ∪ X ⊆ X
dedup _ = [ id , id ]


---------- Terms ----------
infix 1 _⊢_
data _⊢_ (X : Cx) : Type -> Set where
  var : ∀{a} (x : a ∈ X) -> X ⊢ a
  lam : ∀{a b} (M : a ∷ X ⊢ b) -> X ⊢ a ⊃ b
  app : ∀{a b} (M : X ⊢ a ⊃ b) (N : X ⊢ a) -> X ⊢ b

-- Renaming
rename⊢ : ∀{X Y a} -> X ⊆ Y -> X ⊢ a -> Y ⊢ a
rename⊢ f (var x) = var (f x)
rename⊢ {X} f (lam M) = lam (rename⊢ (∷/⊆ X f) M)
rename⊢ f (app M N) = app (rename⊢ f M) (rename⊢ f N)


---------- Substitutions on terms ----------
infix 1 _⊢*_
_⊢*_ : Cx -> Cx -> Set
X ⊢* Y = ∀ {a} -> a ∈ Y -> X ⊢ a

∷/⊢* : ∀{X Y} -> X ⊢* Y -> ∀ {a} -> a ∷ X ⊢* a ∷ Y
∷/⊢* σ here = var here
∷/⊢* σ (next x) = rename⊢ next (σ x)

cons⊢* : ∀{X a} -> X ⊢ a -> X ⊢* a ∷ X
cons⊢* M here = M
cons⊢* M (next x) = var x

∅⊢*∅ : ∅ ⊢* ∅
∅⊢*∅ ()

sub⊢ : ∀{X Y a} -> Y ⊢* X -> X ⊢ a -> Y ⊢ a
sub⊢ σ (var x) = σ x
sub⊢ σ (lam M) = lam (sub⊢ (∷/⊢* σ) M)
sub⊢ σ (app M N) = app (sub⊢ σ M) (sub⊢ σ N)

-- sub⊢-is-id-on-closed-terms : ∀{a} (M : ∅ ⊢ a) {s : ∅ ⊢* ∅} -> sub⊢ s M ≡ M
-- sub⊢-is-id-on-closed-terms (var ())
-- sub⊢-is-id-on-closed-terms (app M N) =
--   cong₂ app (sub⊢-is-id-on-closed-terms M) (sub⊢-is-id-on-closed-terms N)
-- -- argh. induction.
-- sub⊢-is-id-on-closed-terms (lam M) = {!!}


---------- Normal and neutral terms ----------
infix 1 _⇐_ _⇒_
mutual
  -- Normal/canonical/checking terms.
  data _⇐_ (X : Cx) : Type -> Set where
    lam : ∀{a b} (M : a ∷ X ⇐ b) -> X ⇐ a ⊃ b
    -- allowing neutral terms only at base type enforces η-longness. if we
    -- allowed neutral terms at any type, we'd be β-short (no reducible
    -- expressions), but not η-long: that is, an (open) term of type A ⊃ B might
    -- not be a lambda.
    neu : (R : X ⇒ base) -> X ⇐ base

  -- Neutral/atomic/synthesizing terms.
  data _⇒_ (X : Cx) : Type -> Set where
    var : ∀{a} -> a ∈ X -> X ⇒ a
    app : ∀{a b} (R : X ⇒ a ⊃ b) (M : X ⇐ a) -> X ⇒ b

-- "Forgetting" normal/neutral status
forget⇐ : ∀{X a} -> X ⇐ a -> X ⊢ a
forget⇒ : ∀{X a} -> X ⇒ a -> X ⊢ a
forget⇐ (lam M) = lam (forget⇐ M)
forget⇐ (neu R) = forget⇒ R
forget⇒ (var x) = var x
forget⇒ (app R M) = app (forget⇒ R) (forget⇐ M)

-- Renaming on normal/neutral terms
rename⇐ : ∀{X Y a} -> X ⊆ Y -> X ⇐ a -> Y ⇐ a
rename⇒ : ∀{X Y a} -> X ⊆ Y -> X ⇒ a -> Y ⇒ a
rename⇐ {X} r (lam M) = lam (rename⇐ (∷/⊆ X r) M)
rename⇐ r (neu R) = neu (rename⇒ r R)
rename⇒ r (var x) = var (r x)
rename⇒ r (app R M) = app (rename⇒ r R) (rename⇐ r M)


---------- A pretty standard semantics ----------
module Semantics {i} (Base : Set i) where
  -- Denotation of types.
  set : Type -> Set _
  set base = Base
  set (a ⊃ b) = set a -> set b

  set* : Cx -> Set _
  set* X = ∀ {a} (x : a ∈ X) -> set a

  extend : ∀{X a} -> set a -> set* X -> set* (a ∷ X)
  extend v ρ here = v
  extend v ρ (next y) = ρ y

  -- Denotation of terms
  den : ∀{X a} -> X ⊢ a -> set* X -> set a
  den (var x) ρ = ρ x
  den {X} (lam M) ρ v = den M (extend {X} v ρ)
  den (app M N) ρ = den M ρ (den N ρ)
