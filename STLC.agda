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

sub⊢ : ∀{X Y a} -> Y ⊢* X -> X ⊢ a -> Y ⊢ a
sub⊢ σ (var x) = σ x
sub⊢ σ (lam M) = lam (sub⊢ (∷/⊢* σ) M)
sub⊢ σ (app M N) = app (sub⊢ σ M) (sub⊢ σ N)


---------- Normal and neutral terms ----------
infix 1 _⇐_ _⇒_
mutual
  data _⇐_ (X : Cx) : Type -> Set where
    lam : ∀{a b} (M : a ∷ X ⇐ b) -> X ⇐ a ⊃ b
    -- allowing neutral terms only at base type enforces η-longness. if we
    -- allowed neutral terms at any type, we'd be β-short (no reducible
    -- expressions), but not η-long: that is, a term of type A -> B (in a
    -- nonempty context) might not be a lambda.
    neu : (R : X ⇒ base) -> X ⇐ base

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


-- Reify & reflect, parameterized over a given semantics
record ReifySem i : Set (lsuc i) where
  field
    [_⊢_] : Cx -> Type -> Set i
    weaken : ∀{X a c} -> [ X ⊢ c ] -> [ a ∷ X ⊢ c ]
    baseI : ∀{X} -> X ⇒ base -> [ X ⊢ base ]
    baseE : ∀{X} -> [ X ⊢ base ] -> X ⇒ base
    ⊃I : ∀{X a b} -> (∀ {Y} -> X ⊆ Y -> [ Y ⊢ a ] -> [ Y ⊢ b ]) -> [ X ⊢ a ⊃ b ]
    ⊃E : ∀{X a b} -> [ X ⊢ a ⊃ b ] -> [ X ⊢ a ] -> [ X ⊢ b ]

  reify : ∀ {X} a -> [ X ⊢ a ] -> X ⇐ a
  reflect : ∀ {X} a -> X ⇒ a -> [ X ⊢ a ]
  reify base x = neu (baseE x)
  reify {X} (a ⊃ b) f = lam (reify b (⊃E (weaken {c = a ⊃ b} f) (reflect a (var here))))
  reflect base R = baseI R
  reflect (a ⊃ b) R = ⊃I (λ X⊆Y x -> reflect b (app (rename⇒ X⊆Y R) (reify a x)))
