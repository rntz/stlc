open import Level
import Data.Empty
import Data.Sum

module CategorifiedSTLC where

-- We start with some preorder theory, or, as I think of it: lawless category theory.
record Cat i j : Set (suc (i ⊔ j)) where
  infix  1 Hom
  infixr 9 compo
  field Obj : Set i
  field Hom : (a b : Obj) → Set j
  field ident : ∀{a} → Hom a a
  field compo : ∀{a b c} → Hom a b → Hom b c → Hom a c

open Cat public
open Cat {{...}} public using () renaming (Hom to _≤_; ident to id; compo to _•_)

-- Sets and functions form a category.
instance
  sets : Cat _ _
  Obj sets = Set
  Hom sets A B = A → B
  ident sets x = x
  compo sets f g x = g (f x)

-- Monotone maps, or as I think of them, lawless functors.
record Fun {i j k l} (C : Cat i j) (D : Cat k l) : Set (i ⊔ j ⊔ k ⊔ l) where
  field ap  : Obj C → Obj D
  field map : ∀{a b} → Hom C a b → Hom D (ap a) (ap b)

open Fun public

-- The pointwise ordering on monotone maps; or, the lawless category of lawless
-- functors and lawless natural transformations. Yeehaw!
funs : ∀ {i j k l} → Cat i j → Cat k l → Cat _ _
funs C D .Obj = Fun C D
funs C D .Hom F G = ∀ {x} → Hom D (ap F x) (ap G x)
funs C D .ident = ident D
funs C D .compo F≤G G≤H = compo D F≤G G≤H

-- That a preorder forms a join-semilattice, or that a lawless category has
-- lawless cartesian coproducts and a lawless initial element.
record Sums {i} {j} (C : Cat i j) : Set (i ⊔ j) where
  private instance the-cat = C
  infixr 2 Either
  field Either : (a b : Obj C) → Obj C
  field in₁ : ∀{a b} → a ≤ Either a b
  field in₂ : ∀{a b} → b ≤ Either a b
  field either : ∀{a b c} → a ≤ c → b ≤ c → Either a b ≤ c
  field ⊥ : Obj C
  field ⊥-elim : ∀{a} → ⊥ ≤ a

  map∨ : ∀{a b c d} -> a ≤ c -> b ≤ d -> Either a b ≤ Either c d
  map∨ f g = either (f • in₁) (g • in₂)

open Sums public using (Either; either)
module _ {i j} {{C : Cat i j}} {{S : Sums C}} where
  open Sums S public renaming (Either to _∨_; either to [_,_])

instance
  set-sums : Sums sets
  Either set-sums = Data.Sum._⊎_
  Sums.in₁ set-sums = Data.Sum.inj₁
  Sums.in₂ set-sums = Data.Sum.inj₂
  either set-sums = Data.Sum.[_,_]
  Sums.⊥ set-sums = Data.Empty.⊥
  Sums.⊥-elim set-sums ()


-- Types. We have two base types and a subtyping relationship between them, ℕ ≤ ℤ.
infixr 6 _⊃_
data Type : Set where
  ℕ ℤ : Type
  _⊃_ : Type → Type → Type

-- The subtyping relation.
data _<:_ : Type → Type → Set where
  <:refl : ∀{a} → a <: a
  ℕ<:ℤ : ℕ <: ℤ
  <:⊃ : ∀{a1 a2 b1 b2} → a2 <: a1 → b1 <: b2 → (a1 ⊃ b1) <: (a2 ⊃ b2)

instance
  -- Types form a preorder under subtyping.
  types : Cat _ _
  Obj types = Type
  Hom types = _<:_
  ident types = <:refl
  compo types <:refl b≤c = b≤c
  compo types ℕ<:ℤ <:refl = ℕ<:ℤ
  compo types (<:⊃ a₂≤a₁ b₁≤b₂) (<:⊃ a₃≤a₂ b₂≤b₃)
    = <:⊃ (a₃≤a₂ • a₂≤a₁) (b₁≤b₂ • b₂≤b₃)
  compo types a≤b <:refl = a≤b

  -- Contexts are just monotone maps from types under subtyping into Set.
  cxs : Cat _ _
  cxs = funs types sets

Cx : Set1
Cx = Obj cxs -- = Fun types sets

infix 4 _∈_
_∈_ : Type → Cx → Set
a ∈ X = ap X a

-- A context renaming ρ : X ⊆ Y maps every variable in X into a variable of
-- the same type in Y, i.e. X ⊆ Y = ∀{a : Type} → a ∈ X → a ∈ Y.
infix 1 _⊆_
_⊆_ : Cx → Cx → Set
_⊆_ = Hom cxs

-- Contexts form a semilattice under union.
instance
  cx-sums : Sums cxs
  Either cx-sums X Y .ap a = a ∈ X ∨ a ∈ Y
  Either cx-sums X Y .map b≤c = map∨ (map X b≤c) (map Y b≤c)
  Sums.in₁ cx-sums = in₁
  Sums.in₂ cx-sums = in₂
  either cx-sums X Y = [ X , Y ]
  -- The empty context sends all types to ⊥: there are no variables of any type.
  Sums.⊥ cx-sums .ap a = ⊥
  Sums.⊥ cx-sums .map _ ()
  Sums.⊥-elim cx-sums ()

-- A singleton context containing a hypothesis of type `a` maps the type `b` to
-- the set of proofs that `a` is a subtype of `b`.
hyp : Type → Cx
hyp a .ap b = a <: b
hyp a .map b≤c a≤b = a≤b • b≤c

_∷_ : Type → Cx → Cx
a ∷ X = hyp a ∨ X


---------- Terms ----------
infix 1 _⊢_
data _⊢_ (X : Cx) : Type → Set where
  var : ∀{a} (x : a ∈ X) → X ⊢ a
  lam : ∀{a b} (M : (a ∷ X) ⊢ b) → X ⊢ a ⊃ b
  app : ∀{a b} (M : X ⊢ a ⊃ b) (N : X ⊢ a) → X ⊢ b

-- Applying a context renaming to a term.
rename : ∀{X Y} → X ⊆ Y → ∀{a} → X ⊢ a → Y ⊢ a
rename ρ (var x) = var (ρ x)
-- (map∨ id ρ) makes ρ "pass over" the variable introduced by `lam`.
rename ρ {a ⊃ b} (lam M) = lam (rename (map∨ id ρ) M)
rename ρ (app M N) = app (rename ρ M) (rename ρ N)

-- Applying a subtyping to a term
subsume : ∀{X a b} → a <: b → X ⊢ a → X ⊢ b
subsume <:refl M = M
subsume {X} a<:b (var x) = var (map X a<:b x)
subsume (<:⊃ a₂<:a₁ b₁<:b₂) (lam M) =
  lam (rename (map∨ (_•_ a₂<:a₁) id) (subsume b₁<:b₂ M))
subsume a<:b (app M N) = app (subsume (<:⊃ <:refl a<:b) M) N


---------- Substitutions on terms ----------
infix 1 _⊢*_
_⊢*_ : Cx → Cx → Set
X ⊢* Y = ∀ {a} → a ∈ Y → X ⊢ a

∷/⊢* : ∀{X} Y → X ⊢* Y → ∀{a} → a ∷ X ⊢* a ∷ Y
∷/⊢* _ σ = [ in₁ • var , σ • rename in₂ ]

sub : ∀{X Y a} → Y ⊢* X → X ⊢ a → Y ⊢ a
sub σ (var x) = σ x
sub {X} σ (lam M) = lam (sub (∷/⊢* X σ) M)
sub σ (app M N) = app (sub σ M) (sub σ N)

-- The category of contexts & substitutions.
substs : Cat _ _
Obj substs = Cx
Hom substs = _⊢*_
ident substs = var
compo substs σ τ = τ • sub σ

-- Renamings yield substitutions
⊆→⊢* : ∀{X Y} → Y ⊆ X → X ⊢* Y
⊆→⊢* ρ = ρ • var
