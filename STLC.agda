open import Level renaming (zero to lzero; suc to lsuc)

open import Algebra using (module Monoid)
open import Data.Empty
open import Data.Nat
open import Data.Product
open import Data.Sum hiding (map)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

-- UH OH
-- problem: Type is uninhabitable, because it has no base case!
infixr 6 _⊃_
data Type : Set where
  base : Type -> Type
  _⊃_ : Type -> Type -> Type

-- Proof that the existence of any type produces absurdity.
¬Type : Type -> ⊥
¬Type (base a) = ¬Type a
¬Type (a ⊃ b) = ¬Type a


---------- Contexts ----------
Cx : Set1
Cx = Type -> Set

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

-- Context renamings
infix 1 _⊆_
_⊆_ : Cx -> Cx -> Set
X ⊆ Y = ∀ {a} -> X a -> Y a

∪/⊆ : ∀ {X L R} -> L ⊆ R -> X ∪ L ⊆ X ∪ R
∪/⊆ f = Data.Sum.map id f

∷/⊆ : ∀ L {R a} -> L ⊆ R -> a ∷ L ⊆ a ∷ R
∷/⊆ _ = ∪/⊆


---------- Terms ----------
infix 1 _⊢_
data _⊢_ (X : Cx) : Type -> Set where
  var : ∀{a} (x : a ∈ X) -> X ⊢ a
  lam : ∀{a b} (M : a ∷ X ⊢ b) -> X ⊢ a ⊃ b
  app : ∀{a b} (M : X ⊢ a ⊃ b) (N : X ⊢ a) -> X ⊢ b

-- Renaming
rename : ∀{X Y a} -> X ⊆ Y -> X ⊢ a -> Y ⊢ a
rename f (var x) = var (f x)
rename {X} f (lam M) = lam (rename (∷/⊆ X f) M)
rename f (app M N) = app (rename f M) (rename f N)


---------- Normal and neutral terms ----------
infix 1 _⇐_ _⇒_
mutual
  data _⇐_ (X : Cx) : Type -> Set where
    lam : ∀{a b} (M : a ∷ X ⇐ b) -> X ⇐ a ⊃ b
    -- allowing neutral terms only at base type enforces η-longness. if we
    -- allowed neutral terms at any type, we'd be β-short (no reducible
    -- expressions), but not η-long: that is, a term of type A -> B (in a
    -- nonempty context) might not be a lambda.
    neu : ∀{a} (R : X ⇒ base a) -> X ⇐ base a

  data _⇒_ (X : Cx) : Type -> Set where
    var : ∀{a} -> a ∈ X -> X ⇒ a
    app : ∀{a b} (R : X ⇒ a ⊃ b) (M : X ⇐ a) -> X ⇒ b

rename⇐ : ∀{X Y a} -> X ⊆ Y -> X ⇐ a -> Y ⇐ a
rename⇒ : ∀{X Y a} -> X ⊆ Y -> X ⇒ a -> Y ⇒ a
rename⇐ {X} r (lam M) = lam (rename⇐ (∷/⊆ X r) M)
rename⇐ r (neu R) = neu (rename⇒ r R)
rename⇒ r (var x) = var (r x)
rename⇒ r (app R M) = app (rename⇒ r R) (rename⇐ r M)


---------- Normalisation by evaluation ----------
-- Based on a talk by Sam Lindley from 2016:
-- http://homepages.inf.ed.ac.uk/slindley/nbe/nbe-cambridge2016.pdf

-- module Semantics {i} (Base : Type -> Set i) where
--   -- Denotation of types.
--   set : Type -> Set _
--   set (base a) = Base a
--   set (a ⊃ b) = set a -> set b

-- --   set2 : Cx -> Type -> Set _
-- --   set2 X base = {!!}
-- --   set2 X (a ⊃ b) = {!!}

--   set* : Cx -> Set _
--   -- set* X = ∀ {a} (x : a ∈ X) -> set a
--   set* X = All (λ a -> set a) X

--   extend : ∀{X a} -> set a -> set* X -> set* (a ∷ X)
--   -- extend v ρ here = v
--   -- extend v ρ (next y) = ρ y
--   extend v ρ = v ∷ ρ

--   -- Denotation of terms
--   den : ∀{X a} -> X ⊢ a -> set* X -> set a
--   den (var x) ρ = lookup ρ x
--   den {X} (lam M) ρ v = den M (extend {X} v ρ)
--   den (app M N) ρ = den M ρ (den N ρ)


-- HOLY SHIT IT WORKS
module ReifySimple where
  [_⊢_] : Cx -> Type -> Set1
  [ X ⊢ base a ] = Lift (X ⇒ base a)
  [ X ⊢ a ⊃ b ] = ∀ {Y} -> X ⊆ Y -> [ Y ⊢ a ] -> [ Y ⊢ b ]

  reify : ∀ {X} a -> [ X ⊢ a ] -> X ⇐ a
  reflect : ∀ {X} a -> X ⇒ a -> [ X ⊢ a ]
  reify (base a) (lift x) = neu x
  reify (a ⊃ b) f = lam (reify b (f next (reflect a (var here))))
  reflect (base a) R = lift R
  reflect (a ⊃ b) R X⊆Y x = reflect b (app (rename⇒ X⊆Y R) (reify a x))

-- 
-- -- Reify & reflect, parameterized over a given semantics
-- record ReifySem i : Set (lsuc i) where
--   field
--     [_⊢_] : Cx -> Type -> Set i
--     weaken : ∀{X a c} -> [ X ⊢ c ] -> [ a ∷ X ⊢ c ]
--     baseI : ∀{X a} -> X ⇒ base a -> [ X ⊢ base a ]
--     baseE : ∀{X a} -> [ X ⊢ base a ] -> X ⇒ base a
--     ⊃I : ∀{X a b} -> (∀ {Y} -> X ⊆ Y -> [ Y ⊢ a ] -> [ Y ⊢ b ]) -> [ X ⊢ a ⊃ b ]
--     ⊃E : ∀{X a b} -> [ X ⊢ a ⊃ b ] -> [ X ⊢ a ] -> [ X ⊢ b ]

--   reify : ∀ {X} a -> [ X ⊢ a ] -> X ⇐ a
--   reflect : ∀ {X} a -> X ⇒ a -> [ X ⊢ a ]
--   reify (base a) x = neu (baseE x)
--   reify {X} (a ⊃ b) f = lam (reify b (⊃E (weaken {c = a ⊃ b} f) (reflect a (var here))))
--   reflect (base a) R = baseI R
--   reflect (a ⊃ b) R = ⊃I (λ X⊆Y x -> reflect b (app (rename⇒ X⊆Y R) (reify a x)))
