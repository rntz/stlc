open import Level renaming (zero to lzero; suc to lsuc)

open import Algebra using (module Monoid)
open import Data.Empty
open import Data.List hiding ([_])
open import Data.List.All hiding (lookup; tabulate)
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


---------- Contexts ----------
Cx : Set
Cx = List Type

open Monoid (Data.List.monoid Type) using () renaming (assoc to ++-assoc)

infix 4 _∈_
data _∈_ (b : Type) : Cx -> Set where
  here : ∀{as} -> b ∈ b ∷ as
  next : ∀{a as} -> b ∈ as -> b ∈ a ∷ as

-- Context renamings
infix 1 _⊆_
_⊆_ : Cx -> Cx -> Set
X ⊆ Y = ∀ {a} -> a ∈ X -> a ∈ Y

∷/⊆ : ∀ {a L R} -> L ⊆ R -> a ∷ L ⊆ a ∷ R
∷/⊆ f here = here
∷/⊆ f (next x) = next (f x)

⊆++l : ∀ L {R} -> R ⊆ L ++ R
⊆++l [] = id
⊆++l (a ∷ as) x = next (⊆++l as x)


---------- Terms ----------
infix 1 _⊢_
data _⊢_ (X : Cx) : Type -> Set where
  var : ∀{a} (x : a ∈ X) -> X ⊢ a
  lam : ∀{a b} (M : a ∷ X ⊢ b) -> X ⊢ a ⊃ b
  app : ∀{a b} (M : X ⊢ a ⊃ b) (N : X ⊢ a) -> X ⊢ b

-- Renaming
rename : ∀{X Y a} -> X ⊆ Y -> X ⊢ a -> Y ⊢ a
rename f (var x) = var (f x)
rename {a = a ⊃ b} f (lam M) = lam (rename (∷/⊆ f) M)
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
rename⇐ r (lam M) = lam (rename⇐ (∷/⊆ r) M)
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
  [_⊢_] : Cx -> Type -> Set
  [ X ⊢ base a ] = X ⇒ base a
  [ X ⊢ a ⊃ b ] = ∀ {Y} -> X ⊆ Y -> [ Y ⊢ a ] -> [ Y ⊢ b ]

  reify : ∀ {X} a -> [ X ⊢ a ] -> X ⇐ a
  reflect : ∀ {X} a -> X ⇒ a -> [ X ⊢ a ]
  reify (base a) x = neu x
  reify (a ⊃ b) f = lam (reify b (f next (reflect a (var here))))
  reflect (base a) R = R
  reflect (a ⊃ b) R X⊆Y x = reflect b (app (rename⇒ X⊆Y R) (reify a x))


-- Reify & reflect, parameterized over a given semantics
record ReifySem i : Set (lsuc i) where
  field
    [_⊢_] : Cx -> Type -> Set i
    weaken : ∀{X a c} -> [ X ⊢ c ] -> [ a ∷ X ⊢ c ]
    baseI : ∀{X a} -> X ⇒ base a -> [ X ⊢ base a ]
    baseE : ∀{X a} -> [ X ⊢ base a ] -> X ⇒ base a
    ⊃I : ∀{X a b} -> (∀ {Y} -> X ⊆ Y -> [ Y ⊢ a ] -> [ Y ⊢ b ]) -> [ X ⊢ a ⊃ b ]
    ⊃E : ∀{X a b} -> [ X ⊢ a ⊃ b ] -> [ X ⊢ a ] -> [ X ⊢ b ]

  reify : ∀ {X} a -> [ X ⊢ a ] -> X ⇐ a
  reflect : ∀ {X} a -> X ⇒ a -> [ X ⊢ a ]
  reify (base a) x = neu (baseE x)
  reify {X} (a ⊃ b) f = lam (reify b (⊃E (weaken {c = a ⊃ b} f) (reflect a (var here))))
  reflect (base a) R = baseI R
  reflect (a ⊃ b) R = ⊃I (λ X⊆Y x -> reflect b (app (rename⇒ X⊆Y R) (reify a x)))


-- -- HOLY SHIT IT WORKS
-- module ReifyOld where
--   [_⊢_] : Cx -> Type -> Set
--   -- this is the only place I use the context. hmmmm.
--   [ X ⊢ base a ] = X ⇒ base a
--   -- I suspect this is insufficiently generic.
--   [ X ⊢ a ⊃ b ] = ∀ Y -> [ Y ++ X ⊢ a ] -> [ Y ++ X ⊢ b ]
--   -- TODO: Try instead:
--   -- [ X ⊢ a ⊃ b ] = ∀ {Y} -> X ⊆ Y -> [ Y ⊢ a ] -> [ Y ⊢ b ]

--   fux : ∀ {X a} -> [ X ⊢ base a ] -> X ⇒ base a
--   fux = λ z -> z
--   call : ∀ X a b -> [ X ⊢ a ⊃ b ] -> [ X ⊢ a ] -> [ X ⊢ b ]
--   call = λ X a b z → z []
--   weak : ∀ X Y c -> [ X ⊢ c ] -> [ Y ++ X ⊢ c ]
--   weak X Y (base c) x = rename⇒ (⊆++l Y) x
--   weak X Y (c ⊃ d) f Z = subst P (++-assoc Z Y X) (f (Z ++ Y))
--     where P = λ x -> [ x ⊢ c ] -> [ x ⊢ d ]

--   reify : ∀ {X} a -> [ X ⊢ a ] -> X ⇐ a
--   reflect : ∀ {X} a -> X ⇒ a -> [ X ⊢ a ]
--   reify (base a) x = neu (fux x)
--   reify {X} (a ⊃ b) f =
--     lam (reify b (call (a ∷ X) a b (weak X (a ∷ []) (a ⊃ b) f) (reflect a (var here))))
--   reflect (base a) R = R
--   -- reflect (a ⊃ b) R v = reflect b (app R (reify a v))
--   reflect (a ⊃ b) R Y v = reflect b (app (rename⇒ (⊆++l Y) R) (reify a v))
