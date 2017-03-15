open import Level renaming (zero to lzero; suc to lsuc)

open import Algebra using (module Monoid)
open import Data.Empty
open import Data.Nat
open import Data.Product
open import Data.Sum hiding (map)
open import Function
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

-- Context renamings
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


---------- Normalisation by evaluation ----------
-- Based on a talk by Sam Lindley from 2016:
-- http://homepages.inf.ed.ac.uk/slindley/nbe/nbe-cambridge2016.pdf
--
-- Adapted to handle terms with explicitly typed contexts (Sam's slides only
-- consider "open" terms with unspecified environments). It was a pain in the
-- ass to figure out.

module ContextNBE where
  [_⊢_] : Cx -> Type -> Set1
  [ X ⊢ base ] = Lift (X ⇒ base)
  [ X ⊢ a ⊃ b ] = ∀ {Y} -> [ Y ⊢ a ] -> [ Y ∪ X ⊢ b ]

  -- An alternative definition would be:
  --
  --     [ X ⊢ a ⊃ b ] = ∀ {Y} (s : X ⊆ Y) -> [ Y ⊢ a ] -> [ Y ⊢ b ]
  --
  -- I prefer the one with ∪ because it's more precise about what the function
  -- does to variable bindings. I'm not sure if there's any principled reason to
  -- prefer one to the other.

  rename* : ∀{X Y} (s : X ⊆ Y) {a} -> [ X ⊢ a ] -> [ Y ⊢ a ]
  rename* s {base} (lift x) = lift (rename⇒ s x)
  rename* {X} s {a ⊃ b} f {Z} x = rename* (∪/⊆ Z X s) {b} (f x)
  -- rename* {X} X⊆Y {a ⊃ b} f {Z} Y⊆Z x = f (Y⊆Z ∘ X⊆Y) x

  reify : ∀ {X} a -> [ X ⊢ a ] -> X ⇐ a
  reflect : ∀ {X} a -> X ⇒ a -> [ X ⊢ a ]
  reify base (lift x) = neu x
  reify {X} (a ⊃ b) f = lam (reify b (f (reflect a (var refl))))
  -- reify {X} (a ⊃ b) f = lam (reify b (f next (reflect a (var here))))
  reflect base R = lift R
  reflect (a ⊃ b) R x = reflect b (app (rename⇒ inj₂ R) (rename⇐ inj₁ (reify a x)))
  -- reflect (a ⊃ b) R X⊆Y x = reflect b (app (rename⇒ X⊆Y R) (reify a x))

  -- Environments, or semantic substitutions
  [_⊢*_] : Cx -> Cx -> Set1
  [ X ⊢* Y ] = ∀{a} -> a ∈ Y -> [ X ⊢ a ]

  -- We use this weird-ass denotation. 
  den : ∀{X a} -> X ⊢ a -> ∀ {Y} -> [ Y ⊢* X ] -> [ Y ⊢ a ]
  den (var x) ρ = ρ x
  den (lam M) ρ v = den M σ
    where σ : [ _ ∪ _ ⊢* _ ∷ _ ]
          σ (inj₁ refl) = rename* inj₁ v
          σ (inj₂ y) = rename* inj₂ (ρ y)
  den (app M N) {Y} ρ = rename* (dedup Y) (den M ρ (den N ρ))

  id* : ∀ {X} -> [ X ⊢* X ]
  id* x = reflect _ (var x)

  normalize : ∀{X a} -> X ⊢ a -> X ⇐ a
  normalize M = reify _ (den M id*)


-- module BrokenWeirdNBE where
--   [_⊢_] : Cx -> Type -> Set1
--   [ X ⊢ base ] = Lift (X ⇒ base)
--   [ X ⊢ a ⊃ b ] = ∀ {Y} (s : X ⊆ Y) -> [ Y ⊢ a ] -> [ Y ⊢ b ]

--   reify : ∀ {X} a -> [ X ⊢ a ] -> X ⇐ a
--   reflect : ∀ {X} a -> X ⇒ a -> [ X ⊢ a ]
--   reify base (lift x) = neu x
--   reify (a ⊃ b) f = lam (reify b (f next (reflect a (var here))))
--   reflect base R = lift R
--   reflect (a ⊃ b) R X⊆Y x = reflect b (app (rename⇒ X⊆Y R) (reify a x))

--   Lam : ∀{X a b} -> [ a ∷ X ⊢ b ] -> [ X ⊢ a ⊃ b ]
--   Lam body s x = {!reify _ body!}

--   den : ∀{X a} -> X ⊢ a -> [ X ⊢ a ]
--   den (var v) = reflect _ (var v)
--   -- den (lam M) X⊆Y x = {!reify _ (den M)!}
--   den (lam M) = Lam (den M)
--   den (app M N) = den M id (den N)


---------- Normalisation by evaluation ----------
-- Based on a talk by Sam Lindley from 2016:
-- http://homepages.inf.ed.ac.uk/slindley/nbe/nbe-cambridge2016.pdf
--
-- crap, this approach is impossible too!
-- you just can't use terms with intrinsic contexts!
-- you need *named* variables.
module SamNBE where
  NF NE : Type -> Set1
  NF a = Σ[ X ∈ Cx ] (X ⇐ a)
  NE a = Σ[ X ∈ Cx ] (X ⇒ a)

  open Semantics (NE base) public

  Lam : ∀{a b} -> (NE a -> NF b) -> NF (a ⊃ b)
  Lam {a} body with body (hyp _ , var refl)
  ... | X , M = X , lam {!M!}

  -- this is hopeless as well.
  App : ∀{a b} -> NE (a ⊃ b) -> NF a -> NE b
  App (X , R) (Y , M) = {!!}

  reify : ∀ a -> set a -> NF a
  reflect : ∀ a -> NE a -> set a
  reify base (X , R) = X , neu R
  reify (a ⊃ b) f = Lam (λ x -> reify b (f (reflect a x)))
  reflect base R = R
  reflect (a ⊃ b) R x = reflect b (App R (reify a x))


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
