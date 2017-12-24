-- A simply-typed lambda calculus, and a definition of normalisation by
-- evaluation for it.
--
-- The NBE implementation is based on a presentation by Sam Lindley from 2016:
-- http://homepages.inf.ed.ac.uk/slindley/nbe/nbe-cambridge2016.pdf
--
-- Adapted to handle terms with explicitly typed contexts (Sam's slides only
-- consider open terms with the environments left implicit/untyped). This was a
-- pain in the ass to figure out.

module MinimalNBE where

open import Level
open import Data.Empty
open import Data.Sum hiding (map)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

-- We have a base type, and functions. That's it.
infixr 6 _⊃_
data Type : Set where
  base : Type
  _⊃_ : Type -> Type -> Type


---------- Contexts ----------
-- Contexts map types to the set of free variables of that type.
-- I use variables X, Y, Z for contexts; traditional notation is Γ, Δ, etc.
Cx : Set1
Cx = Type -> Set

-- For readability, a ∈ X is the set of variables of type a in the context X.
infix 4 _∈_
_∈_ : Type -> Cx -> Set
a ∈ X = X a

-- The empty context maps all types to the empty set.
∅ : Cx
∅ _ = ⊥

-- (hyp a) is a singleton context, with one variable of type a. For this we use
-- propositional equality; (b ∈ hyp a) is (a ≡ b), which has a unique inhabitant
-- `refl` iff a and b are the same type.
hyp : Type -> Cx
hyp = _≡_

-- The disjoint union of two contexts is simply a pointwise sum.
infixr 4 _∪_
_∪_ : Cx -> Cx -> Cx
(X ∪ Y) a = X a ⊎ Y a

-- Usually our contexts are right-branching unions, (hyp a ∪ (hyp b ∪ ... ∪ ∅)).
-- With some sugar, this becomes (a ∷ b ∷ ... ∷ ∅).
infixr 4 _∷_
_∷_ : Type -> Cx -> Cx
a ∷ X = hyp a ∪ X

-- When our contexts are right-branching unions, (a ∷ b ∷ ... ∷ ∅), then our
-- variables are always of the form (inj₂ ... (inj₂ (inj₁ refl))); the number of
-- repetitions of inj₂ is the position of the variable in the context. This is a
-- form of DeBruijn notation. Some pattern synonyms make this connection
-- explicit; our variables now look like (next ... (next here)).
pattern here = inj₁ refl
pattern next x = inj₂ x


---------- Terms ----------
infix 1 _⊢_
data _⊢_ (X : Cx) : Type -> Set where
  var : ∀{a} (x : a ∈ X) -> X ⊢ a
  lam : ∀{a b} (M : a ∷ X ⊢ b) -> X ⊢ a ⊃ b
  app : ∀{a b} (M : X ⊢ a ⊃ b) (N : X ⊢ a) -> X ⊢ b

---------- Normal and neutral terms ----------
-- I use M, N, O for normal terms and R, S, Q for neutral terms.
-- Lindley's presentation uses M for normal and N for neutral.
infix 1 _⇐_ _⇒_
mutual
  -- Normal/canonical/checking terms; introduction forms.
  data _⇐_ (X : Cx) : Type -> Set where
    lam : ∀{a b} (M : a ∷ X ⇐ b) -> X ⇐ a ⊃ b
    -- Allowing neutral terms to be normal only at base type enforces
    -- η-longness. if we allowed it at any type, we'd be β-short (no reducible
    -- expressions), but not η-long: an (open) term of type A ⊃ B might not be a
    -- lambda.
    --
    -- Sam Lindley's presentation calls β-short η-long "extensional" and merely
    -- β-short "intensional". So we're "extensional".
    neu : (R : X ⇒ base) -> X ⇐ base

  -- Neutral/atomic/synthesizing terms; elimination forms.
  data _⇒_ (X : Cx) : Type -> Set where
    var : ∀{a} -> a ∈ X -> X ⇒ a
    app : ∀{a b} (R : X ⇒ a ⊃ b) (M : X ⇐ a) -> X ⇒ b


---------- Context renamings ----------
-- (X ⊆ Y) is meant to suggest that the context X, imagined as a set of typed
-- variables, is a subset of Y.
--
-- Formally, it maps variables in X to same-typed variables in Y. In my
-- experience, separating renaming (variable-to-variable maps) from substitution
-- (variable-to-term maps) massively simplifies doing metatheory in Agda.
infix 1 _⊆_
_⊆_ : Cx -> Cx -> Set
X ⊆ Y = ∀ {a} -> X a -> Y a

-- Extending environments preserves renaming. If L ⊆ R, then a ∷ L ⊆ a ∷ R.
∷/⊆ : ∀ L {R a} -> L ⊆ R -> a ∷ L ⊆ a ∷ R
∷/⊆ _ f = Data.Sum.map id f

-- Renaming normal/neutral terms.
rename⇐ : ∀{X Y a} -> X ⊆ Y -> X ⇐ a -> Y ⇐ a
rename⇒ : ∀{X Y a} -> X ⊆ Y -> X ⇒ a -> Y ⇒ a
rename⇐ {X} r (lam M) = lam (rename⇐ (∷/⊆ X r) M)
rename⇐ r (neu R) = neu (rename⇒ r R)
rename⇒ r (var x) = var (r x)
rename⇒ r (app R M) = app (rename⇒ r R) (rename⇐ r M)


---------- Normalisation by Evaluation ----------
-- [ X ⊢ a ] is NBE's "semantic" version of (X ⊢ a).
[_⊢_] : Cx -> Type -> Set1
-- A semantic base term is a normal base term. Lift is necessary for inessential
-- Agda reasons.
[ X ⊢ base ] = Lift (X ⇒ base)
-- A semantic function term (a ⊃ b) is a map from semantic terms of type a to
-- semantic terms of type b. It also takes a renaming, to tell it what free
-- variables in its argument and in itself coincide.
--
-- This renaming is not present in Lindley's presentation, which I believe is
-- why he needs to produce fresh variables when reifying functions.
[ X ⊢ a ⊃ b ] = ∀ {Y} (s : X ⊆ Y) -> [ Y ⊢ a ] -> [ Y ⊢ b ]

-- Reify and reflect, the core of NBE.
-- Reify turns semantic terms into normal terms.
-- Reflect turns neutral terms into semantic terms.
reify   : ∀{a X} -> [ X ⊢ a ] -> X ⇐ a
reflect : ∀{a X} -> X ⇒ a -> [ X ⊢ a ]
reify   {base}      = neu ∘ lower
-- Below, `next` is a renaming that tells f (a semantic function term) that f
-- itself doesn't use the first variable - the one `lam` introduces. Stripped of
-- variable munging, this is:
--
--     reify f = λx. reify (f (reflect x))       -- where λ is syntactic.
reify   {a ⊃ b} f   = lam (reify (f next (reflect (var here))))
reflect {base}      = lift
-- Below, `s` is the renaming our semantic function takes to allow its argument
-- to have more variables than its body R. Stripped of variable munging, this
-- is:
--
--     reflect R = λx. reflect (app R (reify x)) -- where λ is semantic.
reflect {a ⊃ b} R s = reflect ∘ app (rename⇒ s R) ∘ reify


-- A little more legwork is necessary to define normalisation: we must turn
-- arbitrary terms (X ⊢ a) into the semantic terms [ X ⊢ a ] they denote. Then
-- we can apply reify to get normal terms (X ⇐ a).

-- Renaming semantic terms.
rename : ∀{X Y} (s : X ⊆ Y) {a} -> [ X ⊢ a ] -> [ Y ⊢ a ]
rename s {base} (lift x) = lift (rename⇒ s x)
rename s {a ⊃ b} f t = f (t ∘ s)

-- Environments, or semantic substitutions.
[_⊢*_] : Cx -> Cx -> Set1
[ X ⊢* Y ] = ∀{a} -> a ∈ Y -> [ X ⊢ a ]

-- Extending a substitution with a single variable-term mapping.
extend : ∀{X Y a} -> [ Y ⊢* X ] -> [ Y ⊢ a ] -> [ Y ⊢* a ∷ X ]
extend ρ x here = x
extend ρ x (next v) = ρ v

-- The identity substitution; maps variables to themselves.
id* : ∀ {X} -> [ X ⊢* X ]
id* = reflect ∘ var

-- We define a slightly strange "denotation" for open terms: Rather than going
-- straight to semantic terms, they take a semantic substitution.
--
-- I'm not sure this is necessary, but it's simple to define, and I haven't
-- found a nice alternative. The obvious approach makes the `lam` case
-- difficult; it wants a substitution lemma for semantic terms.
den : ∀{X a} -> X ⊢ a -> ∀ {Y} -> [ Y ⊢* X ] -> [ Y ⊢ a ]
den (var x) ρ = ρ x
den (lam M) ρ s x = den M (extend (rename s ∘ ρ) x)
den (app M N) ρ = den M ρ id (den N ρ)

-- And finally: normalisation by evaluation.
normalize : ∀{X a} -> X ⊢ a -> X ⇐ a
normalize M = reify (den M id*)
