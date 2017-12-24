module NBE2 where

---------- Normalisation by evaluation ----------
-- Based on a talk by Sam Lindley from 2016:
-- http://homepages.inf.ed.ac.uk/slindley/nbe/nbe-cambridge2016.pdf
--
-- Adapted to handle terms with explicitly typed contexts (Sam's slides only
-- consider "open" terms with unspecified environments). This was a pain in the
-- ass to figure out.

open import Level renaming (zero to lzero; suc to lsuc)

open import Function using (id; _∘_)
open import Data.Sum hiding (map)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import STLC

-- 2017-12-23: Is there an intuition for what this means?
-- [ X ⊢ a ] is a kind of "semantic" version of (X ⊢ a)
-- can I understand NBE w.r.t hereditary substitution?
[_⊢_] : Cx -> Type -> Set1
-- a semantic term of base type is a normal term of base type.
[ X ⊢ base ] = Lift (X ⇒ base)
-- a semantic term of function type (a ⊃ b) is a map from semantic terms of type
-- a to semantic terms of type b. It also takes a renaming, to tell it what free
-- variables in its argument and in itself coincide.
[ X ⊢ a ⊃ b ] = ∀ {Y} (s : X ⊆ Y) -> [ Y ⊢ a ] -> [ Y ⊢ b ]

-- An alternative definition would be:
--
--     [ X ⊢ a ⊃ b ] = ∀ {Y} -> [ Y ⊢ a ] -> [ Y ∪ X ⊢ b ]
--
-- I tried that first, but it makes the code more complex.

rename* : ∀{X Y} (s : X ⊆ Y) {a} -> [ X ⊢ a ] -> [ Y ⊢ a ]
rename* s {base} (lift x) = lift (rename⇒ s x)
rename* s {a ⊃ b} f t = f (t ∘ s)

reify : ∀ {X} a -> [ X ⊢ a ] -> X ⇐ a
reflect : ∀ {X} a -> X ⇒ a -> [ X ⊢ a ]
reify base (lift x) = neu x
reify (a ⊃ b) f = lam (reify b (f next (reflect a (var here))))
reflect base R = lift R
reflect (a ⊃ b) R s x = reflect b (app (rename⇒ s R) (reify a x))

-- Environments, or semantic substitutions
[_⊢*_] : Cx -> Cx -> Set1
[ X ⊢* Y ] = ∀{a} -> a ∈ Y -> [ X ⊢ a ]

-- We use this weird-ass denotation.
-- This reminds me of hereditary substitution somehow.
den : ∀{X a} -> X ⊢ a -> ∀ {Y} -> [ Y ⊢* X ] -> [ Y ⊢ a ]
den (var x) ρ = ρ x
den (lam M) ρ s x = den M σ
  where σ : [ _ ⊢* _ ∷ _ ]
        σ here = x
        σ (next v) = rename* s (ρ v)
den (app M N) ρ = den M ρ id (den N ρ)

id* : ∀ {X} -> [ X ⊢* X ]
id* x = reflect _ (var x)

normalize : ∀{X a} -> X ⊢ a -> X ⇐ a
normalize M = reify _ (den M id*)
