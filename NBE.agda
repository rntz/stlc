module NBE where

---------- Normalisation by evaluation ----------
-- Based on a talk by Sam Lindley from 2016:
-- http://homepages.inf.ed.ac.uk/slindley/nbe/nbe-cambridge2016.pdf
--
-- Adapted to handle terms with explicitly typed contexts (Sam's slides only
-- consider open terms with the environments left implicit/untyped). This was a
-- pain in the ass to figure out.

open import Level
open import Function using (id; _∘_)

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

rename : ∀{X Y} (s : X ⊆ Y) {a} -> [ X ⊢ a ] -> [ Y ⊢ a ]
rename s {base} (lift x) = lift (rename⇒ s x)
rename s {a ⊃ b} f t = f (t ∘ s)

reify   : ∀{a X} -> [ X ⊢ a ] -> X ⇐ a
reflect : ∀{a X} -> X ⇒ a -> [ X ⊢ a ]
reify   {base}      = neu ∘ lower
reify   {a ⊃ b} f   = lam (reify (f next (reflect (var here))))
reflect {base}      = lift
reflect {a ⊃ b} R s = reflect ∘ app (rename⇒ s R) ∘ reify

-- Environments, or semantic substitutions.
[_⊢*_] : Cx -> Cx -> Set1
[ X ⊢* Y ] = ∀{a} -> a ∈ Y -> [ X ⊢ a ]

extend : ∀{X Y a} -> [ Y ⊢* X ] -> [ Y ⊢ a ] -> [ Y ⊢* a ∷ X ]
extend ρ x here = x
extend ρ x (next v) = ρ v

id* : ∀ {X} -> [ X ⊢* X ]
id* = reflect ∘ var

-- We define a slightly strange "denotation" for open terms: Rather than going
-- straight to semantic terms, they take a semantic substitution!
--
-- I'm still not entirely sure if this is necessary, but it's simple to define,
-- and I haven't found a simple alternative. The obvious approach makes the
-- `lam` case difficult; it wants a substitution lemma for semantic terms.
den : ∀{X a} -> X ⊢ a -> ∀ {Y} -> [ Y ⊢* X ] -> [ Y ⊢ a ]
den (var x) ρ = ρ x
den (lam M) ρ s x = den M (extend (rename s ∘ ρ) x)
den (app M N) ρ = den M ρ id (den N ρ)

normalize : ∀{X a} -> X ⊢ a -> X ⇐ a
normalize M = reify (den M id*)
