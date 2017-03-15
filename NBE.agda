module NBE where

---------- Normalisation by evaluation ----------
-- Based on a talk by Sam Lindley from 2016:
-- http://homepages.inf.ed.ac.uk/slindley/nbe/nbe-cambridge2016.pdf
--
-- Adapted to handle terms with explicitly typed contexts (Sam's slides only
-- consider "open" terms with unspecified environments). This was a pain in the
-- ass to figure out.

open import Level renaming (zero to lzero; suc to lsuc)

open import Data.Sum hiding (map)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import STLC

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

reify : ∀ {X} a -> [ X ⊢ a ] -> X ⇐ a
reflect : ∀ {X} a -> X ⇒ a -> [ X ⊢ a ]
reify base (lift x) = neu x
reify {X} (a ⊃ b) f = lam (reify b (f (reflect a (var refl))))
reflect base R = lift R
reflect (a ⊃ b) R x = reflect b (app (rename⇒ inj₂ R) (rename⇐ inj₁ (reify a x)))

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
