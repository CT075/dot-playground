module Data.Context.Lemmas where

open import Data.Fin using (Fin; suc; zero; opposite; toℕ)
open import Data.Fin.Properties
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality as PropEq

open import Data.Context.Base

-- TODO
{-
module _ {ℓ} (T : Pred ℕ ℓ) (ext : Extension T) where
  open WeakenOps T ext public

  roundtripᵣ-idₗ : ∀{x} → roundtripᵣ x ≡ x
  roundtripᵣ-idₗ = refl

  insertUnder-zero : ∀{n} → (Γ : Ctx T n) → (x : T n) →
    insertUnder Γ zero (roundtripᵣ x) ≡ x ∷ Γ
  insertUnder-zero Γ x = {!!}
-}
