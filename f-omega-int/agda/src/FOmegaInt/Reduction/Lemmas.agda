module FOmegaInt.Reduction.Lemmas where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

open import FOmegaInt.Syntax
open import FOmegaInt.Reduction.Base

⟱-spec : ∀{n gas} {H : Env n} {t : Type n} {τ : Type n} →
  H ⊢ t ⟱[ gas ] τ → H ⊢ τ val
⟱-spec (eval-var {x} {v} p) = {! !}
⟱-spec eval-⊤ = v-top
⟱-spec eval-⊥ = v-bot
⟱-spec eval-∀' = v-all
⟱-spec eval-ƛ = v-abs
⟱-spec (eval-arr pA pB) = v-arr (⟱-spec pA) (⟱-spec pB)
⟱-spec (eval-app e e₁ e₂) = {! !}
