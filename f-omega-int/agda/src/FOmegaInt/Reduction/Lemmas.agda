module FOmegaInt.Reduction.Lemmas where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

open import FOmegaInt.Syntax
open import FOmegaInt.Reduction.Base

ctx-subst-val : ∀{n} {H : Env n} {τ : Type (suc n)} {τ' p} →
  (H , τ' [ p ]) ⊢ τ val → H ⊢ (plugTy τ τ') val
ctx-subst-val v-top = v-top
ctx-subst-val v-bot = v-bot
ctx-subst-val v-all = v-all
ctx-subst-val v-abs = v-abs
ctx-subst-val (v-arr pA pB) = v-arr (ctx-subst-val pA) (ctx-subst-val pB)

⟱-spec : ∀{n gas} {H : Env n} {t : Type n} {τ : Type n} →
  H ⊢ t ⟱[ gas ] τ → H ⊢ τ val
⟱-spec {_} {_} {H} (eval-var {x} {v} p) rewrite p = Val.proof v
⟱-spec eval-⊤ = v-top
⟱-spec eval-⊥ = v-bot
⟱-spec eval-∀' = v-all
⟱-spec eval-ƛ = v-abs
⟱-spec (eval-arr pA pB) = v-arr (⟱-spec pA) (⟱-spec pB)
⟱-spec (eval-app pA pB pAB) = ctx-subst-val (⟱-spec pAB)
