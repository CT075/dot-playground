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

val-unique : ∀{n} {H : Env n} {τ : Type n} →
  (τval₁ : H ⊢ τ val) → (τval₂ : H ⊢ τ val) → τval₁ ≡ τval₂
val-unique v-top v-top = refl
val-unique v-bot v-bot = refl
val-unique v-all v-all = refl
val-unique v-abs v-abs = refl
val-unique (v-arr A₁ B₁) (v-arr A₂ B₂)
  rewrite val-unique A₁ A₂ | val-unique B₁ B₂ = refl

⟱-spec : ∀{n gas} {H : Env n} {A τ : Type n} →
  H ⊢ A ⟱[ gas ] τ → H ⊢ τ val
⟱-spec {_} {_} {H} (eval-var {x} {v} p) rewrite p = Val.proof v
⟱-spec eval-⊤ = v-top
⟱-spec eval-⊥ = v-bot
⟱-spec eval-∀' = v-all
⟱-spec eval-ƛ = v-abs
⟱-spec (eval-arr pA pB) = v-arr (⟱-spec pA) (⟱-spec pB)
⟱-spec (eval-app pA pB pAB) = ctx-subst-val (⟱-spec pAB)

⟱-unique : ∀{n gas₁ gas₂} {H : Env n} {A τ₁ τ₂ : Type n} →
  H ⊢ A ⟱[ gas₁ ] τ₁ → H ⊢ A ⟱[ gas₂ ] τ₂ → τ₁ ≡ τ₂
⟱-unique eval-⊤ eval-⊤ = refl
⟱-unique eval-⊥ eval-⊥ = refl
⟱-unique eval-∀' eval-∀' = refl
⟱-unique eval-ƛ eval-ƛ = refl
⟱-unique (eval-arr A₁ B₁) (eval-arr A₂ B₂)
  rewrite ⟱-unique A₁ A₂ | ⟱-unique B₁ B₂ = refl
⟱-unique {n} {a} {b} {H} {A ∙ B} {_} {_}
  (eval-app {A₁} {B₁} {A'₁} {β₁} {τ₁} {K₁} {a₁} {b₁} {βval₁} {n₁}
    A⟱ƛKA₁' B⟱β₁ A₁'⟱τ₁)
  (eval-app {A₂} {B₂} {A'₂} {β₂} {τ₂} {K₂} {a₂} {b₂} {βval₂} {n₂}
    A⟱ƛKA₂' B⟱β₂ A₂'⟱τ₂) =
      todo
  where
    ƛKA₁'≡ƛKA₂' = ⟱-unique A⟱ƛKA₁' A⟱ƛKA₂'
    β₁≡β₂ = ⟱-unique B⟱β₁ B⟱β₂

    {-
    βval₁≡βval₂ : βval₁ ≡ βval₂
    βval₁≡βval₂ rewrite β₁≡β₂ = val-unique βval₁ βval₂
    -}

    postulate
      todo : plugTy τ₁ β₁ ≡ plugTy τ₂ β₂
⟱-unique {n} {0} {0} {H} {Var x} {τ₁} {τ₂}
  (eval-var {x} {v₁} p₁) (eval-var {x} {v₂} p₂) =
    todo
  where
    postulate
      todo : Val.this v₁ ≡ Val.this v₂
