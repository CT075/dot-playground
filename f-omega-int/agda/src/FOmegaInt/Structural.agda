module FOmegaInt.Structural where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc; inject₁)

open import Data.Context
open import FOmegaInt.Syntax renaming (lookup to lookupKd)
open import FOmegaInt.Typing
open import FOmegaInt.Reduction

private
  injectTy : ∀{n} → Type n → Type (suc n)
  injectKd : ∀{n} → Kind n → Kind (suc n)

  injectTy (Var x) = Var (inject₁ x)
  injectTy ⊤ = ⊤
  injectTy ⊥ = ⊥
  injectTy (τ₁ ⇒ τ₂) = injectTy τ₁ ⇒ injectTy τ₂
  injectTy (∀' k τ) = ∀' (injectKd k) (injectTy τ)
  injectTy (ƛ k τ) = ƛ (injectKd k) (injectTy τ)
  injectTy (τ₁ ∙ τ₂) = injectTy τ₁ ∙ injectTy τ₂

  injectKd ✶ = ✶
  injectKd (τ₁ ∙∙ τ₂) = injectTy τ₁ ∙∙ injectTy τ₂
  injectKd (ℿ K J) = ℿ (injectKd K) (injectKd J)

liftTyUnder : ∀{n} → Fin (suc n) → Type n → Type (suc n)
liftKdUnder : ∀{n} → Fin (suc n) → Kind n → Kind (suc n)

liftTyUnder n ⊤ = ⊤
liftTyUnder n ⊥ = ⊥
liftTyUnder n (t₁ ⇒ t₂) = liftTyUnder n t₁ ⇒ liftTyUnder n t₂
liftTyUnder n (∀' K t) = ∀' (liftKdUnder n K) (liftTyUnder (suc n) t)
liftTyUnder n (ƛ K t) = ƛ (liftKdUnder n K) (liftTyUnder (suc n) t)
liftTyUnder n (t₁ ∙ t₂) = liftTyUnder n t₁ ∙ liftTyUnder n t₂
liftTyUnder zero (Var x) = Var (suc x)
liftTyUnder (suc n) (Var zero) = Var zero
liftTyUnder (suc n) (Var (suc i)) = weakenTy (liftTyUnder n (Var i))

liftKdUnder n ✶ = ✶
liftKdUnder n (t₁ ∙∙ t₂) = liftTyUnder n t₁ ∙∙ liftTyUnder n t₂
liftKdUnder n (ℿ K J) = ℿ (liftKdUnder n K) (liftKdUnder (suc n) J)

-- TODO
postulate
  weaken-kinding : ∀{n} {Γ : Context n} {τ : Type n} {K K'} →
    Γ ⊢ty τ ∈ K → K' ∷ Γ ⊢ty (weakenTy τ) ∈ (weakenKd K)

{-
weaken-isKind-under wf-type i = wf-type
weaken-isKind-under (wf-intv pA pB) i =
  wf-intv (weaken-kinding-under pA i) (weaken-kinding-under pB i)
weaken-isKind-under (wf-darr pK pJ) i {K'} =
  wf-darr
    (weaken-isKind-under pK i)
    {!!}

weaken-kinding-under (k-var x x₁) = {! !}
weaken-kinding-under k-top i = k-top
weaken-kinding-under k-bot i = k-bot
weaken-kinding-under (k-arr pA pB) i = k-arr (weaken-kinding-under pA) (weaken-kinding-under pB)
weaken-kinding-under {n} {Γ} {τ} {✶} {K'} (k-all {K} {A} pk pA) i = {!!}
weaken-kinding-under (k-abs x x₁ rule) i = {! !}
weaken-kinding-under (k-app rule rule₁ x x₁) i = {! !}
weaken-kinding-under (k-sing rule) i = {! !}
weaken-kinding-under (k-sub rule x) i = {! !}
-}
