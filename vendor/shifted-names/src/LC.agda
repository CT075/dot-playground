module LC where

open import Data.Var

data Term : Set where
  V : Var → Term
  _∙_ : Term → Term → Term
  ƛ : Term → Term

lift : (Var → Var) → Term → Term
lift f (V v) = V (f v)
lift f (a ∙ b) = lift f a ∙ lift f b
lift f (ƛ t) = ƛ (lift f t)

L : Lift Term
L = record {lift = lift}

open Lift L

subst : (Var → Term) → Term → Term
subst f (V v) = f v
subst f (a ∙ b) = subst f a ∙ subst f b
subst f (ƛ t) = ƛ (subst f t)

open Subst (record {lift = L; var = V; subst = subst})

infix 4 _∼>_

data _∼>_ : Term → Term → Set where
  -- This is equivalent to [bindT t₁ t₂] by [close-open-id], but we use the
  -- full opening and closing for demonstration
  β : ∀{t₁ t₂} → (ƛ t₁) ∙ t₂ ∼> bindT t₁ (closeT "x" (openT "x" t₂))

