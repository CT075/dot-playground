module FOmegaInt.Reduction where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

open import Data.Context as C
open import FOmegaInt.Syntax hiding (Context; lookup)

{-
infix 4 _⊢_val

data _⊢_val {n} (H : Env n) : Type n → Set where
  v-top : H ⊢ ⊤ val
  v-bot : H ⊢ ⊥ val
  v-all : ∀{K A} → H ⊢ ∀' K A val
  v-abs : ∀{K A} → H ⊢ ƛ K A val
  v-arr : ∀{A B} → H ⊢ A val → H ⊢ B val → H ⊢ A ⇒ B val
  -}

module _ where
  Env : ℕ → Set
  Env = C.Ctx Type

  private
    weakenOps : Extension Type
    weakenOps = record { weaken = weakenTy }

  open C.WeakenOps Type weakenOps public

infix 4 _⊢_⟱[_]_

mutual
  data _⊢_⟱[_]_ {n : ℕ} (H : Env n) : Type n → ℕ → Type n → Set where
    eval-var : ∀{x τ} → lookup H x ≡ τ → H ⊢ Var x ⟱[ 0 ] τ
    eval-⊤ : H ⊢ ⊤ ⟱[ 0 ] ⊤
    eval-⊥ : H ⊢ ⊥ ⟱[ 0 ] ⊥
    eval-∀' : ∀{K A} → H ⊢ (∀' K A) ⟱[ 0 ] (∀' K A)
    eval-ƛ : ∀{K A} → H ⊢ (ƛ K A) ⟱[ 0 ] (ƛ K A)
    eval-arr : ∀{A B α β a b} →
      H ⊢ A ⟱[ a ] α → H ⊢ B ⟱[ b ] β → H ⊢ A ⇒ B ⟱[ a + b ] (α ⇒ β)
    eval-app : ∀{A B A' τ τ' K a b n} →
      H ⊢ A ⟱[ a ] (ƛ K A') → H ⊢ B ⟱[ b ] τ → (τ ∷ H) ⊢ A' ⟱[ n ] τ' →
      -- [τ'] exists in a context with [suc n] free variables, but we just
      -- plugged [τ] in for 0, so it should be safe to plug ⊤ in for it.
      H ⊢ A ∙ B ⟱[ a + b + n ] (plugTy τ' ⊤)

