module FOmegaInt.Reduction where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

open import FOmegaInt.Syntax hiding (Context; lookup)

infix 4 _⊢_val

data Env : ℕ → Set

data _⊢_val {n} (H : Env n) : Type n → Set where
  v-top : H ⊢ ⊤ val
  v-bot : H ⊢ ⊥ val
  v-all : ∀{K A} → H ⊢ ∀' K A val
  v-abs : ∀{K A} → H ⊢ ƛ K A val
  v-arr : ∀{A B} → H ⊢ A val → H ⊢ B val → H ⊢ A ⇒ B val

infix 6 vl-∀'_∙⟨_,_⟩

data Val : Set where
  vl-⊤ : Val
  vl-⊥ : Val
  -- It looks weird to use [Env n] with [Type (suc n)], but remember that the
  -- 0th index is bound to the argument to the [∀'] or [ƛ], so once we evaluate
  -- further, it will become an [Env (suc n)].
  --
  -- XXX: Do we actually need H' here?
  vl-∀'_∙⟨_,_⟩ : ∀{n} → Kind n → Env n → Type (suc n) → Val
  vl-ƛ_∙⟨_,_⟩ : ∀{n} → Kind n → Env n → Type (suc n) → Val
  vl-_⇒_ : Val → Val → Val

data Env where
  [] : Env zero
  _∷_ : ∀{n} → (τ : Val) → Env n → Env (suc n)

lookup : ∀{n : ℕ} → Env n → Fin n → Val
lookup {zero} _ ()
lookup {suc _} (τ ∷ _) zero = τ
lookup {suc _} (_ ∷ H) (suc i) = lookup H i

infix 4 _⊢_⟱[_]_

data _⊢_⟱[_]_ {n : ℕ} (H : Env n) : Type n → ℕ → Val → Set where
  eval-var : ∀{x τ} → lookup H x ≡ τ → H ⊢ Var x ⟱[ 0 ] τ
  eval-⊤ : H ⊢ ⊤ ⟱[ 0 ] vl-⊤
  eval-⊥ : H ⊢ ⊥ ⟱[ 0 ] vl-⊤
  eval-∀' : ∀{K A} → H ⊢ (∀' K A) ⟱[ 0 ] (vl-∀' K ∙⟨ H , A ⟩)
  eval-ƛ : ∀{K A} → H ⊢ (ƛ K A) ⟱[ 0 ] (vl-ƛ K ∙⟨ H , A ⟩)
  eval-arr : ∀{A B α β a b} →
    H ⊢ A ⟱[ a ] α → H ⊢ B ⟱[ b ] β → H ⊢ A ⇒ B ⟱[ a + b ] (vl- α ⇒ β)
  eval-app : ∀{A B K A' H' τ τ' a b n} →
    H ⊢ A ⟱[ a ] (vl-ƛ K ∙⟨ H' , A' ⟩) → H ⊢ B ⟱[ b ] τ →
    (τ ∷ H) ⊢ A' ⟱[ n ] τ' →
    H ⊢ A ∙ B ⟱[ a + b + n ] τ'

