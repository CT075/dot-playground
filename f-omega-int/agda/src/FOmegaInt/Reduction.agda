module FOmegaInt.Reduction where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open import Function using (id)

open import FOmegaInt.Syntax hiding (Context; lookup)

infix 4 _⊢_val

data Env : ℕ → Set
record Val : Set

data _⊢_val {n} (H : Env n) : Type n → Set where
  v-top : H ⊢ ⊤ val
  v-bot : H ⊢ ⊥ val
  v-all : ∀{K A} → H ⊢ ∀' K A val
  v-abs : ∀{K A} → H ⊢ ƛ K A val
  v-arr : ∀{A B} → H ⊢ A val → H ⊢ B val → H ⊢ A ⇒ B val

{-
data Val : Set where
  v-⊤ : Val
  v-⊥ : Val
  v-∀'_∙⟨_,_⟩ : {n} → Env (suc n) → Kind n → Type (suc n) → Val
  v-ƛ_∙⟨_,_⟩ : {n} → Env (suc n) → Kind n → Type (suc n) → Val
  v-_⇒_ : {n} → Type n → Type n → Val
  -}

record Val where
  inductive
  constructor [_]⟨_,_⟩
  field
    n : ℕ
    this : Type n
    H : Env n

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
  eval-arr : ∀{A B α β a b} →
    H ⊢ A ⟱[ a ] α → H ⊢ B ⟱[ b ] β → H ⊢ A ⇒ B ⟱[ a + b ] α ⇒ β

