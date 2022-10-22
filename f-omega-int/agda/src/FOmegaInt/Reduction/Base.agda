module FOmegaInt.Reduction.Base where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

open import FOmegaInt.Syntax hiding (Context; lookup)

infix 4 _⊢_val
infix 4 _⊢_⟱[_]_

data Env : ℕ → Set
data _⊢_val {n} (H : Env n) : Type n → Set

data Env where
  ∅ : Env zero
  _,_[_] : ∀{n} → (H : Env n) → (τ : Type n) → H ⊢ τ val → Env (suc n)

data _⊢_val {n} H where
  v-top : H ⊢ ⊤ val
  v-bot : H ⊢ ⊥ val
  v-all : ∀{K A} → H ⊢ ∀' K A val
  v-abs : ∀{K A} → H ⊢ ƛ K A val
  v-arr : ∀{A B} → H ⊢ A val → H ⊢ B val → H ⊢ A ⇒ B val

record Val (n : ℕ) (H : Env n) : Set where
  constructor V
  field
    this : Type n
    proof : H ⊢ this val

weaken-isVal : ∀{n} {H : Env n} {τ} →
  H ⊢ τ val → (τ' : Type n) → (p : H ⊢ τ' val) →
  (H , τ' [ p ]) ⊢ (weakenTy τ) val
weaken-isVal v-top _ _ = v-top
weaken-isVal v-bot _ _ = v-bot
weaken-isVal v-all _ _ = v-all
weaken-isVal v-abs _ _ = v-abs
weaken-isVal (v-arr pA pB) τ' p =
  v-arr (weaken-isVal pA τ' p) (weaken-isVal pB τ' p)

weakenVal : ∀{n H} →
  (v : Val n H) → (τ' : Type n) → (p : H ⊢ τ' val) → Val (suc n) (H , τ' [ p ])
weakenVal (V τ proof) τ' p =
  V (weakenTy τ) (weaken-isVal proof τ' p)

lookup : ∀{n} → (H : Env n) → Fin n → Val n H
lookup ∅ ()
lookup (H , τ [ p ]) zero = weakenVal (V τ p) τ p
lookup (H , τ [ p ]) (suc i) = weakenVal (lookup H i) τ p

lookupTy : ∀{n} → Env n → Fin n → Type n
lookupTy H i = Val.this (lookup H i)

data _⊢_⟱[_]_ {n : ℕ} (H : Env n) : Type n → ℕ → Type n → Set where
  eval-var : ∀{x v} → lookup H x ≡ v → H ⊢ Var x ⟱[ 0 ] (Val.this v)
  eval-⊤ : H ⊢ ⊤ ⟱[ 0 ] ⊤
  eval-⊥ : H ⊢ ⊥ ⟱[ 0 ] ⊥
  eval-∀' : ∀{K A} → H ⊢ (∀' K A) ⟱[ 0 ] (∀' K A)
  eval-ƛ : ∀{K A} → H ⊢ (ƛ K A) ⟱[ 0 ] (ƛ K A)
  eval-arr : ∀{A B α β a b} →
    H ⊢ A ⟱[ a ] α → H ⊢ B ⟱[ b ] β → H ⊢ A ⇒ B ⟱[ a + b ] (α ⇒ β)
  eval-app : ∀{A B A' τ α K a b pτ n} →
    H ⊢ A ⟱[ a ] (ƛ K A') → H ⊢ B ⟱[ b ] τ → (H , τ [ pτ ]) ⊢ A' ⟱[ n ] α →
    -- This [plugTy] makes me uncomfortable; it seems to defeat the entire
    -- purpose of using environment-based semantics over substitution semantics
    -- in the first place.
    H ⊢ A ∙ B ⟱[ a + b + n ] (plugTy α τ)

