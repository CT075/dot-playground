module FOmegaInt.Reduction.Base where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

import Data.Context as C
open C using (_∷_)
open import FOmegaInt.Syntax hiding (Context; lookup)

infix 4 _⊢_val
infix 4 _⊢_⟱[_]_

module Heap where
  open C hiding (Ctx)

  Heap : ℕ → Set
  Heap = C.Ctx Type

  private
    weakenOps : Extension Type
    weakenOps = record { weaken = weakenTy }

  open C.WeakenOps Type weakenOps public

open Heap using (lookup; insertUnder) renaming (Heap to Env) public

data _⊢_val {n} (H : Env n) : Type n → Set where
  v-top : H ⊢ ⊤ val
  v-bot : H ⊢ ⊥ val
  v-all : ∀{K A} → H ⊢ ∀' K A val
  v-abs : ∀{K A} → H ⊢ ƛ K A val
  v-arr : ∀{A B} → H ⊢ A val → H ⊢ B val → H ⊢ A ⇒ B val

data _⊢_⟱[_]_ {n : ℕ} (H : Env n) : Type n → ℕ → Type n → Set where
  eval-var : ∀{x τ} → lookup H x ≡ τ → H ⊢ Var x ⟱[ 0 ] τ
  eval-⊤ : H ⊢ ⊤ ⟱[ 0 ] ⊤
  eval-⊥ : H ⊢ ⊥ ⟱[ 0 ] ⊥
  eval-∀' : ∀{K A} → H ⊢ (∀' K A) ⟱[ 0 ] (∀' K A)
  eval-ƛ : ∀{K A} → H ⊢ (ƛ K A) ⟱[ 0 ] (ƛ K A)
  eval-arr : ∀{A B α β a b} →
    H ⊢ A ⟱[ a ] α → H ⊢ B ⟱[ b ] β → H ⊢ A ⇒ B ⟱[ a + b ] (α ⇒ β)
  eval-app : ∀{A B A' β τ K a b n} →
    H ⊢ A ⟱[ a ] (ƛ K A') → H ⊢ B ⟱[ b ] β → β ∷ H ⊢ A' ⟱[ n ] τ →
    -- XXX: This [plugTy] makes me uncomfortable; it seems to defeat the entire
    -- purpose of using environment-based semantics over substitution semantics
    -- in the first place.
    H ⊢ A ∙ B ⟱[ a + b + n ] (plugTy τ β)

