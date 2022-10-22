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

record Val (n : ℕ) : Set where
  constructor V
  field
    closure : Env n
    this : Type n
    proof : closure ⊢ this val

weaken-isVal : ∀{n} {H : Env n} {τ} →
  H ⊢ τ val → (τ' : Type n) → (p : H ⊢ τ' val) →
  (H , τ' [ p ]) ⊢ (weakenTy τ) val
weaken-isVal v-top _ _ = v-top
weaken-isVal v-bot _ _ = v-bot
weaken-isVal v-all _ _ = v-all
weaken-isVal v-abs _ _ = v-abs
weaken-isVal (v-arr pA pB) τ' p =
  v-arr (weaken-isVal pA τ' p) (weaken-isVal pB τ' p)

weakenVal : ∀{n} →
  (v : Val n) → (τ' : Type n) → (Val.closure v) ⊢ τ' val → Val (suc n)
weakenVal (V H τ proof) τ' p =
  V (H , τ' [ p ]) (weakenTy τ) (weaken-isVal proof τ' p)

lookup : ∀{n} → Env n → Fin n → Val n
lookup-closure : ∀{n} →
  (H : Env n) → (i : Fin n) → Val.closure (lookup H i) ≡ H

roundtrip-closure : ∀{n} (H : Env n) → ∀{τ} → (i : Fin n) →
  H ⊢ τ val → Val.closure (lookup H i) ⊢ τ val

lookup ∅ ()
lookup (H , τ [ p ]) zero = weakenVal (V H τ p) τ p
lookup (H , τ [ p ]) (suc i) =
  weakenVal (lookup H i) τ (roundtrip-closure H i p)

roundtrip-closure H i p rewrite lookup-closure H i = p

lookup-closure ∅ ()
lookup-closure (H , τ [ p ]) zero = let open ≡-Reasoning in begin
  Val.closure (lookup (H , τ [ p ]) zero) ≡⟨ refl ⟩
  Val.closure (weakenVal (V H τ p) τ p) ≡⟨ refl ⟩
  Val.closure (V (H , τ [ p ]) (weakenTy τ) (weaken-isVal p τ p)) ≡⟨ refl ⟩
  (H , τ [ p ])
  ∎
lookup-closure (H , τ [ p ]) (suc i) = let open ≡-Reasoning in begin
  Val.closure (lookup (H , τ [ p ]) (suc i))
    ≡⟨ refl ⟩
  Val.closure (weakenVal (lookup H i) τ (roundtrip-closure H i p))
    ≡⟨ refl ⟩
  Val.closure (V
      (Val.closure (lookup H i) , τ [ roundtrip-closure H i p ])
      (weakenTy (Val.this (lookup H i)))
      (weaken-isVal (Val.proof (lookup H i)) τ (roundtrip-closure H i p)))
    ≡⟨ refl ⟩
  Val.closure (lookup H i) , τ [ roundtrip-closure H i p ]
    ≡⟨ unRoundtrip ⟩
  H , τ [ p ]
    ∎
  where
    unRoundtrip :
      Val.closure (lookup H i) , τ [ roundtrip-closure H i p ] ≡ H , τ [ p ]
    unRoundtrip rewrite lookup-closure H i = refl

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

