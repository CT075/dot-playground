module FOmegaInt.Reduction where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

open import FOmegaInt.Syntax hiding (Context; lookup)

infix 4 _val
infix 4 _⟱[_]_

data _val : Type zero → Set where
  v-top : ⊤ val
  v-bot : ⊥ val
  v-all : ∀{K A} → ∀' K A val
  v-abs : ∀{K A} → ƛ K A val
  v-arr : ∀{A B} → A val → B val → A ⇒ B val

data _⟱[_]_ : Type zero → ℕ → Type zero → Set where
  eval-⊤ : ⊤ ⟱[ 0 ] ⊤
  eval-⊥ : ⊥ ⟱[ 0 ] ⊥
  eval-∀' : ∀{K A} → (∀' K A) ⟱[ 0 ] (∀' K A)
  eval-ƛ : ∀{K A} → (ƛ K A) ⟱[ 0 ] (ƛ K A)
  eval-arr : ∀{A B α β a b} →
    A ⟱[ a ] α → B ⟱[ b ] β → A ⇒ B ⟱[ a + b ] (α ⇒ β)
  eval-app : ∀{A B A' β τ K a b n} →
    A ⟱[ a ] (ƛ K A') → B ⟱[ b ] β → plugTy A' β ⟱[ n ] τ →
    A ∙ B ⟱[ a + b + n ] τ

-- Lemmas

val-unique : ∀{τ : Type zero} →
  (τval₁ : τ val) → (τval₂ : τ val) → τval₁ ≡ τval₂
val-unique v-top v-top = refl
val-unique v-bot v-bot = refl
val-unique v-all v-all = refl
val-unique v-abs v-abs = refl
val-unique (v-arr A₁ B₁) (v-arr A₂ B₂)
  rewrite val-unique A₁ A₂ | val-unique B₁ B₂ = refl

⟱-spec : ∀{gas} {A τ : Type zero} → A ⟱[ gas ] τ → τ val
⟱-spec eval-⊤ = v-top
⟱-spec eval-⊥ = v-bot
⟱-spec eval-∀' = v-all
⟱-spec eval-ƛ = v-abs
⟱-spec (eval-arr A⟱ B⟱) = v-arr (⟱-spec A⟱) (⟱-spec B⟱)
⟱-spec (eval-app A⟱ƛA' B⟱β A'⟱τ) = ⟱-spec A'⟱τ

