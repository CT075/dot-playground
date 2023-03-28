module Data.Nat.Induction.Extensions where

open import Data.Nat
open import Data.Nat.Induction using (<-recBuilder)
open import Induction
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

withMeasure : ∀ {ℓ} {T : Set ℓ} →
  (measure : T → ℕ) →
  (P : T → Set ℓ) →
  (∀ x → (∀ y → measure y < measure x → P y) → P x) →
  (x : T) →
  P x
withMeasure measure P f x = build <-recBuilder
    (λ measureX → (∀ x → (measure x ≡ measureX) → P x))
    f'
    (measure x)
    x
    refl
  where
    f' : ∀ measureX →
        (∀ measureY → measureY < measureX → ∀ y → (measure y ≡ measureY) → P y) →
        ∀ x → (measure x ≡ measureX) → P x
    f' measureX rec x mx≡measureX = f x rec'
      where
        rec' : ∀ y → measure y < measure x → P y
        rec' y my<mx rewrite mx≡measureX = rec (measure y) my<mx y refl
