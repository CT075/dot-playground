module Data.Context where

open import Data.Fin using (Fin; suc; zero)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Relation.Unary using (Pred)

infixr 5 _∷_

data Ctx {ℓ} (T : Pred ℕ ℓ) : ℕ → Set ℓ where
  [] : Ctx T zero
  _∷_ : ∀ {n : ℕ} → T n → Ctx T n → Ctx T (suc n)

record Extension {ℓ} (T : Pred ℕ ℓ) : Set ℓ where
  field
    weaken : ∀{n} → T n → T (suc n)

module _ {ℓ} {T : Pred ℕ ℓ} where
  head : ∀ {n : ℕ} → Ctx T (suc n) → T n
  head (t ∷ ts) = t

  tail : ∀ {n : ℕ} → Ctx T (suc n) → Ctx T n
  tail (t ∷ ts) = ts

  drop : ∀ {n : ℕ} → (m : ℕ) → Ctx T (m + n) → Ctx T n
  drop zero Γ = Γ
  drop (suc m) (_ ∷ Γ) = drop m Γ

map : ∀{ℓ₁ ℓ₂} {T₁ : Pred ℕ ℓ₁} {T₂ : Pred ℕ ℓ₂} {n} →
      (∀{k} → T₁ k → T₂ k) → Ctx T₁ n → Ctx T₂ n
map f [] = []
map f (t ∷ Γ) = f t ∷ map f Γ

module WeakenOps {ℓ} (T : Pred ℕ ℓ) (ext : Extension T) where
  open Extension ext

  lookup : ∀ {n : ℕ} → Ctx T n → Fin n → T n
  -- Weaken [t] because [t] was in a context with [n-1] bound vars, now it's in
  -- a context with [n] bound vars (the extra item is [t] itself).
  lookup (t ∷ _) zero = weaken t
  lookup (_ ∷ Γ) (suc n) = weaken (lookup Γ n)
