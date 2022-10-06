module FOmegaInt.Reduction where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open import Function using (id)

open import FOmegaInt.Syntax hiding (Context; lookup)

infix 4 _⊢_val

data Env : ℕ → Set
record Val {n : ℕ} : Set

data _⊢_val {n} (H : Env n) : Type n → Set where
  v-top : H ⊢ ⊤ val
  v-bot : H ⊢ ⊥ val
  v-all : ∀{K A} → H ⊢ ∀' K A val
  v-abs : ∀{K A} → H ⊢ ƛ K A val
  v-arr : ∀{A B} → H ⊢ A val → H ⊢ B val → H ⊢ A ⇒ B val

record Val {n} where
  inductive
  constructor _[_,_]
  field
    this : Type n
    H : Env n
    p : H ⊢ this val

data Env where
  [] : Env zero
  _∷_ : ∀{n} → (τ : Val) → Env n → Env (suc n)

lookup : ∀{n : ℕ} → Env n → Fin n → Val
lookup {zero} _ ()
lookup {suc _} (τ ∷ _) zero = τ
lookup {suc _} (_ ∷ H) (suc i) = lookup H i

data Finished : Set where
  VAL : Val → Finished
  ERROR : Finished
  TIMEOUT : Finished

_>>=_ : Finished → (Val → Finished) → Finished
VAL v >>= f = f v
ERROR >>= _ = ERROR
TIMEOUT >>= _ = TIMEOUT

_>>_ : Finished → Finished → Finished
a >> b = a >>= (λ _ → b)

-- Big step rules

eval : ∀{n} → (gas : ℕ) → Env n → Type n → Finished
eval n H (Var x) = VAL (lookup H x)
eval n H ⊤ = VAL (⊤ [ H , v-top ])
eval n H ⊥ = VAL (⊥ [ H , v-bot ])
eval n H τ@(∀' _ _) = VAL (τ [ H , v-all ])
eval zero H _ = TIMEOUT
eval (suc n) H (A ⇒ B) = do
  a [ H₁ , pa ] ← eval n H A
  b [ H₂ , pb ] ← eval n H₁ B
  VAL ((a ⇒ b)[ H₂ , v-arr pa pb ])

infix 4 _⊢_⟱[_]_

data _⊢_⟱[_]_ {n : ℕ} (H : Env n) : Type n → ℕ → Type zero → Set where
  eval-var : ∀{x τ} → lookup H x ≡ τ → H ⊢ Var x ⟱[ 0 ] (Val.this τ)
  eval-arr : ∀{A B α β n m} →
    H ⊢ A ⟱[ n ] α → H ⊢ B ⟱[ m ] β → H ⊢ A ⇒ B ⟱[ n + m ] α ⇒ β

