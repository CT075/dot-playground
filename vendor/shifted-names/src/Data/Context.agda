module Data.Context where

open import Data.Nat using (ℕ; suc; zero)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Bool using (if_then_else_)
open import Data.String using (_≟_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; refl)

open import Data.Var using (Name; N; Lift)

record Entry T {{TLift : Lift T}} : Set where
  constructor E
  field
    name : String
    typ : T

Ctx : ∀ T {{TLift : Lift T}} → Set
Ctx T = List (Entry T)

empty : ∀ {T} {{TLift : Lift T}} → Ctx T
empty = []

infix 21 _&_~_

pattern _&_~_ Γ x τ = E x τ ∷ Γ

infix 20 _[_]⊢>_

data _[_]⊢>_ {T} {{TLift : Lift T}} : Ctx T → Name → T → Set where
  bind-hd : ∀{x τ Γ} → (Γ & x ~ τ) [ N x zero ]⊢> τ
  bind-tl-xx : ∀{x τ τ' Γ i} →
    Γ [ N x i ]⊢> τ → (Γ & x ~ τ') [ N x (suc i) ]⊢> Lift.shiftT TLift x τ
  bind-tl-xy : ∀{x y τ τ' Γ i} →
    Γ [ N x i ]⊢> τ → x ≢ y → (Γ & y ~ τ') [ N x i ]⊢> Lift.shiftT TLift y τ

record Lookup T {{TLift : Lift T}} Γ name : Set where
  constructor L
  field
    τ : T
    proof : Γ [ name ]⊢> τ

lookup : ∀{T} {{TLift : Lift T}} →
  (Γ : Ctx T) → (name : Name) → Maybe (Lookup T Γ name)
lookup [] _ = nothing
lookup {T} {{TLift}} (Γ & y ~ τ) (N x zero) with x ≟ y
... | yes p rewrite p = just (L τ bind-hd)
... | no ¬p = map rw (lookup Γ (N x zero))
        where
          rw : Lookup T Γ (N x zero) → Lookup T (Γ & y ~ τ) (N x zero)
          rw (L τ' proof) = L (Lift.shiftT TLift y τ') (bind-tl-xy proof ¬p)
lookup {T} {{TLift}} (Γ & y ~ τ) (N x (suc i)) with x ≟ y
... | yes p rewrite p = map rw (lookup Γ (N y i))
        where
          rw : Lookup T Γ (N y i) → Lookup T (Γ & y ~ τ) (N y (suc i))
          rw (L τ' proof) = L (Lift.shiftT TLift y τ') (bind-tl-xx proof)
... | no ¬p = map rw (lookup Γ (N x (suc i)))
        where
          rw : Lookup T Γ (N x (suc i)) → Lookup T (Γ & y ~ τ) (N x (suc i))
          rw (L τ' proof) = L (Lift.shiftT TLift y τ') (bind-tl-xy proof ¬p)
