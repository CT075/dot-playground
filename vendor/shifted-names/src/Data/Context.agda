module Data.Context where

open import Data.Nat using (ℕ; suc; zero)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Bool using (if_then_else_)
open import Data.String using (_==_)
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
  bind-tl-xx : ∀{x τ Γ i} →
    Γ [ N x i ]⊢> τ → (Γ & x ~ τ) [ N x (suc i) ]⊢> Lift.shiftT TLift x τ
  bind-tl-xy : ∀{x y τ τ' Γ i} →
    Γ [ N x i ]⊢> τ → x ≢ y → (Γ & y ~ τ') [ N x i ]⊢> Lift.shiftT TLift y τ

lookup : ∀{T} {{TLift : Lift T}} → Ctx T → Name → Maybe T
lookup [] _ = nothing
lookup (Γ & x ~ τ) (N y zero) = if x == y then just τ else lookup Γ (N y zero)
lookup {{TLift}} (Γ & x ~ τ) (N y (suc i)) =
  if x == y then
    map (Lift.shiftT TLift x) (lookup Γ (N y i))
  else
    map (Lift.shiftT TLift x) (lookup Γ (N y (suc i)))

lookup-spec-mem : ∀{T} → {{TLift : Lift T}} →
  ∀ (Γ : Ctx T) name {τ} →
    lookup Γ name ≡ just τ →
    Γ [ name ]⊢> τ
lookup-spec-mem [] _ ()
lookup-spec-mem (Γ & x ~ τ) (N y _) _ = {!!}
