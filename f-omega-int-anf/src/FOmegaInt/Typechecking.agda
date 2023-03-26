module FOmegaInt.Typechecking where

-- algorithmic typechecking with only weak-head normalization on types

open import Data.Maybe

open import Data.Var
open import Data.Context

-- TODO: add explicit whnf syntax
open import FOmegaInt.Syntax
open import FOmegaInt.Typing


record KindSynth (Γ : Context) (τ : Type) : Set where
  constructor Synth
  field
    k : Kind
    proof : Γ ⊢ty τ ∈ k

mutual
  synthkind : (Γ : Context) → (τ : Type) → Γ ctx → Maybe (KindSynth Γ τ)
  synthkind Γ (`(Free x)) Γctx = do
    L v Γ[x]⊢>v ← lookup Γ x
    unwrapFact v Γ[x]⊢>v
    where
      unwrapFact : (v : VarFact) → Γ [ x ]⊢> v → Maybe (KindSynth Γ (`(Free x)))
      unwrapFact (Kd k) Γ[x]⊢>v = just (Synth k (k-var Γctx Γ[x]⊢>v))
      unwrapFact (Alias τ k) Γ[x]⊢>v = just (Synth k (k-alias Γctx Γ[x]⊢>v))
      unwrapFact (Ty τ) _ = nothing
  synthkind Γ (`(Bound x)) _ = nothing
  synthkind Γ _ _ = {!!}

  checkkind : (Γ : Context) → (τ : Type) → (k : Kind) → Γ ctx →
    Maybe (Γ ⊢ty τ ∈ k)
  checkkind Γ τ k Γctx = do
    Synth k' Γ⊢τ∈k' ← synthkind Γ τ Γctx
    Γ⊢k'≤k ← subkind Γ k' k Γctx
    just (k-sub Γ⊢τ∈k' Γ⊢k'≤k)

  subkind : (Γ : Context) → (k₁ : Kind) → (k₂ : Kind) → Γ ctx →
    Maybe (Γ ⊢kd k₁ ≤ k₂)
  subkind Γ (A₁ ∙∙ B₁) (A₂ ∙∙ B₂) Γctx = do
    A₂≤A₁ ← subtype Γ A₂ A₁ ✶ Γctx
    B₁≤B₂ ← subtype Γ B₁ B₂ ✶ Γctx
    just (sk-intv A₂≤A₁ B₁≤B₂)
  -- TODO: well-founded
  subkind Γ (ℿ j₁ k₁) (ℿ j₂ k₂) Γctx = {! do
    j₂≤j₁ ← subkind Γ j₂ j₁ Γctx
    k₁≤k₂ ← subkind (Γ & "α" ~ Kd j₂)
              (openKind "α" k₁)
              (openKind "α" k₂)
              (c-bind-kd Γctx {! Γ ⊢ j₂ kd !})
    just (sk-darr j₂≤j₁ k₁≤k₂) !}
  subkind Γ _ _ Γctx = nothing

  subtype : (Γ : Context) → (τ₁ : Type) → (τ₂ : Type) → (k : Kind) → Γ ctx →
    Maybe (Γ ⊢ty τ₁ ≤ τ₂ ∈ k)
  subtype = {!!}
