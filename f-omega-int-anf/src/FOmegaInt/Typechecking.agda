module FOmegaInt.Typechecking where

-- algorithmic typechecking with only weak-head normalization on types

open import Data.Nat using (ℕ; _+_; _<_)
open import Data.Nat.Properties using (+-mono-<; +-comm; m<n⇒m<1+n)
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

open import Data.Nat.Induction.Extensions

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
  subkind Γ k₁ k₂ Γctx = withMeasure kd-size-tup
      (λ (k₁ , k₂) → (∀ Γ → Γ ctx → Maybe (Γ ⊢kd k₁ ≤ k₂)))
      subkind'
      (k₁ , k₂) Γ Γctx
    where
      kd-size-tup : Kind × Kind → ℕ
      kd-size-tup (k₁ , k₂) = kd-size k₁ + kd-size k₂

      subkind' : ∀ ((k₁ , k₂) : Kind × Kind) →
        (∀ ((k₁' , k₂') : Kind × Kind) →
          kd-size-tup (k₁' , k₂') < kd-size-tup (k₁ , k₂) →
          (∀ Γ → Γ ctx → Maybe (Γ ⊢kd k₁' ≤ k₂'))) →
        ∀ Γ → Γ ctx → Maybe (Γ ⊢kd k₁ ≤ k₂)
      subkind' (A₁ ∙∙ B₁ , A₂ ∙∙ B₂) _ Γ Γctx = do
        A₂≤A₁ ← subtype Γ A₂ A₁ ✶ Γctx
        B₁≤B₂ ← subtype Γ B₁ B₂ ✶ Γctx
        just (sk-intv A₂≤A₁ B₁≤B₂)
      subkind' (ℿ j₁ k₁ , ℿ j₂ k₂) rec Γ Γctx = do
        j₂≤j₁ ← rec (j₂ , j₁) j₂+j₁<ℿj₁k₁+ℿj₂k₂ Γ Γctx
        k₁≤k₂ ← rec (openKind "α" k₁ , openKind "α" k₂)
                  k₁[α]+k₂[α]<ℿj₁k₁+ℿj₂k₂
                  (Γ & "α" ~ Kd j₂) (c-bind-kd Γctx {! Γ ⊢ j₂ kd !})
        just (sk-darr j₂≤j₁ k₁≤k₂)
        where
          j₁<ℿj₁k₁ = <kd-ℿ₁ j₁ k₁
          j₂<ℿj₂k₂ = <kd-ℿ₁ j₂ k₂

          j₁+j₂<ℿj₁k₁+ℿj₂k₂ :
            kd-size j₁ + kd-size j₂ < kd-size (ℿ j₁ k₁) + kd-size (ℿ j₂ k₂)
          j₁+j₂<ℿj₁k₁+ℿj₂k₂ = +-mono-< j₁<ℿj₁k₁ j₂<ℿj₂k₂

          j₂+j₁<ℿj₁k₁+ℿj₂k₂ :
            kd-size j₂ + kd-size j₁ < kd-size (ℿ j₁ k₁) + kd-size (ℿ j₂ k₂)
          j₂+j₁<ℿj₁k₁+ℿj₂k₂ rewrite +-comm (kd-size j₂) (kd-size j₁) =
            j₁+j₂<ℿj₁k₁+ℿj₂k₂

          k₁<ℿj₁k₁ = <kd-ℿ₂ j₁ k₁
          k₂<ℿj₂k₂ = <kd-ℿ₂ j₂ k₂

          k₁[α]<ℿj₁k₁ : kd-size (openKind "α" k₁) < kd-size (ℿ j₁ k₁)
          k₁[α]<ℿj₁k₁ =
            liftKind-preserves-<₁ k₁ (ℿ j₁ k₁) (openVar "α") k₁<ℿj₁k₁

          k₂[α]<ℿj₂k₂ : kd-size (openKind "α" k₂) < kd-size (ℿ j₂ k₂)
          k₂[α]<ℿj₂k₂ =
            liftKind-preserves-<₁ k₂ (ℿ j₂ k₂) (openVar "α") k₂<ℿj₂k₂

          k₁[α]+k₂[α]<ℿj₁k₁+ℿj₂k₂ = +-mono-< k₁[α]<ℿj₁k₁ k₂[α]<ℿj₂k₂
      subkind' Γ _ _ Γctx = nothing

  subtype : (Γ : Context) → (τ₁ : Type) → (τ₂ : Type) → (k : Kind) → Γ ctx →
    Maybe (Γ ⊢ty τ₁ ≤ τ₂ ∈ k)
  subtype Γ τ₁ τ₂ k Γctx = {! withMeasure ty-size-tup !}
