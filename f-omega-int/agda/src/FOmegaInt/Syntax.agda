module FOmegaInt.Syntax where

open import Data.Fin using (Fin; suc; zero)
import Data.Fin.Substitution as S
open import Data.Fin.Substitution.Lemmas
open import Data.Nat using (ℕ; suc; zero; _+_; _<_; s≤s)
open import Data.Nat.Properties using (<-transˡ; m≤m+n; m≤n+m)
open import Data.Bool using (if_then_else_)
import Data.Vec as Vec
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open import Induction.WellFounded

open import Induction.WellFounded.Mutual
import Data.Context as C

-- TODO: Separate type and term variables

mutual
  data Kind (n : ℕ) : Set where
    _∙∙_ : Type n → Type n → Kind n
    ℿ : Kind n → Kind (suc n) → Kind n

  data Type (n : ℕ) : Set where
    Var : Fin n -> Type n
    ⊤ : Type n
    ⊥ : Type n
    _⇒_ : Type n → Type n → Type n
    ∀' : Kind n → Type (suc n) → Type n
    ƛ : Kind n → Type (suc n) → Type n
    _∙_ : Type n → Type n → Type n

pattern ✶ = ⊥ ∙∙ ⊤

-- Substitutions

module KindTypeApp {T : ℕ → Set} (l : S.Lift T Type) where
  infix 8 _/ty_
  infix 8 _/kd_

  open S.Lift l

  mutual
    _/kd_ : ∀ {m n : ℕ} → Kind m → S.Sub T m n → Kind n
    A ∙∙ B /kd σ = (A /ty σ) ∙∙ (B /ty σ)
    ℿ K J /kd σ = ℿ (K /kd σ) (J /kd σ ↑)

    _/ty_ : ∀ {m n : ℕ} → Type m → S.Sub T m n → Type n
    Var x /ty σ = lift (Vec.lookup σ x)
    ⊤ /ty σ = ⊤
    ⊥ /ty σ = ⊥
    A ⇒ B /ty σ = (A /ty σ) ⇒ (B /ty σ)
    ∀' K τ /ty σ = ∀' (K /kd σ) (τ /ty σ ↑)
    ƛ K τ /ty σ = ƛ (K /kd σ) (τ /ty σ ↑)
    A ∙ B /ty σ = (A /ty σ) ∙ (B /ty σ)

  module KindApp = S.Application (record { _/_ = _/kd_ })
  module TypeApp = S.Application (record { _/_ = _/ty_ })

open KindTypeApp

module Ops where
  private
    typeSubst : S.TermSubst Type
    typeSubst = record { var = Var; app = TypeApp._/_ }

    module TypeVarSubst = TypeApp (S.TermSubst.varLift typeSubst)
    module KindVarSubst = KindApp (S.TermSubst.varLift typeSubst)

    typeLift = S.TermSubst.termLift typeSubst
    module TypeTypeSubst = TypeApp typeLift

    module KindTypeSubst = KindApp typeLift

    tyVarApp : S.Application Type Fin
    tyVarApp = record { _/_ = TypeVarSubst._/_ }

    kdVarApp : S.Application Kind Fin
    kdVarApp = record { _/_ = KindVarSubst._/_ }

  open S.Application tyVarApp public using () renaming (_/_ to _/TyVar_)
  open S.Application kdVarApp public using () renaming (_/_ to _/KdVar_)

  weakenTy : ∀{n : ℕ} → Type n → Type (suc n)
  weakenTy t = t /TyVar S.VarSubst.wk

  weakenTy* : ∀{n : ℕ} → (m : ℕ) → Type n → Type (m + n)
  weakenTy* zero t = t
  weakenTy* (suc m) t = weakenTy (weakenTy* m t)

  weakenKd : ∀{n : ℕ} → Kind n → Kind (suc n)
  weakenKd k = k /KdVar S.VarSubst.wk

  private
    tyApp : S.Application Type Type
    tyApp = record { _/_ = TypeTypeSubst._/_ }

    kdApp : S.Application Kind Type
    kdApp = record { _/_ = KindTypeSubst._/_ }

  open S.Application tyApp public using () renaming (_/_ to _/Ty_)
  open S.Application kdApp public using () renaming (_/_ to _/Kd_)
  open S.Lift typeLift public using (sub; _↑)

  plugTy : ∀{n : ℕ} → Type (suc n) → Type n → Type n
  plugTy t τ = t /Ty (sub τ)

  plugKd : ∀{n : ℕ} → Kind (suc n) → Type n → Kind n
  plugKd k τ = k /Kd (sub τ)

open Ops using
  ( weakenTy
  ; weakenTy*
  ; weakenKd
  ; plugTy
  ; plugKd
  ; _/Ty_
  ; _/Kd_
  ; sub
  ; _↑
  ) public

-- "Size" of kinds -- necessary to aid the termination checker

size : ∀{n} → Kind n → ℕ
-- Although intervals can themselves contain kinds (e.g., via a ∀' form), we
-- don't consider them, because we never need to actually recurse into those
-- kinds.
size (A ∙∙ B) = zero
size (ℿ J K) = suc (size J + size K)

_<kd_ : ∀{n} → Kind n → Kind n → Set
J <kd K = size J < size K

-- Well-founded recursion on kind size

mutual
  <kd-wf : ∀{n} → WellFounded (_<kd_ {n})
  <kd-wf {n} K = acc (<kd-acc {n} (size K))

  <kd-acc : ∀ {n} i K → size {n} K < i → Acc _<kd_ K
  <kd-acc zero K ()
  <kd-acc (suc n) (A ∙∙ B) _ = acc (λ _ ())
  <kd-acc (suc n) (ℿ J K) (s≤s ℿJK≤n) =
    acc (λ J J<ℿJK → <kd-acc n J (<-transˡ J<ℿJK ℿJK≤n))

module _ {ℓ} {n} where
  open All (<kd-wf {n}) ℓ public
    renaming ( wfRecBuilder to <kd-recBuilder
             ; wfRec to <kd-rec
             )
    hiding (wfRec-builder)

  open Nary (<kd-wf {n}) ℓ public
    renaming (wfMutual to <kd-mutual)

-- Substitution lemmas

subst-preserves-size : ∀{n m} →
  (K : Kind n) → (σ : S.Sub Type n m) → size (K /Kd σ) ≡ size K
subst-preserves-size (A ∙∙ B) σ = refl
subst-preserves-size (ℿ J K) σ = begin
    size ((ℿ J K) /Kd σ)
  ≡⟨ refl ⟩
    size (ℿ (J /Kd σ) (K /Kd σ ↑))
  ≡⟨ refl ⟩
    suc (size (J /Kd σ) + size (K /Kd σ ↑))
  ≡⟨ cong (λ t → suc (t + size (K /Kd σ ↑))) (subst-preserves-size J σ) ⟩
    suc (size J + size (K /Kd σ ↑))
  ≡⟨ cong (λ t → suc (size J + t)) (subst-preserves-size K (σ ↑)) ⟩
    suc (size J + size K)
  ≡⟨ refl ⟩
    size (ℿ J K)
  ∎
  where
    open ≡-Reasoning

<ℿ₁ : ∀{n} (J : Kind n) K → J <kd ℿ J K
<ℿ₁ J K = s≤s (m≤m+n (size J) (size K))

<ℿ₂ : ∀{n} (J : Kind n) K τ → plugKd K τ <kd ℿ J K
<ℿ₂ J K τ rewrite subst-preserves-size K (sub τ) =
  s≤s (m≤n+m (size K) (size J))

size' : ∀{n} → Kind n → ℕ
size' = <kd-rec _ go
  where
    go : ∀ K → (∀ J → J <kd K → ℕ) → ℕ
    go (A ∙∙ B) _ = zero
    go (ℿ J K) rec =
      rec J (<ℿ₁ J K) + rec (plugKd K ⊤) (<ℿ₂ J K ⊤)

-- Kinding Contexts

module Context where
  open C hiding (Ctx)

  Ctx : ℕ → Set
  Ctx = C.Ctx Kind

  private
    weakenOps : Extension Kind
    weakenOps = record { weaken = Ops.weakenKd }

  open C.WeakenOps Kind weakenOps public

open Context using (lookup; insertUnder) renaming (Ctx to Context) public
