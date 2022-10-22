module FOmegaInt.Syntax where

open import Data.Fin using (Fin; suc; zero; inject₁)
import Data.Fin.Substitution as S
open import Data.Fin.Substitution.Lemmas
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Bool using (if_then_else_)
import Data.Vec as Vec

import Data.Context as C

-- TODO: Separate type and term variables

mutual
  data Kind (n : ℕ) : Set where
    ✶ : Kind n
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

module KindTypeApp {T : ℕ → Set} (l : S.Lift T Type) where
  infix 8 _/ty_
  infix 8 _/kd_

  open S.Lift l

  mutual
    _/kd_ : ∀ {m n : ℕ} → Kind m → S.Sub T m n → Kind n
    ✶ /kd σ = ✶
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

module Context where
  open C hiding (Ctx)

  Ctx : ℕ → Set
  Ctx = C.Ctx Kind

  private
    weakenOps : Extension Kind
    weakenOps = record { weaken = Ops.weakenKd }

  open C.WeakenOps Kind weakenOps public

open Context using (lookup; insertUnder) renaming (Ctx to Context) public
