module FOmegaInt.Syntax where

open import Data.Nat using (ℕ; suc; zero; _+_)
import Data.Vec as Vec
open import Function.Base using (id)

open import Data.Var using (Var; Lift; Subst)

mutual
  data Kind : Set where
    _∙∙_ : Type → Type → Kind
    ℿ : Kind → Kind → Kind

  data Type : Set where
    `_ : Var -> Type
    ⊤ : Type
    ⊥ : Type
    _⇒_ : Type → Type → Type
    ∀' : Kind → Type → Type
    ƛ : Kind → Type → Type
    _⊡_ : Var → Var → Type

data Term : Set where
  `_ : Var → Term
  ƛ : Type → Term → Term
  _⊡_ : Var → Var → Term
  Λ : Kind → Term → Term
  _[_] : Var → Var → Term
  let'_in'_ : Term → Term → Term
  lettype_in'_ : Type → Term → Term

pattern ✶ = ⊥ ∙∙ ⊤

mutual
  liftKind : (Var → Var) → Kind → Kind
  liftKind f (τ₁ ∙∙ τ₂) = liftType f τ₁ ∙∙ liftType f τ₂
  liftKind f (ℿ J K) = ℿ (liftKind f J) (liftKind f K)

  liftType : (Var → Var) → Type → Type
  liftType f (` x) = ` (f x)
  liftType f ⊤ = ⊤
  liftType f ⊥ = ⊥
  liftType f (A ⇒ B) = liftType f A ⇒ liftType f B
  liftType f (ƛ k τ) = ƛ (liftKind f k) (liftType f τ)
  liftType f (∀' k τ) = ∀' (liftKind f k) (liftType f τ)
  liftType f (g ⊡ τ) = f g ⊡ f τ

liftTerm : (Var → Var) → Term → Term
liftTerm f (` x) = ` (f x)
liftTerm f (ƛ τ e) = ƛ (liftType f τ) (liftTerm f e)
liftTerm f (g ⊡ x) = f g ⊡ f x
liftTerm f (Λ k e) = Λ (liftKind f k) (liftTerm f e)
liftTerm f (x [ τ ]) = f x [ f τ ]
liftTerm f (let' e₁ in' e₂) = let' liftTerm f e₁ in' liftTerm f e₂
liftTerm f (lettype τ in' e) = lettype liftType f τ in' liftTerm f e

instance
  KindLift : Lift Kind
  KindLift = record {lift = liftKind}

  TypeLift : Lift Type
  TypeLift = record {lift = liftType}

  TermLift : Lift Term
  TermLift = record {lift = liftTerm}

open Subst (record {lift = KindLift; var = id; subst = liftKind}) renaming
  ( openT to openKind
  ; closeT to closeKind
  ; wkT to wkKind
  ; shiftT to shiftKind
  ; renameT to renameKind
  ; bindT to bindKind
  )
  hiding (bindVar)
  public

open Subst (record {lift = TypeLift; var = id; subst = liftType}) renaming
  ( openT to openType
  ; closeT to closeType
  ; wkT to wkType
  ; shiftT to shiftType
  ; renameT to renameType
  ; bindT to bindType
  )
  hiding (bindVar)
  public

open Subst (record {lift = TermLift; var = id; subst = liftTerm}) renaming
  ( openT to openTerm
  ; closeT to closeTerm
  ; wkT to wkTerm
  ; shiftT to shiftTerm
  ; renameT to renameTerm
  ; bindT to bindTerm
  )
  hiding (bindVar)
  public
