module FOmegaInt.Syntax where

open import Data.Nat using (ℕ; suc; zero; _+_; _<_; s≤s)
open import Data.Nat.Properties using (<-transˡ; m≤m+n; m≤n+m)
import Data.Vec as Vec
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open import Induction.WellFounded

open import Data.Var using (Var; Lift; Subst)

infix 21 _⊡_

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

-- locally-nameless operations

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

-- termination measures

infix 19 _<kd_ _<ty_ --_<tm_

-- TODO: finish this explanation
-- We don't need to recurse into the types (even though those types may
-- themselves contain types) because [...]
kd-size : Kind → ℕ
kd-size (A ∙∙ B) = zero
kd-size (ℿ J K) = suc (kd-size J + kd-size K)

_<kd_ : Kind → Kind → Set
J <kd K = kd-size J < kd-size K

<kd-ℿ₁ : ∀ J K → J <kd ℿ J K
<kd-ℿ₁ J K = s≤s (m≤m+n (kd-size J) (kd-size K))

<kd-ℿ₂ : ∀ J K → K <kd ℿ J K
<kd-ℿ₂ J K = s≤s (m≤n+m (kd-size K) (kd-size J))

liftKind-preserves-size : ∀ (f : Var → Var) K →
  kd-size (liftKind f K) ≡ kd-size K
liftKind-preserves-size f (A ∙∙ B) = refl
liftKind-preserves-size f (ℿ J K) = begin
    kd-size (liftKind f (ℿ J K))
  ≡⟨ refl ⟩
    kd-size (ℿ (liftKind f J) (liftKind f K))
  ≡⟨ refl ⟩
    suc (kd-size (liftKind f J) + kd-size (liftKind f K))
  ≡⟨ cong
      (λ t → suc (t + kd-size (liftKind f K)))
      (liftKind-preserves-size f J)
   ⟩
    suc (kd-size J + kd-size (liftKind f K))
  ≡⟨ cong
      (λ t → suc (kd-size J + t))
      (liftKind-preserves-size f K)
   ⟩
    suc (kd-size J + kd-size K)
  ≡⟨ refl ⟩
    kd-size (ℿ J K)
  ∎
  where
    open ≡-Reasoning

liftKind-preserves-<₁ : ∀ J K (f : Var → Var) →
  J <kd K → liftKind f J <kd K
liftKind-preserves-<₁ J K f J<K rewrite liftKind-preserves-size f J = J<K

mutual
  <kd-wf : WellFounded (_<kd_)
  <kd-wf K = acc (<kd-acc (kd-size K))

  <kd-acc : ∀ i K → kd-size K < i → Acc _<kd_ K
  <kd-acc zero K ()
  <kd-acc (suc n) (A ∙∙ B) _ = acc (λ _ ())
  <kd-acc (suc n) (ℿ J K) (s≤s ℿJK≤n) =
    acc (λ J J<ℿJK → <kd-acc n J (<-transˡ J<ℿJK ℿJK≤n))

module _ {ℓ} where
  open All <kd-wf ℓ public
    renaming ( wfRecBuilder to <kd-recBuilder
             ; wfRec to <kd-rec
             )
    hiding (wfRec-builder)

data _<ty_ : Type → Type → Set where
  <ty-⇒₁ : ∀{A B} → A <ty A ⇒ B
  <ty-⇒₂ : ∀{A B} → B <ty A ⇒ B
  <ty-∀ : ∀{k τ} → τ <ty ∀' k τ
  <ty-ƛ : ∀{k τ} → τ <ty ƛ k τ
