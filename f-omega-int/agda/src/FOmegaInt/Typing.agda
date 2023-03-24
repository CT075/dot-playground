module FOmegaInt.Typing where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

open import Data.Context using ([]; _∷_)
open import FOmegaInt.Syntax

infix 4 _ctx _⊢_kd
infix 4 _⊢ty_∈_
infix 4 _⊢kd_≤_ _⊢ty_≤_∈_
infix 4 _⊢ty_==_∈_

mutual
  -- Context validity
  data _ctx : {n : ℕ} → Context n → Set where
    c-empty : [] ctx
    c-kdbind : ∀{n} → {Γ : Context n} → {K : Kind n} →
      Γ ctx → Γ ⊢ K kd → K ∷ Γ ctx

  -- Kind validity
  data _⊢_kd {n : ℕ} (Γ : Context n) : Kind n → Set where
    -- TODO: [wf-type], [k-top] and [k-bot] are redundant, so we should remove
    -- them
    wf-type : Γ ⊢ ✶ kd
    wf-intv : ∀ {A B} → Γ ⊢ty A ∈ ✶ → Γ ⊢ty B ∈ ✶ → Γ ⊢ A ∙∙ B kd
    wf-darr : ∀ {J K} → Γ ⊢ J kd → J ∷ Γ ⊢ K kd → Γ ⊢ ℿ J K kd

  -- Kind assignment
  data _⊢ty_∈_ {n : ℕ} (Γ : Context n) : Type n → Kind n → Set where
    k-var : ∀{x k} → Γ ctx → lookup Γ x ≡ k → Γ ⊢ty Var x ∈ k
    k-top : Γ ⊢ty ⊤ ∈ ✶
    k-bot : Γ ⊢ty ⊥ ∈ ✶
    k-arr : ∀{A B} → Γ ⊢ty A ∈ ✶ → Γ ⊢ty B ∈ ✶ → Γ ⊢ty A ⇒ B ∈ ✶
    k-all : ∀{K A} → Γ ⊢ K kd → K ∷ Γ ⊢ty A ∈ ✶ → Γ ⊢ty ∀' K A ∈ ✶
    k-abs : ∀{J K A} →
      Γ ⊢ J kd → J ∷ Γ ⊢ty A ∈ K →
      Γ ⊢ty ƛ J A ∈ ℿ J K
    k-app : ∀{J K A B} →
      Γ ⊢ty A ∈ ℿ J K → Γ ⊢ty B ∈ J → J ∷ Γ ⊢ K kd → Γ ⊢ plugKd K B kd →
      Γ ⊢ty A ∙ B ∈ plugKd K B
    k-sing : ∀{A B C} → Γ ⊢ty A ∈ B ∙∙ C → Γ ⊢ty A ∈ A ∙∙ A
    k-sub : ∀{J K A} → Γ ⊢ty A ∈ J → Γ ⊢kd J ≤ K → Γ ⊢ty A ∈ K

  -- Subkinding
  data _⊢kd_≤_ {n : ℕ} (Γ : Context n) : Kind n → Kind n → Set where
    sk-intv : ∀{A₁ A₂ B₁ B₂} →
      Γ ⊢ty A₂ ≤ A₁ ∈ ✶ → Γ ⊢ty B₁ ≤ B₂ ∈ ✶ → Γ ⊢kd A₁ ∙∙ B₁ ≤ A₂ ∙∙ B₂
    sk-darr : ∀{J₁ J₂ K₁ K₂} →
      Γ ⊢ ℿ J₁ K₁ kd → Γ ⊢kd J₂ ≤ J₁ → J₂ ∷ Γ ⊢kd K₁ ≤ K₂ →
      Γ ⊢kd ℿ J₁ K₁ ≤ ℿ J₂ K₂

  -- Subtyping
  data _⊢ty_≤_∈_ {n} (Γ : Context n) : Type n → Type n → Kind n → Set where
    st-refl : ∀{K A} → Γ ⊢ty A ∈ K → Γ ⊢ty A ≤ A ∈ K
    st-trans : ∀{K A B C} →
      Γ ⊢ty A ≤ B ∈ K → Γ ⊢ty B ≤ C ∈ K → Γ ⊢ty A ≤ C ∈ K
    st-top : ∀{A B C} → Γ ⊢ty A ∈ B ∙∙ C → Γ ⊢ty A ≤ ⊤ ∈ ✶
    st-bot : ∀{A B C} → Γ ⊢ty A ∈ B ∙∙ C → Γ ⊢ty ⊥ ≤ A ∈ ✶
    st-β₁ : ∀{J K A B} →
      J ∷ Γ ⊢ty A ∈ K → Γ ⊢ty B ∈ J →
      Γ ⊢ty plugTy A B ∈ plugKd K B →
      J ∷ Γ ⊢ K kd → Γ ⊢ plugKd K B kd →
      Γ ⊢ty (ƛ J A) ∙ B ≤ plugTy A B ∈ plugKd K B
    st-β₂ : ∀{J K A B} →
      J ∷ Γ ⊢ty A ∈ K → Γ ⊢ty B ∈ J →
      Γ ⊢ty plugTy A B ∈ plugKd K B →
      J ∷ Γ ⊢ K kd → Γ ⊢ plugKd K B kd →
      Γ ⊢ty plugTy A B ≤ (ƛ J A) ∙ B ∈ plugKd K B
    st-η₁ : ∀{A J K} →
      Γ ⊢ty A ∈ ℿ J K → Γ ⊢ty ƛ J (weakenTy A ∙ Var zero) ≤ A ∈ ℿ J K
    st-η₂ : ∀{A J K} →
      Γ ⊢ty A ∈ ℿ J K → Γ ⊢ty A ≤ ƛ J (weakenTy A ∙ Var zero) ∈ ℿ J K
    st-arr : ∀{A₁ A₂ B₁ B₂} →
      Γ ⊢ty A₂ ≤ A₁ ∈ ✶ → Γ ⊢ty B₁ ≤ B₂ ∈ ✶ → Γ ⊢ty A₁ ⇒ B₁ ≤ A₂ ⇒ B₂ ∈ ✶
    st-all : ∀{K₁ K₂ A₁ A₂} →
      Γ ⊢ty ∀' K₁ A₁ ∈ ✶ → Γ ⊢kd K₂ ≤ K₁ → K₂ ∷ Γ ⊢ty A₁ ≤ A₂ ∈ ✶ →
      Γ ⊢ty ∀' K₁ A₁ ≤ ∀' K₂ A₂ ∈ ✶
    st-abs : ∀{K J J₁ J₂ A₁ A₂} →
      Γ ⊢ty ƛ J₁ A₁ ∈ ℿ J K → Γ ⊢ty ƛ J₂ A₂ ∈ ℿ J K → J ∷ Γ ⊢ty A₁ ≤ A₂ ∈ K →
      Γ ⊢ty ƛ J₁ A₁ ≤ ƛ J₂ A₂ ∈ ℿ J K
    st-app : ∀{K J A₁ A₂ B₁ B₂} →
      Γ ⊢ty A₁ ≤ A₂ ∈ ℿ J K → Γ ⊢ty B₁ == B₂ ∈ J →
      Γ ⊢ty B₁ ∈ J → J ∷ Γ ⊢ K kd → Γ ⊢ plugKd K B₁ kd →
      Γ ⊢ty A₁ ∙ B₁ ≤ A₂ ∙ B₂ ∈ plugKd K B₁
    st-bnd₁ : ∀{A B₁ B₂} → Γ ⊢ty A ∈ B₁ ∙∙ B₂ → Γ ⊢ty B₁ ≤ A ∈ ✶
    st-bnd₂ : ∀{A B₁ B₂} → Γ ⊢ty A ∈ B₁ ∙∙ B₂ → Γ ⊢ty A ≤ B₂ ∈ ✶
    st-intv : ∀{A₁ A₂ B C} → Γ ⊢ty A₁ ≤ A₂ ∈ B ∙∙ C → Γ ⊢ty A₁ ≤ A₂ ∈ A₁ ∙∙ A₂
    st-sub : ∀{J K A₁ A₂} → Γ ⊢ty A₁ ≤ A₂ ∈ J → Γ ⊢kd J ≤ K → Γ ⊢ty A₁ ≤ A₂ ∈ K

  -- Type equality
  record _⊢ty_==_∈_ {n}
      (Γ : Context n) (A : Type n) (B : Type n) (K : Kind n) : Set where
    inductive
    constructor E
    field
      left : Γ ⊢ty A ≤ B ∈ K
      right : Γ ⊢ty B ≤ A ∈ K

  record _⊢kd_==_ {n}
      (Γ : Context n) (K : Kind n) (J : Kind n) : Set where
    inductive
    constructor Ek
    field
      left : Γ ⊢kd K ≤ J
      right : Γ ⊢kd J ≤ K

eq-refl : ∀{n} {Γ : Context n} {A K} → Γ ⊢ty A ∈ K → Γ ⊢ty A == A ∈ K
eq-refl A∈K = E (st-refl A∈K) (st-refl A∈K)

eq-sym : ∀{n} {Γ : Context n} {A B K} → Γ ⊢ty A == B ∈ K → Γ ⊢ty B == A ∈ K
eq-sym (E A≤B B≤A) = E B≤A A≤B

-- Validity lemmas

postulate
  kinding-valid : ∀{n} {Γ : Context n} {A K} → Γ ⊢ty A ∈ K → Γ ⊢ K kd

  subkinding-valid : ∀{n} {Γ : Context n} {J K} →
    Γ ⊢kd J ≤ K → Γ ⊢ J kd × Γ ⊢ K kd

  subtyping-valid : ∀{n} {Γ : Context n} {A B K} →
    Γ ⊢ty A ≤ B ∈ K → Γ ⊢ty A ∈ K × Γ ⊢ty B ∈ K

  kinding-subst : ∀{n} {Γ : Context n} {A τ J K} →
    J ∷ Γ ⊢ty A ∈ K → Γ ⊢ty τ ∈ J → Γ ⊢ty plugTy A τ ∈ plugKd K τ

  wf-narrow : ∀{n} {Γ : Context n} {J J' K} →
    J' ∷ Γ ⊢ K kd → Γ ⊢kd J ≤ J' → J ∷ Γ ⊢ K kd

-- Lemmas

intv-invert : ∀{n} {Γ : Context n} {B C} →
  Γ ⊢ B ∙∙ C kd → Γ ⊢ty B ∈ ✶ × Γ ⊢ty C ∈ ✶
intv-invert wf-type = k-bot , k-top
intv-invert (wf-intv B∈✶ C∈✶) = B∈✶ , C∈✶

intv-proper : ∀{n} {Γ : Context n} {A B C} → Γ ⊢ty A ∈ B ∙∙ C → Γ ⊢ty A ∈ ✶
intv-proper A∈B∙∙C =
  let A∈A∙∙A = k-sing A∈B∙∙C
      ⊥≤A = st-bot A∈B∙∙C
      A≤⊤ = st-top A∈B∙∙C
      A∙∙A≤⊥∙∙⊤ = sk-intv ⊥≤A A≤⊤
   in
  k-sub A∈A∙∙A A∙∙A≤⊥∙∙⊤

postulate
  intv-widen : ∀{n} {Γ : Context n} {A B C} →
    Γ ⊢ty A ∈ B ∙∙ C → Γ ⊢kd B ∙∙ C ≤ ✶

  intv-spec : ∀{n} {Γ : Context n} {A B C K} →
    Γ ⊢ty B ≤ A ∈ K → Γ ⊢ty A ≤ C ∈ K → Γ ⊢ty A ∈ B ∙∙ C

  sk-trans : ∀{n} {Γ : Context n} {J K L} →
    Γ ⊢kd J ≤ K → Γ ⊢kd K ≤ L → Γ ⊢kd J ≤ L

  sk-refl : ∀{n} {Γ : Context n} {K} → Γ ⊢ K kd → Γ ⊢kd K ≤ K

  sk-plug : ∀{n} {Γ : Context n} {K₁ K₂ J τ} →
    J ∷ Γ ⊢kd K₁ ≤ K₂ → Γ ⊢ty τ ∈ J → Γ ⊢kd (plugKd K₁ τ) ≤ (plugKd K₂ τ)

  weaken-st : ∀{n} {Γ : Context n} {A B K K'} →
    Γ ⊢ty A ≤ B ∈ K → K' ∷ Γ ⊢ty (weakenTy A) ≤ (weakenTy B) ∈ (weakenKd K)
