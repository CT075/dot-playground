module FOmegaInt.Typing where

open import Data.List using ([])

open import Data.Var
open import Data.Context

open import FOmegaInt.Syntax

infix 4 _ctx _⊢_kd
infix 4 _⊢ty_∈_
infix 4 _⊢kd_≤_ _⊢ty_≤_∈_
infix 4 _⊢ty_==_∈_

data VarFact : Set where
  Kd : Kind → VarFact              -- Type variable kind assignment
  Ty : Type → VarFact              -- Term variable type assignment
  Alias : Type → Kind → VarFact    -- Type variable alias

liftVarFact : (Var → Var) → VarFact → VarFact
liftVarFact f (Kd k) = Kd (liftKind f k)
liftVarFact f (Ty τ) = Ty (liftType f τ)
liftVarFact f (Alias τ k) = Alias (liftType f τ) (liftKind f k)

instance
  VarFactLift : Lift VarFact
  VarFactLift = record {lift = liftVarFact}

Context = Ctx VarFact

mutual
  -- Context validity
  data _ctx : Context → Set where
    c-empty : [] ctx
    c-bind-kd : ∀{Γ x k} → Γ ctx → Γ ⊢ k kd → Γ & x ~ (Kd k) ctx
    c-bind-ty : ∀{Γ x τ k} → Γ ctx → Γ ⊢ty τ ∈ k → Γ & x ~ Ty τ ctx
    c-bind-alias : ∀{Γ x τ k} → Γ ctx → Γ ⊢ty τ ∈ k → Γ & x ~ Alias τ k ctx

  -- Kind validity
  data _⊢_kd (Γ : Context) : Kind → Set where
    wf-type : Γ ⊢ ✶ kd
    wf-intv : ∀ {A B} → Γ ⊢ty A ∈ ✶ → Γ ⊢ty B ∈ ✶ → Γ ⊢ A ∙∙ B kd
    wf-darr : ∀{x J K} →
      Γ ⊢ J kd →
      Γ & x ~ Kd J ⊢ (openKind x K) kd →
      Γ ⊢ ℿ J K kd

  -- Kind assignment
  data _⊢ty_∈_ (Γ : Context) : Type → Kind → Set where
    k-var : ∀{x k} → Γ ctx → Γ [ x ]⊢> Kd k → Γ ⊢ty `(Free x) ∈ k
    k-alias : ∀{x τ k} → Γ ctx → Γ [ x ]⊢> Alias τ k → Γ ⊢ty `(Free x) ∈ k
    k-top : Γ ⊢ty ⊤ ∈ ✶
    k-bot : Γ ⊢ty ⊥ ∈ ✶
    k-arr : ∀{A B} →
      Γ ⊢ty A ∈ ✶ →
      Γ ⊢ty B ∈ ✶ →
      Γ ⊢ty A ⇒ B ∈ ✶
    k-all : ∀{x k A} →
      Γ ⊢ k kd →
      Γ & x ~ Kd k ⊢ty openType x A ∈ ✶ →
      Γ ⊢ty ∀' k A ∈ ✶
    -- TODO: validity conditions?
    k-abs : ∀{x J K A} →
      Γ ⊢ J kd →
      Γ & x ~ (Kd J) ⊢ty openType x A ∈ openKind x K →
      Γ ⊢ty ƛ J A ∈ ℿ J K
    k-app : ∀{f x J K} →
      Γ ⊢ty `(Free f) ∈ ℿ J K →
      Γ ⊢ty `(Free x) ∈ J →
      Γ ⊢ty Free f ⊡ Free x ∈ bindKind (Free x) K
    k-sing : ∀{A B C} → Γ ⊢ty A ∈ B ∙∙ C → Γ ⊢ty A ∈ A ∙∙ A
    k-sub : ∀{J K A} → Γ ⊢ty A ∈ J → Γ ⊢kd J ≤ K → Γ ⊢ty A ∈ K

  -- Subkinding
  data _⊢kd_≤_ (Γ : Context) : Kind → Kind → Set where
    sk-intv : ∀{A₁ A₂ B₁ B₂} →
      Γ ⊢ty A₂ ≤ A₁ ∈ ✶ → Γ ⊢ty B₁ ≤ B₂ ∈ ✶ → Γ ⊢kd A₁ ∙∙ B₁ ≤ A₂ ∙∙ B₂
    sk-darr : ∀{x J₁ J₂ K₁ K₂} →
      Γ ⊢kd J₂ ≤ J₁ →
      Γ & x ~ (Kd J₂) ⊢kd openKind x K₁ ≤ openKind x K₂ →
      Γ ⊢kd ℿ J₁ K₁ ≤ ℿ J₂ K₂

  -- Subtyping
  data _⊢ty_≤_∈_ (Γ : Context) : Type → Type → Kind → Set where
    st-refl : ∀{K A} → Γ ⊢ty A ∈ K → Γ ⊢ty A ≤ A ∈ K
    st-trans : ∀{K A B C} → Γ ⊢ty A ≤ B ∈ K → Γ ⊢ty B ≤ C ∈ K → Γ ⊢ty A ≤ C ∈ K
    st-top : ∀{A B C} → Γ ⊢ty A ∈ B ∙∙ C → Γ ⊢ty A ≤ ⊤ ∈ ✶
    st-bot : ∀{A B C} → Γ ⊢ty A ∈ B ∙∙ C → Γ ⊢ty ⊥ ≤ A ∈ ✶
    st-arr : ∀{A₁ A₂ B₁ B₂} →
      Γ ⊢ty A₂ ≤ A₁ ∈ ✶ →
      Γ ⊢ty B₁ ≤ B₂ ∈ ✶ →
      Γ ⊢ty A₁ ⇒ B₁ ≤ A₂ ⇒ B₂ ∈ ✶
    st-all : ∀{x K₁ K₂ A₁ A₂} →
      Γ ⊢ty ∀' K₁ A₁ ∈ ✶ →
      Γ ⊢kd K₂ ≤ K₁ →
      Γ & x ~ (Kd K₂) ⊢ty openType x A₁ ≤ openType x A₂ ∈ ✶ →
      Γ ⊢ty ∀' K₁ A₁ ≤ ∀' K₂ A₂ ∈ ✶
    st-abs : ∀{x K J J₁ J₂ A₁ A₂} →
      Γ ⊢ty ƛ J₁ A₁ ∈ ℿ J K →
      Γ ⊢ty ƛ J₂ A₂ ∈ ℿ J K →
      Γ & x ~ (Kd J) ⊢ty openType x A₁ ≤ openType x A₂ ∈ K →
      Γ ⊢ty ƛ J₁ A₁ ≤ ƛ J₂ A₂ ∈ ℿ J K
    st-bnd₁ : ∀{A B₁ B₂} → Γ ⊢ty A ∈ B₁ ∙∙ B₂ → Γ ⊢ty B₁ ≤ A ∈ ✶
    st-bnd₂ : ∀{A B₁ B₂} → Γ ⊢ty A ∈ B₁ ∙∙ B₂ → Γ ⊢ty A ≤ B₂ ∈ ✶
    st-intv : ∀{A₁ A₂ B C} → Γ ⊢ty A₁ ≤ A₂ ∈ B ∙∙ C → Γ ⊢ty A₁ ≤ A₂ ∈ A₁ ∙∙ A₂
    st-sub : ∀{J K A₁ A₂} → Γ ⊢ty A₁ ≤ A₂ ∈ J → Γ ⊢kd J ≤ K → Γ ⊢ty A₁ ≤ A₂ ∈ K
    st-alias₁ : ∀{x τ k} → Γ [ x ]⊢> Alias τ k → Γ ⊢ty `(Free x) ≤ τ ∈ k
    st-alias₂ : ∀{x τ k} → Γ [ x ]⊢> Alias τ k → Γ ⊢ty τ ≤ `(Free x) ∈ k
    -- TODO: validity conditions
    st-β₁ : ∀{J₁ J₂ K x y A} →
      Γ ⊢ty `(Free x) == ƛ J₁ A ∈ ℿ J₂ K →
      Γ ⊢ty Free x ⊡ Free y ≤ bindType (Free y) A ∈ bindKind (Free y) K
    st-β₂ : ∀{J₁ J₂ K x y A} →
      Γ ⊢ty `(Free x) == ƛ J₁ A ∈ ℿ J₂ K →
      Γ ⊢ty bindType (Free y) A ≤ Free x ⊡ Free y ∈ bindKind (Free y) K
    -- TODO: Do we need eta?
    st-app : ∀{K J x₁ x₂ y₁ y₂} →
      Γ ⊢ty `(Free x₁) ≤ `(Free x₂) ∈ ℿ J K →
      Γ ⊢ty `(Free y₁) == `(Free y₂) ∈ J →
      Γ ⊢ty `(Free y₁) ∈ J →
      Γ ⊢ty Free x₁ ⊡ Free y₁ ≤ Free x₂ ⊡ Free y₂ ∈ bindKind (Free y₁) K

  -- Type equality
  data _⊢ty_==_∈_ (Γ : Context) : Type → Type → Kind → Set where
    st-antisym : ∀{K A B} →
      Γ ⊢ty A ≤ B ∈ K → Γ ⊢ty B ≤ A ∈ K → Γ ⊢ty A == B ∈ K

-- Lemmas/derived rules

intv≤✶ : ∀{Γ A B τ₁ τ₂ τ₃ τ₄} →
  Γ ⊢ty A ∈ τ₁ ∙∙ τ₂ → Γ ⊢ty B ∈ τ₃ ∙∙ τ₄ → Γ ⊢kd A ∙∙ B ≤ ✶
intv≤✶ Γ⊢A∈∙∙ Γ⊢B∈∙∙ = sk-intv (st-bot Γ⊢A∈∙∙) (st-top Γ⊢B∈∙∙)

{-
-- Lemmas

postulate
  intv-spec : ∀{n} {Γ : Context n} {A B C} →
    Γ ⊢ty B ≤ A ∈ ✶ → Γ ⊢ty A ≤ C ∈ ✶ → Γ ⊢ty A ∈ B ∙∙ C

  sk-trans : ∀{n} {Γ : Context n} {J K L} →
    Γ ⊢kd J ≤ K → Γ ⊢kd K ≤ L → Γ ⊢kd J ≤ L

  sk-refl : ∀{n} {Γ : Context n} {K} → Γ ⊢ K kd → Γ ⊢kd K ≤ K

  weaken-st : ∀{n} {Γ : Context n} {A B K K'} →
    Γ ⊢ty A ≤ B ∈ K → K' ∷ Γ ⊢ty (weakenTy A) ≤ (weakenTy B) ∈ (weakenKd K)

  st-kinding : ∀{n} {Γ : Context n} {A B K} →
    Γ ⊢ty A ≤ B ∈ K → Γ ⊢ty A ∈ K × Γ ⊢ty B ∈ K
-}
