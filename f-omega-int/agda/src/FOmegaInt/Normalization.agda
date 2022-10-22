module FOmegaInt.Normalization where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality as PropEq

open import Data.Context
open import FOmegaInt.Syntax renaming (lookup to lookupKd)
open import FOmegaInt.Typing
open import FOmegaInt.Structural
open import FOmegaInt.Reduction

mutual
  data ⟨_,_⟩∈⟦_⟧[_] {n : ℕ} : Env n → Type n → Kind n → Context n → Set where
    denot-typ : ∀{H v Γ} → H ⊢ v val → ⟨ H , v ⟩∈⟦ ✶ ⟧[ Γ ]
    denot-intv : ∀{A B H v Γ} →
      Γ ⊢ty A ≤ v ∈ ✶ → Γ ⊢ty v ≤ B ∈ ✶ → H ⊢ v val →
      ⟨ H , v ⟩∈⟦ A ∙∙ B ⟧[ Γ ]
    denot-abs : ∀{J : Kind n} {K : Kind (suc n)} {H : Env n}
        {A : Type (suc n)} {Γ : Context n} →
      -- The on-paper rules use τₓ ∈ ⟦J⟧, but this breaks the positivity
      -- checker. Thankfully, we can use the regular kinding rules (via Γ) as a
      -- surrogate.
      ( (τₓ : Type n) → (px : H ⊢ τₓ val) → Γ ⊢ty τₓ ∈ J
      → ⟨ H , τₓ [ px ] , A ⟩∈ℰ⟦ K ⟧[ J ∷ Γ ]
      ) →
      ⟨ H , ƛ J A ⟩∈⟦ ℿ J K ⟧[ Γ ]

  record ⟨_,_⟩∈ℰ⟦_⟧[_] {n : ℕ}
      (H : Env n) (A : Type n) (K : Kind n) (Γ : Context n) : Set where
    inductive
    constructor N
    field
      gas : ℕ
      τ : Type n
      eval : H ⊢ A ⟱[ gas ] τ
      denot : ⟨ H , τ ⟩∈⟦ K ⟧[ Γ ]

data _⊨_ : ∀{n} → Context n → Env n → Set where
  c-emp : [] ⊨ ∅
  -- I don't really understand why it can't infer the [suc n] on the output
  -- here
  c-cons : ∀{n Γ H K τ p} →
    Γ ⊢ty τ ∈ K → _⊨_ {n} Γ H → _⊨_ {suc n} (K ∷ Γ) (H , τ [ p ])

record Lookup {n : ℕ}
    (Γ : Context n) (H : Env n) (K : Kind n) (v : Fin n) : Set where
  constructor L
  field
    τ : Type n
    kinding : Γ ⊢ty τ ∈ K
    proof : lookupTy H v ≡ τ

consistentEnv : ∀{n} {Γ : Context n} {H : Env n} {K : Kind n} →
  Γ ⊨ H → {v : Fin n} → lookupKd Γ v ≡ K → Lookup Γ H K v
consistentEnv {zero} {[]} {∅} {_} c-emp {()}
consistentEnv {suc n} {K ∷ _} {_ , τ [ _ ]} {_} (c-cons k _) {zero} refl =
  L (weakenTy τ) {!!} refl
consistentEnv {suc n} {K ∷ Γ} {H , t [ pt ]} {_} (c-cons _ p) {suc i} refl =
  let L τ kinding proof = consistentEnv {n} {Γ} {H} p {i} refl

      open ≡-Reasoning
      proof' : lookupTy (H , t [ pt ]) (suc i) ≡ weakenTy τ
      proof' = begin
        lookupTy (H , t [ pt ]) (suc i) ≡⟨ refl ⟩
        weakenTy (lookupTy H i) ≡⟨ cong weakenTy proof ⟩
        weakenTy τ
        ∎
   in
  L (weakenTy τ) (weaken-kinding kinding) proof'

typesNormalize : ∀{n} {Γ : Context n} {H : Env n} {A K} →
  Γ ⊢ty A ∈ K → Γ ⊨ H → ⟨ H , A ⟩∈ℰ⟦ K ⟧[ Γ ]
typesNormalize (k-var Γ-is-ctx trace) cs =
  let L τ kinding proof = consistentEnv cs trace
   in
  N 0 τ {!!} {!!}
typesNormalize k-top _ = N 0 ⊤ eval-⊤ (denot-typ v-top)
typesNormalize k-bot _ = N 0 ⊥ eval-⊥ (denot-typ v-bot)
typesNormalize (k-arr pA pB) cs =
  let N a α evalA denotA = typesNormalize pA cs
      N b β evalB denotB = typesNormalize pB cs
      varr = v-arr (⟱-spec evalA) (⟱-spec evalB)
   in
  N (a + b) (α ⇒ β) (eval-arr evalA evalB) (denot-typ varr)
typesNormalize (k-all {K} {A} pK pA) _ = N 0 (∀' K A) eval-∀' (denot-typ v-all)
typesNormalize {n} {Γ} {H} (k-abs {J} {K} {A} pJ pK pA) cs =
  let d-inner : (τ : Type n) → (vτ : H ⊢ τ val) → Γ ⊢ty τ ∈ J →
        ⟨ (H , τ [ vτ ]) , A ⟩∈ℰ⟦ K ⟧[ J ∷ Γ ]
      d-inner τ vτ pτ = typesNormalize {suc n} pA (c-cons pτ cs)

      denot = denot-abs d-inner
   in
  N 0 (ƛ J A) eval-ƛ denot
typesNormalize (k-app rule rule₁ x x₁) _ = {! !}
typesNormalize (k-sing {A} {B} {C} p) cs =
  let N n τ eval denot = typesNormalize p cs
   in
  N n τ eval {!!}
typesNormalize (k-sub rule x) _ = {! !}
