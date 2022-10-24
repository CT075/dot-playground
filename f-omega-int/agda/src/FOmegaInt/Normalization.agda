module FOmegaInt.Normalization where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

open import Data.Context
open import FOmegaInt.Syntax renaming (lookup to lookupKd)
open import FOmegaInt.Typing
open import FOmegaInt.Structural
open import FOmegaInt.Reduction

mutual
  -- XXX: It worries me a little that we need to rely so much on parameterizing
  -- on the typing context Γ.
  data ⟨_,_⟩∈⟦_⟧[_] {n : ℕ} : Env n → Type n → Kind n → Context n → Set where
    denot-typ : ∀{H v Γ} → Γ ⊢ty v ∈ ✶ → H ⊢ v val → ⟨ H , v ⟩∈⟦ ✶ ⟧[ Γ ]
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
    isVal : H ⊢ τ val
    kinding : Γ ⊢ty τ ∈ K
    proof : lookup H v ≡ V τ isVal

consistentEnv : ∀{n} {Γ : Context n} {H : Env n} {K : Kind n} →
  Γ ⊨ H → {v : Fin n} → lookupKd Γ v ≡ K → Lookup Γ H K v
consistentEnv {zero} {[]} {∅} {_} c-emp {()}
consistentEnv {suc n} {K ∷ _} {_ , τ [ p ]} {_} (c-cons k _) {zero} refl =
  L (weakenTy τ) (weaken-isVal p τ p) (weaken-kinding k) refl
consistentEnv {suc n} {K ∷ Γ} {H , t [ pt ]} {_} (c-cons _ p) {suc i} refl =
  let L τ isVal kinding proof = consistentEnv {n} {Γ} {H} p {i} refl

      open ≡-Reasoning
      proof' : lookup (H , t [ pt ]) (suc i) ≡ weakenVal (V τ isVal) t pt
      proof' = begin
        lookup (H , t [ pt ]) (suc i) ≡⟨ refl ⟩
        weakenVal (lookup H i) t pt ≡⟨ cong (λ tm → weakenVal tm t pt) proof ⟩
        weakenVal (V τ isVal) t pt
        ∎
   in
  L (weakenTy τ) (weaken-isVal isVal t pt) (weaken-kinding kinding) proof'

kinding-rev-preservation : ∀{n gas}
  {Γ : Context n} {H : Env n} {A τ : Type n} {K : Kind n} →
  Γ ⊢ty τ ∈ K → Γ ⊨ H → H ⊢ A ⟱[ gas ] τ → Γ ⊢ty A ∈ K
kinding-rev-preservation k cs (eval-var trace) = {!!}
kinding-rev-preservation k cs eval-⊤ = k
kinding-rev-preservation k cs eval-⊥ = k
kinding-rev-preservation k cs eval-∀' = k
kinding-rev-preservation k cs eval-ƛ = k
kinding-rev-preservation k cs (eval-arr pA pB) = {! !}
kinding-rev-preservation k cs (eval-app pA pB pAB) = {! !}

denot-val : ∀{n} {Γ : Context n} {H : Env n} {τ : Type n} {K : Kind n} →
  ⟨ H , τ ⟩∈⟦ K ⟧[ Γ ] → H ⊢ τ val
denot-val (denot-typ _ τ-is-val) = τ-is-val
denot-val (denot-intv lower upper τ-is-val) = τ-is-val
denot-val (denot-abs τ-is-val) = v-abs

denot-kind-ℰ : ∀{n} {Γ : Context n} {H : Env n} {A : Type n} {K : Kind n} →
  ⟨ H , A ⟩∈ℰ⟦ K ⟧[ Γ ] → Γ ⊨ H → Γ ⊢ty A ∈ K
denot-kind : ∀{n} {Γ : Context n} {H : Env n} {τ : Type n} {K : Kind n} →
  ⟨ H , τ ⟩∈⟦ K ⟧[ Γ ] → Γ ⊨ H → Γ ⊢ty τ ∈ K

denot-kind-ℰ (N gas τ eval denot) cs =
  kinding-rev-preservation (denot-kind denot cs) cs eval

denot-kind (denot-typ pk x) cs = pk
denot-kind (denot-intv lower upper τ-is-val) cs = {!!}
denot-kind (denot-abs f) cs = {! !}

record FunctionInversion {n}
    (Γ : Context n) (H : Env n) (J : Kind n) (K : Kind (suc n))
    (τₓ : Type n) : Set where
  constructor F
  field
    body : Type (suc n)
    px : H ⊢ τₓ val
    proof : ⟨ (H , τₓ [ px ]) , body ⟩∈ℰ⟦ K ⟧[ J ∷ Γ ]

functionInversion : ∀{n} {Γ : Context n} {H : Env n} {τ J K} →
  ⟨ H , τ ⟩∈⟦ ℿ J K ⟧[ Γ ] → Γ ⊨ H →
  ((τₓ : Type n) → ⟨ H , τₓ ⟩∈⟦ J ⟧[ Γ ] → FunctionInversion Γ H J K τₓ)
functionInversion (denot-abs {_} {_} {_} {body} {_} f) cs = λ τₓ p →
  F body (denot-val p) (f τₓ (denot-val p) {!!})

-- Technically, the [H ⊢ τ val] premise in [val-denot] is implied by the
-- consistent environment premise. However, it simplifies the proofs a lot to
-- pass it explicitly.
val-denot : ∀{n} {Γ : Context n} {H : Env n} {τ : Type n} {K : Kind n} →
  Γ ⊢ty τ ∈ K → Γ ⊨ H → H ⊢ τ val → ⟨ H , τ ⟩∈⟦ K ⟧[ Γ ]

-- Following the other schemes, another name for [typesNormalize] would be
-- kind-denot-ℰ
typesNormalize : ∀{n} {Γ : Context n} {H : Env n} {A K} →
  Γ ⊢ty A ∈ K → Γ ⊨ H → ⟨ H , A ⟩∈ℰ⟦ K ⟧[ Γ ]

val-denot (k-var Γ-is-ctx trace) _ ()
val-denot k-top _ = denot-typ k-top
val-denot k-bot _ = denot-typ k-bot
val-denot (k-arr τ₁ τ₂) _ (v-arr p₁ p₂) = denot-typ (k-arr τ₁ τ₂) (v-arr p₁ p₂)
val-denot (k-all x p) _ = denot-typ (k-all x p)
val-denot {n} {Γ} {H} {ƛ J A} {ℿ J K}
  (k-abs J-is-kd K-is-kd body-is-J) cs v-abs =
  let body-normalizes :
        (τₓ : Type n) → (px : H ⊢ τₓ val) → Γ ⊢ty τₓ ∈ J →
        ⟨ H , τₓ [ px ] , A ⟩∈ℰ⟦ K ⟧[ J ∷ Γ ]
      body-normalizes τₓ px τₓ-is-J =
        typesNormalize
          -- TODO: need a substitution lemma here
          {!!}
          (c-cons τₓ-is-J cs)
   in
  denot-abs body-normalizes
val-denot (k-app p p₁ x x₁) _ ()
val-denot (k-sing A-is-bounded) _ =
  denot-intv (st-bnd₁ (k-sing A-is-bounded)) (st-bnd₂ (k-sing A-is-bounded))
val-denot (k-sub A-is-J J≤K) _ _ = {! !}

typesNormalize (k-var Γ-is-ctx trace) cs =
  let L τ isVal kinding proof = consistentEnv cs trace
   in
  -- TODO: structural lemmas wheeeeeeeee
  N 0 τ (eval-var proof) (val-denot kinding cs isVal)
typesNormalize k-top _ = N 0 ⊤ eval-⊤ (denot-typ k-top v-top)
typesNormalize k-bot _ = N 0 ⊥ eval-⊥ (denot-typ k-bot v-bot)
typesNormalize (k-arr pA pB) cs =
  let N a α evalA denotA = typesNormalize pA cs
      N b β evalB denotB = typesNormalize pB cs
      varr = v-arr (⟱-spec evalA) (⟱-spec evalB)
   in
  N (a + b)
    (α ⇒ β)
    (eval-arr evalA evalB)
    (denot-typ (k-arr (denot-kind denotA cs) (denot-kind denotB cs)) varr)
typesNormalize (k-all {K} {A} pK pA) _ =
  N 0 (∀' K A) eval-∀' (denot-typ (k-all pK pA) v-all)
typesNormalize {n} {Γ} {H} (k-abs {J} {K} {A} pJ pK pA) cs =
  let d-inner : (τ : Type n) → (vτ : H ⊢ τ val) → Γ ⊢ty τ ∈ J →
        ⟨ (H , τ [ vτ ]) , A ⟩∈ℰ⟦ K ⟧[ J ∷ Γ ]
      d-inner τ vτ pτ = typesNormalize {suc n} pA (c-cons pτ cs)

      denot = denot-abs d-inner
   in
  N 0 (ƛ J A) eval-ƛ denot
typesNormalize (k-app a-is-prod b-is-j k-is-kd kb-is-kd) cs = {! !}
typesNormalize (k-sing p) cs =
  let N n τ eval denot = typesNormalize p cs
   in
  -- TODO: need to show that A ⟱ τ implies τ ≤ A
  N n τ eval (denot-intv {!!} {!!} (⟱-spec eval))
-- TODO: Semantic widening
typesNormalize (k-sub rule x) _ = {! !}
