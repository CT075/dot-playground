module FOmegaInt.Normalization where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product
open import Data.Unit renaming (⊤ to Unit)
open import Data.Empty renaming (⊥ to Void)
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

open import Data.Context
open import FOmegaInt.Syntax renaming (lookup to lookupKd)
open import FOmegaInt.Typing
open import FOmegaInt.Structural
open import FOmegaInt.Reduction

{-
Morally, we'd like to define our relation like this:

  module NotStrictlyPositive where
    mutual
      data ⟨_⟩∈⟦_⟧ : Type zero → Kind zero → Set where
        denot-intv : ∀{A B v} →
          [] ⊢ty A ≤ v ∈ ✶ → [] ⊢ty v ≤ B ∈ ✶ → v val →
          ⟨ v ⟩∈⟦ A ∙∙ B ⟧
        denot-abs : ∀{J J' : Kind zero} {K : Kind (suc zero)}
            {A : Type (suc zero)} →
          [] ⊢kd J ≤ J' →
          ((τₓ : Type zero) → ⟨ τₓ ⟩∈⟦ J ⟧ → ⟨ plug A τₓ ⟩∈ℰ⟦ plug K τₓ ⟧) →
          ⟨ ƛ J' A ⟩∈⟦ ℿ J K ⟧

However, this type isn't strictly positive (see the ⟨_,_⟩∈⟦_⟧ as a function
input in the denot-abs constructor), so we need to use structural recursion to
define this datatype.
-}

private mutual
  unfold-denot :
    (K : Kind zero) →
    (∀ J → J <kd K → Type zero → Set) →
    (∀ J → J <kd K → Type zero → Set) →
    Type zero → Set
  unfold-denot (A ∙∙ B) _ _ τ = τ val × [] ⊢ty A ≤ τ ∈ ✶ × [] ⊢ty τ ≤ B ∈ ✶
  unfold-denot (ℿ J K) recV recE (ƛ J' A) =
    -- This monstrosity is necessary to appease the termination checker,
    -- which otherwise can't tell that [plugTy K τₓ] is smaller than
    -- [ℿ J K].
    [] ⊢kd J ≤ J' ×
      (∀ τₓ →
        -- ⟨ τₓ ⟩∈'⟦ J ⟧
        recV J (<ℿ₁ J K) τₓ →
        --⟨ plugTy A τₓ ⟩∈'ℰ⟦ plugKd K τₓ ⟧
        recE (plugKd K τₓ) (<ℿ₂ J K τₓ) (plugTy A τₓ))
  unfold-denot (ℿ J K) _ _ _ = Void

  unfold-denot-eval :
    (K : Kind zero) →
    (∀ J → J <kd K → Type zero → Set) →
    (∀ J → J <kd K → Type zero → Set) →
    Type zero → Set
  unfold-denot-eval K recV recE A = Σ[ W ∈ (ℕ × Type zero) ](
    let (gas , τ) = W
     in
    A ⟱[ gas ] τ × unfold-denot K recV recE τ)

  unfold-joined : Fin 2 → Kind zero → Type zero → Set
  unfold-joined = <kd-mutual _ unfold-denots
    where
      unfold-denots :
        Fin 2 →
        (K : Kind zero) → (Fin 2 → (∀ J → J <kd K → Type zero → Set)) →
        Type zero → Set
      unfold-denots i K f with i
      ...                   | zero = unfold-denot K (f zero) (f (suc zero))
      ...                   | (suc zero) =
                                unfold-denot-eval K (f zero) (f (suc zero))

⟨_⟩∈'⟦_⟧ : Type zero → Kind zero → Set
⟨ τ ⟩∈'⟦ K ⟧ = unfold-joined zero K τ

⟨_⟩∈'ℰ⟦_⟧ : Type zero → Kind zero → Set
⟨ A ⟩∈'ℰ⟦ K ⟧ = unfold-joined (suc zero) K A

mutual
  -- While the recursive functions above are actually sufficient for our
  -- purposes, they're a pain to pattern match on, so we provide an
  -- inductive-recursive view here. Notice the use of ∈' (instead of just ∈) in
  -- the denot-abs constructor.
  data ⟨_⟩∈⟦_⟧ : Type zero → Kind zero → Set where
    denot-intv : ∀{A B v} →
      v val → [] ⊢ty A ≤ v ∈ ✶ → [] ⊢ty v ≤ B ∈ ✶ → ⟨ v ⟩∈⟦ A ∙∙ B ⟧
    denot-abs : ∀{J J' K A} →
      [] ⊢kd J ≤ J' →
      (∀ τₓ → ⟨ τₓ ⟩∈'⟦ J ⟧ → ⟨ plugTy A τₓ ⟩∈ℰ⟦ plugKd K τₓ ⟧) →
      ⟨ ƛ J' A ⟩∈⟦ ℿ J K ⟧

  record ⟨_⟩∈ℰ⟦_⟧ (A : Type zero) (K : Kind zero) : Set where
    inductive
    constructor N
    field
      gas : ℕ
      τ : Type zero
      eval : A ⟱[ gas ] τ
      denot : ⟨ τ ⟩∈⟦ K ⟧

-- Proof that the recursive view implies the inductive view
private mutual
  denot-ind-rec-v : ∀{τ : Type zero} {K : Kind zero} →
    ⟨ τ ⟩∈'⟦ K ⟧ → ⟨ τ ⟩∈⟦ K ⟧
  denot-ind-rec-v {_} {A ∙∙ B} (τ-val , A≤τ , τ≤B) =
    denot-intv τ-val A≤τ τ≤B
  denot-ind-rec-v {ƛ J' A} {ℿ J K} (J≤J' , f) = denot-abs J≤J' f'
    where
      f' : (τₓ : Type zero) → ⟨ τₓ ⟩∈'⟦ J ⟧ → ⟨ plugTy A τₓ ⟩∈ℰ⟦ plugKd K τₓ ⟧
      f' τₓ τₓ∈'⟦J⟧ = {!!}

  denot-rec-ind-e : ∀{τ : Type zero} {K : Kind zero} →
    ⟨ τ ⟩∈'ℰ⟦ K ⟧ → ⟨ τ ⟩∈ℰ⟦ K ⟧
  denot-rec-ind-e ((gas , τ) , (eval , denot)) =
    N gas τ eval (denot-ind-rec-v denot)

{-
mutual
  -- While the recursive functions above are actually sufficient for our
  -- purposes, they're a pain to pattern match on, so we provide an
  -- inductive-recursive view here. Notice the use of ∈' (instead of just ∈) in
  -- the denot-abs constructor.
  data ⟨_,_⟩∈⟦_⟧[_] {n : ℕ} : Env n → Type n → Kind n → Context n → Set where
    denot-intv : ∀{A B H v Γ} →
      H ⊢ v val →
      Σ[ W ∈ (ℕ × Type n) ] (norm-sub₁ Γ H A v W) →
      Σ[ W ∈ (ℕ × Type n) ] (norm-sub₂ Γ H B v W) →
      ⟨ H , v ⟩∈⟦ A ∙∙ B ⟧[ Γ ]
    denot-abs : ∀{J J' : Kind n} {K : Kind (suc n)} {H : Env n}
        {A : Type (suc n)} {Γ : Context n} →
      Γ ⊢kd J ≤ J' →
      ( ∀ τₓ τₓval → ⟨ H , τₓ ⟩∈'⟦ J ⟧[ Γ ] →
          ⟨ (H , τₓ [ τₓval ]) , A ⟩∈ℰ⟦ K ⟧[ J ∷ Γ ]) →
      ⟨ H , ƛ J' A ⟩∈⟦ ℿ J K ⟧[ Γ ]

  denot-typ : ∀{n } {Γ : Context n} {H : Env n} {τ : Type n} →
    H ⊢ τ val → Γ ⊢ty τ ∈ ✶ → ⟨ H , τ ⟩∈⟦ ✶ ⟧[ Γ ]
  denot-typ τval τ∈✶ =
    denot-intv
      τval
      ((0 , ⊥) , (eval-⊥ , st-bot τ∈✶))
      ((0 , ⊤) , (eval-⊤ , st-top τ∈✶))

mutual
  -- Proof that the inductive view implies the recursive view
  denot-ind-rec-v :
    ∀{n} {Γ : Context n} {H : Env n} {τ : Type n} {K : Kind n} →
    ⟨ H , τ ⟩∈⟦ K ⟧[ Γ ] → ⟨ H , τ ⟩∈'⟦ K ⟧[ Γ ]
  denot-ind-rec-v (denot-intv τ-val A≤τ τ≤B) = (τ-val , A≤τ , τ≤B)
  denot-ind-rec-v {n} {Γ} {H} {ƛ J' A} {ℿ J K} (denot-abs J≤J' f') =
    let f : ∀ τₓ τₓval → ⟨ H , τₓ ⟩∈'⟦ J ⟧[ Γ ] →
          ⟨ (H , τₓ [ τₓval ]) , A ⟩∈'ℰ⟦ K ⟧[ J ∷ Γ ]
        f τₓ τₓval p = denot-ind-rec-e (f' τₓ τₓval p)
     in
    (J≤J' , f)

  denot-ind-rec-e :
    ∀{n} {Γ : Context n} {H : Env n} {τ : Type n} {K : Kind n} →
    ⟨ H , τ ⟩∈ℰ⟦ K ⟧[ Γ ] → ⟨ H , τ ⟩∈'ℰ⟦ K ⟧[ Γ ]
  denot-ind-rec-e (N gas τ eval denot) =
    ((gas , τ) , (eval , denot-ind-rec-v denot))

denot-val : ∀{n} {Γ : Context n} {H : Env n} {τ : Type n} {K : Kind n} →
  ⟨ H , τ ⟩∈⟦ K ⟧[ Γ ] → H ⊢ τ val
denot-val (denot-intv τ-val lower upper) = τ-val
denot-val (denot-abs _ _) = v-abs

-- TODO: The ordering of arguments here is a huge mess.
postulate
  weaken-denot : ∀{n} {Γ : Context n} {H : Env n} {τ τ' τ'val} {K} K' →
    ⟨ H , τ ⟩∈⟦ K ⟧[ Γ ] →
    ⟨ (H , τ' [ τ'val ]) , weakenTy τ ⟩∈⟦ weakenKd K ⟧[ K' ∷ Γ ]
  {-
  weaken-denot {n} {Γ} {H} {τ} {τ'} {τ'val} {K} {K'} (denot-intv τval A≤τ τ≤B) =
    denot-intv (weaken-isVal τval τ' τ'val) (weaken-st A≤τ) (weaken-st τ≤B)
  -}

  weaken-isVal≡denot-val○weaken-denot :
    ∀{n} {Γ : Context n} {H : Env n} {τ' τ'val}
      (τ : Type n) (τval : H ⊢ τ val) K K' τ∈⟦K⟧
    →
        weaken-isVal τval τ' τ'val
      ≡ denot-val (weaken-denot {n} {Γ} {H} {τ} {τ'} {τ'val} {K} K' τ∈⟦K⟧)

data _⊨_ : ∀{n} → Context n → Env n → Set where
  c-emp : [] ⊨ ∅
  -- I don't really understand why it can't infer the [suc n] on the output
  -- here
  c-cons : ∀{n Γ H K τ p} →
    ⟨ H , τ ⟩∈⟦ K ⟧[ Γ ] → _⊨_ {n} Γ H → _⊨_ {suc n} (K ∷ Γ) (H , τ [ p ])

record Lookup {n : ℕ}
    (Γ : Context n) (H : Env n) (K : Kind n) (v : Fin n) : Set where
  constructor L
  field
    τ : Type n
    denot : ⟨ H , τ ⟩∈⟦ K ⟧[ Γ ]
    proof : lookup H v ≡ V τ (denot-val denot)

consistentEnv : ∀{n} {Γ : Context n} {H : Env n} {K : Kind n} →
  Γ ⊨ H → {v : Fin n} → lookupKd Γ v ≡ K → Lookup Γ H K v
consistentEnv {zero} {[]} {∅} {_} c-emp {()}
consistentEnv {suc n} {K ∷ Γ} {H , τ [ τval ]} {_} (c-cons τ∈⟦K⟧ _) {zero} refl =
    L (weakenTy τ) (weaken-denot K τ∈⟦K⟧) lookup-refl
  where
    open ≡-Reasoning

    lookup-refl :
        lookup (H , τ [ τval ]) zero
      ≡ V (weakenTy τ) (denot-val (weaken-denot K τ∈⟦K⟧))
    lookup-refl = begin
        lookup (H , τ [ τval ]) zero
      ≡⟨ refl ⟩
        weakenVal (V τ τval) τ τval
      ≡⟨ refl ⟩
        V (weakenTy τ) (weaken-isVal τval τ τval)
      ≡⟨ cong
           (V (weakenTy τ))
           (weaken-isVal≡denot-val○weaken-denot τ τval K K τ∈⟦K⟧)
       ⟩
        V (weakenTy τ) (denot-val (weaken-denot K τ∈⟦K⟧))
      ∎
consistentEnv {suc n} {K ∷ Γ} {H , t [ tval ]} {_} (c-cons _ p) {suc i} refl =
  let L τ τ∈⟦K'⟧ subproof = consistentEnv {n} {Γ} {H} p {i} refl

      τval = denot-val τ∈⟦K'⟧

      open ≡-Reasoning
      lookup-recursive :
          lookup (H , t [ tval ]) (suc i)
        ≡ V (weakenTy τ) (denot-val (weaken-denot K τ∈⟦K'⟧))
      lookup-recursive = begin
          lookup (H , t [ tval ]) (suc i)
        ≡⟨ refl ⟩
          weakenVal (lookup H i) t tval
        ≡⟨ cong (λ tm → weakenVal tm t tval) subproof ⟩
          weakenVal (V τ τval) t tval
        ≡⟨ refl ⟩
          V (weakenTy τ) (weaken-isVal τval t tval)
        ≡⟨ cong
             (V (weakenTy τ))
             (weaken-isVal≡denot-val○weaken-denot
               τ τval (lookupKd Γ i) K τ∈⟦K'⟧)
         ⟩
          V (weakenTy τ) (denot-val (weaken-denot K τ∈⟦K'⟧))
        ∎
   in
  L (weakenTy τ) (weaken-denot K τ∈⟦K'⟧) lookup-recursive

record FunctionInversion {n}
    (Γ : Context n) (H : Env n) (J : Kind n)
    (K : Kind (suc n)) (τ : Type n)
    : Set where
  constructor F
  field
    body : Type (suc n)
    realJ : Kind n
    realJ≤J : Γ ⊢kd J ≤ realJ
    expand : τ ≡ ƛ realJ body
    proof : ( (τₓ : Type n) → (px : H ⊢ τₓ val) → ⟨ H , τₓ ⟩∈'⟦ J ⟧[ Γ ]
            → ⟨ H , τₓ [ px ] , body ⟩∈ℰ⟦ K ⟧[ J ∷ Γ ])

functionInversion : ∀{n} {Γ : Context n} {H : Env n} {τ J K} →
  ⟨ H , τ ⟩∈⟦ ℿ J K ⟧[ Γ ] → Γ ⊨ H → FunctionInversion Γ H J K τ
functionInversion (denot-abs {J} {J'} {K} {H} {body} {Γ} J≤J' f) Γ⊨H =
  F body J' J≤J' refl f

rewriteInversionStep : ∀{n gas} {Γ : Context n} {H : Env n} {A τ J body} →
  τ ≡ ƛ J body → H ⊢ A ⟱[ gas ] τ → H ⊢ A ⟱[ gas ] (ƛ J body)
rewriteInversionStep eq A⟱τ rewrite eq = A⟱τ

postulate
  preservation : ∀{n gas} {Γ : Context n} {H : Env n} {K A τ} →
    Γ ⊨ H → Γ ⊢ty A ∈ K → H ⊢ A ⟱[ gas ] τ → Γ ⊢ty τ ∈ K

  evaluationPreservesSubtyping :
    ∀{n gas₁ gas₂} {Γ : Context n} {H : Env n} {A₁ A₂ α₁ α₂ τ K} →
      Γ ⊨ H → Γ ⊢ty A₁ ≤ A₂ ∈ K →
      H ⊢ A₁ ⟱[ gas₁ ] α₁ → H ⊢ A₂ ⟱[ gas₂ ] α₂ → Γ ⊢ty α₁ ≤ τ ∈ K →
      Γ ⊢ty α₂ ≤ τ ∈ K

semanticWidening : ∀{n} {Γ : Context n} {K₁ K₂} →
  Γ ⊢kd K₁ ≤ K₂ → ∀{H τ} → ⟨ H , τ ⟩∈⟦ K₁ ⟧[ Γ ] → ⟨ H , τ ⟩∈⟦ K₂ ⟧[ Γ ]
semanticWidening (sk-intv A₂≤A₁ B₁≤B₂) (denot-intv τ-val A₁≤τ τ≤B₁) =
  denot-intv τ-val {! (st-trans A₂≤A₁ A₁≤τ) !} {! (st-trans τ≤B₁ B₁≤B₂) !}
semanticWidening {n} {Γ} {_}
    (sk-darr {J₁} {J₂} {K₁} {K₂} ℿJ₁K₁kd J₂≤J₁ K₁≤K₂)
    {H}
    (denot-abs {J₁} {J₁'} {K₁} {H} {A} J₁≤J₁' f) =
  let f' : (τₓ : Type n) → (px : H ⊢ τₓ val) → ⟨ H , τₓ ⟩∈'⟦ J₂ ⟧[ Γ ]
         → ⟨ H , τₓ [ px ] , A ⟩∈ℰ⟦ K₂ ⟧[ J₂ ∷ Γ ]
      f' τₓ px τₓ∈'⟦J₂⟧ =
        let τ∈⟦J₁⟧ = semanticWidening J₂≤J₁ (denot-rec-ind-v τₓ∈'⟦J₂⟧)
            N gas τ A⟱τ τ∈⟦K₁⟧ = f τₓ px (denot-ind-rec-v τ∈⟦J₁⟧)
         in
        N gas τ A⟱τ (semanticWidening K₁≤K₂ {!!})
   in
  denot-abs (sk-trans J₂≤J₁ J₁≤J₁') f'

-- Following the other schemes, another name for [typesNormalize] would be
-- kind-denot-ℰ
typesNormalize : ∀{n} {Γ : Context n} {H : Env n} {A K} →
  Γ ⊢ty A ∈ K → Γ ⊨ H → ⟨ H , A ⟩∈ℰ⟦ K ⟧[ Γ ]
typesNormalize (k-var Γ-is-ctx trace) Γ⊨H =
  let L τ τ∈⟦K⟧ τ∈H = consistentEnv Γ⊨H trace
   in
  N 0 τ (eval-var τ∈H) τ∈⟦K⟧
typesNormalize k-top _ = N 0 ⊤ eval-⊤ (denot-typ v-top k-top)
typesNormalize k-bot _ = N 0 ⊥ eval-⊥ (denot-typ v-bot k-bot)
typesNormalize (k-arr A∈✶ B∈✶) Γ⊨H =
  let N a α A⟱α denotA = typesNormalize A∈✶ Γ⊨H
      N b β B⟱β denotB = typesNormalize B∈✶ Γ⊨H
      varr = v-arr (⟱-spec A⟱α) (⟱-spec B⟱β)
   in
  N (a + b)
    (α ⇒ β)
    (eval-arr A⟱α B⟱β)
    (denot-typ varr
               (k-arr (preservation Γ⊨H A∈✶ A⟱α) (preservation Γ⊨H B∈✶ B⟱β)))
typesNormalize (k-all {K} {A} pK pA) _ =
  N 0 (∀' K A) eval-∀' (denot-typ v-all (k-all pK pA))
typesNormalize {n} {Γ} {H} (k-abs {J} {K} {A} J-isKd A∈K) Γ⊨H =
  let d-inner : (τ : Type n) → (τval : H ⊢ τ val) → ⟨ H , τ ⟩∈'⟦ J ⟧[ Γ ] →
        ⟨ (H , τ [ τval ]) , A ⟩∈ℰ⟦ K ⟧[ J ∷ Γ ]
      d-inner τ τval τ∈'J =
        typesNormalize {suc n} A∈K (c-cons (denot-rec-ind-v τ∈'J) Γ⊨H)

      denot = denot-abs (sk-refl J-isKd) d-inner
   in
  N 0 (ƛ J A) eval-ƛ denot
typesNormalize {_} {Γ} {H}
    (k-app {J} {K} {A} {B} A∈ℿJK B∈J K-isKd KB-isKd) Γ⊨H =
  let N a α A⟱α α∈⟦ℿJK⟧ = typesNormalize A∈ℿJK Γ⊨H
      F body _ _ expand proof = functionInversion α∈⟦ℿJK⟧ Γ⊨H
      N b β B⟱β β∈⟦J⟧ = typesNormalize B∈J Γ⊨H
      βval = denot-val β∈⟦J⟧
      N n τ α∙β⟱τ τ∈⟦KB⟧ = proof β (denot-val β∈⟦J⟧) (denot-ind-rec-v β∈⟦J⟧)
   in
  N (a + b + n)
    (plugTy τ β)
    (eval-app {_} {_} {_} {_} {_} {β} {τ} {_} {a} {b} {βval} {n}
      (rewriteInversionStep {_} {a} {Γ} {H} {_} {α} expand A⟱α)
      B⟱β
      α∙β⟱τ)
    -- Have τ ∈ ⟦plugKd K B⟧, need plugTy τ β ∈ ⟦plugKd K β⟧
    {! τ∈⟦KB⟧ !}
typesNormalize (k-sing A∈B∙∙C) Γ⊨H =
  let N gas τ A⟱τ A∈⟦B∙∙C⟧ = typesNormalize A∈B∙∙C Γ⊨H
   in
  -- TODO: need to show that A ⟱ τ implies τ ≤ A
  N gas τ A⟱τ (denot-intv (⟱-spec A⟱τ) {!!} {!!})
typesNormalize (k-sub A∈J J≤K) Γ⊨H =
  let N gas τ A⟱τ τ∈⟦J⟧ = typesNormalize A∈J Γ⊨H
   in
  N gas τ A⟱τ (semanticWidening J≤K τ∈⟦J⟧)
  -}
