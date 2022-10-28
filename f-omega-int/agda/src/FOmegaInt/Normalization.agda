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
      data ⟨_,_⟩∈⟦_⟧[_] {n : ℕ} : Env n → Type n → Kind n → Context n → Set where
        denot-typ : ∀{H v Γ} → Γ ⊢ty v ∈ ✶ → H ⊢ v val → ⟨ H , v ⟩∈⟦ ✶ ⟧[ Γ ]
        denot-intv : ∀{A B H v Γ} →
          Γ ⊢ty A ≤ v ∈ ✶ → Γ ⊢ty v ≤ B ∈ ✶ → H ⊢ v val →
          ⟨ H , v ⟩∈⟦ A ∙∙ B ⟧[ Γ ]
        denot-abs : ∀{J J' : Kind n} {K : Kind (suc n)} {H : Env n}
            {A : Type (suc n)} {Γ : Context n} →
          Γ ⊢kd J ≤ J' →
          ( (τₓ : Type n) → (px : H ⊢ τₓ val) → ⟨ H , τₓ ⟩∈⟦ J ⟧
          → ⟨ H , τₓ [ px ] , A ⟩∈ℰ⟦ K ⟧[ J ∷ Γ ]
          ) →
          ⟨ H , ƛ J' A ⟩∈⟦ ℿ J K ⟧[ Γ ]

However, this type isn't strictly positive (see the ⟨_,_⟩∈⟦_⟧ as a function
input in the denot-abs constructor), so we need to use structural recursion to
define this datatype.
-}

mutual
  norm-stmt : ∀{n} → Context n → Env n → Type n → Kind n → ℕ × Type n → Set
  norm-stmt Γ H A K (gas , τ) = (H ⊢ A ⟱[ gas ] τ) × (⟨ H , τ ⟩∈'⟦ K ⟧[ Γ ])

  ⟨_,_⟩∈'⟦_⟧[_] : ∀{n : ℕ} → Env n → Type n → Kind n → Context n → Set
  ⟨ H , v ⟩∈'⟦ A ∙∙ B ⟧[ Γ ] = H ⊢ v val × Γ ⊢ty A ≤ v ∈ ✶ × Γ ⊢ty v ≤ B ∈ ✶
  ⟨ H , ƛ J' A ⟩∈'⟦ ℿ J K ⟧[ Γ ] =
    Γ ⊢kd J ≤ J' ×
    (∀ τₓ τₓval → ⟨ H , τₓ ⟩∈'⟦ J ⟧[ Γ ] →
      ⟨ (H , τₓ [ τₓval ]) , A ⟩∈'ℰ⟦ K ⟧[ J ∷ Γ ])
  ⟨ H , _ ⟩∈'⟦ ℿ J K ⟧[ Γ ] = Void

  ⟨_,_⟩∈'ℰ⟦_⟧[_] : ∀{n : ℕ} (H : Env n) (A : Type n) (K : Kind n) (Γ : Context n) → Set
  ⟨_,_⟩∈'ℰ⟦_⟧[_] {n} H A K Γ =
    Σ[ W ∈ (ℕ × Type n) ] (norm-stmt Γ H A K W)

mutual
  -- While the recursive functions above are actually sufficient for our
  -- purposes, they're a pain to pattern match on, so we provide an
  -- inductive-recursive view here. Notice the use of ∈' (instead of just ∈) in
  -- the denot-abs constructor.
  data ⟨_,_⟩∈⟦_⟧[_] {n : ℕ} : Env n → Type n → Kind n → Context n → Set where
    denot-intv : ∀{A B H v Γ} →
      H ⊢ v val → Γ ⊢ty A ≤ v ∈ ✶ → Γ ⊢ty v ≤ B ∈ ✶ →
      ⟨ H , v ⟩∈⟦ A ∙∙ B ⟧[ Γ ]
    denot-abs : ∀{J J' : Kind n} {K : Kind (suc n)} {H : Env n}
        {A : Type (suc n)} {Γ : Context n} →
      Γ ⊢kd J ≤ J' →
      ( ∀ τₓ τₓval → ⟨ H , τₓ ⟩∈'⟦ J ⟧[ Γ ] →
          ⟨ (H , τₓ [ τₓval ]) , A ⟩∈ℰ⟦ K ⟧[ J ∷ Γ ]) →
      ⟨ H , ƛ J' A ⟩∈⟦ ℿ J K ⟧[ Γ ]

  record ⟨_,_⟩∈ℰ⟦_⟧[_] {n : ℕ}
      (H : Env n) (A : Type n) (K : Kind n) (Γ : Context n) : Set where
    inductive
    constructor N
    field
      gas : ℕ
      τ : Type n
      eval : H ⊢ A ⟱[ gas ] τ
      denot : ⟨ H , τ ⟩∈⟦ K ⟧[ Γ ]

mutual
  -- Proof that the recursive view implies the inductive view
  denot-rec-ind-v :
    ∀{n} {Γ : Context n} {H : Env n} {τ : Type n} {K : Kind n} →
    ⟨ H , τ ⟩∈'⟦ K ⟧[ Γ ] → ⟨ H , τ ⟩∈⟦ K ⟧[ Γ ]
  denot-rec-ind-v {_} {_} {_} {_} {A ∙∙ B} (τ-val , A≤τ , τ≤B) =
    denot-intv τ-val A≤τ τ≤B
  denot-rec-ind-v {n} {Γ} {H} {ƛ J' A} {ℿ J K} (J≤J' , f) =
    let f' : (τₓ : Type n) → (τₓval : H ⊢ τₓ val) → ⟨ H , τₓ ⟩∈'⟦ J ⟧[ Γ ] →
               ⟨ (H , τₓ [ τₓval ]) , A ⟩∈ℰ⟦ K ⟧[ J ∷ Γ ]
        f' τₓ τₓval p = denot-rec-ind-e (f τₓ τₓval p)
     in
    denot-abs J≤J' f'

  denot-rec-ind-e :
    ∀{n} {Γ : Context n} {H : Env n} {τ : Type n} {K : Kind n} →
    ⟨ H , τ ⟩∈'ℰ⟦ K ⟧[ Γ ] → ⟨ H , τ ⟩∈ℰ⟦ K ⟧[ Γ ]
  denot-rec-ind-e ((gas , τ) , (eval , denot)) =
    N gas τ eval (denot-rec-ind-v denot)

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

denot-kind : ∀{n} {Γ : Context n} {H : Env n} {τ : Type n} {K : Kind n} →
  ⟨ H , τ ⟩∈⟦ K ⟧[ Γ ] → Γ ⊢ty τ ∈ K
denot-kind (denot-intv τ-val lower upper) = intv-spec lower upper
denot-kind (denot-abs {J} {J'} {K} J≤J' f) =
  k-sub {!!} (sk-darr {!!} J≤J' (sk-refl {!!}))

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

semanticWidening : ∀{n} {Γ : Context n} {K₁ K₂} →
  Γ ⊢kd K₁ ≤ K₂ → ∀{H τ} → ⟨ H , τ ⟩∈⟦ K₁ ⟧[ Γ ] → ⟨ H , τ ⟩∈⟦ K₂ ⟧[ Γ ]
semanticWidening (sk-intv A₂≤A₁ B₁≤B₂) (denot-intv τ-val A₁≤τ τ≤B₁) =
  denot-intv τ-val (st-trans A₂≤A₁ A₁≤τ) (st-trans τ≤B₁ B₁≤B₂)
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

{-
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
  (k-abs J-is-kd K-is-kd) Γ⊨H v-abs =
  let body-normalizes :
        (τₓ : Type n) → (px : H ⊢ τₓ val) → Γ ⊢ty τₓ ∈ J →
        ⟨ H , τₓ [ px ] , A ⟩∈ℰ⟦ K ⟧[ J ∷ Γ ]
      body-normalizes τₓ τₓval τₓ∈J =
        typesNormalize
          -- TODO: need a substitution lemma here
          {! Γ ⊢ty body[τₓ] ∈ J !}
          (c-cons (val-denot τₓ∈J Γ⊨H τₓval) Γ⊨H)
   in
  denot-abs (sk-refl J-is-kd) body-normalizes
val-denot (k-app p p₁ x x₁) _ ()
val-denot (k-sing A-is-bounded) _ =
  denot-intv (st-bnd₁ (k-sing A-is-bounded)) (st-bnd₂ (k-sing A-is-bounded))
val-denot (k-sub A∈J J≤K) Γ⊨H A-val =
  semanticWidening J≤K (val-denot A∈J Γ⊨H A-val)

typesNormalize (k-var Γ-is-ctx trace) Γ⊨H =
  let L τ τ∈⟦K⟧ τ∈H = consistentEnv Γ⊨H trace
   in
  -- We run into issues with the termination checker here. τ is not a subterm
  -- of (Var n) and can be arbitrarily large. The problematic case is when
  -- [τ] is [ƛ J (Var m)], as we then re-recurse on [typesNormalize] to
  -- generate the witness for [denot-abs].
  N 0 τ (eval-var τ∈H) τ∈⟦K⟧
typesNormalize k-top _ = N 0 ⊤ eval-⊤ (denot-typ k-top v-top)
typesNormalize k-bot _ = N 0 ⊥ eval-⊥ (denot-typ k-bot v-bot)
typesNormalize (k-arr A∈✶ B∈✶) Γ⊨H =
  let N a α evalA denotA = typesNormalize A∈✶ Γ⊨H
      N b β evalB denotB = typesNormalize B∈✶ Γ⊨H
      varr = v-arr (⟱-spec evalA) (⟱-spec evalB)
   in
  N (a + b)
    (α ⇒ β)
    (eval-arr evalA evalB)
    (denot-typ (k-arr {!!} (denot-kind denotB)) varr)
typesNormalize (k-all {K} {A} pK pA) _ =
  N 0 (∀' K A) eval-∀' (denot-typ (k-all pK pA) v-all)
typesNormalize {n} {Γ} {H} (k-abs {J} {K} {A} J-isKd A∈K) Γ⊨H =
  let d-inner : (τ : Type n) → (vτ : H ⊢ τ val) → Γ ⊢ty τ ∈ J →
        ⟨ (H , τ [ vτ ]) , A ⟩∈ℰ⟦ K ⟧[ J ∷ Γ ]
      d-inner τ τval τ∈J =
        typesNormalize {suc n} A∈K (c-cons ({! val-denot τ∈J Γ⊨H τval !}) Γ⊨H)

      denot = denot-abs (sk-refl J-isKd) d-inner
   in
  N 0 (ƛ J A) eval-ƛ denot
typesNormalize {_} {Γ} {H}
    (k-app {J} {K} {A} {B} A∈ℿJK B∈J K-isKd KB-isKd) Γ⊨H =
  let N a α A⟱α α∈⟦ℿJK⟧ = typesNormalize A∈ℿJK Γ⊨H
      F body _ _ expand proof = functionInversion α∈⟦ℿJK⟧ Γ⊨H
      N b β B⟱β β∈⟦J⟧ = typesNormalize B∈J Γ⊨H
      βval = denot-val β∈⟦J⟧
      N n τ α∙β⟱τ τ∈⟦KB⟧ = proof β (denot-val β∈⟦J⟧) (denot-kind β∈⟦J⟧)
   in
  N (a + b + n)
    (plugTy τ β)
    (eval-app {_} {_} {_} {_} {_} {β} {τ} {_} {a} {b} {βval} {n}
      (rewriteInversionStep {_} {a} {Γ} {H} {_} {α} expand A⟱α)
      B⟱β
      α∙β⟱τ)
    {! τ∈⟦KB⟧ !}
typesNormalize (k-sing p) Γ⊨H =
  let N gas τ eval denot = typesNormalize p Γ⊨H
   in
  -- TODO: need to show that A ⟱ τ implies τ ≤ A
  N gas τ eval (denot-intv {!!} {!!} (⟱-spec eval))
typesNormalize (k-sub A∈J J≤K) Γ⊨H =
  let N gas τ A⟱τ τ∈⟦J⟧ = typesNormalize A∈J Γ⊨H
   in
  N gas τ A⟱τ (semanticWidening J≤K τ∈⟦J⟧)
  -}
