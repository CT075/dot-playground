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
open import FOmegaInt.Lemmas
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

-- TODO: remove this
--
-- This TERMINATING pragma is safe -- every recursive occurrence reduces the
-- number of outer ℿs, and this measure is preserved by substitution of types
-- (even if we substitute [ℿ J K] into a big-lambda, that can only appear in an
-- interval kind, which halts the recursion anyway).
--
-- We can make Agda accept this definition by using [Induction.WellFounded] in
-- the standard library using the above measure. However, actually _using+ such
-- a definition becomes impossible, as Agda's type checker seems to be unable
-- to tell that the recursive calls necessary in the [ℿ J K] clause are in fact
-- equal to the outermost type, so the inner function becomes unusable.
{-# TERMINATING #-}
mutual
  ⟨_⟩∈'⟦_⟧ : Type zero → Kind zero → Set
  ⟨ τ ⟩∈'⟦ A ∙∙ B ⟧ = τ val × [] ⊢ty A ≤ τ ∈ ✶ × [] ⊢ty τ ≤ B ∈ ✶
  ⟨ ƛ J' A ⟩∈'⟦ ℿ J K ⟧ =
    [] ⊢kd J ≤ J' ×
      (∀ τₓ →
        ⟨ τₓ ⟩∈'⟦ J ⟧ →
        ⟨ plugTy A τₓ ⟩∈'ℰ⟦ plugKd K τₓ ⟧)
  ⟨ _ ⟩∈'⟦ ℿ J K ⟧ = Void

  ⟨_⟩∈'ℰ⟦_⟧ : Type zero → Kind zero → Set
  ⟨ A ⟩∈'ℰ⟦ K ⟧ = Σ[ W ∈ (ℕ × Type zero) ](
    let (gas , τ) = W
     in
    A ⟱[ gas ] τ × ⟨ τ ⟩∈'⟦ K ⟧)

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

denot-typ : ∀{τ : Type zero} → [] ⊢ty τ ∈ ✶ → τ val → ⟨ τ ⟩∈⟦ ✶ ⟧
denot-typ τ∈✶ τ-val = denot-intv τ-val (st-bot τ∈✶) (st-top τ∈✶)

denot-val : ∀{τ : Type zero} {K : Kind zero} → ⟨ τ ⟩∈⟦ K ⟧ → τ val
denot-val (denot-intv τ-val lower upper) = τ-val
denot-val (denot-abs _ _) = v-abs

-- Proof that the recursive view implies the inductive view

-- TODO: remove this
--
-- It's safe for the same reason as above; the type of the recursive call to
-- [denot-rec-ind-e] is smaller than the type of the outermost
-- [denot-ind-rec-v] call.
{-# TERMINATING #-}
mutual
  denot-rec-ind-v : ∀{τ : Type zero} {K : Kind zero} →
    ⟨ τ ⟩∈'⟦ K ⟧ → ⟨ τ ⟩∈⟦ K ⟧
  denot-rec-ind-v {τ} {A ∙∙ B} (τval , A≤τ , τ≤B) = denot-intv τval A≤τ τ≤B
  denot-rec-ind-v {ƛ J' A} {ℿ J K} (J≤J' , f) = denot-abs J≤J' f'
    where
      f' : (τₓ : Type zero) → ⟨ τₓ ⟩∈'⟦ J ⟧ → ⟨ plugTy A τₓ ⟩∈ℰ⟦ plugKd K τₓ ⟧
      f' τₓ τₓ∈'⟦J⟧ = denot-rec-ind-e (f τₓ τₓ∈'⟦J⟧)

  denot-rec-ind-e : ∀{τ : Type zero} {K : Kind zero} →
    ⟨ τ ⟩∈'ℰ⟦ K ⟧ → ⟨ τ ⟩∈ℰ⟦ K ⟧
  denot-rec-ind-e ((gas , τ) , (eval , denot)) =
    N gas τ eval (denot-rec-ind-v denot)

-- Proof that the inductive view implies the recursive view

mutual
  denot-ind-rec-v : ∀{τ : Type zero} {K : Kind zero} →
    ⟨ τ ⟩∈⟦ K ⟧ → ⟨ τ ⟩∈'⟦ K ⟧
  denot-ind-rec-v (denot-intv τ-val lower upper) = τ-val , lower , upper
  denot-ind-rec-v {ƛ J' A} {ℿ J K} (denot-abs J≤J' f') = J≤J' , f
    where
      f : (τₓ : Type zero) → ⟨ τₓ ⟩∈'⟦ J ⟧ → ⟨ plugTy A τₓ ⟩∈'ℰ⟦ plugKd K τₓ ⟧
      f τₓ τₓ∈'⟦J⟧ = denot-ind-rec-e (f' τₓ τₓ∈'⟦J⟧)

  denot-ind-rec-e : ∀{τ : Type zero} {K : Kind zero} →
    ⟨ τ ⟩∈ℰ⟦ K ⟧ → ⟨ τ ⟩∈'ℰ⟦ K ⟧
  denot-ind-rec-e (N gas τ eval denot) =
    ((gas , τ) , (eval , denot-ind-rec-v denot))

record FunctionInversion (J : Kind 0) (K : Kind 1) (τ : Type 0) : Set where
  constructor F
  field
    body : Type 1
    realJ : Kind 0
    realJ≤J : [] ⊢kd J ≤ realJ
    expand : τ ≡ ƛ realJ body
    proof : ( (τₓ : Type zero) → ⟨ τₓ ⟩∈'⟦ J ⟧
            → ⟨ plugTy body τₓ ⟩∈ℰ⟦ plugKd K τₓ ⟧)

functionInversion : ∀{τ J K} → ⟨ τ ⟩∈⟦ ℿ J K ⟧ → FunctionInversion J K τ
functionInversion (denot-abs {J} {J'} {K} {body} J≤J' f) =
  F body J' J≤J' refl f

rewriteInversionStep : ∀{gas} {A τ J body} →
  τ ≡ ƛ J body → A ⟱[ gas ] τ → A ⟱[ gas ] (ƛ J body)
rewriteInversionStep eq A⟱τ rewrite eq = A⟱τ

semanticWidening : ∀{K₁ K₂} →
  [] ⊢kd K₁ ≤ K₂ → ∀{τ} → ⟨ τ ⟩∈⟦ K₁ ⟧ → ⟨ τ ⟩∈⟦ K₂ ⟧
semanticWidening (sk-intv A₂≤A₁ B₁≤B₂) (denot-intv τ-val A₁≤τ τ≤B₁) =
  denot-intv τ-val (st-trans A₂≤A₁ A₁≤τ) (st-trans τ≤B₁ B₁≤B₂)
semanticWidening
    (sk-darr {J₁} {J₂} {K₁} {K₂} ℿJ₁K₁kd J₂≤J₁ K₁≤K₂)
    (denot-abs {J₁} {J₁'} {K₁} {A} J₁≤J₁' f) =
  let f' : (τₓ : Type 0) → ⟨ τₓ ⟩∈'⟦ J₂ ⟧
         → ⟨ plugTy A τₓ ⟩∈ℰ⟦ plugKd K₂ τₓ ⟧
      f' τₓ τₓ∈'⟦J₂⟧ =
        let τ∈⟦J₁⟧ = semanticWidening J₂≤J₁ (denot-rec-ind-v τₓ∈'⟦J₂⟧)
            N gas τ A⟱τ τ∈⟦K₁⟧ = f τₓ (denot-ind-rec-v τ∈⟦J₁⟧)
         in
        N gas τ A⟱τ (semanticWidening (sk-plug K₁≤K₂ {!!}) τ∈⟦K₁⟧)
   in
  denot-abs (sk-trans J₂≤J₁ J₁≤J₁') f'

-- Following the other schemes, another name for [typesNormalize] would be
-- kind-denot-ℰ
typesNormalize : ∀ {A K} → [] ⊢ty A ∈ K → ⟨ A ⟩∈ℰ⟦ K ⟧
typesNormalize k-top = N 0 ⊤ eval-⊤ (denot-typ k-top v-top)
typesNormalize k-bot = N 0 ⊥ eval-⊥ (denot-typ k-bot v-bot)
typesNormalize (k-arr A∈✶ B∈✶) =
  let
    N a α A⟱α α∈⟦✶⟧ = typesNormalize A∈✶
    N b β B⟱β β∈⟦✶⟧ = typesNormalize B∈✶
    α-val = denot-val α∈⟦✶⟧
    β-val = denot-val β∈⟦✶⟧
    α∈✶ = preservation A∈✶ A⟱α
    β∈✶ = preservation B∈✶ B⟱β
  in
    N (a + b)
      (α ⇒ β)
      (eval-arr A⟱α B⟱β)
      (denot-typ (k-arr α∈✶ β∈✶) (v-arr α-val β-val))
typesNormalize {∀' K A} proof@(k-all K-kd A∈✶) =
  N 0 (∀' K A) eval-∀' (denot-typ proof v-all)
typesNormalize {ƛ J A} {ℿ J K} (k-abs J-kd A∈K) =
  let
    d-inner : (τₓ : Type zero) → ⟨ τₓ ⟩∈'⟦ J ⟧ →
      ⟨ plugTy A τₓ ⟩∈ℰ⟦ plugKd K τₓ ⟧
    d-inner τₓ τₓ∈'⟦J⟧ = typesNormalize (kinding-subst A∈K {!!})

    denot = denot-abs (sk-refl J-kd) d-inner
   in
  N 0 (ƛ J A) eval-ƛ denot
typesNormalize (k-app A∈ℿJK B∈J K-kd KB-kd) =
  let N a α A⟱α α∈⟦ℿJK⟧ = typesNormalize A∈ℿJK
      F body _ _ α≡ƛ body-terminates = functionInversion α∈⟦ℿJK⟧
      N b β B⟱β β∈⟦J⟧ = typesNormalize B∈J
      β-val = denot-val β∈⟦J⟧
      N n τ α∙β⟱τ τ∈⟦Kβ⟧ = body-terminates β (denot-ind-rec-v β∈⟦J⟧)
   in
  N (a + b + n)
    τ
    (eval-app (rewriteInversionStep α≡ƛ A⟱α) B⟱β α∙β⟱τ)
    -- Have τ ∈ (plugTy K β), need τ ∈ (plugTy K B)
    {!!}
typesNormalize (k-sing A∈B∙∙C) =
  let N gas τ A⟱τ τ∈⟦B∙∙C⟧ = typesNormalize A∈B∙∙C
   in
  N gas τ A⟱τ {!!}
typesNormalize (k-sub A∈J J≤K) =
  let N gas τ A⟱τ τ∈⟦J⟧ = typesNormalize A∈J
   in
  N gas τ A⟱τ (semanticWidening J≤K τ∈⟦J⟧)

