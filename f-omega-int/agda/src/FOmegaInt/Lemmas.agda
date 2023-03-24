-- XXX: use a more informative name
module FOmegaInt.Lemmas where

open import Data.Product

open import Data.Context
open import FOmegaInt.Syntax
open import FOmegaInt.Typing
open import FOmegaInt.Reduction

postulate
  reduction-under-subst-preserves-isKd : ∀{gas Γ K A τ} →
    Γ ⊢ plugKd K A kd → A ⟱[ gas ] τ → Γ ⊢ plugKd K τ kd

  reduction-under-subst-preserves-kinding : ∀{gas Γ K A T τ} →
    Γ ⊢ty plugTy A T ∈ K → T ⟱[ gas ] τ → Γ ⊢ty plugTy A τ ∈ K

  preservation : ∀{gas K A τ} → [] ⊢ty A ∈ K → A ⟱[ gas ] τ → [] ⊢ty τ ∈ K

  reduction-refl : ∀{gas K A τ} →
    [] ⊢ty A ∈ K → A ⟱[ gas ] τ → [] ⊢ty A == τ ∈ K

  reduction-refl-kd : ∀{J K} → J ⟱kd K → [] ⊢kd J == K

{-
reduction-refl (k-sub A∈J J≤K) A⟱τ =
  let E τ≤A∈J A≤τ∈J = reduction-refl A∈J A⟱τ
   in
  E (st-sub τ≤A∈J J≤K) (st-sub A≤τ∈J J≤K)
reduction-refl {_} {A ∙∙ A} {A} {τ} (k-sing {_} {B} {C} A∈B∙∙C) A⟱τ =
  let E A≤τ∈B∙∙C τ≤A∈B∙∙C = reduction-refl A∈B∙∙C A⟱τ
      A∈B∙∙C , τ∈B∙∙C = subtyping-valid A≤τ∈B∙∙C
      A∈✶ = intv-proper A∈B∙∙C
      B∙∙C≤✶ = intv-widen A∈B∙∙C
      A≤τ∈✶ = st-sub A≤τ∈B∙∙C B∙∙C≤✶
      τ≤A∈✶ = st-sub τ≤A∈B∙∙C B∙∙C≤✶
      τ≤A∈τ∙∙A = st-intv τ≤A∈B∙∙C
      A≤τ∈A∙∙τ = st-intv A≤τ∈B∙∙C
      τ∙∙A≤A∙∙A = sk-intv A≤τ∈✶ (st-refl A∈✶)
      A∙∙τ≤A∙∙A = sk-intv (st-refl A∈✶) τ≤A∈✶
      τ≤A∈A∙∙A = st-sub τ≤A∈τ∙∙A τ∙∙A≤A∙∙A
      A≤τ∈A∙∙A = st-sub A≤τ∈A∙∙τ A∙∙τ≤A∙∙A
   in
  E A≤τ∈A∙∙A τ≤A∈A∙∙A
reduction-refl k-top eval-⊤ = eq-refl k-top
reduction-refl k-bot eval-⊥ = eq-refl k-bot
reduction-refl (k-all K-kd A∈✶) eval-∀' = eq-refl (k-all K-kd A∈✶)
reduction-refl (k-abs J-kd A∈K) eval-ƛ = eq-refl (k-abs J-kd A∈K)
reduction-refl (k-arr A∈✶ B∈✶) (eval-arr A⟱α B⟱β) =
  let E α≤A A≤α = reduction-refl A∈✶ A⟱α
      E β≤B B≤β = reduction-refl B∈✶ B⟱β
   in
  E (st-arr A≤α β≤B) (st-arr α≤A B≤β)
reduction-refl (k-app A∈ℿJK B∈J K-kd KB-kd) (eval-app A⟱ƛJA' B⟱β A'⟱τ) =
  let E ƛJA'≤A A≤ƛJA' = reduction-refl A∈ℿJK A⟱ƛJA'
      β==B = reduction-refl B∈J B⟱β
      ƛJA'∙β≤A∙B = st-app ƛJA'≤A β==B B∈J K-kd KB-kd
      A'β≤ƛJA'∙β =
        st-β₂ {! [J] ⊢ A' ∈ K !}
              {! β∈J !}
              {! A'[β]∈K[β] !}
              K-kd
              (reduction-under-subst-preserves-isKd KB-kd B⟱β)
      A∙B≤ƛJA'∙B = st-app A≤ƛJA' (eq-refl B∈J) B∈J K-kd KB-kd
   in
  {! !}
  -}
