module Induction.WellFounded.Mutual where

open import Data.Fin
open import Data.Vec
open import Level renaming (zero to lzero; suc to lsuc)
open import Induction.WellFounded
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (trans)
open import Relation.Unary

private
  variable
    a b ℓ r : Level
    A : Set a
    B : Set b

module Nary {_<_ : Rel A r} (wf : WellFounded _<_) ℓ where
  open All wf ℓ

  wfMutual : ∀ {k} (R : REL (Fin k) A ℓ) →
    (∀ i → (∀ n → (∀ j → (∀ m → m < n → R j m)) → R i n)) →
    (∀ i → (∀ n → R i n))
  wfMutual {k} R fs i n = wfRec _ go n i
    where
      go : ∀ n → (∀ m → m < n → (j : Fin k) → R j m) → (j : Fin k) → R j n
      go n rec j = fs j n recI
        where
          recI : (j : Fin k) → (m : A) → m < n → R j m
          recI j m m<n = rec m m<n j

