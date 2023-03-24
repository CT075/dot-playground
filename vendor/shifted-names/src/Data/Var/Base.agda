module Data.Var.Base where

open import Data.Nat using (ℕ; suc; zero)
open import Data.String using (String; _==_)
open import Data.Bool using (if_then_else_)
open import Level using (Level)
open import Relation.Unary using (Pred)

record Name : Set where
  constructor N
  field
    name : String
    index : ℕ

bump : String → Name → Name
bump x (N y i) = if x == y then N y (suc i) else N y i

lower : ∀{T : Set} → (Name → T) → T → String → Name → T
lower free bzero x (N y zero) = if x == y then bzero else free (N y zero)
lower free bzero x (N y (suc i)) = if x == y then free (N y i) else free (N y (suc i))

-- Shifted names are a variation on locally-nameless types, in which each name
-- is annotated with an index marking how many times it's been shadowed.
--
-- It's worth noting that [Bound] in this formulation uses de Bruijin _levels_
-- (0 refers to the outermost binding), not de Bruijin _indicies_ (0 refers to
-- the innermost binding). This was the numbering scheme used by Dolan and
-- repeated here, as it simplifies the operation definitions a lot.
data Var : Set where
  Bound : ℕ → Var
  Free : Name → Var

openVar : String → Var → Var
openVar x (Bound zero) = Free (N x zero)
openVar x (Bound (suc n)) = Bound n
openVar x (Free name) = Free (bump x name)

closeVar : String → Var → Var
closeVar x (Bound n) = Bound (suc n)
closeVar x (Free name) = lower Free (Bound zero) x name

wkVar : Var → Var
wkVar (Bound n) = Bound (suc n)
wkVar (Free name) = Free name

shiftVar : String → Var → Var
shiftVar x v = openVar x (wkVar v)

renameVar : String → String → Var → Var
renameVar y x v = openVar y (closeVar x v)

-- Simple generalization of variable-level transforms to full ASTs
record Lift {ℓ : Level} (T : Set ℓ) : Set ℓ where
  field
    lift : (Var → Var) → T → T

  openT : String → T → T
  openT x = lift (openVar x)

  closeT : String → T → T
  closeT x = lift (closeVar x)

  wkT : T → T
  wkT = lift wkVar

  shiftT : String → T → T
  shiftT x = lift (shiftVar x)

  renameT : String → String → T → T
  renameT y x = lift (renameVar y x)

-- A [Subst T S] substitutes an [S] for a variable in [T]. In most cases, we
-- will have [T = T], but in some cases only certain substitutions are valid.
record Subst {ℓ : Level} (T : Set ℓ) (S : Set ℓ) : Set ℓ where
  field
    lift : Lift T
    var : Var → S
    subst : (Var → S) → T → T

  open Lift lift public

  bindVar : S → Var → S
  bindVar u (Bound zero) = u
  bindVar u (Bound (suc n)) = var (Bound n)
  bindVar u (Free name) = var (Free name)

  bindT : S → T → T
  bindT u = subst (bindVar u)
