{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.BinProduct.ProductOfSets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
import Cubical.Categories.Constructions.BinProduct.Redundant.Base as R
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Bifunctor.Base
import Cubical.Categories.Bifunctor.Redundant as R

open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Instances.Sets

private
  variable
    ℓ ℓ' : Level

open Iso
open UnivElt
open isUniversal
open BinProduct
open Category
open Functor

private
  variable
    ℓS : Level

module _ (bp : BinProducts (SET ℓS))
  where

  open Notation (SET ℓS) bp

  -- Want that product in the category of sets coincides with
  -- the type theoretic product
  prodIsΣ : (A B : (SET ℓS) .ob) →
      (A × B) .fst ≡ {!Σ (A .fst) (λ _ → B .fst)!}
  prodIsΣ = λ A B → refl

  -- Assuming prodIsΣ, we would also want π₁ ≡ fst and π₂ ≡ snd
  _ : (A B : (SET ℓS) .ob) →
      π₁ {a = A}{b = B} ≡ {!fst {A = A .fst}{B = λ _ → B .fst}!}
  _ = λ A B → refl

  _ : (A B : (SET ℓS) .ob) →
      π₂ {a = A}{b = B} ≡ {!snd {A = A .fst}{B = λ _ → B .fst}!}
  _ = λ A B → refl
