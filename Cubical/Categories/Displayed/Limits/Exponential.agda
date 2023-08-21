{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Limits.Exponential where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma renaming (_×_ to _×Type_)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Exponentials
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Adjoint
open import Cubical.Categories.Displayed.Limits.BinProduct

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD') where
  open Categoryᴰ D
  -- open BinProductsᴰNotation

  Exponentialᴰ : {!!}
  -- ∀ {c}{d}{ c×- } → (e : (Exponential C c d c×-)) →
                 -- (bp : BinProduct' C (c , d) ) →
                 -- (cᴰ : ob[ c ])(dᴰ : ob[ d ]) →
                 -- (∀ (eᴰ : ob[ e .UniversalElement.vertex ]) →
                   -- BinProductᴰ D bp (cᴰ , dᴰ))
                 -- → Type _
  Exponentialᴰ = {!!}
