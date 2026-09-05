{-# OPTIONS --lossy-unification #-}
{- PIE limits: products, inserters and equifiers. -}
module Cubical.Categories.Bicategory.Limits.PIE where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Limits.Terminal
open import Cubical.Categories.Bicategory.Limits.Product
open import Cubical.Categories.Bicategory.Limits.Inserter
open import Cubical.Categories.Bicategory.Limits.Equifier
open import Cubical.Categories.Bicategory.Limits.Comma

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  record hasPIEᴮ : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
    field
      terminalᴮ : Terminalᴮ B
      productsᴮ : (a b : B.0Cell) → BinProductᴮ B a b
      insertersᴮ : hasInsertersᴮ B
      equifiersᴮ : hasEquifiersᴮ B

  open hasPIEᴮ

  -- Comma objects cost no equifiers: given the product, `Commaᴮ` is
  -- definitionally an inserter over it (`Limits/Comma.agda`).  The
  -- products are still needed -- they are a parameter of
  -- `hasCommaObjectsᴮ` -- and `hasPIEᴮ` supplies them.
  hasPIE→hasCommasᴮ : hasPIEᴮ → hasCommaObjectsᴮ B
  hasPIE→hasCommasᴮ pie = commaFromInsertersᴮ B (pie .insertersᴮ)
