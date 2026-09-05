{-# OPTIONS --lossy-unification #-}
{- CAT has all PIE limits. -}
module Cubical.Categories.Bicategory.Instances.CAT.PIE where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Limits.Terminal
open import Cubical.Categories.Bicategory.Limits.Product
open import Cubical.Categories.Bicategory.Limits.PIE
open import Cubical.Categories.Bicategory.Instances.CAT.Inserter
open import Cubical.Categories.Bicategory.Instances.CAT.Equifier
open import Cubical.Categories.Bicategory.Instances.CAT.Terminal
open import Cubical.Categories.Bicategory.Instances.CAT.Product

private
  variable
    ℓ ℓ' : Level

module _ {ℓ ℓ' : Level} where
  -- CAT has all PIE limits as soon as it has a terminal object and
  -- binary products; inserters and equifiers are the work above.
  pieCAT : Terminalᴮ (CAT {ℓ-max ℓ ℓ'} {ℓ'})
    → ((a b : Category (ℓ-max ℓ ℓ') ℓ')
        → BinProductᴮ (CAT {ℓ-max ℓ ℓ'} {ℓ'}) a b)
    → hasPIEᴮ (CAT {ℓ-max ℓ ℓ'} {ℓ'})
  pieCAT t p .hasPIEᴮ.terminalᴮ = t
  pieCAT t p .hasPIEᴮ.productsᴮ = p
  pieCAT t p .hasPIEᴮ.insertersᴮ = insertersCAT
  pieCAT t p .hasPIEᴮ.equifiersᴮ = equifiersCAT

  pieLimitsCAT : hasPIEᴮ (CAT {ℓ-max ℓ ℓ'} {ℓ'})
  pieLimitsCAT = pieCAT terminalCAT binProductCAT
