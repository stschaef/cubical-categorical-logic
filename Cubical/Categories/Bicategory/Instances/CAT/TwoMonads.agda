{-# OPTIONS --lossy-unification #-}
{-
  The terminal 2-monad on CAT: the constant 2-monad at CAT's terminal
  0-cell, so `T C` is the unit category.
-}
module Cubical.Categories.Bicategory.Instances.CAT.TwoMonads where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Terminal.More

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Instances.CAT.Terminal
open import Cubical.Categories.Bicategory.Instances.CAT.Product
open import Cubical.Categories.Bicategory.Instances.CAT.PIE
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Limits.Terminal.TwoMonad
open import Cubical.Categories.Bicategory.TwoMonad.Base

private
  variable
    ℓ ℓ' : Level

module _ {ℓ ℓ' : Level} where
  open ConstantTwoMonad (terminalCAT {ℓ} {ℓ'}) public
    using () renaming (ConstLaxᴮ to TerminalLax; ConstPsᴮ to TerminalPs)

  TerminalTwoMonad : TwoMonad (CAT {ℓ} {ℓ'})
  TerminalTwoMonad = constTwoMonad terminalCAT

  TIsUnitCategory : (X : Category ℓ ℓ')
    → Pseudofunctor.F-ob (TwoMonad.T TerminalTwoMonad) X
      ≡ UnitCategory ℓ ℓ'
  TIsUnitCategory _ = refl
