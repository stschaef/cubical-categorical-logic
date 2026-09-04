{-# OPTIONS --lossy-unification #-}
{- Terminal 0-cells: biuniversal elements of the constant prestack at 𝟙C. -}
module Cubical.Categories.Bicategory.Limits.Terminal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.Terminal.More

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Constant
open import Cubical.Categories.Bicategory.Universal.Base

private
  variable
    ℓ ℓ' ℓ'' ℓc ℓc' ℓc'' : Level

module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  TerminalPrestack : Prestack B ℓ' ℓ''
  TerminalPrestack = ConstPrestack B (UnitCategory ℓ' ℓ'')

  isTerminalᴮ : B.0Cell → Type _
  isTerminalᴮ t = isBiuniversal TerminalPrestack t tt*

  Terminalᴮ : Type _
  Terminalᴮ = BiuniversalElement TerminalPrestack

module TerminalᴮNotation {B : Bicategory ℓ ℓ' ℓ''} (T : Terminalᴮ B) where
  private
    module B = Bicategory B
  module !bue = BiuniversalElementNotation T
  open BiuniversalElementNotation T public

  !ᴮ : (x : B.0Cell) → B.1Cell x vertex
  !ᴮ x = intro tt*

  -- any two 1-cells into the vertex are isomorphic
  !ᴮ-unique : {x : B.0Cell} (h : B.1Cell x vertex) → h B.≅₂ !ᴮ x
  !ᴮ-unique h = intro≡ idCatIso

module _ {B : Bicategory ℓ ℓ' ℓ''} {C : Bicategory ℓc ℓc' ℓc''}
  (F : Pseudofunctor B C) where
  private
    module F = Pseudofunctor F

  preservesTerminalᴮ : Terminalᴮ B → Type _
  preservesTerminalᴮ T = isTerminalᴮ C (F.F-ob (BiuniversalElement.vertex T))
