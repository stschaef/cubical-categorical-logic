{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Bicategory.Instances.CAT where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Terminal

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Instances.CAT.Base public
open import Cubical.Categories.Bicategory.Instances.CAT.LeftUnitor public
open import Cubical.Categories.Bicategory.Instances.CAT.RightUnitor public
open import Cubical.Categories.Bicategory.Instances.CAT.Associator public
open import Cubical.Categories.Bicategory.Instances.CAT.Triangle public
open import Cubical.Categories.Bicategory.Instances.CAT.Pentagon public

private
  variable
    ℓ ℓ' : Level

open Bicategory

module _ {ℓ ℓ' : Level} where

  CAT : Bicategory (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  CAT .ob = Category ℓ ℓ'
  CAT .Hom[_,_] = FUNCTOR
  CAT .id = FunctorFromTerminal Id
  CAT .seq = seqCAT
  CAT .λU = λU-CAT
  CAT .ρU = ρU-CAT
  CAT .α = α-CAT
  CAT .triangle x y z F G = triangle-CAT x y z F G
  CAT .pentagon x y z w v F G H K =
    sym (FUNCTOR x v .Category.⋆Assoc _ _ _)
    ∙ pentagon-CAT x y z w v F G H K
