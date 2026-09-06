{-# OPTIONS --lossy-unification #-}
{- The Artin glue of a functor as a comma object in `CAT`. -}
module Gluing.Bicategorical.Comma where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Displayed.Instances.Dialgebras
open import Cubical.Categories.Displayed.Instances.Comma as Cma

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Instances.CAT.Limits.Inserter
open import Cubical.Categories.Bicategory.Instances.CAT.Limits.Product
open import Cubical.Categories.Bicategory.Universal.Base
open import Cubical.Categories.Bicategory.Limits.Product
open import Cubical.Categories.Bicategory.Limits.Comma

private
  variable
    ℓ ℓ' : Level

open Category
open Functor
open BiuniversalElement

module _ {ℓ ℓ' : Level} {C D : Category (ℓ-max ℓ ℓ') ℓ'}
  (F : Functor C D) where
  private
    ℓo : Level
    ℓo = ℓ-max ℓ ℓ'

  glueProd : BinProductᴮ (CAT {ℓo} {ℓ'}) D C
  glueProd = binProductCAT D C

  glueComma : Commaᴮ (CAT {ℓo} {ℓ'}) glueProd (Id {C = D}) F
  glueComma = commaObjectsCAT glueProd (Id {C = D}) F

  glueCat : Category ℓo ℓ'
  glueCat = glueComma .vertex

  glueCat≡DIALG : glueCat ≡ DIALG (Id ∘F Fst D C) (F ∘F Snd D C)
  glueCat≡DIALG = refl

  -- objects agree with the library's comma category on the nose; its
  -- homs state the naturality square in the opposite orientation, so
  -- the two categories are not equal
  glueOb≡Comma : glueCat .ob ≡ Cma.Comma (Id {C = D}) F .ob
  glueOb≡Comma = refl
