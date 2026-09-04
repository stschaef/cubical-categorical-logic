{-# OPTIONS --lossy-unification #-}
{- Reindexing a prestack along a pseudofunctor. -}
module Cubical.Categories.Bicategory.Prestack.Reindex where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Constructions.Op
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Functor.Composition
open import Cubical.Categories.Bicategory.Functor.Op
open import Cubical.Categories.Bicategory.Prestack.Base

private
  variable
    ℓa ℓa' ℓa'' ℓb ℓb' ℓb'' ℓp ℓp' : Level

module _ {A : Bicategory ℓa ℓa' ℓa''} {B : Bicategory ℓb ℓb' ℓb''}
  (F : Pseudofunctor A B) where

  reindexPrestack : Prestack B ℓp ℓp' → Prestack A ℓp ℓp'
  reindexPrestack P = P ∘Ps OpPs F
