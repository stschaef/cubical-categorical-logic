{-# OPTIONS --safe #-}
module Cubical.Categories.Monad.Alt where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor renaming (𝟙⟨_⟩ to funcId)
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Reflection.RecordEquiv
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Displayed.WideSubcategory

open import Cubical.Tactics.CategorySolver.Reflection
open import Cubical.Tactics.FunctorSolver.Reflection


open import Cubical.Foundations.Isomorphism.More

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ (C : Category ℓ ℓ') where
  open Category
  private
    variable
      a b c : C .ob
      f g h : C [ a , b ]
  module _ (T : C .ob → C .ob) where
    TC : Category ℓ ℓ'
    TC .ob = C .ob
    TC .Hom[_,_] x y = C [ T x , T y ]
    TC .id = C .id
    TC ._⋆_ = C ._⋆_
    TC .⋆IdL = C .⋆IdL
    TC .⋆IdR = C .⋆IdR
    TC .⋆Assoc = C .⋆Assoc
    TC .isSetHom = C .isSetHom

    U : Functor TC C
    U .Functor.F-ob x = T x
    U .Functor.F-hom = λ z → z
    U .Functor.F-id = refl
    U .Functor.F-seq f g = refl

    -- notion of when a morphism is a homomorphism of free algebras
    module _ (isFreeAlgHom : WideSubcategory TC ℓ'') where
      Kleisliᴰ : Categoryᴰ C ℓ ℓ'
