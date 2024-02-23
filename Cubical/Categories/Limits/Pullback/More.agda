{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Limits.Pullback.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma as Ty hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.Presented
open import Cubical.Categories.Constructions.BinProduct.More
import Cubical.Categories.Constructions.Pullback.Redundant.Base as R
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.FunctorComprehension
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Bifunctor.Redundant as R

open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Constructions.Free.Category.Quiver as Free
  hiding (rec)

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where
  open Functor
  open R.RedundantPullback C public
  PbPresCat = PresCat
  PullbackProf : Profunctor PbPresCat C ℓ'
  PullbackProf = {!!}
