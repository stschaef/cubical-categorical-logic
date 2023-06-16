{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Preorders.Forgetful where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Relation.Binary.Preorder
open import Cubical.Categories.Instances.Preorders.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functor.Base

open import Cubical.Categories.Instances.Preorders.Monotone

open Category
open Functor
open IsPreorder
open PreorderStr
open MonFun

module _ (ℓ ℓ' : Level) where
  PREORDER→SET : Functor (PREORDER ℓ ℓ') (SET ℓ)
  PREORDER→SET .F-ob = λ x → x .fst , x .snd .isPreorder .is-set
  PREORDER→SET .F-hom ϕ = ϕ .f
  PREORDER→SET .F-id = refl
  PREORDER→SET .F-seq = λ f g → refl
