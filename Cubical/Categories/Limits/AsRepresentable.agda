{-# OPTIONS --safe #-}

module Cubical.Categories.Limits.AsRepresentable where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Limits.AsRepresentable.Cone
open import Cubical.Categories.Limits.Limits

module _ {ℓj}{ℓj'}{ℓc}{ℓc'}(J : Category ℓj ℓj')(C : Category ℓc ℓc') where
  Limit : (D : Functor J C) → Type (ℓ-max (ℓ-max (ℓ-max ℓj ℓj') ℓc) ℓc')
  Limit D = UnivElt C (CONE J C ∘F (Id {C = C ^op} ,F Constant (C ^op) (FUNCTOR J C) D))

  open Cone
  open LimCone
  open UnivElt
  open isUniversal
  open Functor

  Limit→LimCone : ∀ {D : Functor J C} → Limit D → LimCone D
  Limit→LimCone x .lim = x .vertex
  Limit→LimCone {D} x .limCone = CONE→Cone J C D (lim (Limit→LimCone x)) (x .element)
  Limit→LimCone x .univProp = λ c cc →
    (x .universal .coinduction {!!} ,
      (λ v → {!!})) ,
      (λ y → {!!})
