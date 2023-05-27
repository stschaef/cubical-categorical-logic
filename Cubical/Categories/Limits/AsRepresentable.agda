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

open import Cubical.Tactics.CategorySolver.Reflection

module _ {ℓj}{ℓj'}{ℓc}{ℓc'}(J : Category ℓj ℓj')(C : Category ℓc ℓc') where
  Limit : (D : Functor J C) → Type (ℓ-max (ℓ-max (ℓ-max ℓj ℓj') ℓc) ℓc')
  Limit D = UnivElt C (CONE J C ∘F (Id {C = C ^op} ,F Constant (C ^op) (FUNCTOR J C) D))

  open Cone
  open LimCone
  open UnivElt
  open isUniversal
  open Functor
  open NatTrans

  Limit→LimCone : ∀ {D : Functor J C} → Limit D → LimCone D
  Limit→LimCone x .lim = x .vertex
  Limit→LimCone {D} x .limCone = CONE→Cone J C D (lim (Limit→LimCone x)) (x .element)
  Limit→LimCone x .univProp = λ c cc →
    ({!!} ,
      (λ v → {!!})) ,
      (λ y → {!!})

  LimCone→Limit : ∀ {D : Functor J C} → LimCone D → Limit D
  LimCone→Limit x .vertex = x .lim
  LimCone→Limit x .element .N-ob v = x .limCone .coneOut v
  LimCone→Limit x .element .N-hom {u}{v} ϕ = {!!}
  LimCone→Limit x .universal .coinduction = λ x₁ → {!!}
  LimCone→Limit x .universal .commutes = λ ϕ → {!!}
  LimCone→Limit x .universal .is-uniq = λ ϕ f x₁ → {!!}
