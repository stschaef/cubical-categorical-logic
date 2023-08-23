{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Fibration where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Instances.Sets
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Displayed.Functor

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓ ℓ' : Level

open Category

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD') where
  CartesianLift : (∫C (C /C (Fst {Cᴰ = D}))) .ob → Type _
  CartesianLift (c , (d , f)) = LocalRightAdjointAtᴰ (cod D) (d , f)

  isFibration : Type _
  isFibration = LocalRightAdjointᴰ (cod D)


module _ ℓ ℓ' where
  open UniversalElementᴰ
  open Categoryᴰ
  open Functor
  open Functorᴰ
  isFibrationSETS : isFibration (SETS ℓ ℓ')
  isFibrationSETS {x} ((d , dᴰ) , f) .vertexᴰ z = dᴰ (f z)
  isFibrationSETS ((d , dᴰ) , f) .elementᴰ .fst .fst = f
  isFibrationSETS ((d , dᴰ) , f) .elementᴰ .fst .snd x = (λ z → z)
  isFibrationSETS ((d , dᴰ) , f) .elementᴰ .snd = refl
  isFibrationSETS ((d , dᴰ) , f) .universalᴰ xᴰ {g} =
    isoToIsEquiv
      (iso
        (λ x₁ → ((λ z → f (g z)) , λ z → x₁ z) , {!!})
        (λ x₁ x₂ x₃ → transport (cong (λ a → fst (dᴰ (a x₂))) (x₁ .snd)) (x₁ .fst .snd x₂ x₃))
        (λ b → sym (cong (λ a → (a , λ x₁ x₂ → transport (cong (λ k → {!fst (dᴰ (k ?))!}) (b .snd)) (b .fst .snd x₁ x₂)) , {!!}) (b .snd)))
        {!!}
      )
