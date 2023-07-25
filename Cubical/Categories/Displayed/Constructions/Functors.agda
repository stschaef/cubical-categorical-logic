{-
  category of displayed functors displayed over the category of functors
-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.Functors where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
         (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
         where

  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ
  open Category
  open Categoryᴰ
  open Functor
  open Functorᴰ
  open NatTrans
  open NatTransᴰ

  FUNCTORᴰ : Categoryᴰ (FUNCTOR C D) _ _
  FUNCTORᴰ .ob[_] F = Functorᴰ F Cᴰ Dᴰ
  FUNCTORᴰ .Hom[_][_,_] α Fᴰ Gᴰ = NatTransᴰ α Fᴰ Gᴰ
  FUNCTORᴰ .idᴰ = idTransᴰ _
  FUNCTORᴰ ._⋆ᴰ_ = seqTransᴰ
  FUNCTORᴰ .⋆IdLᴰ αᴰ = NatTransᴰPathP _ _ _ _ _ (λ zᴰ → Dᴰ .⋆IdLᴰ _)
  FUNCTORᴰ .⋆IdRᴰ αᴰ = NatTransᴰPathP _ _ _ _ _ (λ zᴰ → Dᴰ .⋆IdRᴰ _)
  FUNCTORᴰ .⋆Assocᴰ αᴰ βᴰ γᴰ = NatTransᴰPathP _ _ _ _ _ (λ _ → Dᴰ .⋆Assocᴰ _ _ _)
  FUNCTORᴰ .isSetHomᴰ = isSetNatTransᴰ _ _ _
