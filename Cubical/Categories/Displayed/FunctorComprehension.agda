{-
    The displayed version of functor comprehension: any point-wise
    representable profunctor is the graph of a functor.
-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.FunctorComprehension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Sets
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.Presheaf

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' ℓP ℓPᴰ : Level

open Functor
open Functorᴰ
open NatTrans
open NatTransᴰ
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
         {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
         {F~ : Functor C (PresheafCategory D ℓP)} -- A "specification" for a functor
         {F~-repr : ∀ c → UniversalElement D (F~ ⟅ c ⟆)}
         {Fᴰ~ : Functorᴰ F~ Cᴰ (PRESHEAFᴰ Dᴰ ℓP ℓPᴰ)}
         (Fᴰ~-repr : ∀ {c} cᴰ → UniversalElementᴰ Dᴰ (Fᴰ~ .F-obᴰ {c} cᴰ) (F~-repr c))
         where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    open UniversalElement --     module UE {c} {cᴰ : Cᴰ.ob[ c ]} = UniversalElementᴰ Fᴰ~-repr cᴰ
    open UniversalElementᴰ --     module UE {c} {cᴰ : Cᴰ.ob[ c ]} = UniversalElementᴰ Fᴰ~-repr cᴰ
  FunctorComprehensionᴰ : Functorᴰ (FunctorComprehension' F~ F~-repr) Cᴰ Dᴰ
  FunctorComprehensionᴰ .F-obᴰ xᴰ = Fᴰ~-repr xᴰ .vertexᴰ
  FunctorComprehensionᴰ .F-homᴰ {x}{y}{f}{xᴰ}{yᴰ} fᴰ =
    introᴰ (Fᴰ~-repr yᴰ) (Fᴰ~ .F-homᴰ fᴰ .N-obᴰ (Fᴰ~-repr xᴰ .vertexᴰ) _ (Fᴰ~-repr xᴰ .elementᴰ))
  FunctorComprehensionᴰ .F-idᴰ =
    {!!}
    -- (λ i → introᴰ {!Fᴰ~ .F-idᴰ i .N-obᴰ!} (FunctorComprehension' F~ F~-repr .F-id i)) ▷ {!!}
  FunctorComprehensionᴰ .F-seqᴰ = {!!}
