{-# OPTIONS --lossy-unification #-}
{- The identity pseudofunctor. -}
module Cubical.Categories.Bicategory.Functor.Identity where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Isomorphism

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo

private
  variable
    ℓ ℓ' ℓ'' : Level

open Functor
open NatTrans
open LaxFunctor
open Pseudofunctor

module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  LaxId : LaxFunctor B B
  LaxId .F-ob x = x
  LaxId .F-Hom = Id
  LaxId .F-id .N-ob _ = B.id₂
  LaxId .F-id .N-hom _ = B.⋆₂IdR _ ∙ sym (B.⋆₂IdL _)
  LaxId .F-seq .N-ob _ = B.id₂
  LaxId .F-seq .N-hom _ = B.⋆₂IdR _ ∙ sym (B.⋆₂IdL _)
  LaxId .lax-λ x y f =
      B.⟨⟩⋆₂⟨ B.⋆₂IdL (B.λ⁺ f) ⟩
    ∙ B.⟨ B.▷wId f ⟩⋆₂⟨⟩
    ∙ B.⋆₂IdL (B.λ⁺ f)
  LaxId .lax-ρ x y f =
      B.⟨⟩⋆₂⟨ B.⋆₂IdL (B.ρ⁺ f) ⟩
    ∙ B.⟨ B.◁wId f ⟩⋆₂⟨⟩
    ∙ B.⋆₂IdL (B.ρ⁺ f)
  LaxId .lax-α x y z w f g h =
      (B.⟨⟩⋆₂⟨ B.⋆₂IdL (B.α⁺ f g h) ⟩
        ∙ B.⟨ B.▷wId h ⟩⋆₂⟨⟩
        ∙ B.⋆₂IdL (B.α⁺ f g h))
    ∙ sym (B.⟨⟩⋆₂⟨ B.⟨ B.◁wId f ⟩⋆₂⟨⟩ ∙ B.⋆₂IdL B.id₂ ⟩
        ∙ B.⋆₂IdR (B.α⁺ f g h))

  Idᴮ : Pseudofunctor B B
  Idᴮ .laxFunctor = LaxId
  Idᴮ .F-id-isIso _ = idCatIso .snd
  Idᴮ .F-seq-isIso _ = idCatIso .snd
