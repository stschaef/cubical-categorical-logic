{-# OPTIONS --lossy-unification #-}
{-
  Triangle coherence for the CAT bicategory.
-}
module Cubical.Categories.Bicategory.Instances.CAT.Coherence.Triangle where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors

open import Cubical.Categories.Bicategory.Instances.CAT.Base
open import Cubical.Categories.Bicategory.Instances.CAT.Coherence.LeftUnitor
open import Cubical.Categories.Bicategory.Instances.CAT.Coherence.RightUnitor
open import Cubical.Categories.Bicategory.Instances.CAT.Coherence.Associator

private
  variable
    ℓ ℓ' : Level

open Functor
open NatTrans
open Category

module _ {ℓ ℓ' : Level} where

  triangle-CAT : (C D E : Category ℓ ℓ')
    (F : Functor C D) (G : Functor D E)
    →   α-trans-N-ob C D D E (F , Id , G)
      ⋆⟨ FUNCTOR C E ⟩
        seqCAT C D E .F-hom (idTrans F , λU-trans-N-ob D E (tt* , G))
      ≡ seqCAT C D E .F-hom (ρU-trans-N-ob C D (F , tt*) , idTrans G)
  triangle-CAT C D E F G = makeNatTransPath (funExt λ _ → E.⋆IdL _)
    where
    module C = Category C
    module D = Category D
    module E = Category E
