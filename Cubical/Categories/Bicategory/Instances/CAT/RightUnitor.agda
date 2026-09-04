{-# OPTIONS --lossy-unification #-}
{-
  Right unitor NatIso for the CAT bicategory.
-}
module Cubical.Categories.Bicategory.Instances.CAT.RightUnitor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Terminal

open import Cubical.Categories.Bicategory.Instances.CAT.Base

private
  variable
    ℓ ℓ' : Level

open Functor
open NatTrans
open NatIso
open Category

module _ {ℓ ℓ' : Level} (C D : Category ℓ ℓ') where
  private
    module CC = Category C
    module DD = Category D

  ρU-trans-N-ob : (p : Functor C D ×Σ Unit*)
    → NatTrans (RU-srcCAT C D .F-ob p) (RU-tgtCAT C D .F-ob p)
  ρU-trans-N-ob (F , _) .N-ob _ = DD.id
  ρU-trans-N-ob (F , _) .N-hom f = DD.⋆IdR _ ∙ sym (DD.⋆IdL _)

  ρU-trans : NatTrans (RU-srcCAT C D) (RU-tgtCAT C D)
  ρU-trans .N-ob = ρU-trans-N-ob
  ρU-trans .N-hom {x = F , _} (α , _) =
    makeNatTransPath (funExt λ c →
      DD.⋆IdR _ ∙ DD.⋆IdR _ ∙ sym (DD.⋆IdL _))

  ρU-inv-N-ob : (p : Functor C D ×Σ Unit*)
    → NatTrans (RU-tgtCAT C D .F-ob p) (RU-srcCAT C D .F-ob p)
  ρU-inv-N-ob (F , _) .N-ob _ = DD.id
  ρU-inv-N-ob (F , _) .N-hom f = DD.⋆IdR _ ∙ sym (DD.⋆IdL _)

  ρU-isIso : (p : Functor C D ×Σ Unit*) → isIso (FUNCTOR C D) (ρU-trans-N-ob p)
  ρU-isIso (F , _) .isIso.inv = ρU-inv-N-ob (F , _)
  ρU-isIso (F , _) .isIso.sec =
    makeNatTransPath (funExt λ _ → DD.⋆IdL _)
  ρU-isIso (F , _) .isIso.ret =
    makeNatTransPath (funExt λ _ → DD.⋆IdL _)

  ρU-CAT : NatIso (RU-srcCAT C D) (RU-tgtCAT C D)
  ρU-CAT .trans = ρU-trans
  ρU-CAT .nIso = ρU-isIso
