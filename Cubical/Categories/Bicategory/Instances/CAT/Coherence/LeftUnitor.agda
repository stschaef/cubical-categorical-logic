{-# OPTIONS --lossy-unification #-}
{-
  Left unitor NatIso for the CAT bicategory.
-}
module Cubical.Categories.Bicategory.Instances.CAT.Coherence.LeftUnitor where

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

  λU-trans-N-ob : (p : Unit* ×Σ Functor C D)
    → NatTrans (LU-srcCAT C D .F-ob p) (LU-tgtCAT C D .F-ob p)
  λU-trans-N-ob (_ , F) .N-ob _ = DD.id
  λU-trans-N-ob (_ , F) .N-hom f = DD.⋆IdR _ ∙ sym (DD.⋆IdL _)

  λU-trans : NatTrans (LU-srcCAT C D) (LU-tgtCAT C D)
  λU-trans .N-ob = λU-trans-N-ob
  λU-trans .N-hom {x = _ , F} (_ , α) =
    makeNatTransPath (funExt λ c →
        DD.⋆IdR _
      ∙ cong (λ m → m ⋆⟨ D ⟩ α .N-ob c) (F .F-id))

  λU-inv-N-ob : (p : Unit* ×Σ Functor C D)
    → NatTrans (LU-tgtCAT C D .F-ob p) (LU-srcCAT C D .F-ob p)
  λU-inv-N-ob (_ , F) .N-ob _ = DD.id
  λU-inv-N-ob (_ , F) .N-hom f = DD.⋆IdR _ ∙ sym (DD.⋆IdL _)

  λU-isIso : (p : Unit* ×Σ Functor C D) → isIso (FUNCTOR C D) (λU-trans-N-ob p)
  λU-isIso (_ , F) .isIso.inv = λU-inv-N-ob (_ , F)
  λU-isIso (_ , F) .isIso.sec =
    makeNatTransPath (funExt λ _ → DD.⋆IdL _)
  λU-isIso (_ , F) .isIso.ret =
    makeNatTransPath (funExt λ _ → DD.⋆IdL _)

  λU-CAT : NatIso (LU-srcCAT C D) (LU-tgtCAT C D)
  λU-CAT .trans = λU-trans
  λU-CAT .nIso = λU-isIso
