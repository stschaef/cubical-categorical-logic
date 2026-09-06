{-# OPTIONS --lossy-unification #-}
{-
  Associator NatIso for the CAT bicategory.
-}
module Cubical.Categories.Bicategory.Instances.CAT.Coherence.Associator where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Functors

open import Cubical.Categories.Bicategory.Instances.CAT.Base

private
  variable
    ℓ ℓ' : Level

open Functor
open NatTrans
open NatIso
open Category

module _ {ℓ ℓ' : Level} (C D E W : Category ℓ ℓ') where
  private
    module CC = Category C
    module DD = Category D
    module EE = Category E
    module WW = Category W

  α-trans-N-ob : (p : Functor C D ×Σ (Functor D E ×Σ Functor E W))
    → NatTrans (A-srcCAT C D E W .F-ob p) (A-tgtCAT C D E W .F-ob p)
  α-trans-N-ob (F , G , H) .N-ob _ = WW.id
  α-trans-N-ob (F , G , H) .N-hom f = WW.⋆IdR _ ∙ sym (WW.⋆IdL _)

  α-trans : NatTrans (A-srcCAT C D E W) (A-tgtCAT C D E W)
  α-trans .N-ob = α-trans-N-ob
  α-trans .N-hom {x = F , G , H} {y = F' , G' , H'} (γ , δ , ε) =
    makeNatTransPath (funExt λ c →
        WW.⋆IdR _
      ∙ cong (λ m → m ⋆⟨ W ⟩ ε .N-ob (G' .F-ob (F' .F-ob c))) (H .F-seq _ _)
      ∙ WW.⋆Assoc _ _ _
      ∙ sym (WW.⋆IdL _))

  α-inv-N-ob : (p : Functor C D ×Σ (Functor D E ×Σ Functor E W))
    → NatTrans (A-tgtCAT C D E W .F-ob p) (A-srcCAT C D E W .F-ob p)
  α-inv-N-ob (F , G , H) .N-ob _ = WW.id
  α-inv-N-ob (F , G , H) .N-hom f = WW.⋆IdR _ ∙ sym (WW.⋆IdL _)

  α-isIso : (p : Functor C D ×Σ (Functor D E ×Σ Functor E W))
    → isIso (FUNCTOR C W) (α-trans-N-ob p)
  α-isIso (F , G , H) .isIso.inv = α-inv-N-ob (F , G , H)
  α-isIso (F , G , H) .isIso.sec =
    makeNatTransPath (funExt λ _ → WW.⋆IdL _)
  α-isIso (F , G , H) .isIso.ret =
    makeNatTransPath (funExt λ _ → WW.⋆IdL _)

  α-CAT : NatIso (A-srcCAT C D E W) (A-tgtCAT C D E W)
  α-CAT .trans = α-trans
  α-CAT .nIso = α-isIso
