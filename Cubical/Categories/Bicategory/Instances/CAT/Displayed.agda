{-# OPTIONS --lossy-unification #-}
{- The displayed bicategory CATᴰ of displayed categories over CAT -}
module Cubical.Categories.Bicategory.Instances.CAT.Displayed where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Terminal
open import Cubical.Categories.Instances.TotalCategory

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
  hiding (idTransᴰ)
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.BinProduct.More
  hiding (introF)
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.Instances.Functor.Base
import Cubical.Categories.Displayed.Reasoning as Reasoning

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Displayed
open import Cubical.Categories.Bicategory.Instances.CAT

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level

open Category
open Functor
open Functorᴰ
open NatTrans
open NatTransᴰ
open NatIsoᴰ
open isIsoᴰ

-- ------------------------------------------------------------
-- Displayed horizontal composition of natural transformations,
-- mirroring `hSeqCAT`.
-- ------------------------------------------------------------
module _ {C D E : Category ℓ ℓ'}
  {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'} {Dᴰ : Categoryᴰ D ℓᴰ ℓᴰ'}
  {Eᴰ : Categoryᴰ E ℓᴰ ℓᴰ'} where
  private
    module Eᴰ = Categoryᴰ Eᴰ
    module RD = Reasoning Dᴰ
    module RE = Reasoning Eᴰ

  hSeqCATᴰ : {F F' : Functor C D} {G G' : Functor D E}
    {β : NatTrans F F'} {γ : NatTrans G G'}
    {Fᴰ : Functorᴰ F Cᴰ Dᴰ} {F'ᴰ : Functorᴰ F' Cᴰ Dᴰ}
    {Gᴰ : Functorᴰ G Dᴰ Eᴰ} {G'ᴰ : Functorᴰ G' Dᴰ Eᴰ}
    (βᴰ : NatTransᴰ β Fᴰ F'ᴰ) (γᴰ : NatTransᴰ γ Gᴰ G'ᴰ)
    → NatTransᴰ (hSeqCAT β γ) (Gᴰ ∘Fᴰ Fᴰ) (G'ᴰ ∘Fᴰ F'ᴰ)
  hSeqCATᴰ {Gᴰ = Gᴰ} βᴰ γᴰ .N-obᴰ cᴰ =
    Gᴰ .F-homᴰ (βᴰ .N-obᴰ cᴰ) Eᴰ.⋆ᴰ γᴰ .N-obᴰ _
  hSeqCATᴰ {F'ᴰ = F'ᴰ} {Gᴰ = Gᴰ} βᴰ γᴰ .N-homᴰ fᴰ = RE.rectify (RE.≡out
    ( sym (RE.⋆Assoc _ _ _)
    ∙ cong₂ RE._⋆_
        ( sym (∫F Gᴰ .F-seq _ _)
        ∙ cong (∫F Gᴰ .F-hom) (RD.≡in (βᴰ .N-homᴰ fᴰ))
        ∙ ∫F Gᴰ .F-seq _ _) refl
    ∙ RE.⋆Assoc _ _ _
    ∙ cong₂ RE._⋆_ refl (RE.≡in (γᴰ .N-homᴰ (F'ᴰ .F-homᴰ fᴰ)))
    ∙ sym (RE.⋆Assoc _ _ _)))

-- ------------------------------------------------------------
-- Displayed identity 1-cell functor.
-- ------------------------------------------------------------
module _ {C : Category ℓ ℓ'} (Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ') where
  idCATᴰ : Functorᴰ (FunctorFromTerminal {C = FUNCTOR C C} Id)
             UnitCᴰ (FUNCTORᴰ Cᴰ Cᴰ)
  idCATᴰ .F-obᴰ _ = Idᴰ
  idCATᴰ .F-homᴰ _ = idTransᴰ Cᴰ Cᴰ Id Idᴰ
  idCATᴰ .F-idᴰ = refl
  idCATᴰ .F-seqᴰ _ _ = symP (idLTransᴰ Cᴰ Cᴰ (idTransᴰ Cᴰ Cᴰ Id Idᴰ))

-- ------------------------------------------------------------
-- Displayed horizontal composition functor.
-- ------------------------------------------------------------
module _ {C D E : Category ℓ ℓ'}
  (Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ') (Dᴰ : Categoryᴰ D ℓᴰ ℓᴰ')
  (Eᴰ : Categoryᴰ E ℓᴰ ℓᴰ') where
  private
    module RE = Reasoning Eᴰ

  seqCATᴰ : Functorᴰ (seqCAT C D E)
    (FUNCTORᴰ Cᴰ Dᴰ ×Cᴰ FUNCTORᴰ Dᴰ Eᴰ) (FUNCTORᴰ Cᴰ Eᴰ)
  seqCATᴰ .F-obᴰ (Fᴰ , Gᴰ) = Gᴰ ∘Fᴰ Fᴰ
  seqCATᴰ .F-homᴰ (βᴰ , γᴰ) = hSeqCATᴰ βᴰ γᴰ
  seqCATᴰ .F-idᴰ {x = F , G} {xᴰ = Fᴰ , Gᴰ} =
    makeNatTransPathᴰ Cᴰ Eᴰ (seqCAT C D E .F-id)
      (implicitFunExt (λ {c} → funExt (λ cᴰ →
        RE.rectify (RE.≡out
          ( cong₂ RE._⋆_ (∫F Gᴰ .F-id) refl
          ∙ RE.⋆IdL _)))))
  seqCATᴰ .F-seqᴰ {x = F , G} {y = F' , G'} {z = F'' , G''}
    {xᴰ = Fᴰ , Gᴰ} {yᴰ = F'ᴰ , G'ᴰ} {zᴰ = F''ᴰ , G''ᴰ}
    (βᴰ , γᴰ) (β'ᴰ , γ'ᴰ) =
    makeNatTransPathᴰ Cᴰ Eᴰ (seqCAT C D E .F-seq _ _)
      (implicitFunExt (λ {c} → funExt (λ cᴰ →
        RE.rectify (RE.≡out
          ( cong₂ RE._⋆_ (∫F Gᴰ .F-seq _ _) refl
          ∙ RE.⋆Assoc _ _ _
          ∙ cong₂ RE._⋆_ refl
              ( sym (RE.⋆Assoc _ _ _)
              ∙ cong₂ RE._⋆_ (RE.≡in (γᴰ .N-homᴰ (β'ᴰ .N-obᴰ cᴰ))) refl
              ∙ RE.⋆Assoc _ _ _)
          ∙ sym (RE.⋆Assoc _ _ _))))))

-- ------------------------------------------------------------
-- Displayed left unitor.
-- ------------------------------------------------------------
module _ {C D : Category ℓ ℓ'}
  (Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ') (Dᴰ : Categoryᴰ D ℓᴰ ℓᴰ') where
  private
    module Dᴰ = Categoryᴰ Dᴰ
    module RD = Reasoning Dᴰ

  λU-CATᴰ-N-ob : {F : Functor C D} (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
    → NatTransᴰ (λU-trans-N-ob C D (tt* , F)) (Fᴰ ∘Fᴰ Idᴰ) Fᴰ
  λU-CATᴰ-N-ob Fᴰ .N-obᴰ cᴰ = Dᴰ.idᴰ
  λU-CATᴰ-N-ob Fᴰ .N-homᴰ fᴰ =
    RD.rectify (RD.≡out (RD.⋆IdR _ ∙ sym (RD.⋆IdL _)))

  λU-CATᴰ-inv : {F : Functor C D} (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
    → NatTransᴰ (λU-inv-N-ob C D (tt* , F)) Fᴰ (Fᴰ ∘Fᴰ Idᴰ)
  λU-CATᴰ-inv Fᴰ .N-obᴰ cᴰ = Dᴰ.idᴰ
  λU-CATᴰ-inv Fᴰ .N-homᴰ fᴰ =
    RD.rectify (RD.≡out (RD.⋆IdR _ ∙ sym (RD.⋆IdL _)))

  λU-CATᴰ : NatIsoᴰ (λU-CAT C D)
    (seqCATᴰ Cᴰ Cᴰ Dᴰ ∘Fᴰ (idCATᴰ Cᴰ ×Fᴰ 𝟙ᴰ⟨ FUNCTORᴰ Cᴰ Dᴰ ⟩))
    (Sndᴰ UnitCᴰ (FUNCTORᴰ Cᴰ Dᴰ))
  λU-CATᴰ .transᴰ .N-obᴰ (_ , Fᴰ) = λU-CATᴰ-N-ob Fᴰ
  λU-CATᴰ .transᴰ .N-homᴰ {x = _ , F} {y = _ , F'} {f = _ , α}
    {xᴰ = _ , Fᴰ} {yᴰ = _ , F'ᴰ} (_ , αᴰ) =
    makeNatTransPathᴰ Cᴰ Dᴰ (λU-trans C D .N-hom (_ , α))
      (implicitFunExt (λ {c} → funExt (λ cᴰ →
        RD.rectify (RD.≡out
          ( RD.⋆IdR _
          ∙ cong₂ RD._⋆_ (∫F Fᴰ .F-id) refl)))))
  λU-CATᴰ .nIsoᴰ (_ , Fᴰ) .invᴰ = λU-CATᴰ-inv Fᴰ
  λU-CATᴰ .nIsoᴰ (_ , Fᴰ) .secᴰ =
    makeNatTransPathᴰ Cᴰ Dᴰ _
      (implicitFunExt (λ {c} → funExt (λ cᴰ → Dᴰ.⋆IdLᴰ Dᴰ.idᴰ)))
  λU-CATᴰ .nIsoᴰ (_ , Fᴰ) .retᴰ =
    makeNatTransPathᴰ Cᴰ Dᴰ _
      (implicitFunExt (λ {c} → funExt (λ cᴰ → Dᴰ.⋆IdLᴰ Dᴰ.idᴰ)))

-- ------------------------------------------------------------
-- Displayed right unitor.
-- ------------------------------------------------------------
module _ {C D : Category ℓ ℓ'}
  (Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ') (Dᴰ : Categoryᴰ D ℓᴰ ℓᴰ') where
  private
    module Dᴰ = Categoryᴰ Dᴰ
    module RD = Reasoning Dᴰ

  ρU-CATᴰ-N-ob : {F : Functor C D} (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
    → NatTransᴰ (ρU-trans-N-ob C D (F , tt*)) (Idᴰ ∘Fᴰ Fᴰ) Fᴰ
  ρU-CATᴰ-N-ob Fᴰ .N-obᴰ cᴰ = Dᴰ.idᴰ
  ρU-CATᴰ-N-ob Fᴰ .N-homᴰ fᴰ =
    RD.rectify (RD.≡out (RD.⋆IdR _ ∙ sym (RD.⋆IdL _)))

  ρU-CATᴰ-inv : {F : Functor C D} (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
    → NatTransᴰ (ρU-inv-N-ob C D (F , tt*)) Fᴰ (Idᴰ ∘Fᴰ Fᴰ)
  ρU-CATᴰ-inv Fᴰ .N-obᴰ cᴰ = Dᴰ.idᴰ
  ρU-CATᴰ-inv Fᴰ .N-homᴰ fᴰ =
    RD.rectify (RD.≡out (RD.⋆IdR _ ∙ sym (RD.⋆IdL _)))

  ρU-CATᴰ : NatIsoᴰ (ρU-CAT C D)
    (seqCATᴰ Cᴰ Dᴰ Dᴰ ∘Fᴰ (𝟙ᴰ⟨ FUNCTORᴰ Cᴰ Dᴰ ⟩ ×Fᴰ idCATᴰ Dᴰ))
    (Fstᴰ (FUNCTORᴰ Cᴰ Dᴰ) UnitCᴰ)
  ρU-CATᴰ .transᴰ .N-obᴰ (Fᴰ , _) = ρU-CATᴰ-N-ob Fᴰ
  ρU-CATᴰ .transᴰ .N-homᴰ {x = F , _} {f = α , _}
    {xᴰ = Fᴰ , _} {yᴰ = F'ᴰ , _} (αᴰ , _) =
    makeNatTransPathᴰ Cᴰ Dᴰ (ρU-trans C D .N-hom (α , _))
      (implicitFunExt (λ {c} → funExt (λ cᴰ →
        RD.rectify (RD.≡out
          ( RD.⋆IdR _ ∙ RD.⋆IdR _ ∙ sym (RD.⋆IdL _))))))
  ρU-CATᴰ .nIsoᴰ (Fᴰ , _) .invᴰ = ρU-CATᴰ-inv Fᴰ
  ρU-CATᴰ .nIsoᴰ (Fᴰ , _) .secᴰ =
    makeNatTransPathᴰ Cᴰ Dᴰ _
      (implicitFunExt (λ {c} → funExt (λ cᴰ → Dᴰ.⋆IdLᴰ Dᴰ.idᴰ)))
  ρU-CATᴰ .nIsoᴰ (Fᴰ , _) .retᴰ =
    makeNatTransPathᴰ Cᴰ Dᴰ _
      (implicitFunExt (λ {c} → funExt (λ cᴰ → Dᴰ.⋆IdLᴰ Dᴰ.idᴰ)))

-- ------------------------------------------------------------
-- Displayed associator.
-- ------------------------------------------------------------
module _ {C D E W : Category ℓ ℓ'}
  (Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ') (Dᴰ : Categoryᴰ D ℓᴰ ℓᴰ')
  (Eᴰ : Categoryᴰ E ℓᴰ ℓᴰ') (Wᴰ : Categoryᴰ W ℓᴰ ℓᴰ') where
  private
    module Wᴰ = Categoryᴰ Wᴰ
    module RW = Reasoning Wᴰ

  α-CATᴰ-N-ob : {F : Functor C D} {G : Functor D E} {H : Functor E W}
    (Fᴰ : Functorᴰ F Cᴰ Dᴰ) (Gᴰ : Functorᴰ G Dᴰ Eᴰ) (Hᴰ : Functorᴰ H Eᴰ Wᴰ)
    → NatTransᴰ (α-trans-N-ob C D E W (F , G , H))
        (Hᴰ ∘Fᴰ (Gᴰ ∘Fᴰ Fᴰ)) ((Hᴰ ∘Fᴰ Gᴰ) ∘Fᴰ Fᴰ)
  α-CATᴰ-N-ob Fᴰ Gᴰ Hᴰ .N-obᴰ cᴰ = Wᴰ.idᴰ
  α-CATᴰ-N-ob Fᴰ Gᴰ Hᴰ .N-homᴰ fᴰ =
    RW.rectify (RW.≡out (RW.⋆IdR _ ∙ sym (RW.⋆IdL _)))

  α-CATᴰ-inv : {F : Functor C D} {G : Functor D E} {H : Functor E W}
    (Fᴰ : Functorᴰ F Cᴰ Dᴰ) (Gᴰ : Functorᴰ G Dᴰ Eᴰ) (Hᴰ : Functorᴰ H Eᴰ Wᴰ)
    → NatTransᴰ (α-inv-N-ob C D E W (F , G , H))
        ((Hᴰ ∘Fᴰ Gᴰ) ∘Fᴰ Fᴰ) (Hᴰ ∘Fᴰ (Gᴰ ∘Fᴰ Fᴰ))
  α-CATᴰ-inv Fᴰ Gᴰ Hᴰ .N-obᴰ cᴰ = Wᴰ.idᴰ
  α-CATᴰ-inv Fᴰ Gᴰ Hᴰ .N-homᴰ fᴰ =
    RW.rectify (RW.≡out (RW.⋆IdR _ ∙ sym (RW.⋆IdL _)))

  α-CATᴰ : NatIsoᴰ (α-CAT C D E W)
    (seqCATᴰ Cᴰ Eᴰ Wᴰ
      ∘Fᴰ ((seqCATᴰ Cᴰ Dᴰ Eᴰ ×Fᴰ 𝟙ᴰ⟨ FUNCTORᴰ Eᴰ Wᴰ ⟩)
      ∘Fᴰ ×Cᴰ-assoc (FUNCTORᴰ Cᴰ Dᴰ) (FUNCTORᴰ Dᴰ Eᴰ) (FUNCTORᴰ Eᴰ Wᴰ)))
    (seqCATᴰ Cᴰ Dᴰ Wᴰ
      ∘Fᴰ (𝟙ᴰ⟨ FUNCTORᴰ Cᴰ Dᴰ ⟩ ×Fᴰ seqCATᴰ Dᴰ Eᴰ Wᴰ))
  α-CATᴰ .transᴰ .N-obᴰ {x = F , G , H} (Fᴰ , Gᴰ , Hᴰ) =
    α-CATᴰ-N-ob {F = F} {G = G} {H = H} Fᴰ Gᴰ Hᴰ
  α-CATᴰ .transᴰ .N-homᴰ {x = F , G , H} {y = F' , G' , H'}
    {f = γ , δ , ε} {xᴰ = Fᴰ , Gᴰ , Hᴰ} {yᴰ = F'ᴰ , G'ᴰ , H'ᴰ}
    (γᴰ , δᴰ , εᴰ) =
    makeNatTransPathᴰ Cᴰ Wᴰ (α-trans C D E W .N-hom (γ , δ , ε))
      (implicitFunExt (λ {c} → funExt (λ cᴰ →
        RW.rectify (RW.≡out
          ( RW.⋆IdR _
          ∙ cong₂ RW._⋆_ (∫F Hᴰ .F-seq _ _) refl
          ∙ RW.⋆Assoc _ _ _
          ∙ sym (RW.⋆IdL _))))))
  α-CATᴰ .nIsoᴰ {x = F , G , H} (Fᴰ , Gᴰ , Hᴰ) .invᴰ =
    α-CATᴰ-inv {F = F} {G = G} {H = H} Fᴰ Gᴰ Hᴰ
  α-CATᴰ .nIsoᴰ (Fᴰ , Gᴰ , Hᴰ) .secᴰ =
    makeNatTransPathᴰ Cᴰ Wᴰ _
      (implicitFunExt (λ {c} → funExt (λ cᴰ → Wᴰ.⋆IdLᴰ Wᴰ.idᴰ)))
  α-CATᴰ .nIsoᴰ (Fᴰ , Gᴰ , Hᴰ) .retᴰ =
    makeNatTransPathᴰ Cᴰ Wᴰ _
      (implicitFunExt (λ {c} → funExt (λ cᴰ → Wᴰ.⋆IdLᴰ Wᴰ.idᴰ)))

-- ------------------------------------------------------------
-- The displayed bicategory of displayed categories over CAT.
-- ------------------------------------------------------------
module _ {ℓ ℓ' ℓᴰ ℓᴰ' : Level} where
  open Bicategoryᴰ

  CATᴰ : Bicategoryᴰ (CAT {ℓ} {ℓ'}) _ _ _
  CATᴰ .ob[_] C = Categoryᴰ C ℓᴰ ℓᴰ'
  CATᴰ .Homᴰ[_,_] Cᴰ Dᴰ =
    FUNCTORᴰ {ℓC = ℓ} {ℓC' = ℓ'} {ℓD = ℓ} {ℓD' = ℓ'}
             {ℓCᴰ = ℓᴰ} {ℓCᴰ' = ℓᴰ'} {ℓDᴰ = ℓᴰ} {ℓDᴰ' = ℓᴰ'} Cᴰ Dᴰ
  CATᴰ .idᴰ {xᴰ = Cᴰ} = idCATᴰ Cᴰ
  CATᴰ .seqᴰ Cᴰ Dᴰ Eᴰ = seqCATᴰ Cᴰ Dᴰ Eᴰ
  CATᴰ .λUᴰ Cᴰ Dᴰ = λU-CATᴰ Cᴰ Dᴰ
  CATᴰ .ρUᴰ Cᴰ Dᴰ = ρU-CATᴰ Cᴰ Dᴰ
  CATᴰ .αᴰ Cᴰ Dᴰ Eᴰ Wᴰ = α-CATᴰ Cᴰ Dᴰ Eᴰ Wᴰ
  CATᴰ .triangleᴰ {x = C} {y = D} {z = E} {f = F} {g = G}
    {xᴰ = Cᴰ} {yᴰ = Dᴰ} {zᴰ = Eᴰ} Fᴰ Gᴰ =
    makeNatTransPathᴰ Cᴰ Eᴰ (CAT .Bicategory.triangle C D E F G)
      (implicitFunExt (λ {c} → funExt (λ cᴰ →
        RE.rectify (RE.≡out (RE.⋆IdL _)))))
    where module RE = Reasoning Eᴰ
  CATᴰ .pentagonᴰ {x = C} {y = D} {z = E} {w = W} {v = V}
    {f = F} {g = G} {h = H} {k = K}
    {xᴰ = Cᴰ} {yᴰ = Dᴰ} {zᴰ = Eᴰ} {wᴰ = Wᴰ} {vᴰ = Vᴰ} Fᴰ Gᴰ Hᴰ Kᴰ =
    makeNatTransPathᴰ Cᴰ Vᴰ (CAT .Bicategory.pentagon C D E W V F G H K)
      (implicitFunExt (λ {c} → funExt (λ cᴰ →
        RV.rectify (RV.≡out
          ( sym (RV.⋆Assoc _ _ _)
          ∙ cong₂ RV._⋆_
              ( cong₂ RV._⋆_ (RV.⋆IdR _ ∙ ∫F Kᴰ .F-id) refl
              ∙ RV.⋆IdR _) refl
          ∙ cong₂ RV._⋆_ refl
              ( RV.⋆IdR _
              ∙ cong (∫F Kᴰ .F-hom)
                  (cong (∫F Hᴰ .F-hom) (∫F Gᴰ .F-id) ∙ ∫F Hᴰ .F-id)
              ∙ ∫F Kᴰ .F-id))))))
    where
      module RE = Reasoning Eᴰ
      module RW = Reasoning Wᴰ
      module RV = Reasoning Vᴰ

-- ------------------------------------------------------------
-- Sanity checks: the displayed cells really are the displayed
-- categorical notions, and the levels are not degenerate.
-- ------------------------------------------------------------
module _ {ℓ ℓ' ℓᴰ ℓᴰ' : Level} where
  private
    module CATᴰ = Bicategoryᴰ (CATᴰ {ℓ} {ℓ'} {ℓᴰ} {ℓᴰ'})

  _ : CATᴰ.ob[_] ≡ (λ (C : Category ℓ ℓ') → Categoryᴰ C ℓᴰ ℓᴰ')
  _ = refl

  _ : {C D : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
      {Dᴰ : Categoryᴰ D ℓᴰ ℓᴰ'} {F : Functor C D}
    → CATᴰ.1Cellᴰ Cᴰ Dᴰ F ≡ Functorᴰ F Cᴰ Dᴰ
  _ = refl

  _ : {C D : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
      {Dᴰ : Categoryᴰ D ℓᴰ ℓᴰ'} {F G : Functor C D}
      {Fᴰ : Functorᴰ F Cᴰ Dᴰ} {Gᴰ : Functorᴰ G Cᴰ Dᴰ} {α : NatTrans F G}
    → CATᴰ.2Cellᴰ Fᴰ Gᴰ α ≡ NatTransᴰ α Fᴰ Gᴰ
  _ = refl
