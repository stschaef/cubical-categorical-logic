{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.NaturalTransformation.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation

open import Cubical.Reflection.RecordEquiv.More

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  open Category
  open NatTrans
  open NatTransᴰ
  open Functorᴰ

  module _ {F : Functor C D} {G : Functor C D}
    (α : NatTrans F G)
    {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
    (Fᴰ : Functorᴰ F Cᴰ Dᴰ) (Gᴰ : Functorᴰ G Cᴰ Dᴰ) where

    private
      module Cᴰ = Categoryᴰ Cᴰ
      module Dᴰ = Categoryᴰ Dᴰ

    private
      N-obᴰ-type = {x : C .ob} (xᴰ : Cᴰ.ob[ x ])
        → Dᴰ [ α .N-ob x ][ Fᴰ .F-obᴰ xᴰ , Gᴰ .F-obᴰ xᴰ ]
      N-homᴰ-type : N-obᴰ-type → _
      N-homᴰ-type Nobᴰ = ({x y : C .ob} {f : C [ x , y ]}
        {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} (fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ])
        → PathP (λ i → Dᴰ [ α .N-hom f i ][ Fᴰ .F-obᴰ xᴰ , Gᴰ .F-obᴰ yᴰ ])
            (Fᴰ .F-homᴰ fᴰ Dᴰ.⋆ᴰ Nobᴰ yᴰ) (Nobᴰ xᴰ Dᴰ.⋆ᴰ Gᴰ .F-homᴰ fᴰ))

    NatTransΣ : Type _
    NatTransΣ = Σ[ Nobᴰ ∈ N-obᴰ-type ] N-homᴰ-type Nobᴰ

    isPropIsNatᴰ : (Nobᴰ : N-obᴰ-type) → isProp (N-homᴰ-type Nobᴰ)
    isPropIsNatᴰ Nobᴰ = (isPropImplicitΠ2 (λ _ _ → isPropImplicitΠ2 (λ _ _ →
        isPropImplicitΠ λ _ → isPropΠ (λ _ →
        isOfHLevelPathP' 1 Dᴰ.isSetHomᴰ _ _))))

    NatTransIsoΣ : Iso (NatTransᴰ α Fᴰ Gᴰ) NatTransΣ
    unquoteDef NatTransIsoΣ = defineRecordIsoΣ NatTransIsoΣ (quote NatTransᴰ)

    isSetNatTransᴰ : isSet (NatTransᴰ α Fᴰ Gᴰ)
    isSetNatTransᴰ = isOfHLevelRetractFromIso 2 NatTransIsoΣ (isSetΣ
      (isSetImplicitΠ (λ x → isSetΠ (λ xᴰ → Dᴰ.isSetHomᴰ))) λ Nobᴰ →
      isProp→isSet (isPropIsNatᴰ Nobᴰ))

  module _ {F : Functor C D} {G : Functor C D}
    {α β} (p : Path (NatTrans F G) α β)
    {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
    (Fᴰ : Functorᴰ F Cᴰ Dᴰ) (Gᴰ : Functorᴰ G Cᴰ Dᴰ)
    (αᴰ : NatTransᴰ α Fᴰ Gᴰ) (βᴰ : NatTransᴰ β Fᴰ Gᴰ)
    where
    private
      module Cᴰ = Categoryᴰ Cᴰ
      module Dᴰ = Categoryᴰ Dᴰ

    transport-N-obᴰ : ∀ {x : C .ob}(xᴰ : Cᴰ.ob[ x ]) →
      transport (λ i → NatTransᴰ (p i) Fᴰ Gᴰ) αᴰ .N-obᴰ xᴰ
      ≡ transport (λ i → Dᴰ [ p i .N-ob x ][ Fᴰ .F-obᴰ xᴰ , Gᴰ .F-obᴰ xᴰ ])
                  (αᴰ .N-obᴰ xᴰ)
    transport-N-obᴰ {x = x} xᴰ = J (λ β p →
      transport (λ i → NatTransᴰ (p i) Fᴰ Gᴰ) αᴰ .N-obᴰ xᴰ
      ≡ transport (λ i → Dᴰ [ p i .N-ob x ][ Fᴰ .F-obᴰ xᴰ , Gᴰ .F-obᴰ xᴰ ])
          (αᴰ .N-obᴰ xᴰ))
      ((λ i → transportRefl αᴰ i .N-obᴰ xᴰ)
        ▷ sym (transportRefl (αᴰ .N-obᴰ xᴰ)))
      p

    NatTransᴰPathP :
        (∀ {x : C .ob}(xᴰ : Cᴰ.ob[ x ])
           → PathP (λ i → Dᴰ [ p i .N-ob x ][ Fᴰ .F-obᴰ xᴰ , Gᴰ .F-obᴰ xᴰ ])
                   (αᴰ .N-obᴰ xᴰ)
                   (βᴰ .N-obᴰ xᴰ))
      → PathP (λ i → NatTransᴰ (p i) Fᴰ Gᴰ) αᴰ βᴰ
    NatTransᴰPathP αᴰNob≡βᴰNob = toPathP (isoFunInjective
      (NatTransIsoΣ β Fᴰ Gᴰ) _ _
      (ΣPathPProp (isPropIsNatᴰ β Fᴰ Gᴰ)
      (implicitFunExt (λ {x} → funExt (λ xᴰ →
        transport-N-obᴰ xᴰ
        ∙ fromPathP (αᴰNob≡βᴰNob xᴰ)))))) 
  
  module _ {F : Functor C D}
           {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
           {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
           (Fᴰ : Functorᴰ F Cᴰ Dᴰ) where

    private
      module Dᴰ = Categoryᴰ Dᴰ

    idTransᴰ : NatTransᴰ (idTrans F) Fᴰ Fᴰ
    idTransᴰ .N-obᴰ xᴰ = Dᴰ.idᴰ
    idTransᴰ .N-homᴰ fᴰ =
      compPathP' {B = Dᴰ [_][ Fᴰ .F-obᴰ _ , Fᴰ .F-obᴰ _ ]}(Dᴰ.⋆IdRᴰ _)
      (compPathP' {B = Dᴰ [_][ Fᴰ .F-obᴰ _ , Fᴰ .F-obᴰ _ ]} (symP (Dᴰ.⋆IdLᴰ _))
      refl)

