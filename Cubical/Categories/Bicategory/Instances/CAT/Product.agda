{-# OPTIONS --lossy-unification #-}
{- CAT has binary products: the product category. -}
module Cubical.Categories.Bicategory.Instances.CAT.Product where


open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.BinProduct.More
open import Cubical.Categories.Equivalence.Base

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Hom
open import Cubical.Categories.Bicategory.Prestack.BinProduct
open import Cubical.Categories.Bicategory.Universal.Base
open import Cubical.Categories.Bicategory.Limits.Product
open import Cubical.Categories.Bicategory.Instances.CAT.Inserter
open import Cubical.Categories.Bicategory.Instances.CAT.Equifier

private
  variable
    ℓ ℓ' : Level

open Category
open Functor
open NatTrans
open NatIso
open isIso
module _ {ℓ ℓ' : Level} (a b : Category ℓ ℓ') where
  private
    module Ca = Category a
    module Cb = Category b
    module Cab = Category (a ×C b)

  open PrestackNotation (BinProductPrestack (CAT {ℓ} {ℓ'}) a b)

  private
    prodElem : p[ a ×C b ]
    prodElem = Fst a b , Snd a b

  module _ {X : Category ℓ ℓ'} where
    private
      pairF : Functor P⟨ X ⟩ (FUNCTOR X (a ×C b))
      pairF = ,F-functor {C = X} {C' = a} {D' = b}

      ε₁ : (P : Functor X a) (Q : Functor X b)
        → NatTrans (Fst a b ∘F (P ,F Q)) P
      ε₁ P Q .N-ob x = Ca.id
      ε₁ P Q .N-hom f = Ca.⋆IdR _ ∙ sym (Ca.⋆IdL _)

      ε₁⁻ : (P : Functor X a) (Q : Functor X b)
        → NatTrans P (Fst a b ∘F (P ,F Q))
      ε₁⁻ P Q .N-ob x = Ca.id
      ε₁⁻ P Q .N-hom f = Ca.⋆IdR _ ∙ sym (Ca.⋆IdL _)

      ε₂ : (P : Functor X a) (Q : Functor X b)
        → NatTrans (Snd a b ∘F (P ,F Q)) Q
      ε₂ P Q .N-ob x = Cb.id
      ε₂ P Q .N-hom f = Cb.⋆IdR _ ∙ sym (Cb.⋆IdL _)

      ε₂⁻ : (P : Functor X a) (Q : Functor X b)
        → NatTrans Q (Snd a b ∘F (P ,F Q))
      ε₂⁻ P Q .N-ob x = Cb.id
      ε₂⁻ P Q .N-hom f = Cb.⋆IdR _ ∙ sym (Cb.⋆IdL _)

    εIso× : NatIso (⟨ prodElem ⟩ X ∘F pairF) 𝟙⟨ P⟨ X ⟩ ⟩
    εIso× .trans .N-ob (P , Q) = ε₁ P Q , ε₂ P Q
    εIso× .trans .N-hom (σ , τ) = ≡-×
      (makeNatTransPath (funExt λ x →
        cong (Ca._⋆ Ca.id) (Ca.⋆IdR _) ∙ Ca.⋆IdR _ ∙ sym (Ca.⋆IdL _)))
      (makeNatTransPath (funExt λ x →
        cong (Cb._⋆ Cb.id) (Cb.⋆IdR _) ∙ Cb.⋆IdR _ ∙ sym (Cb.⋆IdL _)))
    εIso× .nIso (P , Q) .inv = ε₁⁻ P Q , ε₂⁻ P Q
    εIso× .nIso (P , Q) .sec = ≡-×
      (makeNatTransPath (funExt λ x → Ca.⋆IdL _))
      (makeNatTransPath (funExt λ x → Cb.⋆IdL _))
    εIso× .nIso (P , Q) .ret = ≡-×
      (makeNatTransPath (funExt λ x → Ca.⋆IdL _))
      (makeNatTransPath (funExt λ x → Cb.⋆IdL _))

    private
      η× : (H : Functor X (a ×C b))
        → NatTrans H ((Fst a b ∘F H) ,F (Snd a b ∘F H))
      η× H .N-ob x = Cab.id
      η× H .N-hom f = Cab.⋆IdR _ ∙ sym (Cab.⋆IdL _)

      η×⁻ : (H : Functor X (a ×C b))
        → NatTrans ((Fst a b ∘F H) ,F (Snd a b ∘F H)) H
      η×⁻ H .N-ob x = Cab.id
      η×⁻ H .N-hom f = Cab.⋆IdR _ ∙ sym (Cab.⋆IdL _)

    ηIso× : NatIso 𝟙⟨ FUNCTOR X (a ×C b) ⟩ (pairF ∘F ⟨ prodElem ⟩ X)
    ηIso× .trans .N-ob = η×
    ηIso× .trans .N-hom σ = makeNatTransPath (funExt λ x → ≡-×
      (Ca.⋆IdR _ ∙ sym (Ca.⋆IdL _ ∙ Ca.⋆IdR _))
      (Cb.⋆IdR _ ∙ sym (Cb.⋆IdL _ ∙ Cb.⋆IdR _)))
    ηIso× .nIso H .inv = η×⁻ H
    ηIso× .nIso H .sec = makeNatTransPath (funExt λ x → Cab.⋆IdL _)
    ηIso× .nIso H .ret = makeNatTransPath (funExt λ x → Cab.⋆IdL _)

  binProductCAT : BinProductᴮ (CAT {ℓ} {ℓ'}) a b
  binProductCAT .BiuniversalElement.vertex = a ×C b
  binProductCAT .BiuniversalElement.element = prodElem
  binProductCAT .BiuniversalElement.universal X .WeakInverse.invFunc =
    ,F-functor {C = X} {C' = a} {D' = b}
  binProductCAT .BiuniversalElement.universal X .WeakInverse.η = ηIso×
  binProductCAT .BiuniversalElement.universal X .WeakInverse.ε = εIso×
