{-# OPTIONS --lossy-unification #-}
{- CAT has a terminal 0-cell and binary products, hence all PIE limits. -}
module Cubical.Categories.Bicategory.Instances.CAT.Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.BinProduct.More
open import Cubical.Categories.Instances.Terminal.More
open import Cubical.Categories.Equivalence.Base

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Hom
open import Cubical.Categories.Bicategory.Prestack.BinProduct
open import Cubical.Categories.Bicategory.Universal.Base
open import Cubical.Categories.Bicategory.Limits.Terminal
open import Cubical.Categories.Bicategory.Limits.Product
open import Cubical.Categories.Bicategory.Limits.Equifier
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

module _ {ℓ ℓ' : Level} where
  private
    𝟙c : Category ℓ ℓ'
    𝟙c = UnitCategory ℓ ℓ'

  open PrestackNotation (TerminalPrestack (CAT {ℓ} {ℓ'}))

  private
    toUnit : (X : Category ℓ ℓ') → Functor X 𝟙c
    toUnit X .F-ob _ = tt*
    toUnit X .F-hom _ = tt*
    toUnit X .F-id = refl
    toUnit X .F-seq _ _ = refl

    unitInv : (X : Category ℓ ℓ') → Functor P⟨ X ⟩ (FUNCTOR X 𝟙c)
    unitInv X .F-ob _ = toUnit X
    unitInv X .F-hom _ = idTrans (toUnit X)
    unitInv X .F-id = refl
    unitInv X .F-seq _ _ = makeNatTransPath refl

    !NT : {X : Category ℓ ℓ'} (H : Functor X 𝟙c) → NatTrans H (toUnit X)
    !NT H .N-ob _ = tt*
    !NT H .N-hom _ = refl

    !NT⁻ : {X : Category ℓ ℓ'} (H : Functor X 𝟙c) → NatTrans (toUnit X) H
    !NT⁻ H .N-ob _ = tt*
    !NT⁻ H .N-hom _ = refl

    εIso𝟙 : (X : Category ℓ ℓ')
      → NatIso (⟨ tt* ⟩ X ∘F unitInv X) 𝟙⟨ P⟨ X ⟩ ⟩
    εIso𝟙 X .trans .N-ob _ = tt*
    εIso𝟙 X .trans .N-hom _ = refl
    εIso𝟙 X .nIso _ .inv = tt*
    εIso𝟙 X .nIso _ .sec = refl
    εIso𝟙 X .nIso _ .ret = refl

    ηIso𝟙 : (X : Category ℓ ℓ')
      → NatIso 𝟙⟨ FUNCTOR X 𝟙c ⟩ (unitInv X ∘F ⟨ tt* ⟩ X)
    ηIso𝟙 X .trans .N-ob = !NT
    ηIso𝟙 X .trans .N-hom _ = makeNatTransPath refl
    ηIso𝟙 X .nIso H .inv = !NT⁻ H
    ηIso𝟙 X .nIso H .sec = makeNatTransPath refl
    ηIso𝟙 X .nIso H .ret = makeNatTransPath refl

  terminalCAT : Terminalᴮ (CAT {ℓ} {ℓ'})
  terminalCAT .BiuniversalElement.vertex = 𝟙c
  terminalCAT .BiuniversalElement.element = tt*
  terminalCAT .BiuniversalElement.universal X .WeakInverse.invFunc =
    unitInv X
  terminalCAT .BiuniversalElement.universal X .WeakInverse.η = ηIso𝟙 X
  terminalCAT .BiuniversalElement.universal X .WeakInverse.ε = εIso𝟙 X

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

module _ {ℓ ℓ' : Level} where
  -- inserters and equifiers were already available, so CAT has PIE
  pieLimitsCAT : hasPIEᴮ (CAT {ℓ-max ℓ ℓ'} {ℓ'})
  pieLimitsCAT = pieCAT {ℓ} {ℓ'} terminalCAT binProductCAT
