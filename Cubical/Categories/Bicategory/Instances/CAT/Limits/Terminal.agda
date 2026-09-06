{-# OPTIONS --lossy-unification #-}
{- CAT has a terminal 0-cell: the unit category. -}
module Cubical.Categories.Bicategory.Instances.CAT.Limits.Terminal where


open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Terminal.More
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Equivalence.Base

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Hom
open import Cubical.Categories.Bicategory.Universal.Base
open import Cubical.Categories.Bicategory.Limits.Terminal
open import Cubical.Categories.Bicategory.Instances.CAT.Limits.Inserter
open import Cubical.Categories.Bicategory.Instances.CAT.Limits.Equifier

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
