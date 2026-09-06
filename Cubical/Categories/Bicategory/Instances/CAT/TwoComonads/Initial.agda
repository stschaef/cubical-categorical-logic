{-# OPTIONS --lossy-unification #-}
{-
  The initial 2-comonad on CAT: `T C` is the empty category.  An
  initial 0-cell of CAT is a terminal 0-cell of `CAT ^opᴮ`, and
  `TwoComonad K = TwoMonad (K ^opᴮ)`, so this is the constant 2-monad
  of `TwoMonad.Constant` at that vertex.  The terminal 2-monad
  itself does *not* dualise: a counit would need `𝟙 → X`.
-}
module Cubical.Categories.Bicategory.Instances.CAT.TwoComonads.Initial where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Equivalence.Base

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Constructions.Op
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Universal.Base
open import Cubical.Categories.Bicategory.Limits.Terminal
open import Cubical.Categories.Bicategory.TwoMonad.Constant
open import Cubical.Categories.Bicategory.TwoMonad.Base
open import Cubical.Categories.Bicategory.TwoComonad

open Category
open Functor
open NatTrans
open NatIso
open isIso

module _ {ℓ ℓ' : Level} where
  private
    CATᵒᵖ : Bicategory _ _ _
    CATᵒᵖ = (CAT {ℓ} {ℓ'}) ^opᴮ

  𝟘 : Category ℓ ℓ'
  𝟘 .ob = ⊥*
  𝟘 .Hom[_,_] _ _ = ⊥*
  𝟘 .id {()}
  𝟘 ._⋆_ ()
  𝟘 .⋆IdL ()
  𝟘 .⋆IdR ()
  𝟘 .⋆Assoc ()
  𝟘 .isSetHom = isProp→isSet isProp⊥*

  empt : {X : Category ℓ ℓ'} → Functor 𝟘 X
  empt .F-ob ()
  empt .F-hom {()}
  empt .F-id {()}
  empt .F-seq {()}

  private
    triv : {X : Category ℓ ℓ'} {P Q : Functor 𝟘 X} → NatTrans P Q
    triv .N-ob ()
    triv .N-hom {()}

    isPropTriv : {X : Category ℓ ℓ'} {P Q : Functor 𝟘 X}
      → isProp (NatTrans P Q)
    isPropTriv _ _ = makeNatTransPath (funExt λ ())

  open PrestackNotation (TerminalPrestack CATᵒᵖ)

  private
    emptInv : (X : Category ℓ ℓ') → Functor P⟨ X ⟩ (FUNCTOR 𝟘 X)
    emptInv X .F-ob _ = empt
    emptInv X .F-hom _ = idTrans empt
    emptInv X .F-id = refl
    emptInv X .F-seq _ _ = isPropTriv _ _

    εIso𝟘 : (X : Category ℓ ℓ')
      → NatIso (⟨ tt* ⟩ X ∘F emptInv X) 𝟙⟨ P⟨ X ⟩ ⟩
    εIso𝟘 X .trans .N-ob _ = tt*
    εIso𝟘 X .trans .N-hom _ = refl
    εIso𝟘 X .nIso _ .inv = tt*
    εIso𝟘 X .nIso _ .sec = refl
    εIso𝟘 X .nIso _ .ret = refl

    ηIso𝟘 : (X : Category ℓ ℓ')
      → NatIso 𝟙⟨ FUNCTOR 𝟘 X ⟩ (emptInv X ∘F ⟨ tt* ⟩ X)
    ηIso𝟘 X .trans .N-ob _ = triv
    ηIso𝟘 X .trans .N-hom _ = isPropTriv _ _
    ηIso𝟘 X .nIso _ .inv = triv
    ηIso𝟘 X .nIso _ .sec = isPropTriv _ _
    ηIso𝟘 X .nIso _ .ret = isPropTriv _ _

  -- an initial 0-cell of CAT is a terminal 0-cell of CAT ^opᴮ
  initialCAT : Terminalᴮ CATᵒᵖ
  initialCAT .BiuniversalElement.vertex = 𝟘
  initialCAT .BiuniversalElement.element = tt*
  initialCAT .BiuniversalElement.universal X .WeakInverse.invFunc =
    emptInv X
  initialCAT .BiuniversalElement.universal X .WeakInverse.η = ηIso𝟘 X
  initialCAT .BiuniversalElement.universal X .WeakInverse.ε = εIso𝟘 X

  open ConstantTwoMonad initialCAT public
    using () renaming (ConstLaxᴮ to InitialLax; ConstPsᴮ to InitialPs)

  InitialTwoComonad : TwoComonad (CAT {ℓ} {ℓ'})
  InitialTwoComonad = constTwoMonad initialCAT

  εIsEmpt : (X : Category ℓ ℓ')
    → TwoComonadNotation.ε InitialTwoComonad X ≡ empt {X}
  εIsEmpt _ = refl

  δIsId : (X : Category ℓ ℓ')
    → TwoComonadNotation.δ InitialTwoComonad X ≡ Id {C = 𝟘}
  δIsId _ = refl
