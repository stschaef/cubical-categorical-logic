{-# OPTIONS --lossy-unification #-}
{-
  The initial 2-comonad on CAT: `T C` is the empty category.  This is
  the honest dual of `TerminalTwoMonad`; the terminal 2-monad itself
  does *not* dualise, since a counit would need `𝟙 → X`.  Every 2-cell
  in sight is a natural transformation out of the empty category, so
  all the data is the empty one and all the laws are `isPropEmpt`.
-}
module Cubical.Categories.Bicategory.Instances.CAT.TwoComonads.Initial where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as ⊥

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.Functors

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Constructions.Op
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Functor.Identity
open import Cubical.Categories.Bicategory.Functor.Composition
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.Transformation.Properties
open import Cubical.Categories.Bicategory.TwoMonad
open import Cubical.Categories.Bicategory.TwoComonad

open Category
open Functor
open isIso
open LaxFunctor
open Pseudofunctor
open LaxNatTrans
open Modification

module _ {ℓ ℓ' : Level} where
  private
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

    triv : {X : Category ℓ ℓ'} {P Q : Functor 𝟘 X} → NatTrans P Q
    triv .NatTrans.N-ob ()
    triv .NatTrans.N-hom {()}

    isPropTriv : {X : Category ℓ ℓ'} {P Q : Functor 𝟘 X}
      → isProp (NatTrans P Q)
    isPropTriv _ _ = makeNatTransPath (funExt λ ())

    TFun : {X Y : Category ℓ ℓ'} → Functor (FUNCTOR Y X) (FUNCTOR 𝟘 𝟘)
    TFun .F-ob _ = empt
    TFun .F-hom _ = triv
    TFun .F-id = isPropTriv _ _
    TFun .F-seq _ _ = isPropTriv _ _

    natTriv : {ℓw ℓw' : Level} {W : Category ℓw ℓw'}
      {P Q : Functor W (FUNCTOR 𝟘 𝟘)} → NatTrans P Q
    natTriv .NatTrans.N-ob _ = triv
    natTriv .NatTrans.N-hom _ = isPropTriv _ _

    isoTriv : {P Q : Functor 𝟘 𝟘} {σ : NatTrans P Q}
      → isIso (FUNCTOR 𝟘 𝟘) σ
    isoTriv .inv = triv
    isoTriv .sec = isPropTriv _ _
    isoTriv .ret = isPropTriv _ _

    CATᵒᵖ : Bicategory _ _ _
    CATᵒᵖ = (CAT {ℓ} {ℓ'}) ^opᴮ

  InitialLax : LaxFunctor CATᵒᵖ CATᵒᵖ
  InitialLax .F-ob _ = 𝟘
  InitialLax .F-Hom = TFun
  InitialLax .F-id = natTriv
  InitialLax .F-seq = natTriv
  InitialLax .lax-λ _ _ _ = isPropTriv _ _
  InitialLax .lax-ρ _ _ _ = isPropTriv _ _
  InitialLax .lax-α _ _ _ _ _ _ _ = isPropTriv _ _

  InitialPs : Pseudofunctor CATᵒᵖ CATᵒᵖ
  InitialPs .laxFunctor = InitialLax
  InitialPs .F-id-isIso _ = isoTriv
  InitialPs .F-seq-isIso _ = isoTriv

  InitialCounit : LaxNatTrans (LaxId CATᵒᵖ) InitialLax
  InitialCounit .N-1cell _ = empt
  InitialCounit .N-hom _ = triv
  InitialCounit .N-natural _ = isPropTriv _ _
  InitialCounit .lax-id _ = isPropTriv _ _
  InitialCounit .lax-seq _ _ = isPropTriv _ _

  InitialComult : LaxNatTrans (InitialLax ∘Lax InitialLax) InitialLax
  InitialComult .N-1cell _ = empt
  InitialComult .N-hom _ = triv
  InitialComult .N-natural _ = isPropTriv _ _
  InitialComult .lax-id _ = isPropTriv _ _
  InitialComult .lax-seq _ _ = isPropTriv _ _

  private
    trivM : {F : LaxFunctor CATᵒᵖ CATᵒᵖ}
      {α β : LaxNatTrans F InitialLax} → Modification α β
    trivM .M-ob _ = triv
    trivM .M-hom _ = isPropTriv _ _

    trivIso : {F : LaxFunctor CATᵒᵖ CATᵒᵖ}
      {α β : LaxNatTrans F InitialLax}
      → CatIso (LaxNatTransCat {F = F} {G = InitialLax}) α β
    trivIso = trivM , isI
      where
      isI : isIso _ trivM
      isI .inv = trivM
      isI .sec = makeModificationPath λ _ → isPropTriv _ _
      isI .ret = makeModificationPath λ _ → isPropTriv _ _

  InitialTwoComonad : TwoComonad (CAT {ℓ} {ℓ'})
  InitialTwoComonad .TwoMonad.T = InitialPs
  InitialTwoComonad .TwoMonad.η = InitialCounit
  InitialTwoComonad .TwoMonad.μ = InitialComult
  InitialTwoComonad .TwoMonad.unitL = trivIso
  InitialTwoComonad .TwoMonad.unitR = trivIso
  InitialTwoComonad .TwoMonad.assoc = trivIso

  εIsEmpt : (X : Category ℓ ℓ')
    → TwoComonadNotation.ε InitialTwoComonad X ≡ empt {X}
  εIsEmpt _ = refl

  δIsEmpt : (X : Category ℓ ℓ')
    → TwoComonadNotation.δ InitialTwoComonad X ≡ empt {𝟘}
  δIsEmpt _ = refl
