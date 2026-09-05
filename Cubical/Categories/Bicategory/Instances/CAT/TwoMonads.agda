{-# OPTIONS --lossy-unification #-}
{-
  The terminal 2-monad on CAT: `T C` is the unit category.  Every
  2-cell in sight is a natural transformation into a category with
  `Unit*` hom-sets, so all the data is the trivial one and all the
  laws are `isPropTriv`.
-}
module Cubical.Categories.Bicategory.Instances.CAT.TwoMonads where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Terminal.More

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Functor.Identity
open import Cubical.Categories.Bicategory.Functor.Composition
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.Transformation.Properties
open import Cubical.Categories.Bicategory.TwoMonad

private
  variable
    ℓ ℓ' : Level

open Category
open Functor
open isIso
open LaxFunctor
open Pseudofunctor
open LaxNatTrans
open Modification

module _ {ℓ ℓ' : Level} where
  private
    𝟙 : Category ℓ ℓ'
    𝟙 = UnitCategory ℓ ℓ'

    triv : {X : Category ℓ ℓ'} {P Q : Functor X 𝟙} → NatTrans P Q
    triv .NatTrans.N-ob _ = tt*
    triv .NatTrans.N-hom _ = refl

    isPropTriv : {X : Category ℓ ℓ'} {P Q : Functor X 𝟙}
      → isProp (NatTrans P Q)
    isPropTriv _ _ = makeNatTransPath (funExt λ _ → refl)

    TFun : {X Y : Category ℓ ℓ'} → Functor (FUNCTOR X Y) (FUNCTOR 𝟙 𝟙)
    TFun .F-ob _ = Id
    TFun .F-hom _ = triv
    TFun .F-id = isPropTriv _ _
    TFun .F-seq _ _ = isPropTriv _ _

    -- factored out: nesting these under `.F-id`/`.F-seq` beside a
    -- sibling clause makes Agda read `TerminalLax` as recursive.
    natTriv : {ℓw ℓw' : Level} {W : Category ℓw ℓw'}
      {P Q : Functor W (FUNCTOR 𝟙 𝟙)} → NatTrans P Q
    natTriv .NatTrans.N-ob _ = triv
    natTriv .NatTrans.N-hom _ = isPropTriv _ _

    isoTriv : {P Q : Functor 𝟙 𝟙} {σ : NatTrans P Q}
      → isIso (FUNCTOR 𝟙 𝟙) σ
    isoTriv .inv = triv
    isoTriv .sec = isPropTriv _ _
    isoTriv .ret = isPropTriv _ _

  TerminalLax : LaxFunctor (CAT {ℓ} {ℓ'}) (CAT {ℓ} {ℓ'})
  TerminalLax .F-ob _ = 𝟙
  TerminalLax .F-Hom = TFun
  TerminalLax .F-id = natTriv
  TerminalLax .F-seq = natTriv
  TerminalLax .lax-λ _ _ _ = isPropTriv _ _
  TerminalLax .lax-ρ _ _ _ = isPropTriv _ _
  TerminalLax .lax-α _ _ _ _ _ _ _ = isPropTriv _ _

  TerminalPs : Pseudofunctor (CAT {ℓ} {ℓ'}) (CAT {ℓ} {ℓ'})
  TerminalPs .laxFunctor = TerminalLax
  TerminalPs .F-id-isIso _ = isoTriv
  TerminalPs .F-seq-isIso _ = isoTriv

  private
    bang : (X : Category ℓ ℓ') → Functor X 𝟙
    bang X .F-ob _ = tt*
    bang X .F-hom _ = tt*
    bang X .F-id = refl
    bang X .F-seq _ _ = refl

  TerminalUnit : LaxNatTrans (LaxId (CAT {ℓ} {ℓ'})) TerminalLax
  TerminalUnit .N-1cell = bang
  TerminalUnit .N-hom _ = triv
  TerminalUnit .N-natural _ = isPropTriv _ _
  TerminalUnit .lax-id _ = isPropTriv _ _
  TerminalUnit .lax-seq _ _ = isPropTriv _ _

  TerminalMult : LaxNatTrans (TerminalLax ∘Lax TerminalLax) TerminalLax
  TerminalMult .N-1cell _ = Id
  TerminalMult .N-hom _ = triv
  TerminalMult .N-natural _ = isPropTriv _ _
  TerminalMult .lax-id _ = isPropTriv _ _
  TerminalMult .lax-seq _ _ = isPropTriv _ _

  private
    trivM : {F : LaxFunctor (CAT {ℓ} {ℓ'}) (CAT {ℓ} {ℓ'})}
      {α β : LaxNatTrans F TerminalLax} → Modification α β
    trivM .M-ob _ = triv
    trivM .M-hom _ = isPropTriv _ _

    trivIso : {F : LaxFunctor (CAT {ℓ} {ℓ'}) (CAT {ℓ} {ℓ'})}
      {α β : LaxNatTrans F TerminalLax}
      → CatIso (LaxNatTransCat {F = F} {G = TerminalLax}) α β
    trivIso = trivM , isI
      where
      isI : isIso _ trivM
      isI .inv = trivM
      isI .sec = makeModificationPath λ _ → isPropTriv _ _
      isI .ret = makeModificationPath λ _ → isPropTriv _ _

  TerminalTwoMonad : TwoMonad (CAT {ℓ} {ℓ'})
  TerminalTwoMonad .TwoMonad.T = TerminalPs
  TerminalTwoMonad .TwoMonad.η = TerminalUnit
  TerminalTwoMonad .TwoMonad.μ = TerminalMult
  TerminalTwoMonad .TwoMonad.unitL = trivIso
  TerminalTwoMonad .TwoMonad.unitR = trivIso
  TerminalTwoMonad .TwoMonad.assoc = trivIso
