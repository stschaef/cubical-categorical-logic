{-# OPTIONS --lossy-unification #-}
{-
  A bicategory with a terminal 0-cell `t` carries a constant 2-monad:
  `T x = t`, with `η` the unique 1-cell into `t` and `μ` the identity.
  Terminality makes `Hom[ x , t ]` locally contractible, so every
  2-cell in sight is `!₂` and every law is `isProp2`.
-}
module Cubical.Categories.Bicategory.TwoMonad.Constant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Isomorphism

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Limits.Terminal
open import Cubical.Categories.Bicategory.Universal.Base
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Functor.Identity
open import Cubical.Categories.Bicategory.Functor.Composition
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.Transformation.Properties
open import Cubical.Categories.Bicategory.TwoMonad.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

open Category
open isIso
open LaxFunctor
open Pseudofunctor
open LaxNatTrans
open Modification

module ConstantTwoMonad {K : Bicategory ℓ ℓ' ℓ''} (T : Terminalᴮ K) where
  private
    module K = Bicategory K
  open TerminalᴮNotation T using (vertex; ff; !ᴮ)

  -- Terminality is fully faithfulness of `Hom[ x , t ] → 𝟙`.
  isContr2 : {x : K.0Cell} (h k : K.1Cell x vertex) → isContr (K.2Cell h k)
  isContr2 {x} h k =
    isOfHLevelRespectEquiv 0 (invEquiv (_ , ff x h k)) isContrUnit*

  !₂ : {x : K.0Cell} {h k : K.1Cell x vertex} → K.2Cell h k
  !₂ = isContr2 _ _ .fst

  isProp2 : {x : K.0Cell} {h k : K.1Cell x vertex} → isProp (K.2Cell h k)
  isProp2 = isContr→isProp (isContr2 _ _)

  private
    -- factored out: nesting these under `.F-id`/`.F-seq` beside a
    -- sibling clause makes Agda read `ConstLaxᴮ` as recursive.
    natTriv : {ℓw ℓw' : Level} {W : Category ℓw ℓw'} {x : K.0Cell}
      {P Q : Functor W K.Hom[ x , vertex ]} → NatTrans P Q
    natTriv .NatTrans.N-ob _ = !₂
    natTriv .NatTrans.N-hom _ = isProp2 _ _

    isoTriv : {x : K.0Cell} {h k : K.1Cell x vertex} {α : K.2Cell h k}
      → isIso K.Hom[ x , vertex ] α
    isoTriv .inv = !₂
    isoTriv .sec = isProp2 _ _
    isoTriv .ret = isProp2 _ _

  ConstLaxᴮ : LaxFunctor K K
  ConstLaxᴮ .F-ob _ = vertex
  ConstLaxᴮ .F-Hom = Constant _ _ K.id₁
  ConstLaxᴮ .F-id = natTriv
  ConstLaxᴮ .F-seq = natTriv
  ConstLaxᴮ .lax-λ _ _ _ = isProp2 _ _
  ConstLaxᴮ .lax-ρ _ _ _ = isProp2 _ _
  ConstLaxᴮ .lax-α _ _ _ _ _ _ _ = isProp2 _ _

  ConstPsᴮ : Pseudofunctor K K
  ConstPsᴮ .laxFunctor = ConstLaxᴮ
  ConstPsᴮ .F-id-isIso _ = isoTriv
  ConstPsᴮ .F-seq-isIso _ = isoTriv

  ConstUnit : LaxNatTrans (LaxId K) ConstLaxᴮ
  ConstUnit .N-1cell = !ᴮ
  ConstUnit .N-hom _ = !₂
  ConstUnit .N-natural _ = isProp2 _ _
  ConstUnit .lax-id _ = isProp2 _ _
  ConstUnit .lax-seq _ _ = isProp2 _ _

  ConstMult : LaxNatTrans (ConstLaxᴮ ∘Lax ConstLaxᴮ) ConstLaxᴮ
  ConstMult .N-1cell _ = K.id₁
  ConstMult .N-hom _ = !₂
  ConstMult .N-natural _ = isProp2 _ _
  ConstMult .lax-id _ = isProp2 _ _
  ConstMult .lax-seq _ _ = isProp2 _ _

  private
    trivM : {F : LaxFunctor K K} {α β : LaxNatTrans F ConstLaxᴮ}
      → Modification α β
    trivM .M-ob _ = !₂
    trivM .M-hom _ = isProp2 _ _

    trivIso : {F : LaxFunctor K K} {α β : LaxNatTrans F ConstLaxᴮ}
      → CatIso (LaxNatTransCat {F = F} {G = ConstLaxᴮ}) α β
    trivIso = trivM , isI
      where
      isI : isIso _ trivM
      isI .inv = trivM
      isI .sec = makeModificationPath λ _ → isProp2 _ _
      isI .ret = makeModificationPath λ _ → isProp2 _ _

  constTwoMonad : TwoMonad K
  constTwoMonad .TwoMonad.T = ConstPsᴮ
  constTwoMonad .TwoMonad.η = ConstUnit
  constTwoMonad .TwoMonad.μ = ConstMult
  constTwoMonad .TwoMonad.unitL = trivIso
  constTwoMonad .TwoMonad.unitR = trivIso
  constTwoMonad .TwoMonad.assoc = trivIso

open ConstantTwoMonad public using (constTwoMonad)
