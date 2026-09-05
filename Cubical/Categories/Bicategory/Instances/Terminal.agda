{- The terminal bicategory: one 0-cell, one 1-cell, one 2-cell. -}
module Cubical.Categories.Bicategory.Instances.Terminal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Terminal.More

open import Cubical.Categories.Bicategory.Base

open Category
open Functor
open NatTrans
open NatIso
open isIso

-- `UnitCategory` has `Hom[_,_] = Unit*`, so every unit and
-- associativity equation below is `refl`.
module _ (ℓ ℓ' ℓ'' : Level) where

  TerminalBicategory : Bicategory ℓ ℓ' ℓ''
  TerminalBicategory .Bicategory.ob = Unit*
  TerminalBicategory .Bicategory.Hom[_,_] _ _ = UnitCategory ℓ' ℓ''
  TerminalBicategory .Bicategory.id .F-ob _ = tt*
  TerminalBicategory .Bicategory.id .F-hom _ = tt*
  TerminalBicategory .Bicategory.id .F-id = refl
  TerminalBicategory .Bicategory.id .F-seq _ _ = refl
  TerminalBicategory .Bicategory.seq _ _ _ .F-ob _ = tt*
  TerminalBicategory .Bicategory.seq _ _ _ .F-hom _ = tt*
  TerminalBicategory .Bicategory.seq _ _ _ .F-id = refl
  TerminalBicategory .Bicategory.seq _ _ _ .F-seq _ _ = refl
  TerminalBicategory .Bicategory.λU _ _ .trans .N-ob _ = tt*
  TerminalBicategory .Bicategory.λU _ _ .trans .N-hom _ = refl
  TerminalBicategory .Bicategory.λU _ _ .nIso _ .inv = tt*
  TerminalBicategory .Bicategory.λU _ _ .nIso _ .sec = refl
  TerminalBicategory .Bicategory.λU _ _ .nIso _ .ret = refl
  TerminalBicategory .Bicategory.ρU _ _ .trans .N-ob _ = tt*
  TerminalBicategory .Bicategory.ρU _ _ .trans .N-hom _ = refl
  TerminalBicategory .Bicategory.ρU _ _ .nIso _ .inv = tt*
  TerminalBicategory .Bicategory.ρU _ _ .nIso _ .sec = refl
  TerminalBicategory .Bicategory.ρU _ _ .nIso _ .ret = refl
  TerminalBicategory .Bicategory.α _ _ _ _ .trans .N-ob _ = tt*
  TerminalBicategory .Bicategory.α _ _ _ _ .trans .N-hom _ = refl
  TerminalBicategory .Bicategory.α _ _ _ _ .nIso _ .inv = tt*
  TerminalBicategory .Bicategory.α _ _ _ _ .nIso _ .sec = refl
  TerminalBicategory .Bicategory.α _ _ _ _ .nIso _ .ret = refl
  TerminalBicategory .Bicategory.triangle _ _ _ _ _ = refl
  TerminalBicategory .Bicategory.pentagon _ _ _ _ _ _ _ _ _ = refl
