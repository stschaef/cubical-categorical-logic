{-# OPTIONS --lossy-unification #-}
{- The bicategory of cartesian categories -}
module Cubical.Categories.Bicategory.Instances.CAT.Structured.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Constructions hiding (π₁; π₂)
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Displayed
open import Cubical.Categories.Bicategory.Displayed.Constructions.StructureOver
open import Cubical.Categories.Bicategory.Displayed.Constructions.Total
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Instances.CAT.Structured.Terminal

private
  variable
    ℓ ℓ' : Level

open UniversalElement

-- Cartesian structure on a category and its preservation by a
-- (strict) functor.
module _ (C : Category ℓ ℓ') where
  CartesianStr : Type (ℓ-max ℓ ℓ')
  CartesianStr = Terminal' C × BinProducts C

module _ {C D : Category ℓ ℓ'} (F : Functor C D)
  (strC : CartesianStr C) (strD : CartesianStr D) where
  preservesCartesianStr : Type (ℓ-max ℓ ℓ')
  preservesCartesianStr =
    preservesTerminal' F (strC .fst)
    × preservesProvidedBinProducts F (strC .snd)

-- Closure under identity.
module _ {C : Category ℓ ℓ'} where

  idPreservesBinProducts : (bp : BinProducts C)
    → preservesProvidedBinProducts (Id {C = C}) bp
  idPreservesBinProducts bp c c' = bp (c , c') .universal

-- Closure under composition.
module _ {C D E : Category ℓ ℓ'} where

  compPreservesBinProducts : {F : Functor C D} {G : Functor D E}
    {bpC : BinProducts C} {bpD : BinProducts D}
    → preservesProvidedBinProducts F bpC
    → preservesProvidedBinProducts G bpD
    → preservesProvidedBinProducts (G ∘F F) bpC
  compPreservesBinProducts {F = F} {G} {bpC} {bpD} Fp Gp c c' =
    preservesUniversalElement→PreservesUniversalElements
      (preservesBinProdCones G
        (F .Functor.F-ob c) (F .Functor.F-ob c'))
      (bpD _) (Gp _ _)
      (becomesUniversal→UniversalElement
        (preservesBinProdCones F c c')
        (Fp c c'))

module _ {ℓ ℓ' : Level} where
  open StructureOverᴮ

  private
    preservesCartesianStr-cell : {C D : Category ℓ ℓ'}
      (F : Functor C D) → CartesianStr C → CartesianStr D
      → Type (ℓ-max ℓ ℓ')
    preservesCartesianStr-cell = preservesCartesianStr

  CartesianStructure : StructureOverᴮ (CAT {ℓ} {ℓ'})
    (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  CartesianStructure .ob[_] = CartesianStr
  CartesianStructure .1Cellᴰ[_][_,_] = preservesCartesianStr-cell
  CartesianStructure .id₁ᴰ {xᴰ = term , bp} =
    idPreservesTerminal' term , idPreservesBinProducts bp
  CartesianStructure ._⋆₁ᴰ_ {f = F} {g = G}
    {xᴰ = termC , bpC} {yᴰ = termD , bpD} (Fpt , Fpb) (Gpt , Gpb) =
    compPreservesTerminal' {F = F} {G = G} {termC = termC} {termD = termD}
      Fpt Gpt
    , compPreservesBinProducts {F = F} {G = G} {bpC = bpC} {bpD = bpD}
        Fpb Gpb

  -- The displayed bicategory of cartesian structure over CAT,
  -- and the bicategory of cartesian categories.
  CartesianCATᴰ : Bicategoryᴰ (CAT {ℓ} {ℓ'}) _ _ _
  CartesianCATᴰ = StructureOverᴮ→Bicategoryᴰ CartesianStructure

  CartesianCAT : Bicategory _ _ _
  CartesianCAT = ∫ᴮ CartesianCATᴰ
