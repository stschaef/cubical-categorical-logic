{-# OPTIONS --lossy-unification #-}
{- The bicategory of categories with a terminal object -}
module Cubical.Categories.Bicategory.Instances.CAT.Structured.Terminal where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Displayed
open import Cubical.Categories.Bicategory.Displayed.Constructions.StructureOver
open import Cubical.Categories.Bicategory.Displayed.Constructions.Total
open import Cubical.Categories.Bicategory.Instances.CAT

private
  variable
    ℓ ℓ' : Level

open UniversalElement

-- Closure of terminal-object preservation under identity and
-- composition of functors.
module _ {C : Category ℓ ℓ'} where

  idPreservesTerminal' : (term : Terminal' C)
    → preservesTerminal' (Id {C = C}) term
  idPreservesTerminal' term = term .universal

module _ {C D E : Category ℓ ℓ'} where

  compPreservesTerminal' : {F : Functor C D} {G : Functor D E}
    {termC : Terminal' C} {termD : Terminal' D}
    → preservesTerminal' F termC
    → preservesTerminal' G termD
    → preservesTerminal' (G ∘F F) termC
  compPreservesTerminal' {F = F} {G} {termC} {termD} Fp Gp =
    preservesUniversalElement→PreservesUniversalElements
      (invPshIso (reindPsh-Unit G) .PshIso.trans)
      termD Gp
      (becomesUniversal→UniversalElement
        (invPshIso (reindPsh-Unit F) .PshIso.trans)
        Fp)

module _ {ℓ ℓ' : Level} where
  open StructureOverᴮ

  private
    -- standalone so the result level is pinned explicitly
    preservesTerminal'-cell : {C D : Category ℓ ℓ'}
      (F : Functor C D) → Terminal' C → Terminal' D
      → Type (ℓ-max ℓ ℓ')
    preservesTerminal'-cell F termC termD = preservesTerminal' F termC

  TerminalStructure : StructureOverᴮ (CAT {ℓ} {ℓ'})
    (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  TerminalStructure .ob[_] C = Terminal' C
  TerminalStructure .1Cellᴰ[_][_,_] = preservesTerminal'-cell
  TerminalStructure .id₁ᴰ {xᴰ = term} = idPreservesTerminal' term
  TerminalStructure ._⋆₁ᴰ_ {f = F} {g = G} {xᴰ = termC} {yᴰ = termD} Fp Gp =
    compPreservesTerminal' {F = F} {G = G} {termC = termC} {termD = termD}
      Fp Gp

  -- The displayed bicategory of terminal-object structure over
  -- CAT, and the bicategory of categories-with-terminal-object.
  TerminalCATᴰ : Bicategoryᴰ (CAT {ℓ} {ℓ'}) _ _ _
  TerminalCATᴰ = StructureOverᴮ→Bicategoryᴰ TerminalStructure

  TerminalCAT : Bicategory _ _ _
  TerminalCAT = ∫ᴮ TerminalCATᴰ
