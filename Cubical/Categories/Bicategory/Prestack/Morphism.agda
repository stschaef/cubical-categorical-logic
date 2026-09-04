{-# OPTIONS --lossy-unification #-}
{- Morphisms of prestacks: lax natural transformations of the
   underlying lax functors, cut down to the pseudonatural ones. -}
module Cubical.Categories.Bicategory.Prestack.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.FullSubcategory
open import Cubical.Categories.Equivalence.Base

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Constructions.Op
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.Transformation.Properties
open import Cubical.Categories.Bicategory.Prestack.Base

private
  variable
    ℓ ℓ' ℓ'' ℓp ℓp' : Level

open Pseudofunctor
open LaxNatTrans

module _ {B : Bicategory ℓ ℓ' ℓ''} where
  private
    module B = Bicategory B

  PrestackHom : (P Q : Prestack B ℓp ℓp') → Type _
  PrestackHom P Q = LaxNatTrans (P .laxFunctor) (Q .laxFunctor)

  module _ (P Q : Prestack B ℓp ℓp') where
    private
      module P = PrestackNotation P
      module Q = PrestackNotation Q

    -- Componentwise equivalence only implies invertibility of a
    -- transformation when its naturality cell is invertible.
    isPseudoNat : PrestackHom P Q → Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓp ℓp')))
    isPseudoNat α = {x y : B.0Cell} (k : B.1Cell y x)
      → isIso (FUNCTOR P.P⟨ x ⟩ Q.P⟨ y ⟩) (α .N-hom k)

    PrestackPseudoHom : Type (ℓ-max (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
                                    (ℓ-suc (ℓ-max ℓp ℓp')))
    PrestackPseudoHom = Σ[ α ∈ PrestackHom P Q ] isPseudoNat α

    -- The hom-category of prestacks: pseudonatural transformations and
    -- modifications between them.
    PrestackHomCat : Category _ _
    PrestackHomCat =
      FullSubcategory (LaxNatTransCat {F = P .laxFunctor} {G = Q .laxFunctor})
                      isPseudoNat

    isPrestackIso : PrestackHom P Q → Type (ℓ-max ℓ (ℓ-max ℓp ℓp'))
    isPrestackIso α = (x : B.0Cell) → WeakInverse (α .N-1cell x)

  record PrestackIso (P Q : Prestack B ℓp ℓp')
    : Type (ℓ-max (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) (ℓ-suc (ℓ-max ℓp ℓp'))) where
    field
      trans : PrestackPseudoHom P Q
      nIso  : isPrestackIso P Q (trans .fst)
