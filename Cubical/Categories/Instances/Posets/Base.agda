{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Posets.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Relation.Binary.Preorder
open import Cubical.Relation.Binary.Poset
open import Cubical.Categories.Constructions.FullSubcategory

open import Cubical.Categories.Instances.Preorders.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Posets.MonotoneAdjoint


open import Cubical.Categories.Constructions.Subcategory

private
  variable
    ℓ ℓ' : Level

open Category
open PreorderStr

-- Category of Posets
POSET : (ℓ ℓ' : Level) → Category _ _
POSET ℓ ℓ' = FullSubcategory
  (PREORDER ℓ ℓ')
  λ p → IsPoset (p .snd ._≤_)


-- Displayed Poset for picking out Posets
-- and monotone functions with adjoints
AdjDisplay : DisplayedPoset (PREORDER ℓ ℓ') {ℓ-max ℓ ℓ'}
AdjDisplay = record
  { D-ob = λ p → IsPoset (p .snd ._≤_)
  ; D-Hom_[_,_] = λ f x y → HasBothAdj f
  ; isPropHomf = λ {a} {b} {f} → (isPropHasBothAdj f)
  ; D-id = IdHasBothAdj
  ; _D-⋆_ = CompHasBothAdj
  }

-- Category of Posets w/ Adjoints
POSETADJ : (ℓ ℓ' : Level) → Category _ _
POSETADJ ℓ ℓ' = Grothendieck
  (PREORDER ℓ ℓ')
  (DisplayedPoset→Cat (PREORDER ℓ ℓ') AdjDisplay)
