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

-- Category of Posets w/ Adjoints

-- Displayed Category for picking out Posets
-- and monotone functions with adjoints
AdjDisplay : DisplayedCategory (PREORDER ℓ ℓ') {{!!}}
AdjDisplay = record
  { D-ob = λ p → IsPoset (p .snd ._≤_)
  ; D-Hom_[_,_] = λ f x y → HasBothAdj f
  ; isSetHomf = {!!}
  ; D-id = {!IdHasBothAdj!}
  ; _D-⋆_ = {!!}
  ; D-⋆IdL = {!!}
  ; D-⋆IdR = {!!}
  ; D-⋆Assoc = {!!}
  }

POSETADJ : (ℓ ℓ' : Level) → Category _ _
POSETADJ ℓ ℓ' = Grothendieck
  (PREORDER ℓ ℓ')
  AdjDisplay
{-
POSETADJ ℓ ℓ' = record
  { ob = Poset ℓ ℓ'
  ; Hom[_,_] = λ X Y → MonFunAdj X Y
  ; id = MonIdAdj
  ; _⋆_ = MonCompAdj
  ; ⋆IdL = λ {X} {Y} f → eqMonAdj _ _
         (eqMon _ _ refl) (eqMon _ _ refl) (eqMon _ _ refl)
  ; ⋆IdR = λ {X} {Y} f → eqMonAdj _ _
         (eqMon _ _ refl) (eqMon _ _ refl) (eqMon _ _ refl)
  ; ⋆Assoc = λ {X} {Y} {Z} {W} f g h → eqMonAdj _ _
           (eqMon _ _ refl) (eqMon _ _ refl) (eqMon _ _ refl)
  ; isSetHom = MonFunAdjIsSet
  }
-}
