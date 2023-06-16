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
AdjDisplay : DisplayedCategory (PREORDER ℓ ℓ') {ℓ-max ℓ ℓ'}
AdjDisplay = record
  { D-ob = λ p → IsPoset (p .snd ._≤_)
  ; D-Hom_[_,_] = λ f x y → HasBothAdj f
  ; isSetHomf = λ {a} {b} {f} → isProp→isSet (isPropHasBothAdj f)
  ; D-id = IdHasBothAdj
  ; _D-⋆_ = CompHasBothAdj
  ; D-⋆IdL = λ {a} {b} {f} k →
    isProp→PathP (λ i → isPropHasBothAdj (((PREORDER _ _ .⋆IdL f) i))) _ _
  ; D-⋆IdR = λ {a} {b} {f} k →
    isProp→PathP (λ i → isPropHasBothAdj (((PREORDER _ _ .⋆IdR f) i))) _ _
  ; D-⋆Assoc = λ {a} {b} {c} {d} {f} {g} {h} k l m →
    isProp→PathP (λ i → isPropHasBothAdj (((PREORDER _ _ .⋆Assoc f g h) i))) _ _}

POSETADJ : (ℓ ℓ' : Level) → Category _ _
POSETADJ ℓ ℓ' = Grothendieck
  (PREORDER ℓ ℓ')
  AdjDisplay
