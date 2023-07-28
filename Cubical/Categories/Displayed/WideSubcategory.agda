{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.WideSubcategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Preorder

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

record WideSubcategory (C : Category ℓC ℓC') ℓCᴰ' :
  Type (ℓ-suc (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ')) where
  open Category C
  field
    Good : {x y : ob} → Hom[ x , y ] → Type ℓCᴰ'
    idᴰ : ∀ {x} → Good (id {x})
    _⋆ᴰ_ : ∀ {x y z} {f : Hom[ x , y ]} {g : Hom[ y , z ]}
      → Good f → Good g → Good (f ⋆ g)
    isPropHomᴰ : ∀ {x y} {f : Hom[ x , y ]} → (isProp (Good f ))

open WideSubcategory
open Preorderᴰ

WideSubcategory→Preorderᴰ : ∀ {C : Category ℓC ℓC'} → WideSubcategory C ℓCᴰ' → Preorderᴰ C ℓ-zero ℓCᴰ'
ob[ WideSubcategory→Preorderᴰ {C = C} Cᴰ ] x = Unit
Hom[ WideSubcategory→Preorderᴰ {C = C} Cᴰ ][ f , _ ] _ = Cᴰ .Good f
WideSubcategory→Preorderᴰ {C = C} Cᴰ .idᴰ = idᴰ Cᴰ
WideSubcategory→Preorderᴰ {C = C} Cᴰ ._⋆ᴰ_ = _⋆ᴰ_ Cᴰ
WideSubcategory→Preorderᴰ {C = C} Cᴰ .isPropHomᴰ = isPropHomᴰ Cᴰ
