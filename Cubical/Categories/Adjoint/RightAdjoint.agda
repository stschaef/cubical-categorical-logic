{- A right adjoint to `F` is a universal element of `X ↦ Hom(F X , B)`
   at each `B`, i.e. a representation of that presheaf. -}
module Cubical.Categories.Adjoint.RightAdjoint where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Representable

private
  variable
    ℓ ℓ' : Level

open Category

module _ {C : Category ℓ ℓ'} (F : Functor C C) where
  private module C = Category C

  RPsh : C.ob → Presheaf C ℓ'
  RPsh B = reindPsh F (C [-, B ])

  HasRightAdjoint : Type (ℓ-max ℓ ℓ')
  HasRightAdjoint = ∀ B → UniversalElement C (RPsh B)
