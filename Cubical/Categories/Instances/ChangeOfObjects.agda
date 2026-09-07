{-

  Given a category C and a function X → C .ob, make a new category
  whose objects are X and morphisms are given by C.

  This is useful for cleaning up compositional constructions that end
  up with useless data in the objects like X × 1.

-}
module Cubical.Categories.Instances.ChangeOfObjects where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PropTrunc

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.FullSubcategory

private
  variable
    ℓC ℓC' ℓD ℓD' ℓX : Level


open Category
open Functor

module _
  {X : Type ℓX}
  (C : Category ℓC ℓC')
  (F : X → (C .ob)) where

  -- This can't be defined as the FullImage of a functor out of the
  -- discrete category unless X is a hGroupoid
  ChangeOfObjects : Category ℓX ℓC'
  ChangeOfObjects .ob = X
  ChangeOfObjects .Hom[_,_] x y = C [ F x , F y ]
  ChangeOfObjects .id = C .id
  ChangeOfObjects ._⋆_ = C ._⋆_
  ChangeOfObjects .⋆IdL = C .⋆IdL
  ChangeOfObjects .⋆IdR = C .⋆IdR
  ChangeOfObjects .⋆Assoc = C .⋆Assoc
  ChangeOfObjects .isSetHom = C .isSetHom

  π : Functor ChangeOfObjects C
  π .F-ob = F
  π .F-hom = λ z → z
  π .F-id = refl
  π .F-seq _ _ = refl

  -- the following is the right corecursion principle but I didn't
  -- bother to finish it bc transport and I haven't needed it yet.
  -- If GF in this case is refl, it's easier to η expand anyway.
  -- corec : ∀ {D : Category ℓD ℓD'}
  --   → (G : Functor D C)
  --   → (Go : D .ob → X)
  --   → (G .F-ob ≡ λ d → F (Go d))
  --   → Functor D ChangeOfObjects
  -- corec G Go GF .F-ob = Go
  -- corec G Go GF .F-hom {x}{y} f =
  --   transport (λ i → C [ GF i x , GF i y ]) (G .F-hom f)
  -- corec G Go GF .F-id = {!!}
  -- corec G Go GF .F-seq = {!!}

-- Raising a category's OBJECT level, leaving its homs where they are.
-- `Lift` on the objects and `lower` as the reindexing: the homs are
-- literally C's, so every universal property of C is one of `LiftOb C`
-- after `lift`/`lower`.  This is the direction upstream's `LiftHoms`
-- does not go, and it is what lets two categories whose object levels
-- differ be compared inside a single `CAT ℓ ℓ'`.
module _ (C : Category ℓC ℓC') (ℓ : Level) where
  LiftOb : Category (ℓ-max ℓC ℓ) ℓC'
  LiftOb = ChangeOfObjects {X = Lift ℓ (C .ob)} C lower

  -- `lower`, as a functor.  An isomorphism of categories: it is the
  -- identity on homs, and `lift`/`lower` are inverse on objects.
  lowerOb : Functor LiftOb C
  lowerOb = π {X = Lift ℓ (C .ob)} C lower

  liftOb : Functor C LiftOb
  liftOb .F-ob = lift
  liftOb .F-hom f = f
  liftOb .F-id = refl
  liftOb .F-seq _ _ = refl

  lowerOb∘liftOb : lowerOb ∘F liftOb ≡ Id
  lowerOb∘liftOb = Functor≡ (λ _ → refl) (λ _ → refl)

  liftOb∘lowerOb : liftOb ∘F lowerOb ≡ Id
  liftOb∘lowerOb = Functor≡ (λ _ → refl) (λ _ → refl)
