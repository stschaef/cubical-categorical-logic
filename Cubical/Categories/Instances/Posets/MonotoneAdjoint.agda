{-# OPTIONS --safe #-}

-- defines adjoint for monotone functions and morphisms in the Poset Category
-- where each morphism has left and right adjoints

module Cubical.Categories.Instances.Posets.MonotoneAdjoint where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Binary.Poset
open import Cubical.Relation.Binary.Preorder
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.HITs.PropositionalTruncation.Properties

open import Cubical.Categories.Instances.Preorders.Monotone


private
  variable
    ℓ ℓ' : Level


module _ {ℓ ℓ' : Level} where

  -- the Galois Connection between Posets
  -- adjoints for monotone functions
  record _⊣_ {X Y : Preorder ℓ ℓ'}
             (L : MonFun X Y) (R : MonFun Y X) : Type (ℓ-max ℓ ℓ') where
    field
      adjIff : ∀ {x y} → Iso
        ((PreorderStr._≤_ (Y .snd)) (MonFun.f L x) y)
        ((PreorderStr._≤_ (X .snd)) x (MonFun.f R y))

  -- monotone functions that have left and right adjoint
  HasLeftAdj : {X Y : Preorder ℓ ℓ'} → (f : MonFun X Y) → Type ((ℓ-max ℓ ℓ'))
  HasLeftAdj {X} {Y} f = ∃[ L ∈ MonFun Y X ] (L ⊣ f)

  isPropHasLeftAdj : {X Y : Preorder ℓ ℓ'} → (f : MonFun X Y)
    → isProp (HasLeftAdj f)
  isPropHasLeftAdj f = isPropPropTrunc

  HasRightAdj : {X Y : Preorder ℓ ℓ'} → (f : MonFun X Y) → Type ((ℓ-max ℓ ℓ'))
  HasRightAdj {X} {Y} f = ∃[ R ∈ MonFun Y X ] (f ⊣ R)


  isPropHasRightAdj : {X Y : Preorder ℓ ℓ'} → (f : MonFun X Y)
    → isProp (HasRightAdj f)
  isPropHasRightAdj f = isPropPropTrunc

  record HasBothAdj {X Y : Preorder ℓ ℓ'} (f : MonFun X Y) : Type ((ℓ-max ℓ ℓ')) where
    field
      left-adj : HasLeftAdj f
      right-adj : HasRightAdj f

  open HasBothAdj
  open _⊣_

  isPropHasBothAdj : {X Y : Preorder ℓ ℓ'} → (f : MonFun X Y)
    → isProp (HasBothAdj f)
  isPropHasBothAdj f = λ adj1 adj2 →
    λ i → record {
      left-adj = isPropHasLeftAdj f (adj1 .left-adj) (adj2 .left-adj) i ;
      right-adj = isPropHasRightAdj f (adj1 .right-adj) (adj2 .right-adj) i }

  MonId⊣MonId : {X : Preorder ℓ ℓ'} → MonId {X = X} ⊣ MonId {X = X}
  MonId⊣MonId {X} =
    record { adjIff = iso (λ h → h) (λ h → h) ( λ _ → refl)  (λ _ → refl) }


  IdHasBothAdj : {X : Preorder ℓ ℓ'} → HasBothAdj {X} {X} MonId
  IdHasBothAdj {X} = record {
    left-adj = ∣ MonId , MonId⊣MonId ∣₁ ;
    right-adj = ∣ MonId , MonId⊣MonId ∣₁ }

  CompHasBothAdj : {X Y Z : Preorder ℓ ℓ'} →
    {f : MonFun X Y} → {g : MonFun Y Z } →
    HasBothAdj f → HasBothAdj g → HasBothAdj (MonComp f g)
  CompHasBothAdj f-adj g-adj = record {
    left-adj = rec2 isPropPropTrunc
      (λ (l1 , l1⊣f) (l2 , l2⊣g) →  ∣ MonComp l2 l1 ,
        record { adjIff = compIso (l1⊣f .adjIff) (l2⊣g .adjIff) } ∣₁
      )
      (f-adj .left-adj) (g-adj .left-adj) ;
    right-adj = rec2 isPropPropTrunc
      (λ (r1 , f⊣r1) (r2 , g⊣r2) →  ∣ MonComp r2 r1 ,
        record { adjIff = compIso (g⊣r2 .adjIff) (f⊣r1 .adjIff) } ∣₁
      )
      (f-adj .right-adj) (g-adj .right-adj) }

