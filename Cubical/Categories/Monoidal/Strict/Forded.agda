{-# OPTIONS --lossy-unification #-}
{-
  Forded strict monoidal categories.

  `StrictMonStr` states the morphism-level unit/associativity laws as
  PathPs over the object-level ones.  Here the *target objects* of the
  tensor of two morphisms are forded, so every law is an ordinary
  path, and both bracketings of a triple tensor already live in one
  hom-set (`test-*-type` below).

  Fording stops there.  `_⊗_` and `unit` are record fields, so `m ⊗
  unit` is a neutral term: no amount of fording makes it *reduce* to
  `m`, and `⊗ₕ-coh` shows the forded cells are just the transports of
  the unforded ones.  There is therefore no analogue of
  `StrictFunctor`'s `test-lUnit`; a strictly unital tensor needs a
  different *representation of objects* (Cayley), not a ford.

  Consequently the `M ×C _` 2-monad on CAT in
  `Bicategory.Instances.CAT.TwoMonads.Monoidal` is built over an
  arbitrary `MonoidalCategory`, where the three 2-monad laws are the
  unitors and associator of M and no transport arises at all.
-}
module Cubical.Categories.Monoidal.Strict.Forded where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Monoidal.Base

private
  variable
    ℓ ℓ' : Level

open Functor

record StrictMonoidalCategoryᶠ (ℓ ℓ' : Level) :
  Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  no-eta-equality
  field
    C : Category ℓ ℓ'

  open Category C public

  field
    _⊗_  : ob → ob → ob
    unit : ob

    -- forded tensor of morphisms
    ⊗ₕ : {x y z w a b : ob}
       → x ⊗ z ≡ a → y ⊗ w ≡ b
       → Hom[ x , y ] → Hom[ z , w ] → Hom[ a , b ]

    ⊗ₕId : {x z a : ob} (p : x ⊗ z ≡ a) → ⊗ₕ p p id id ≡ id

    ⊗ₕSeq : {x y z x' y' z' a b c : ob}
      (p : x ⊗ x' ≡ a) (q : y ⊗ y' ≡ b) (r : z ⊗ z' ≡ c)
      (f : Hom[ x , y ]) (g : Hom[ y , z ])
      (f' : Hom[ x' , y' ]) (g' : Hom[ y' , z' ])
      → ⊗ₕ p r (f ⋆ g) (f' ⋆ g') ≡ ⊗ₕ p q f f' ⋆ ⊗ₕ q r g g'

    ⊗IdL   : (x : ob) → unit ⊗ x ≡ x
    ⊗IdR   : (x : ob) → x ⊗ unit ≡ x
    ⊗Assoc : (x y z : ob) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)

  _⊗₂_ : {x y z w : ob} → Hom[ x , y ] → Hom[ z , w ]
       → Hom[ x ⊗ z , y ⊗ w ]
  f ⊗₂ g = ⊗ₕ refl refl f g

  field
    ⊗IdLₕ : {x y : ob} (f : Hom[ x , y ])
      → ⊗ₕ (⊗IdL x) (⊗IdL y) id f ≡ f
    ⊗IdRₕ : {x y : ob} (f : Hom[ x , y ])
      → ⊗ₕ (⊗IdR x) (⊗IdR y) f id ≡ f
    ⊗Assocₕ : {x y z x' y' z' : ob}
      (f : Hom[ x , x' ]) (g : Hom[ y , y' ]) (h : Hom[ z , z' ])
      → ⊗ₕ (⊗Assoc x y z) (⊗Assoc x' y' z') (f ⊗₂ g) h
        ≡ f ⊗₂ (g ⊗₂ h)

  -- the unforded tensor, recovered at `refl`
  ─⊗─ : Functor (C ×C C) C
  ─⊗─ .F-ob (x , y) = x ⊗ y
  ─⊗─ .F-hom (f , g) = f ⊗₂ g
  ─⊗─ .F-id = ⊗ₕId refl
  ─⊗─ .F-seq (f , f') (g , g') = ⊗ₕSeq refl refl refl f g f' g'

  tenstr : TensorStr C
  tenstr .TensorStr.─⊗─ = ─⊗─
  tenstr .TensorStr.unit = unit

module _ (M : StrictMonoidalCategoryᶠ ℓ ℓ') where
  open StrictMonoidalCategoryᶠ M

  -- What fording buys: tensoring with the unit lands in the hom-set
  -- you wanted *definitionally*, so `⊗IdRₕ` is a path, not a PathP.
  test-unitR-type : {x y : ob} → Hom[ x , y ] → Hom[ x , y ]
  test-unitR-type {x} {y} f = ⊗ₕ (⊗IdR x) (⊗IdR y) f id

  test-unitL-type : {x y : ob} → Hom[ x , y ] → Hom[ x , y ]
  test-unitL-type {x} {y} f = ⊗ₕ (⊗IdL x) (⊗IdL y) id f

  -- ... and both bracketings of a triple tensor land in one hom-set.
  test-assoc-type : {x y z x' y' z' : ob}
    (f : Hom[ x , x' ]) (g : Hom[ y , y' ]) (h : Hom[ z , z' ])
    → Hom[ x ⊗ (y ⊗ z) , x' ⊗ (y' ⊗ z') ] ×
      Hom[ x ⊗ (y ⊗ z) , x' ⊗ (y' ⊗ z') ]
  test-assoc-type {x} {y} {z} {x'} {y'} {z'} f g h =
      ⊗ₕ (⊗Assoc x y z) (⊗Assoc x' y' z') (f ⊗₂ g) h
    , f ⊗₂ (g ⊗₂ h)

  -- What fording does *not* buy: the ford is uniquely determined, so
  -- every forded cell is the transport of an unforded one.  The
  -- transports are relocated, not removed.
  ⊗ₕ-coh : {x y z w : ob} (f : Hom[ x , y ]) (g : Hom[ z , w ])
    {a b : ob} (p : x ⊗ z ≡ a) (q : y ⊗ w ≡ b)
    → ⊗ₕ p q f g ≡ subst2 (λ u v → Hom[ u , v ]) p q (f ⊗₂ g)
  ⊗ₕ-coh f g p q =
    J (λ a p → (b : ob) (q : _ ≡ b)
         → ⊗ₕ p q f g ≡ subst2 (λ u v → Hom[ u , v ]) p q (f ⊗₂ g))
      (λ b q → J (λ b q → ⊗ₕ refl q f g
                    ≡ subst2 (λ u v → Hom[ u , v ]) refl q (f ⊗₂ g))
                 (sym (transportRefl (f ⊗₂ g)))
                 q)
      p _ q
