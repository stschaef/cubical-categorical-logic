{-# OPTIONS --lossy-unification #-}
{-
  The two 1-cell-level universal properties of a bicategory.

  `B` already has the two functors between hom-categories that they
  extend along: `precomp j : Hom[ b , c ] → Hom[ a , c ]` and
  `postcomp g : Hom[ x , y ] → Hom[ x , z ]`.  A right *extension* is
  a right adjoint to `precomp` at a 1-cell, a right *lifting* is a
  right adjoint to `postcomp` at a 1-cell, so both are
  `HasRightAdjointAt` and share `RightAdjointNotation`.

  `KanExtension.agda` develops the extension theory (composition,
  pointwiseness, duals), `Adjunction/Universal.agda` the lifting one.
-}
module Cubical.Categories.Bicategory.Limits.Extension where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Adjoint.RightAdjoint

open import Cubical.Categories.Bicategory.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  -- g ↦ 2-cells j ⋆₁ g ⇒ f, contravariant by whiskering with j
  RanPshᴮ : {a b c : B.0Cell} (j : B.1Cell a b) (f : B.1Cell a c)
    → Presheaf B.Hom[ b , c ] ℓ''
  RanPshᴮ {c = c} j f = RPsh (B.precomp {z = c} j) f

  RightExtensionᴮ : {a b c : B.0Cell} (j : B.1Cell a b) (f : B.1Cell a c)
    → Type (ℓ-max ℓ' ℓ'')
  RightExtensionᴮ {c = c} j f = HasRightAdjointAt (B.precomp {z = c} j) f

  -- h ↦ 2-cells h ⋆₁ g ⇒ f, contravariant by whiskering with g
  RiftPshᴮ : {x y z : B.0Cell} (g : B.1Cell y z) (f : B.1Cell x z)
    → Presheaf B.Hom[ x , y ] ℓ''
  RiftPshᴮ {x = x} g f = RPsh (B.postcomp {x = x} g) f

  RightLiftingᴮ : {x y z : B.0Cell} (g : B.1Cell y z) (f : B.1Cell x z)
    → Type (ℓ-max ℓ' ℓ'')
  RightLiftingᴮ {x = x} g f = HasRightAdjointAt (B.postcomp {x = x} g) f

  -- the `isUniversal` forms, for probe-indexed statements
  isRightExtensionᴮ : {a b c : B.0Cell} (j : B.1Cell a b)
    {f : B.1Cell a c} (r : B.1Cell b c) → B.2Cell (j B.⋆₁ r) f
    → Type (ℓ-max ℓ' ℓ'')
  isRightExtensionᴮ {b = b} {c} j {f} r ε =
    isUniversal B.Hom[ b , c ] (RanPshᴮ j f) r ε

  isRightLiftingᴮ : {x y z : B.0Cell} (g : B.1Cell y z)
    {f : B.1Cell x z} (r : B.1Cell x y) → B.2Cell (r B.⋆₁ g) f
    → Type (ℓ-max ℓ' ℓ'')
  isRightLiftingᴮ {x = x} {y} g {f} r ε =
    isUniversal B.Hom[ x , y ] (RiftPshᴮ g f) r ε

module RightExtensionᴮNotation {B : Bicategory ℓ ℓ' ℓ''}
  {a b c : Bicategory.0Cell B} {j : Bicategory.1Cell B a b}
  {f : Bicategory.1Cell B a c} (R : RightExtensionᴮ B j f) where
  private
    module B = Bicategory B
  open RightAdjointNotation {F = B.precomp {z = c} j} {d = f} R public

module RightLiftingᴮNotation {B : Bicategory ℓ ℓ' ℓ''}
  {x y z : Bicategory.0Cell B} {g : Bicategory.1Cell B y z}
  {f : Bicategory.1Cell B x z} (R : RightLiftingᴮ B g f) where
  private
    module B = Bicategory B
  open RightAdjointNotation {F = B.postcomp {x = x} g} {d = f} R public

  rift : B.1Cell x y
  rift = vertex

  -- the counit
  riftε : B.2Cell (rift B.⋆₁ g) f
  riftε = element

  -- the counit whiskered by a 1-cell into x, i.e. the candidate
  -- counit exhibiting `k ⋆₁ rift` as a lifting of `k ⋆₁ f`
  riftεPre : {w : Bicategory.0Cell B} (k : B.1Cell w x)
    → B.2Cell ((k B.⋆₁ rift) B.⋆₁ g) (k B.⋆₁ f)
  riftεPre k = B.α⁺ k rift g B.⋆₂ (k B.◁w riftε)

-- Absolute right liftings: stable under precomposition, the mirror
-- of `KanExtension.isAbsoluteRanᴮ`, which is stable under
-- postcomposition.
module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  isAbsoluteRiftᴮ : {x y z : B.0Cell} {g : B.1Cell y z} {f : B.1Cell x z}
    → RightLiftingᴮ B g f → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  isAbsoluteRiftᴮ {x} {g = g} R = {w : B.0Cell} (k : B.1Cell w x)
    → isRightLiftingᴮ B {x = w} g (k B.⋆₁ RightLiftingᴮNotation.rift R)
        (RightLiftingᴮNotation.riftεPre R k)
