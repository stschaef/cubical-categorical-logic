{-# OPTIONS --lossy-unification #-}
{- Transposition across a formal adjunction: whiskering by a 1-cell
   turns `f ⊣ u` into an adjunction of hom-categories, whose bijection
   on 2-cells is the mate correspondence. -}
module Cubical.Categories.Bicategory.Adjunction.Transposition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Properties.Coherence
open import Cubical.Categories.Bicategory.Constructions.Co
open import Cubical.Categories.Bicategory.Constructions.Op
open import Cubical.Categories.Bicategory.Adjunction

private
  variable
    ℓ ℓ' ℓ'' : Level

open NatIso
open Cubical.Categories.Category.isIso

module _ {C : Bicategory ℓ ℓ' ℓ''} (A : Adjunction C) where
  private
    module C = Bicategory C
  open AdjunctionNotation A

  -- The unit and counit of `(_ ⋆₁ f) ⊣ (_ ⋆₁ u)` on hom-categories.
  ηw : {e : C.0Cell} (x : C.1Cell e c) → C.2Cell x ((x C.⋆₁ f) C.⋆₁ u)
  ηw x = C.ρ⁻ x C.⋆₂ (x C.◁w η) C.⋆₂ C.α⁻ x f u

  -- `ε` acting on the left is `εAct` at the opposite bicategory.
  εw : {e : C.0Cell} (y : C.1Cell e d) → C.2Cell ((y C.⋆₁ u) C.⋆₁ f) y
  εw = εAct (C ^opᴮ) ε

  εwNat : {e : C.0Cell} {m n : C.1Cell e d} (θ : C.2Cell m n)
    → ((θ C.▷w u) C.▷w f) C.⋆₂ εw n ≡ εw m C.⋆₂ θ
  εwNat = εActNat (C ^opᴮ) ε

  ηwNat : {e : C.0Cell} {m n : C.1Cell e c} (θ : C.2Cell m n)
    → ηw m C.⋆₂ ((θ C.▷w f) C.▷w u) ≡ θ C.⋆₂ ηw n
  ηwNat {m = m} {n = n} θ =
      C.⋆₂Assoc _ _ _
    ∙ C.⟨⟩⋆₂⟨ C.⋆₂Assoc _ _ _ ⟩
    ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ sym (α⁻natL C θ f u) ⟩ ⟩
    ∙ C.⟨⟩⋆₂⟨ sym (C.⋆₂Assoc _ _ _) ⟩
    ∙ C.⟨⟩⋆₂⟨ C.⟨ sym (▷◁exch C θ η) ⟩⋆₂⟨⟩ ⟩
    ∙ C.⟨⟩⋆₂⟨ C.⋆₂Assoc _ _ _ ⟩
    ∙ sym (C.⋆₂Assoc _ _ _)
    ∙ C.⟨ sym (ρ⁻-nat C θ) ⟩⋆₂⟨⟩
    ∙ C.⋆₂Assoc _ _ _

  -- The zigzag, whiskered by a 1-cell on the left.
  whiskerZigzagL : {e : C.0Cell} (x : C.1Cell e c)
    → (ηw x C.▷w f) C.⋆₂ εw (x C.⋆₁ f) ≡ C.id₂
  whiskerZigzagL {e} x =
      C.⟨ ▷wSeq C _ _ f ⟩⋆₂⟨⟩
    ∙ C.⋆₂Assoc _ _ _
    ∙ C.⟨⟩⋆₂⟨ tri ⟩
    ∙ sym (▷wSeq C _ _ f)
    ∙ C.⟨ C.ρU e c .nIso (x , tt*) .sec ⟩▷ f
    ∙ C.▷wId f
    where
    -- `ε` absorbed, leaving the unwhiskered zigzag under `x ◁w _`.
    mid :   (C.α⁻ x f u C.▷w f) C.⋆₂ εw (x C.⋆₁ f)
          ≡ C.α⁺ x (f C.⋆₁ u) f C.⋆₂ (x C.◁w Gf)
    mid =
        sym (C.⋆₂Assoc _ _ _)
      ∙ C.⟨ sym (pentP4 C x f u f) ⟩⋆₂⟨⟩
      ∙ C.⋆₂Assoc _ _ _
      ∙ C.⟨⟩⋆₂⟨ C.⋆₂Assoc _ _ _ ⟩
      ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ sym (C.⋆₂Assoc _ _ _)
                       ∙ C.⟨ sym (α⁻natR C x f ε) ⟩⋆₂⟨⟩
                       ∙ C.⋆₂Assoc _ _ _
                       ∙ C.⟨⟩⋆₂⟨ α⁻ρ◁ C x f ⟩
                       ∙ sym (◁wSeq C x _ _) ⟩ ⟩
      ∙ C.⟨⟩⋆₂⟨ sym (◁wSeq C x _ _) ⟩

    tri :   (((x C.◁w η) C.⋆₂ C.α⁻ x f u) C.▷w f) C.⋆₂ εw (x C.⋆₁ f)
          ≡ C.ρ⁺ x C.▷w f
    tri =
        C.⟨ ▷wSeq C _ _ f ⟩⋆₂⟨⟩
      ∙ C.⋆₂Assoc _ _ _
      ∙ C.⟨⟩⋆₂⟨ mid ⟩
      ∙ sym (C.⋆₂Assoc _ _ _)
      ∙ C.⟨ α⁺natM C x η f ⟩⋆₂⟨⟩
      ∙ C.⋆₂Assoc _ _ _
      ∙ C.⟨⟩⋆₂⟨ sym (◁wSeq C x _ _) ⟩
      ∙ C.⟨⟩⋆₂⟨ x C.◁⟨ zigzagL⁺ ⟩ ⟩
      ∙ C.triangle e c d x f

{- The other whiskered zigzag is the first one at the co-dual, where
   the unit and counit swap; only the nesting has to be redone. -}
module _ {C : Bicategory ℓ ℓ' ℓ''} (A : Adjunction C) where
  private
    module C = Bicategory C
  open AdjunctionNotation A

  whiskerZigzagR : {e : C.0Cell} (y : C.1Cell e d)
    → ηw A (y C.⋆₁ u) C.⋆₂ (εw A y C.▷w u) ≡ C.id₂
  whiskerZigzagR y =
      C.⟨ sym (C.⋆₂Assoc _ _ _) ⟩⋆₂⟨⟩
    ∙ C.⟨⟩⋆₂⟨ C.⟨ sym (C.⋆₂Assoc _ _ _) ⟩▷ u ⟩
    ∙ whiskerZigzagL (coAdjunction A) y

  {- Mates: transposition across the adjunction.  `transpose` is the
     unit followed by the 2-cell, `transpose⁻` the 2-cell followed by
     the counit, and the whiskered zigzags make them inverse. -}
  transpose : {e : C.0Cell} {x : C.1Cell e c} {y : C.1Cell e d}
    → C.2Cell (x C.⋆₁ f) y → C.2Cell x (y C.⋆₁ u)
  transpose {x = x} θ = ηw A x C.⋆₂ (θ C.▷w u)

  transpose⁻ : {e : C.0Cell} {x : C.1Cell e c} {y : C.1Cell e d}
    → C.2Cell x (y C.⋆₁ u) → C.2Cell (x C.⋆₁ f) y
  transpose⁻ {y = y} φ = (φ C.▷w f) C.⋆₂ εw A y

  -- Transposition is natural in both variables.
  transposeNatL : {e : C.0Cell} {x x' : C.1Cell e c} {y : C.1Cell e d}
    (σ : C.2Cell x' x) (θ : C.2Cell (x C.⋆₁ f) y)
    → transpose ((σ C.▷w f) C.⋆₂ θ) ≡ σ C.⋆₂ transpose θ
  transposeNatL σ θ =
      C.⟨⟩⋆₂⟨ ▷wSeq C _ _ u ⟩
    ∙ sym (C.⋆₂Assoc _ _ _)
    ∙ C.⟨ ηwNat A σ ⟩⋆₂⟨⟩
    ∙ C.⋆₂Assoc _ _ _

  transposeNatR : {e : C.0Cell} {x : C.1Cell e c} {y y' : C.1Cell e d}
    (θ : C.2Cell (x C.⋆₁ f) y) (τ : C.2Cell y y')
    → transpose (θ C.⋆₂ τ) ≡ transpose θ C.⋆₂ (τ C.▷w u)
  transposeNatR θ τ =
      C.⟨⟩⋆₂⟨ ▷wSeq C _ _ u ⟩
    ∙ sym (C.⋆₂Assoc _ _ _)

  transposeIso : {e : C.0Cell} {x : C.1Cell e c} {y : C.1Cell e d}
    → Iso (C.2Cell (x C.⋆₁ f) y) (C.2Cell x (y C.⋆₁ u))
  transposeIso .Iso.fun = transpose
  transposeIso .Iso.inv = transpose⁻
  transposeIso {y = y} .Iso.sec φ =
      C.⟨⟩⋆₂⟨ ▷wSeq C _ _ u ⟩
    ∙ sym (C.⋆₂Assoc _ _ _)
    ∙ C.⟨ ηwNat A φ ⟩⋆₂⟨⟩
    ∙ C.⋆₂Assoc _ _ _
    ∙ C.⟨⟩⋆₂⟨ whiskerZigzagR y ⟩
    ∙ C.⋆₂IdR _
  transposeIso {x = x} .Iso.ret θ =
      C.⟨ ▷wSeq C _ _ f ⟩⋆₂⟨⟩
    ∙ C.⋆₂Assoc _ _ _
    ∙ C.⟨⟩⋆₂⟨ εwNat A θ ⟩
    ∙ sym (C.⋆₂Assoc _ _ _)
    ∙ C.⟨ whiskerZigzagL A x ⟩⋆₂⟨⟩
    ∙ C.⋆₂IdL _

-- The same bijection for precomposition, at the opposite bicategory.
module _ {C : Bicategory ℓ ℓ' ℓ''} (A : Adjunction C) where
  private
    module C = Bicategory C
  open AdjunctionNotation A

  transposeIsoOp : {e : C.0Cell} {x : C.1Cell c e} {y : C.1Cell d e}
    → Iso (C.2Cell (u C.⋆₁ x) y) (C.2Cell x (f C.⋆₁ y))
  transposeIsoOp = transposeIso (opAdjunction A)
