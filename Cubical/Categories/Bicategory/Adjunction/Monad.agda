{-# OPTIONS --lossy-unification #-}
{- Every formal adjunction induces a formal monad on the source of its
   left leg, and dually a comonad on the source of its right leg. -}
module Cubical.Categories.Bicategory.Adjunction.Monad where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Properties.Coherence
open import Cubical.Categories.Bicategory.Adjunction
open import Cubical.Categories.Bicategory.Monad.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

open NatIso
open isIso

{- The monad induced by an adjunction: carrier `f ⋆₁ u`, unit `η`, and
   multiplication given by `ε` acting in the middle. -}
module _ {C : Bicategory ℓ ℓ' ℓ''} (A : Adjunction C) where
  private
    module C = Bicategory C
  open AdjunctionNotation A

  private
    μ : C.2Cell (fu C.⋆₁ fu) fu
    μ = C.α⁺ f u fu C.⋆₂ (f C.◁w Eu)

    -- `μ` with `ε` whiskered on the left of `f` instead of the right.
    μalt : μ ≡ C.α⁻ fu f u C.⋆₂ (Gf C.▷w u)
    μalt =
        C.⟨⟩⋆₂⟨ ◁wSeq C f _ _ ⟩
      ∙ sym (C.⋆₂Assoc _ _ _)
      ∙ C.⟨ pentMove ⟩⋆₂⟨⟩
      ∙ C.⋆₂Assoc _ _ _
      ∙ C.⟨⟩⋆₂⟨ unitMid C f u ε ⟩
      ∙ C.⋆₂Assoc _ _ _
      ∙ C.⟨⟩⋆₂⟨ sym (▷wSeq C _ _ u) ⟩
      where
      pentMove :   C.α⁺ f u fu C.⋆₂ (f C.◁w C.α⁻ u f u)
                 ≡ (C.α⁻ fu f u C.⋆₂ (C.α⁺ f u f C.▷w u)) C.⋆₂ C.α⁺ f uf u
      pentMove = ⋆InvRMove (invIso (αI C f uf u))
        (C.⋆₂Assoc _ _ _ ∙ sym (pentP3 C f u f u))

  adjunctionMonad : Monad C
  adjunctionMonad .Monad.a = c
  adjunctionMonad .Monad.t = fu
  adjunctionMonad .Monad.η = η
  adjunctionMonad .Monad.μ = μ
  adjunctionMonad .Monad.idL =
      C.⟨⟩⋆₂⟨ μalt ⟩
    ∙ sym (C.⋆₂Assoc _ _ _)
    ∙ C.⟨ α⁻natL C η f u ⟩⋆₂⟨⟩
    ∙ C.⋆₂Assoc _ _ _
    ∙ C.⟨⟩⋆₂⟨ sym (▷wSeq C _ _ u) ⟩
    ∙ C.⟨⟩⋆₂⟨ C.⟨ zigzagL⁺ ⟩▷ u ⟩
    ∙ λ⋆₁ C f u
  adjunctionMonad .Monad.idR =
      sym (C.⋆₂Assoc _ _ _)
    ∙ C.⟨ α⁺natR C f u η ⟩⋆₂⟨⟩
    ∙ C.⋆₂Assoc _ _ _
    ∙ C.⟨⟩⋆₂⟨ sym (◁wSeq C f _ _) ⟩
    ∙ C.⟨⟩⋆₂⟨ f C.◁⟨ zigzagR⁺ ⟩ ⟩
    ∙ ρ⋆₁ C u f
  adjunctionMonad .Monad.μAssoc =
      C.⟨⟩⋆₂⟨ sym (C.⋆₂Assoc _ _ _) ⟩
    ∙ C.⟨⟩⋆₂⟨ C.⟨ α⁺natR C f u μ ⟩⋆₂⟨⟩ ⟩
    ∙ C.⟨⟩⋆₂⟨ C.⋆₂Assoc _ _ _ ⟩
    ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ sym (◁wSeq C f _ _) ⟩ ⟩
    ∙ sym (C.⋆₂Assoc _ _ _)
    ∙ C.⟨ sym (C.pentagon c d c c c f u fu fu) ⟩⋆₂⟨⟩
    ∙ C.⋆₂Assoc _ _ _
    ∙ C.⟨⟩⋆₂⟨ C.⋆₂Assoc _ _ _ ⟩
    ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ sym (◁wSeq C f _ _) ⟩ ⟩
    ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ f C.◁⟨ star ⟩ ⟩ ⟩
    ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ ◁wSeq C f _ _ ⟩ ⟩
    ∙ C.⟨⟩⋆₂⟨ sym (C.⋆₂Assoc _ _ _) ⟩
    ∙ C.⟨⟩⋆₂⟨ C.⟨ sym (α⁺natM C f Eu fu) ⟩⋆₂⟨⟩ ⟩
    ∙ C.⟨⟩⋆₂⟨ C.⋆₂Assoc _ _ _ ⟩
    ∙ sym (C.⋆₂Assoc _ _ _)
    ∙ C.⟨ sym (▷wSeq C _ _ fu) ⟩⋆₂⟨⟩
    where
    -- `Eu` is an associative right action of the monad on `u`.
    star :   C.α⁺ u fu fu C.⋆₂ ((u C.◁w μ) C.⋆₂ Eu)
           ≡ (Eu C.▷w fu) C.⋆₂ Eu
    star =
        C.⟨⟩⋆₂⟨ C.⟨ ◁wSeq C u _ _ ⟩⋆₂⟨⟩ ⟩
      ∙ C.⟨⟩⋆₂⟨ C.⋆₂Assoc _ _ _ ⟩
      ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ εActNat C ε Eu ⟩ ⟩
      ∙ C.⟨⟩⋆₂⟨ sym (C.⋆₂Assoc _ _ _) ⟩
      ∙ sym (C.⋆₂Assoc _ _ _)
      ∙ C.⟨ εAct▷ C ε u fu ⟩⋆₂⟨⟩

{- The dual comonad, on `u ⋆₁ f`.  `Comonad C` is `Monad (C ^coᴮ)`, so
   it is the monad above at the co-dual adjunction; no reproof. -}
module _ {C : Bicategory ℓ ℓ' ℓ''} (A : Adjunction C) where
  private
    module C = Bicategory C
  open AdjunctionNotation A

  adjunctionComonad : Comonad C
  adjunctionComonad = adjunctionMonad (coAdjunction A)

  -- Its carrier is the other composite, and its counit is `ε`.
  adjunctionComonadCarrier : Monad.t adjunctionComonad ≡ uf
  adjunctionComonadCarrier = refl

  adjunctionComonadCounit : ComonadNotation.ε adjunctionComonad ≡ ε
  adjunctionComonadCounit = refl
