{-# OPTIONS --lossy-unification #-}
{-
  Binary products in a bicategory.

  A product cone IS a biuniversal element of `B [-, a ] × B [-, b ]`:
  the vertex is the product 0-cell and the ELEMENT is the pair of
  projections, so the comparison `⟨ (π₁ , π₂) ⟩ x` is `h ↦ (h ⋆₁ π₁ ,
  h ⋆₁ π₂)` by construction.  Everything shape-independent is
  inherited from `Universal/Base.agda`; only the two projections of
  `β` and of the `η`-rule are proved here.
-}
module Cubical.Categories.Bicategory.Limits.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.Morphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.BinProduct.More

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Hom
open import Cubical.Categories.Bicategory.Prestack.BinProduct
open import Cubical.Categories.Bicategory.Universal.Base

private
  variable
    ℓ ℓ' ℓ'' ℓc ℓc' ℓc'' : Level

open Functor
open isIso

module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  BinProductPrestack : (a b : B.0Cell) → Prestack B ℓ' ℓ''
  BinProductPrestack a b = Hom B a ×Pre Hom B b

  BinProductᴮ : (a b : B.0Cell) → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  BinProductᴮ a b = BiuniversalElement (BinProductPrestack a b)

module BinProductᴮNotation {B : Bicategory ℓ ℓ' ℓ''}
  {a b : Bicategory.0Cell B} (P : BinProductᴮ B a b) where
  private
    module B = Bicategory B
  module ×bue = BiuniversalElementNotation P
  open BiuniversalElementNotation P public

  π₁ᴮ : B.1Cell vertex a
  π₁ᴮ = fst element

  π₂ᴮ : B.1Cell vertex b
  π₂ᴮ = snd element

  pairᴮ : {x : B.0Cell} → B.1Cell x a → B.1Cell x b → B.1Cell x vertex
  pairᴮ f g = intro (f , g)

  pairᴮβ₁ : {x : B.0Cell} (f : B.1Cell x a) (g : B.1Cell x b)
    → (pairᴮ f g B.⋆₁ π₁ᴮ) B.≅₂ f
  pairᴮβ₁ f g = CatIsoFst (β (f , g))

  pairᴮβ₂ : {x : B.0Cell} (f : B.1Cell x a) (g : B.1Cell x b)
    → (pairᴮ f g B.⋆₁ π₂ᴮ) B.≅₂ g
  pairᴮβ₂ f g = CatIsoSnd (β (f , g))

  pairᴮη : {x : B.0Cell} {h : B.1Cell x vertex}
    {f : B.1Cell x a} {g : B.1Cell x b}
    → (h B.⋆₁ π₁ᴮ) B.≅₂ f → (h B.⋆₁ π₂ᴮ) B.≅₂ g
    → h B.≅₂ pairᴮ f g
  pairᴮη {x} φ ψ = intro≡ (CatIso× B.Hom[ x , a ] B.Hom[ x , b ] φ ψ)

  pairᴮη-β₁ : {x : B.0Cell} {h : B.1Cell x vertex}
    {f : B.1Cell x a} {g : B.1Cell x b}
    (φ : (h B.⋆₁ π₁ᴮ) B.≅₂ f) (ψ : (h B.⋆₁ π₂ᴮ) B.≅₂ g)
    → ⋆Iso (F-Iso {F = B.postcomp π₁ᴮ} (pairᴮη φ ψ)) (pairᴮβ₁ f g) ≡ φ
  pairᴮη-β₁ {x} {h} {f} {g} φ ψ =
    CatIso≡ _ _
      (cong (λ m → m ⋆⟨ B.Hom[ x , a ] ⟩ pairᴮβ₁ f g .fst)
            (cong (λ ξ → ξ .fst .fst) (intro≡-β _))
      ∙ ⋆InvRMove⁻ (pairᴮβ₁ f g) refl)

  pairᴮη-β₂ : {x : B.0Cell} {h : B.1Cell x vertex}
    {f : B.1Cell x a} {g : B.1Cell x b}
    (φ : (h B.⋆₁ π₁ᴮ) B.≅₂ f) (ψ : (h B.⋆₁ π₂ᴮ) B.≅₂ g)
    → ⋆Iso (F-Iso {F = B.postcomp π₂ᴮ} (pairᴮη φ ψ)) (pairᴮβ₂ f g) ≡ ψ
  pairᴮη-β₂ {x} {h} {f} {g} φ ψ =
    CatIso≡ _ _
      (cong (λ m → m ⋆⟨ B.Hom[ x , b ] ⟩ pairᴮβ₂ f g .fst)
            (cong (λ ξ → ξ .fst .snd) (intro≡-β _))
      ∙ ⋆InvRMove⁻ (pairᴮβ₂ f g) refl)

  pairᴮ-ext : {x : B.0Cell} {h k : B.1Cell x vertex}
    (α γ : B.2Cell h k)
    → B.postcomp π₁ᴮ ⟪ α ⟫ ≡ B.postcomp π₁ᴮ ⟪ γ ⟫
    → B.postcomp π₂ᴮ ⟪ α ⟫ ≡ B.postcomp π₂ᴮ ⟪ γ ⟫
    → α ≡ γ
  pairᴮ-ext α γ q r = extensionality α γ (≡-× q r)

  -- naturality in the probe, from the generic `intro-natural`; the
  -- coherence it needs is the prestack's F², i.e. B's associator
  pairᴮ-nat : {x' x : B.0Cell} (k : B.1Cell x' x)
    (f : B.1Cell x a) (g : B.1Cell x b)
    → (k B.⋆₁ pairᴮ f g) B.≅₂ pairᴮ (k B.⋆₁ f) (k B.⋆₁ g)
  pairᴮ-nat k f g = intro-natural k (f , g)

module _ {B : Bicategory ℓ ℓ' ℓ''} {C : Bicategory ℓc ℓc' ℓc''}
  (F : Pseudofunctor B C) where
  private
    module F = Pseudofunctor F

  preservesBinProductᴮ : ∀ {a b} → BinProductᴮ B a b → Type _
  preservesBinProductᴮ {a} {b} P =
    isBiuniversal (BinProductPrestack C (F.F-ob a) (F.F-ob b))
      (F.F-ob (BiuniversalElement.vertex P))
      ( F.F-1cell (BinProductᴮNotation.π₁ᴮ P)
      , F.F-1cell (BinProductᴮNotation.π₂ᴮ P))
