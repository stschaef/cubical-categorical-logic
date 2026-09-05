{-# OPTIONS --lossy-unification #-}
{-
  Equifiers in a bicategory.

  An equifier of `θ φ : f ⇒ g` IS a biuniversal element of the
  equifier prestack: the vertex is the equifier 0-cell and the ELEMENT
  is the pair `(eqᴮ , eqᴮ-pred)` of the equifier projection and the
  witness that it equifies `θ` and `φ`.
-}
module Cubical.Categories.Bicategory.Limits.Equifier where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Equifier
open import Cubical.Categories.Bicategory.Universal.Base
open import Cubical.Categories.Bicategory.Limits.Terminal
open import Cubical.Categories.Bicategory.Limits.Product
open import Cubical.Categories.Bicategory.Limits.Inserter
open import Cubical.Categories.Bicategory.Limits.Comma

private
  variable
    ℓ ℓ' ℓ'' : Level

open Functor

module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  Equifierᴮ : {a b : B.0Cell} {f g : B.1Cell a b} (θ φ : B.2Cell f g)
    → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  Equifierᴮ {a} {b} θ φ = BiuniversalElement (EquifierPrestack B θ φ)

  hasEquifiersᴮ : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  hasEquifiersᴮ = {a b : B.0Cell} {f g : B.1Cell a b}
    (θ φ : B.2Cell f g) → Equifierᴮ θ φ

module EquifierᴮNotation {B : Bicategory ℓ ℓ' ℓ''}
  {a b : Bicategory.0Cell B} {f g : Bicategory.1Cell B a b}
  {θ φ : Bicategory.2Cell B f g} (E : Equifierᴮ B θ φ) where
  private
    module B = Bicategory B
  module Eq = EquifierPre {B = B} {a = a} {b = b} θ φ
  open BiuniversalElementNotation E public

  eqᴮ : B.1Cell vertex a
  eqᴮ = element .fst

  eqᴮ-pred : (eqᴮ B.◁w θ) ≡ (eqᴮ B.◁w φ)
  eqᴮ-pred = element .snd

  introᴱ : {x : B.0Cell} (h : B.1Cell x a) → Eq.EqPred h → B.1Cell x vertex
  introᴱ h p = intro (h , p)

  introᴱβ : {x : B.0Cell} (h : B.1Cell x a) (p : Eq.EqPred h)
    → (introᴱ h p B.⋆₁ eqᴮ) B.≅₂ h
  introᴱβ {x} h p = F-Iso {F = Eq.eqForget x} (β (h , p))

  introᴱη : {x : B.0Cell} {h : B.1Cell x vertex} {k : B.1Cell x a}
    {p : Eq.EqPred k} → (h B.⋆₁ eqᴮ) B.≅₂ k → h B.≅₂ introᴱ k p
  introᴱη ψ = intro≡ (Eq.eqIso ψ)

  eqᴮ-ext : {x : B.0Cell} {h k : B.1Cell x vertex} (α γ : B.2Cell h k)
    → (α B.▷w eqᴮ) ≡ (γ B.▷w eqᴮ) → α ≡ γ
  eqᴮ-ext = extensionality

  introᴱ-nat : {x' x : B.0Cell} (k : B.1Cell x' x)
    (h : B.1Cell x a) (p : Eq.EqPred h)
    → (k B.⋆₁ introᴱ h p) B.≅₂ introᴱ (k B.⋆₁ h) (Eq.reindPred k p)
  introᴱ-nat k h p = intro-natural k (h , p)

-- PIE limits: products, inserters, equifiers.
module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  record hasPIEᴮ : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
    field
      terminalᴮ : Terminalᴮ B
      productsᴮ : (a b : B.0Cell) → BinProductᴮ B a b
      insertersᴮ : hasInsertersᴮ B
      equifiersᴮ : hasEquifiersᴮ B

  open hasPIEᴮ

  -- Comma objects cost no equifiers: `Commaᴮ` is definitionally an
  -- inserter over the product (`Limits/Comma.agda`).
  hasPIE→hasCommasᴮ : hasPIEᴮ → hasCommaObjectsᴮ B
  hasPIE→hasCommasᴮ pie = commaFromInsertersᴮ B (pie .insertersᴮ)
