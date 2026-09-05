{-# OPTIONS --lossy-unification #-}
{- Notation for displayed bicategories -}
module Cubical.Categories.Bicategory.Displayed.Notation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (Σ-syntax)
open import Cubical.Foundations.More
  using (module depReasoning; module hSetReasoning)

import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Displayed

private
  variable
    ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' ℓᴰ'' : Level

-- ------------------------------------------------------------
-- Base-level actions: transporting a 2-cell along identifications
-- of its boundary 1-cells.
-- ------------------------------------------------------------
module BicatNotation (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  reindDom : ∀ {x y} {f f' g : B.1Cell x y}
    → f ≡ f' → B.2Cell f g → B.2Cell f' g
  reindDom {g = g} p = subst (λ v → B.2Cell v g) p

  reindCod : ∀ {x y} {f g g' : B.1Cell x y}
    → g ≡ g' → B.2Cell f g → B.2Cell f g'
  reindCod {f = f} p = subst (λ v → B.2Cell f v) p

  reindDomEq : ∀ {x y} {f f' g : B.1Cell x y}
    → f Eq.≡ f' → B.2Cell f g → B.2Cell f' g
  reindDomEq Eq.refl β = β

  reindCodEq : ∀ {x y} {f g g' : B.1Cell x y}
    → g Eq.≡ g' → B.2Cell f g → B.2Cell f g'
  reindCodEq Eq.refl β = β

-- ------------------------------------------------------------
-- Displayed-level actions and re-emitted reasoning.
-- ------------------------------------------------------------
module BicatᴰNotation
  {B : Bicategory ℓ ℓ' ℓ''} (Bᴰ : Bicategoryᴰ B ℓᴰ ℓᴰ' ℓᴰ'')
  where
  private
    module B = Bicategory B
    module Bᴰ = Bicategoryᴰ Bᴰ
  open BicatNotation B public

  -- 1-cell level: the dependent-reasoning fragment for each family
  -- of displayed 1-cells (no rectification — base 1-cells need not
  -- form a set).
  module 1Cellᴰ[_,_] {x y : B.ob} (xᴰ : Bᴰ.ob[ x ]) (yᴰ : Bᴰ.ob[ y ]) =
    depReasoning (Bᴰ.1Cellᴰ xᴰ yᴰ)

  -- 2-cell level: the full hSet-reasoning interface for each family
  -- of displayed 2-cells.
  module 2Cellᴰ[_,_] {x y : B.ob} {f g : B.1Cell x y}
    {xᴰ : Bᴰ.ob[ x ]} {yᴰ : Bᴰ.ob[ y ]}
    (fᴰ : Bᴰ.1Cellᴰ xᴰ yᴰ f) (gᴰ : Bᴰ.1Cellᴰ xᴰ yᴰ g) =
    hSetReasoning
      (B.2Cell f g , B.isSet2Cell)
      (Bᴰ.2Cellᴰ fᴰ gᴰ)

  -- The six reindexing actions, as thin aliases.

  reind¹ : ∀ {x y} {xᴰ : Bᴰ.ob[ x ]} {yᴰ : Bᴰ.ob[ y ]}
    {f g : B.1Cell x y}
    → f ≡ g → Bᴰ.1Cellᴰ xᴰ yᴰ f → Bᴰ.1Cellᴰ xᴰ yᴰ g
  reind¹ {xᴰ = xᴰ} {yᴰ = yᴰ} = subst (Bᴰ.1Cellᴰ xᴰ yᴰ)

  reind¹Eq : ∀ {x y} {xᴰ : Bᴰ.ob[ x ]} {yᴰ : Bᴰ.ob[ y ]}
    {f g : B.1Cell x y}
    → f Eq.≡ g → Bᴰ.1Cellᴰ xᴰ yᴰ f → Bᴰ.1Cellᴰ xᴰ yᴰ g
  reind¹Eq Eq.refl fᴰ = fᴰ

  reind² : ∀ {x y} {xᴰ : Bᴰ.ob[ x ]} {yᴰ : Bᴰ.ob[ y ]}
    {f g : B.1Cell x y}
    {fᴰ : Bᴰ.1Cellᴰ xᴰ yᴰ f} {gᴰ : Bᴰ.1Cellᴰ xᴰ yᴰ g}
    {β β' : B.2Cell f g}
    → β ≡ β' → Bᴰ.2Cellᴰ fᴰ gᴰ β → Bᴰ.2Cellᴰ fᴰ gᴰ β'
  reind² {fᴰ = fᴰ} {gᴰ = gᴰ} = subst (Bᴰ.2Cellᴰ fᴰ gᴰ)

  reind²Eq : ∀ {x y} {xᴰ : Bᴰ.ob[ x ]} {yᴰ : Bᴰ.ob[ y ]}
    {f g : B.1Cell x y}
    {fᴰ : Bᴰ.1Cellᴰ xᴰ yᴰ f} {gᴰ : Bᴰ.1Cellᴰ xᴰ yᴰ g}
    {β β' : B.2Cell f g}
    → β Eq.≡ β' → Bᴰ.2Cellᴰ fᴰ gᴰ β → Bᴰ.2Cellᴰ fᴰ gᴰ β'
  reind²Eq Eq.refl βᴰ = βᴰ

  reind²Dom : ∀ {x y} {xᴰ : Bᴰ.ob[ x ]} {yᴰ : Bᴰ.ob[ y ]}
    {f f' g : B.1Cell x y}
    {fᴰ : Bᴰ.1Cellᴰ xᴰ yᴰ f} {gᴰ : Bᴰ.1Cellᴰ xᴰ yᴰ g}
    {β : B.2Cell f g}
    (p : f ≡ f')
    → Bᴰ.2Cellᴰ fᴰ gᴰ β
    → Bᴰ.2Cellᴰ (reind¹ p fᴰ) gᴰ (reindDom p β)
  reind²Dom {x = x} {y = y} {xᴰ = xᴰ} {yᴰ = yᴰ} {g = g}
    {fᴰ = fᴰ} {gᴰ = gᴰ} {β = β} p βᴰ =
    subst
      {A = Σ[ v ∈ B.1Cell x y ]
           Σ[ vᴰ ∈ Bᴰ.1Cellᴰ xᴰ yᴰ v ] B.2Cell v g}
      (λ (v , vᴰ , γ) → Bᴰ.2Cellᴰ {f = v} vᴰ gᴰ γ)
      (λ i → p i
           , subst-filler (Bᴰ.1Cellᴰ xᴰ yᴰ) p fᴰ i
           , subst-filler (λ v → B.2Cell v g) p β i)
      βᴰ

  reind²Cod : ∀ {x y} {xᴰ : Bᴰ.ob[ x ]} {yᴰ : Bᴰ.ob[ y ]}
    {f g g' : B.1Cell x y}
    {fᴰ : Bᴰ.1Cellᴰ xᴰ yᴰ f} {gᴰ : Bᴰ.1Cellᴰ xᴰ yᴰ g}
    {β : B.2Cell f g}
    (p : g ≡ g')
    → Bᴰ.2Cellᴰ fᴰ gᴰ β
    → Bᴰ.2Cellᴰ fᴰ (reind¹ p gᴰ) (reindCod p β)
  reind²Cod {x = x} {y = y} {xᴰ = xᴰ} {yᴰ = yᴰ} {f = f}
    {fᴰ = fᴰ} {gᴰ = gᴰ} {β = β} p βᴰ =
    subst
      {A = Σ[ v ∈ B.1Cell x y ]
           Σ[ vᴰ ∈ Bᴰ.1Cellᴰ xᴰ yᴰ v ] B.2Cell f v}
      (λ (v , vᴰ , γ) → Bᴰ.2Cellᴰ {g = v} fᴰ vᴰ γ)
      (λ i → p i
           , subst-filler (Bᴰ.1Cellᴰ xᴰ yᴰ) p gᴰ i
           , subst-filler (λ v → B.2Cell f v) p β i)
      βᴰ

  reind²DomEq : ∀ {x y} {xᴰ : Bᴰ.ob[ x ]} {yᴰ : Bᴰ.ob[ y ]}
    {f f' g : B.1Cell x y}
    {fᴰ : Bᴰ.1Cellᴰ xᴰ yᴰ f} {gᴰ : Bᴰ.1Cellᴰ xᴰ yᴰ g}
    {β : B.2Cell f g}
    (e : f Eq.≡ f')
    → Bᴰ.2Cellᴰ fᴰ gᴰ β
    → Bᴰ.2Cellᴰ (reind¹Eq e fᴰ) gᴰ (reindDomEq e β)
  reind²DomEq Eq.refl βᴰ = βᴰ

  reind²CodEq : ∀ {x y} {xᴰ : Bᴰ.ob[ x ]} {yᴰ : Bᴰ.ob[ y ]}
    {f g g' : B.1Cell x y}
    {fᴰ : Bᴰ.1Cellᴰ xᴰ yᴰ f} {gᴰ : Bᴰ.1Cellᴰ xᴰ yᴰ g}
    {β : B.2Cell f g}
    (e : g Eq.≡ g')
    → Bᴰ.2Cellᴰ fᴰ gᴰ β
    → Bᴰ.2Cellᴰ fᴰ (reind¹Eq e gᴰ) (reindCodEq e β)
  reind²CodEq Eq.refl βᴰ = βᴰ

  -- A seventh pair of actions: transporting a displayed 2-cell along
  -- identifications of its *displayed* boundary 1-cells (fixed base).
  reind²ᴰ : ∀ {x y} {xᴰ : Bᴰ.ob[ x ]} {yᴰ : Bᴰ.ob[ y ]}
    {f g : B.1Cell x y} {β : B.2Cell f g}
    {X X' : Bᴰ.1Cellᴰ xᴰ yᴰ f} {Y Y' : Bᴰ.1Cellᴰ xᴰ yᴰ g}
    → X ≡ X' → Y ≡ Y'
    → Bᴰ.2Cellᴰ X Y β → Bᴰ.2Cellᴰ X' Y' β
  reind²ᴰ {β = β} {Y = Y} p q βᴰ =
    subst (λ Y' → Bᴰ.2Cellᴰ _ Y' β) q
      (subst (λ X' → Bᴰ.2Cellᴰ X' Y β) p βᴰ)

  reind²ᴰEq : ∀ {x y} {xᴰ : Bᴰ.ob[ x ]} {yᴰ : Bᴰ.ob[ y ]}
    {f g : B.1Cell x y} {β : B.2Cell f g}
    {X X' : Bᴰ.1Cellᴰ xᴰ yᴰ f} {Y Y' : Bᴰ.1Cellᴰ xᴰ yᴰ g}
    → X Eq.≡ X' → Y Eq.≡ Y'
    → Bᴰ.2Cellᴰ X Y β → Bᴰ.2Cellᴰ X' Y' β
  reind²ᴰEq Eq.refl Eq.refl βᴰ = βᴰ
