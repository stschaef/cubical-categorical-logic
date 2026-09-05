{-# OPTIONS --lossy-unification #-}
{- Displayed bicategories of structure over a base -}
module Cubical.Categories.Bicategory.Displayed.Constructions.StructureOver where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.Instances.StructureOver.Base

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Displayed

private
  variable
    ℓᴰ'' : Level
    ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' : Level

open Functorᴰ
open NatTransᴰ
open NatIsoᴰ

module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  record StructureOverᴮ (ℓᴰ ℓᴰ' : Level)
    : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓᴰ ℓᴰ'))) where
    field
      ob[_] : B.ob → Type ℓᴰ
      1Cellᴰ[_][_,_] : {x y : B.ob}
        → B.1Cell x y → ob[ x ] → ob[ y ] → Type ℓᴰ'
      id₁ᴰ : ∀ {x} {xᴰ : ob[ x ]} → 1Cellᴰ[ B.id₁ ][ xᴰ , xᴰ ]
      _⋆₁ᴰ_ : ∀ {x y z} {f : B.1Cell x y} {g : B.1Cell y z}
        {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]}
        → 1Cellᴰ[ f ][ xᴰ , yᴰ ] → 1Cellᴰ[ g ][ yᴰ , zᴰ ]
        → 1Cellᴰ[ f B.⋆₁ g ][ xᴰ , zᴰ ]

module _ {B : Bicategory ℓ ℓ' ℓ''} (S : StructureOverᴮ B ℓᴰ ℓᴰ') where
  private
    module B = Bicategory B
    module S = StructureOverᴮ S

    -- The displayed hom-category over B.Hom[ x , y ]: objects over f
    -- are 1-cell structures, morphisms over any 2-cell are trivial.
    homStr : {x y : B.ob} (xᴰ : S.ob[ x ]) (yᴰ : S.ob[ y ])
      → StructureOver B.Hom[ x , y ] ℓᴰ' ℓ-zero
    homStr xᴰ yᴰ .StructureOver.ob[_] f = S.1Cellᴰ[ f ][ xᴰ , yᴰ ]
    homStr xᴰ yᴰ .StructureOver.Hom[_][_,_] _ _ _ = Unit
    homStr xᴰ yᴰ .StructureOver.idᴰ = tt
    homStr xᴰ yᴰ .StructureOver._⋆ᴰ_ _ _ = tt
    homStr xᴰ yᴰ .StructureOver.isPropHomᴰ = isPropUnit

  open Bicategoryᴰ

  StructureOverᴮ→Bicategoryᴰ : Bicategoryᴰ B ℓᴰ ℓᴰ' ℓ-zero
  StructureOverᴮ→Bicategoryᴰ .ob[_] = S.ob[_]
  StructureOverᴮ→Bicategoryᴰ .Homᴰ[_,_] xᴰ yᴰ =
    StructureOver→Catᴰ (homStr xᴰ yᴰ)
  StructureOverᴮ→Bicategoryᴰ .idᴰ .F-obᴰ _ = S.id₁ᴰ
  StructureOverᴮ→Bicategoryᴰ .idᴰ .F-homᴰ _ = tt
  StructureOverᴮ→Bicategoryᴰ .idᴰ .F-idᴰ = refl
  StructureOverᴮ→Bicategoryᴰ .idᴰ .F-seqᴰ _ _ = refl
  StructureOverᴮ→Bicategoryᴰ .seqᴰ _ _ _ .F-obᴰ (fᴰ , gᴰ) = fᴰ S.⋆₁ᴰ gᴰ
  StructureOverᴮ→Bicategoryᴰ .seqᴰ _ _ _ .F-homᴰ _ = tt
  StructureOverᴮ→Bicategoryᴰ .seqᴰ _ _ _ .F-idᴰ = refl
  StructureOverᴮ→Bicategoryᴰ .seqᴰ _ _ _ .F-seqᴰ _ _ = refl
  StructureOverᴮ→Bicategoryᴰ .λUᴰ _ _ .transᴰ .N-obᴰ _ = tt
  StructureOverᴮ→Bicategoryᴰ .λUᴰ _ _ .transᴰ .N-homᴰ _ = refl
  StructureOverᴮ→Bicategoryᴰ .λUᴰ _ _ .nIsoᴰ _ = isisoᴰ tt refl refl
  StructureOverᴮ→Bicategoryᴰ .ρUᴰ _ _ .transᴰ .N-obᴰ _ = tt
  StructureOverᴮ→Bicategoryᴰ .ρUᴰ _ _ .transᴰ .N-homᴰ _ = refl
  StructureOverᴮ→Bicategoryᴰ .ρUᴰ _ _ .nIsoᴰ _ = isisoᴰ tt refl refl
  StructureOverᴮ→Bicategoryᴰ .αᴰ _ _ _ _ .transᴰ .N-obᴰ _ = tt
  StructureOverᴮ→Bicategoryᴰ .αᴰ _ _ _ _ .transᴰ .N-homᴰ _ = refl
  StructureOverᴮ→Bicategoryᴰ .αᴰ _ _ _ _ .nIsoᴰ _ = isisoᴰ tt refl refl
  StructureOverᴮ→Bicategoryᴰ .triangleᴰ _ _ = refl
  StructureOverᴮ→Bicategoryᴰ .pentagonᴰ _ _ _ _ = refl

-- Inhabitation check: the terminal displayed bicategory is the
-- instance at trivial structure.
private
  module _ (B : Bicategory ℓ ℓ' ℓ'') where
    open StructureOverᴮ

    UnitStrᴮ : StructureOverᴮ B ℓ-zero ℓ-zero
    UnitStrᴮ .ob[_] _ = Unit
    UnitStrᴮ .1Cellᴰ[_][_,_] _ _ _ = Unit
    UnitStrᴮ .id₁ᴰ = tt
    UnitStrᴮ ._⋆₁ᴰ_ _ _ = tt

    _ : Bicategoryᴰ B ℓ-zero ℓ-zero ℓ-zero
    _ = StructureOverᴮ→Bicategoryᴰ UnitStrᴮ

-- ------------------------------------------------------------
-- The locally-prop variant: displayed 2-cells are a propositional
-- predicate on base 2-cells (e.g. "this natural transformation is
-- monoidal"), rather than trivial.  Every law of the resulting
-- displayed bicategory collapses by `isProp→PathP`.
-- ------------------------------------------------------------
module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  record PropStructureOverᴮ (ℓᴰ ℓᴰ' ℓᴰ'' : Level)
    : Type (ℓ-suc (ℓ-max (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
             (ℓ-max ℓᴰ (ℓ-max ℓᴰ' ℓᴰ'')))) where
    field
      ob[_] : B.ob → Type ℓᴰ
      1Cellᴰ[_][_,_] : {x y : B.ob}
        → B.1Cell x y → ob[ x ] → ob[ y ] → Type ℓᴰ'
      id₁ᴰ : ∀ {x} {xᴰ : ob[ x ]} → 1Cellᴰ[ B.id₁ ][ xᴰ , xᴰ ]
      _⋆₁ᴰ_ : ∀ {x y z} {f : B.1Cell x y} {g : B.1Cell y z}
        {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]}
        → 1Cellᴰ[ f ][ xᴰ , yᴰ ] → 1Cellᴰ[ g ][ yᴰ , zᴰ ]
        → 1Cellᴰ[ f B.⋆₁ g ][ xᴰ , zᴰ ]
      2Cellᴰ[_][_,_] : {x y : B.ob} {f g : B.1Cell x y}
        {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
        → B.2Cell f g
        → 1Cellᴰ[ f ][ xᴰ , yᴰ ] → 1Cellᴰ[ g ][ xᴰ , yᴰ ]
        → Type ℓᴰ''
      isProp2Cellᴰ : ∀ {x y} {f g : B.1Cell x y}
        {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {β : B.2Cell f g}
        {fᴰ : 1Cellᴰ[ f ][ xᴰ , yᴰ ]} {gᴰ : 1Cellᴰ[ g ][ xᴰ , yᴰ ]}
        → isProp (2Cellᴰ[ β ][ fᴰ , gᴰ ])
      id₂ᴰ : ∀ {x y} {f : B.1Cell x y}
        {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {fᴰ : 1Cellᴰ[ f ][ xᴰ , yᴰ ]}
        → 2Cellᴰ[ B.id₂ ][ fᴰ , fᴰ ]
      _⋆₂ᴰ_ : ∀ {x y} {f g h : B.1Cell x y}
        {β : B.2Cell f g} {γ : B.2Cell g h}
        {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
        {fᴰ : 1Cellᴰ[ f ][ xᴰ , yᴰ ]} {gᴰ : 1Cellᴰ[ g ][ xᴰ , yᴰ ]}
        {hᴰ : 1Cellᴰ[ h ][ xᴰ , yᴰ ]}
        → 2Cellᴰ[ β ][ fᴰ , gᴰ ] → 2Cellᴰ[ γ ][ gᴰ , hᴰ ]
        → 2Cellᴰ[ β B.⋆₂ γ ][ fᴰ , hᴰ ]
      _⊙ᴰ_ : ∀ {x y z} {f f' : B.1Cell x y} {g g' : B.1Cell y z}
        {β : B.2Cell f f'} {γ : B.2Cell g g'}
        {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]}
        {fᴰ : 1Cellᴰ[ f ][ xᴰ , yᴰ ]} {fᴰ' : 1Cellᴰ[ f' ][ xᴰ , yᴰ ]}
        {gᴰ : 1Cellᴰ[ g ][ yᴰ , zᴰ ]} {gᴰ' : 1Cellᴰ[ g' ][ yᴰ , zᴰ ]}
        → 2Cellᴰ[ β ][ fᴰ , fᴰ' ] → 2Cellᴰ[ γ ][ gᴰ , gᴰ' ]
        → 2Cellᴰ[ β B.⋆ₕ γ ][ fᴰ ⋆₁ᴰ gᴰ , fᴰ' ⋆₁ᴰ gᴰ' ]
      λ⁺ᴰ : ∀ {x y} {f : B.1Cell x y}
        {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} (fᴰ : 1Cellᴰ[ f ][ xᴰ , yᴰ ])
        → 2Cellᴰ[ B.λ⁺ f ][ id₁ᴰ ⋆₁ᴰ fᴰ , fᴰ ]
      λ⁻ᴰ : ∀ {x y} {f : B.1Cell x y}
        {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} (fᴰ : 1Cellᴰ[ f ][ xᴰ , yᴰ ])
        → 2Cellᴰ[ B.λ⁻ f ][ fᴰ , id₁ᴰ ⋆₁ᴰ fᴰ ]
      ρ⁺ᴰ : ∀ {x y} {f : B.1Cell x y}
        {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} (fᴰ : 1Cellᴰ[ f ][ xᴰ , yᴰ ])
        → 2Cellᴰ[ B.ρ⁺ f ][ fᴰ ⋆₁ᴰ id₁ᴰ , fᴰ ]
      ρ⁻ᴰ : ∀ {x y} {f : B.1Cell x y}
        {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} (fᴰ : 1Cellᴰ[ f ][ xᴰ , yᴰ ])
        → 2Cellᴰ[ B.ρ⁻ f ][ fᴰ , fᴰ ⋆₁ᴰ id₁ᴰ ]
      α⁺ᴰ : ∀ {x y z w}
        {f : B.1Cell x y} {g : B.1Cell y z} {h : B.1Cell z w}
        {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]} {wᴰ : ob[ w ]}
        (fᴰ : 1Cellᴰ[ f ][ xᴰ , yᴰ ]) (gᴰ : 1Cellᴰ[ g ][ yᴰ , zᴰ ])
        (hᴰ : 1Cellᴰ[ h ][ zᴰ , wᴰ ])
        → 2Cellᴰ[ B.α⁺ f g h ][ (fᴰ ⋆₁ᴰ gᴰ) ⋆₁ᴰ hᴰ , fᴰ ⋆₁ᴰ (gᴰ ⋆₁ᴰ hᴰ) ]
      α⁻ᴰ : ∀ {x y z w}
        {f : B.1Cell x y} {g : B.1Cell y z} {h : B.1Cell z w}
        {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]} {wᴰ : ob[ w ]}
        (fᴰ : 1Cellᴰ[ f ][ xᴰ , yᴰ ]) (gᴰ : 1Cellᴰ[ g ][ yᴰ , zᴰ ])
        (hᴰ : 1Cellᴰ[ h ][ zᴰ , wᴰ ])
        → 2Cellᴰ[ B.α⁻ f g h ][ fᴰ ⋆₁ᴰ (gᴰ ⋆₁ᴰ hᴰ) , (fᴰ ⋆₁ᴰ gᴰ) ⋆₁ᴰ hᴰ ]

    -- Transport along paths of base 2-cells is free (the predicate
    -- is prop-valued but the family is over a set).
    reind₂ : ∀ {x y} {f g : B.1Cell x y} {β γ : B.2Cell f g}
      {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
      {fᴰ : 1Cellᴰ[ f ][ xᴰ , yᴰ ]} {gᴰ : 1Cellᴰ[ g ][ xᴰ , yᴰ ]}
      → β ≡ γ → 2Cellᴰ[ β ][ fᴰ , gᴰ ] → 2Cellᴰ[ γ ][ fᴰ , gᴰ ]
    reind₂ {fᴰ = fᴰ} {gᴰ = gᴰ} p = subst 2Cellᴰ[_][ fᴰ , gᴰ ] p

module _ {B : Bicategory ℓ ℓ' ℓ''}
  (S : PropStructureOverᴮ B ℓᴰ ℓᴰ' ℓᴰ'') where
  private
    module B = Bicategory B
    module S = PropStructureOverᴮ S

    homStrᴾ : {x y : B.ob} (xᴰ : S.ob[ x ]) (yᴰ : S.ob[ y ])
      → StructureOver B.Hom[ x , y ] ℓᴰ' ℓᴰ''
    homStrᴾ xᴰ yᴰ .StructureOver.ob[_] f = S.1Cellᴰ[ f ][ xᴰ , yᴰ ]
    homStrᴾ xᴰ yᴰ .StructureOver.Hom[_][_,_] β fᴰ gᴰ =
      S.2Cellᴰ[ β ][ fᴰ , gᴰ ]
    homStrᴾ xᴰ yᴰ .StructureOver.idᴰ = S.id₂ᴰ
    homStrᴾ xᴰ yᴰ .StructureOver._⋆ᴰ_ = S._⋆₂ᴰ_
    homStrᴾ xᴰ yᴰ .StructureOver.isPropHomᴰ = S.isProp2Cellᴰ

  open Bicategoryᴰ

  PropStructureOverᴮ→Bicategoryᴰ : Bicategoryᴰ B ℓᴰ ℓᴰ' ℓᴰ''
  PropStructureOverᴮ→Bicategoryᴰ .ob[_] = S.ob[_]
  PropStructureOverᴮ→Bicategoryᴰ .Homᴰ[_,_] xᴰ yᴰ =
    StructureOver→Catᴰ (homStrᴾ xᴰ yᴰ)
  PropStructureOverᴮ→Bicategoryᴰ .idᴰ .F-obᴰ _ = S.id₁ᴰ
  PropStructureOverᴮ→Bicategoryᴰ .idᴰ {x} .F-homᴰ {f = t} _ =
    S.reind₂
      ( sym (Functor.F-id (B.id {x}))
      ∙ cong (Functor.F-hom (B.id {x})) (isOfHLevelUnit* 2 _ _ refl t))
      S.id₂ᴰ
  PropStructureOverᴮ→Bicategoryᴰ .idᴰ .F-idᴰ =
    isProp→PathP (λ i → S.isProp2Cellᴰ) _ _
  PropStructureOverᴮ→Bicategoryᴰ .idᴰ .F-seqᴰ _ _ =
    isProp→PathP (λ i → S.isProp2Cellᴰ) _ _
  PropStructureOverᴮ→Bicategoryᴰ .seqᴰ _ _ _ .F-obᴰ (fᴰ , gᴰ) =
    fᴰ S.⋆₁ᴰ gᴰ
  PropStructureOverᴮ→Bicategoryᴰ .seqᴰ _ _ _ .F-homᴰ (βᴾ , γᴾ) =
    βᴾ S.⊙ᴰ γᴾ
  PropStructureOverᴮ→Bicategoryᴰ .seqᴰ _ _ _ .F-idᴰ =
    isProp→PathP (λ i → S.isProp2Cellᴰ) _ _
  PropStructureOverᴮ→Bicategoryᴰ .seqᴰ _ _ _ .F-seqᴰ _ _ =
    isProp→PathP (λ i → S.isProp2Cellᴰ) _ _
  PropStructureOverᴮ→Bicategoryᴰ .λUᴰ _ _ .transᴰ .N-obᴰ (_ , fᴰ) =
    S.λ⁺ᴰ fᴰ
  PropStructureOverᴮ→Bicategoryᴰ .λUᴰ _ _ .transᴰ .N-homᴰ _ =
    isProp→PathP (λ i → S.isProp2Cellᴰ) _ _
  PropStructureOverᴮ→Bicategoryᴰ .λUᴰ _ _ .nIsoᴰ (_ , fᴰ) =
    isisoᴰ (S.λ⁻ᴰ fᴰ)
      (isProp→PathP (λ i → S.isProp2Cellᴰ) _ _)
      (isProp→PathP (λ i → S.isProp2Cellᴰ) _ _)
  PropStructureOverᴮ→Bicategoryᴰ .ρUᴰ _ _ .transᴰ .N-obᴰ (fᴰ , _) =
    S.ρ⁺ᴰ fᴰ
  PropStructureOverᴮ→Bicategoryᴰ .ρUᴰ _ _ .transᴰ .N-homᴰ _ =
    isProp→PathP (λ i → S.isProp2Cellᴰ) _ _
  PropStructureOverᴮ→Bicategoryᴰ .ρUᴰ _ _ .nIsoᴰ (fᴰ , _) =
    isisoᴰ (S.ρ⁻ᴰ fᴰ)
      (isProp→PathP (λ i → S.isProp2Cellᴰ) _ _)
      (isProp→PathP (λ i → S.isProp2Cellᴰ) _ _)
  PropStructureOverᴮ→Bicategoryᴰ .αᴰ _ _ _ _ .transᴰ .N-obᴰ
    (fᴰ , gᴰ , hᴰ) = S.α⁺ᴰ fᴰ gᴰ hᴰ
  PropStructureOverᴮ→Bicategoryᴰ .αᴰ _ _ _ _ .transᴰ .N-homᴰ _ =
    isProp→PathP (λ i → S.isProp2Cellᴰ) _ _
  PropStructureOverᴮ→Bicategoryᴰ .αᴰ _ _ _ _ .nIsoᴰ (fᴰ , gᴰ , hᴰ) =
    isisoᴰ (S.α⁻ᴰ fᴰ gᴰ hᴰ)
      (isProp→PathP (λ i → S.isProp2Cellᴰ) _ _)
      (isProp→PathP (λ i → S.isProp2Cellᴰ) _ _)
  PropStructureOverᴮ→Bicategoryᴰ .triangleᴰ _ _ =
    isProp→PathP (λ i → S.isProp2Cellᴰ) _ _
  PropStructureOverᴮ→Bicategoryᴰ .pentagonᴰ _ _ _ _ =
    isProp→PathP (λ i → S.isProp2Cellᴰ) _ _
