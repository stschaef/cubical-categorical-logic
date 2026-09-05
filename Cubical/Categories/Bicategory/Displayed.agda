{-# OPTIONS --lossy-unification #-}
{- Bicategories displayed over a base bicategory -}
module Cubical.Categories.Bicategory.Displayed where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Terminal

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.BinProduct.More
  hiding (introF)
open import Cubical.Categories.Displayed.Instances.Terminal

open import Cubical.Categories.Bicategory.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

open Functor
open Functorᴰ
open NatTrans
open NatIso
open NatTransᴰ
open NatIsoᴰ
open isIsoᴰ

module _ {ℓ ℓ' ℓ'' : Level} (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  record Bicategoryᴰ (ℓᴰ ℓᴰ' ℓᴰ'' : Level)
    : Type (ℓ-max (ℓ-max ℓ (ℓ-suc ℓᴰ))
             (ℓ-suc (ℓ-max (ℓ-max ℓ' ℓ'') (ℓ-max ℓᴰ' ℓᴰ'')))) where
    no-eta-equality
    field
      ob[_] : B.ob → Type ℓᴰ
      Homᴰ[_,_] : {x y : B.ob} → ob[ x ] → ob[ y ]
        → Categoryᴰ B.Hom[ x , y ] ℓᴰ' ℓᴰ''

      idᴰ : ∀ {x : B.ob} {xᴰ : ob[ x ]}
        → Functorᴰ (B.id {x}) UnitCᴰ Homᴰ[ xᴰ , xᴰ ]
      seqᴰ : ∀ {x y z : B.ob} (xᴰ : ob[ x ]) (yᴰ : ob[ y ]) (zᴰ : ob[ z ])
        → Functorᴰ (B.seq x y z)
            (Homᴰ[ xᴰ , yᴰ ] ×Cᴰ Homᴰ[ yᴰ , zᴰ ])
            Homᴰ[ xᴰ , zᴰ ]

    -- ------------------------------------------------------------
    -- Displayed cells and basic operations
    -- ------------------------------------------------------------

    0Cellᴰ : B.0Cell → Type ℓᴰ
    0Cellᴰ = ob[_]

    1Cellᴰ : ∀ {x y} (xᴰ : ob[ x ]) (yᴰ : ob[ y ])
      → B.1Cell x y → Type ℓᴰ'
    1Cellᴰ xᴰ yᴰ f = Categoryᴰ.ob[_] Homᴰ[ xᴰ , yᴰ ] f

    2Cellᴰ : ∀ {x y} {f g : B.1Cell x y} {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
      → 1Cellᴰ xᴰ yᴰ f → 1Cellᴰ xᴰ yᴰ g → B.2Cell f g → Type ℓᴰ''
    2Cellᴰ {xᴰ = xᴰ} {yᴰ = yᴰ} fᴰ gᴰ β = Homᴰ[ xᴰ , yᴰ ] [ β ][ fᴰ , gᴰ ]

    -- Horizontal composition of displayed 1-cells.
    _⋆₁ᴰ_ : ∀ {x y z} {f : B.1Cell x y} {g : B.1Cell y z}
      {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]}
      → 1Cellᴰ xᴰ yᴰ f → 1Cellᴰ yᴰ zᴰ g → 1Cellᴰ xᴰ zᴰ (f B.⋆₁ g)
    _⋆₁ᴰ_ fᴰ gᴰ = seqᴰ _ _ _ .F-obᴰ (fᴰ , gᴰ)
    infixr 9 _⋆₁ᴰ_

    -- Displayed identity 1-cell.
    id₁ᴰ : ∀ {x} {xᴰ : ob[ x ]} → 1Cellᴰ xᴰ xᴰ B.id₁
    id₁ᴰ = idᴰ .F-obᴰ tt

    -- Displayed identity 2-cell.
    id₂ᴰ : ∀ {x y} {f : B.1Cell x y} {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
      {fᴰ : 1Cellᴰ xᴰ yᴰ f} → 2Cellᴰ fᴰ fᴰ B.id₂
    id₂ᴰ {xᴰ = xᴰ} {yᴰ = yᴰ} = Categoryᴰ.idᴰ Homᴰ[ xᴰ , yᴰ ]

    -- Vertical composition of displayed 2-cells.
    _⋆₂ᴰ_ : ∀ {x y} {f g h : B.1Cell x y}
      {β : B.2Cell f g} {γ : B.2Cell g h}
      {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
      {fᴰ : 1Cellᴰ xᴰ yᴰ f} {gᴰ : 1Cellᴰ xᴰ yᴰ g} {hᴰ : 1Cellᴰ xᴰ yᴰ h}
      → 2Cellᴰ fᴰ gᴰ β → 2Cellᴰ gᴰ hᴰ γ → 2Cellᴰ fᴰ hᴰ (β B.⋆₂ γ)
    _⋆₂ᴰ_ {xᴰ = xᴰ} {yᴰ = yᴰ} = Categoryᴰ._⋆ᴰ_ Homᴰ[ xᴰ , yᴰ ]
    infixr 9 _⋆₂ᴰ_

    ⋆₂ᴰAssoc : ∀ {x y} {f g h k : B.1Cell x y}
      {β : B.2Cell f g} {γ : B.2Cell g h} {δ : B.2Cell h k}
      {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
      {fᴰ : 1Cellᴰ xᴰ yᴰ f} {gᴰ : 1Cellᴰ xᴰ yᴰ g}
      {hᴰ : 1Cellᴰ xᴰ yᴰ h} {kᴰ : 1Cellᴰ xᴰ yᴰ k}
      (βᴰ : 2Cellᴰ fᴰ gᴰ β) (γᴰ : 2Cellᴰ gᴰ hᴰ γ) (δᴰ : 2Cellᴰ hᴰ kᴰ δ)
      → PathP (λ i → 2Cellᴰ fᴰ kᴰ (B.⋆₂Assoc β γ δ i))
          ((βᴰ ⋆₂ᴰ γᴰ) ⋆₂ᴰ δᴰ) (βᴰ ⋆₂ᴰ (γᴰ ⋆₂ᴰ δᴰ))
    ⋆₂ᴰAssoc {xᴰ = xᴰ} {yᴰ = yᴰ} = Categoryᴰ.⋆Assocᴰ Homᴰ[ xᴰ , yᴰ ]

    -- Left whiskering.
    _◁wᴰ_ : ∀ {x y z} {f : B.1Cell x y} {g h : B.1Cell y z}
      {β : B.2Cell g h}
      {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]}
      (fᴰ : 1Cellᴰ xᴰ yᴰ f) {gᴰ : 1Cellᴰ yᴰ zᴰ g} {hᴰ : 1Cellᴰ yᴰ zᴰ h}
      → 2Cellᴰ gᴰ hᴰ β → 2Cellᴰ (fᴰ ⋆₁ᴰ gᴰ) (fᴰ ⋆₁ᴰ hᴰ) (f B.◁w β)
    _◁wᴰ_ fᴰ βᴰ = seqᴰ _ _ _ .F-homᴰ (id₂ᴰ , βᴰ)

    -- Right whiskering.
    _▷wᴰ_ : ∀ {x y z} {f g : B.1Cell x y} {h : B.1Cell y z}
      {β : B.2Cell f g}
      {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]}
      {fᴰ : 1Cellᴰ xᴰ yᴰ f} {gᴰ : 1Cellᴰ xᴰ yᴰ g}
      → 2Cellᴰ fᴰ gᴰ β → (hᴰ : 1Cellᴰ yᴰ zᴰ h)
      → 2Cellᴰ (fᴰ ⋆₁ᴰ hᴰ) (gᴰ ⋆₁ᴰ hᴰ) (β B.▷w h)
    _▷wᴰ_ βᴰ hᴰ = seqᴰ _ _ _ .F-homᴰ (βᴰ , id₂ᴰ)

    -- ------------------------------------------------------------
    -- Displayed source and target functors for the unitor and
    -- associator NatIsoᴰs, mirroring the (private) base functors.
    -- ------------------------------------------------------------
    private
      LUᴰ-src : ∀ {x y} (xᴰ : ob[ x ]) (yᴰ : ob[ y ])
        → Functorᴰ (B.seq x x y ∘F (B.id {x} ×F 𝟙⟨ B.Hom[ x , y ] ⟩))
            (UnitCᴰ ×Cᴰ Homᴰ[ xᴰ , yᴰ ]) Homᴰ[ xᴰ , yᴰ ]
      LUᴰ-src xᴰ yᴰ = seqᴰ xᴰ xᴰ yᴰ ∘Fᴰ (idᴰ ×Fᴰ 𝟙ᴰ⟨ Homᴰ[ xᴰ , yᴰ ] ⟩)

      LUᴰ-tgt : ∀ {x y} (xᴰ : ob[ x ]) (yᴰ : ob[ y ])
        → Functorᴰ (Snd 𝟙C B.Hom[ x , y ])
            (UnitCᴰ ×Cᴰ Homᴰ[ xᴰ , yᴰ ]) Homᴰ[ xᴰ , yᴰ ]
      LUᴰ-tgt xᴰ yᴰ = Sndᴰ UnitCᴰ Homᴰ[ xᴰ , yᴰ ]

      RUᴰ-src : ∀ {x y} (xᴰ : ob[ x ]) (yᴰ : ob[ y ])
        → Functorᴰ (B.seq x y y ∘F (𝟙⟨ B.Hom[ x , y ] ⟩ ×F B.id {y}))
            (Homᴰ[ xᴰ , yᴰ ] ×Cᴰ UnitCᴰ) Homᴰ[ xᴰ , yᴰ ]
      RUᴰ-src xᴰ yᴰ = seqᴰ xᴰ yᴰ yᴰ ∘Fᴰ (𝟙ᴰ⟨ Homᴰ[ xᴰ , yᴰ ] ⟩ ×Fᴰ idᴰ)

      RUᴰ-tgt : ∀ {x y} (xᴰ : ob[ x ]) (yᴰ : ob[ y ])
        → Functorᴰ (Fst B.Hom[ x , y ] 𝟙C)
            (Homᴰ[ xᴰ , yᴰ ] ×Cᴰ UnitCᴰ) Homᴰ[ xᴰ , yᴰ ]
      RUᴰ-tgt xᴰ yᴰ = Fstᴰ Homᴰ[ xᴰ , yᴰ ] UnitCᴰ

      Aᴰ-src : ∀ {x y z w}
        (xᴰ : ob[ x ]) (yᴰ : ob[ y ]) (zᴰ : ob[ z ]) (wᴰ : ob[ w ])
        → Functorᴰ
            (B.seq x z w
              ∘F (B.seq x y z ×F 𝟙⟨ B.Hom[ z , w ] ⟩)
              ∘F ×C-assoc B.Hom[ x , y ] B.Hom[ y , z ] B.Hom[ z , w ])
            (Homᴰ[ xᴰ , yᴰ ] ×Cᴰ (Homᴰ[ yᴰ , zᴰ ] ×Cᴰ Homᴰ[ zᴰ , wᴰ ]))
            Homᴰ[ xᴰ , wᴰ ]
      Aᴰ-src xᴰ yᴰ zᴰ wᴰ =
        seqᴰ xᴰ zᴰ wᴰ
        ∘Fᴰ ((seqᴰ xᴰ yᴰ zᴰ ×Fᴰ 𝟙ᴰ⟨ Homᴰ[ zᴰ , wᴰ ] ⟩)
        ∘Fᴰ ×Cᴰ-assoc Homᴰ[ xᴰ , yᴰ ] Homᴰ[ yᴰ , zᴰ ] Homᴰ[ zᴰ , wᴰ ])

      Aᴰ-tgt : ∀ {x y z w}
        (xᴰ : ob[ x ]) (yᴰ : ob[ y ]) (zᴰ : ob[ z ]) (wᴰ : ob[ w ])
        → Functorᴰ (B.seq x y w ∘F (𝟙⟨ B.Hom[ x , y ] ⟩ ×F B.seq y z w))
            (Homᴰ[ xᴰ , yᴰ ] ×Cᴰ (Homᴰ[ yᴰ , zᴰ ] ×Cᴰ Homᴰ[ zᴰ , wᴰ ]))
            Homᴰ[ xᴰ , wᴰ ]
      Aᴰ-tgt xᴰ yᴰ zᴰ wᴰ =
        seqᴰ xᴰ yᴰ wᴰ ∘Fᴰ (𝟙ᴰ⟨ Homᴰ[ xᴰ , yᴰ ] ⟩ ×Fᴰ seqᴰ yᴰ zᴰ wᴰ)

    field
      λUᴰ : ∀ {x y} (xᴰ : ob[ x ]) (yᴰ : ob[ y ])
        → NatIsoᴰ (B.λU x y) (LUᴰ-src xᴰ yᴰ) (LUᴰ-tgt xᴰ yᴰ)
      ρUᴰ : ∀ {x y} (xᴰ : ob[ x ]) (yᴰ : ob[ y ])
        → NatIsoᴰ (B.ρU x y) (RUᴰ-src xᴰ yᴰ) (RUᴰ-tgt xᴰ yᴰ)
      αᴰ : ∀ {x y z w}
        (xᴰ : ob[ x ]) (yᴰ : ob[ y ]) (zᴰ : ob[ z ]) (wᴰ : ob[ w ])
        → NatIsoᴰ (B.α x y z w) (Aᴰ-src xᴰ yᴰ zᴰ wᴰ) (Aᴰ-tgt xᴰ yᴰ zᴰ wᴰ)

    -- ------------------------------------------------------------
    -- Component 2-cells of the displayed unitors and associator.
    -- ------------------------------------------------------------

    λ⁺ᴰ : ∀ {x y} {f : B.1Cell x y} {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
      (fᴰ : 1Cellᴰ xᴰ yᴰ f)
      → 2Cellᴰ (id₁ᴰ ⋆₁ᴰ fᴰ) fᴰ (B.λ⁺ f)
    λ⁺ᴰ fᴰ = λUᴰ _ _ .transᴰ .N-obᴰ (tt , fᴰ)

    λ⁻ᴰ : ∀ {x y} {f : B.1Cell x y} {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
      (fᴰ : 1Cellᴰ xᴰ yᴰ f)
      → 2Cellᴰ fᴰ (id₁ᴰ ⋆₁ᴰ fᴰ) (B.λ⁻ f)
    λ⁻ᴰ fᴰ = λUᴰ _ _ .nIsoᴰ (tt , fᴰ) .invᴰ

    ρ⁺ᴰ : ∀ {x y} {f : B.1Cell x y} {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
      (fᴰ : 1Cellᴰ xᴰ yᴰ f)
      → 2Cellᴰ (fᴰ ⋆₁ᴰ id₁ᴰ) fᴰ (B.ρ⁺ f)
    ρ⁺ᴰ fᴰ = ρUᴰ _ _ .transᴰ .N-obᴰ (fᴰ , tt)

    ρ⁻ᴰ : ∀ {x y} {f : B.1Cell x y} {xᴰ : ob[ x ]} {yᴰ : ob[ y ]}
      (fᴰ : 1Cellᴰ xᴰ yᴰ f)
      → 2Cellᴰ fᴰ (fᴰ ⋆₁ᴰ id₁ᴰ) (B.ρ⁻ f)
    ρ⁻ᴰ fᴰ = ρUᴰ _ _ .nIsoᴰ (fᴰ , tt) .invᴰ

    α⁺ᴰ : ∀ {x y z w}
      {f : B.1Cell x y} {g : B.1Cell y z} {h : B.1Cell z w}
      {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]} {wᴰ : ob[ w ]}
      (fᴰ : 1Cellᴰ xᴰ yᴰ f) (gᴰ : 1Cellᴰ yᴰ zᴰ g) (hᴰ : 1Cellᴰ zᴰ wᴰ h)
      → 2Cellᴰ ((fᴰ ⋆₁ᴰ gᴰ) ⋆₁ᴰ hᴰ) (fᴰ ⋆₁ᴰ (gᴰ ⋆₁ᴰ hᴰ)) (B.α⁺ f g h)
    α⁺ᴰ fᴰ gᴰ hᴰ = αᴰ _ _ _ _ .transᴰ .N-obᴰ (fᴰ , gᴰ , hᴰ)

    α⁻ᴰ : ∀ {x y z w}
      {f : B.1Cell x y} {g : B.1Cell y z} {h : B.1Cell z w}
      {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]} {wᴰ : ob[ w ]}
      (fᴰ : 1Cellᴰ xᴰ yᴰ f) (gᴰ : 1Cellᴰ yᴰ zᴰ g) (hᴰ : 1Cellᴰ zᴰ wᴰ h)
      → 2Cellᴰ (fᴰ ⋆₁ᴰ (gᴰ ⋆₁ᴰ hᴰ)) ((fᴰ ⋆₁ᴰ gᴰ) ⋆₁ᴰ hᴰ) (B.α⁻ f g h)
    α⁻ᴰ fᴰ gᴰ hᴰ = αᴰ _ _ _ _ .nIsoᴰ (fᴰ , gᴰ , hᴰ) .invᴰ

    field
      -- Triangle over B.triangle.
      triangleᴰ : ∀ {x y z} {f : B.1Cell x y} {g : B.1Cell y z}
        {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]}
        (fᴰ : 1Cellᴰ xᴰ yᴰ f) (gᴰ : 1Cellᴰ yᴰ zᴰ g)
        → PathP
            (λ i → 2Cellᴰ ((fᴰ ⋆₁ᴰ id₁ᴰ) ⋆₁ᴰ gᴰ) (fᴰ ⋆₁ᴰ gᴰ)
                     (B.triangle x y z f g i))
            (α⁺ᴰ fᴰ id₁ᴰ gᴰ ⋆₂ᴰ (fᴰ ◁wᴰ λ⁺ᴰ gᴰ))
            (ρ⁺ᴰ fᴰ ▷wᴰ gᴰ)

      -- Pentagon over B.pentagon.
      pentagonᴰ : ∀ {x y z w v}
        {f : B.1Cell x y} {g : B.1Cell y z}
        {h : B.1Cell z w} {k : B.1Cell w v}
        {xᴰ : ob[ x ]} {yᴰ : ob[ y ]} {zᴰ : ob[ z ]}
        {wᴰ : ob[ w ]} {vᴰ : ob[ v ]}
        (fᴰ : 1Cellᴰ xᴰ yᴰ f) (gᴰ : 1Cellᴰ yᴰ zᴰ g)
        (hᴰ : 1Cellᴰ zᴰ wᴰ h) (kᴰ : 1Cellᴰ wᴰ vᴰ k)
        → PathP
            (λ i → 2Cellᴰ (((fᴰ ⋆₁ᴰ gᴰ) ⋆₁ᴰ hᴰ) ⋆₁ᴰ kᴰ)
                     (fᴰ ⋆₁ᴰ (gᴰ ⋆₁ᴰ (hᴰ ⋆₁ᴰ kᴰ)))
                     (B.pentagon x y z w v f g h k i))
            ((α⁺ᴰ fᴰ gᴰ hᴰ ▷wᴰ kᴰ)
              ⋆₂ᴰ α⁺ᴰ fᴰ (gᴰ ⋆₁ᴰ hᴰ) kᴰ
              ⋆₂ᴰ (fᴰ ◁wᴰ α⁺ᴰ gᴰ hᴰ kᴰ))
            (α⁺ᴰ (fᴰ ⋆₁ᴰ gᴰ) hᴰ kᴰ ⋆₂ᴰ α⁺ᴰ fᴰ gᴰ (hᴰ ⋆₁ᴰ kᴰ))

  -- ------------------------------------------------------------
  -- The terminal displayed bicategory over any base, as an
  -- inhabitation check: everything is Unit, all laws are refl.
  -- ------------------------------------------------------------
  open Bicategoryᴰ

  Unitᴮᴰ : Bicategoryᴰ ℓ-zero ℓ-zero ℓ-zero
  Unitᴮᴰ .ob[_] _ = Unit
  Unitᴮᴰ .Homᴰ[_,_] {x} {y} _ _ = Unitᴰ B.Hom[ x , y ]
  Unitᴮᴰ .idᴰ {x} = introF (B.id {x})
  Unitᴮᴰ .seqᴰ {x} {y} {z} _ _ _ = introF (B.seq x y z)
  Unitᴮᴰ .λUᴰ _ _ .transᴰ .N-obᴰ _ = tt
  Unitᴮᴰ .λUᴰ _ _ .transᴰ .N-homᴰ _ = refl
  Unitᴮᴰ .λUᴰ _ _ .nIsoᴰ _ = isisoᴰ tt refl refl
  Unitᴮᴰ .ρUᴰ _ _ .transᴰ .N-obᴰ _ = tt
  Unitᴮᴰ .ρUᴰ _ _ .transᴰ .N-homᴰ _ = refl
  Unitᴮᴰ .ρUᴰ _ _ .nIsoᴰ _ = isisoᴰ tt refl refl
  Unitᴮᴰ .αᴰ _ _ _ _ .transᴰ .N-obᴰ _ = tt
  Unitᴮᴰ .αᴰ _ _ _ _ .transᴰ .N-homᴰ _ = refl
  Unitᴮᴰ .αᴰ _ _ _ _ .nIsoᴰ _ = isisoᴰ tt refl refl
  Unitᴮᴰ .triangleᴰ _ _ = refl
  Unitᴮᴰ .pentagonᴰ _ _ _ _ = refl
