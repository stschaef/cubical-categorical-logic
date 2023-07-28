{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Limits.BinProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma renaming (_×_ to _×Type_)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Presheaf

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD') where
  module D = Categoryᴰ D
  BinProductᴰ : ∀ {c12} → BinProduct' C c12
              → (D.ob[ c12 .fst ] ×Type D.ob[ c12 .snd ])
              → Type _
  BinProductᴰ = RightAdjointAtᴰ (ΔCᴰ D)

  BinProductsᴰ : BinProducts' C → Type _
  BinProductsᴰ = RightAdjointᴰ (ΔCᴰ D)

  FibBinProductsAtᴰ : ∀ {c} → (D.ob[ c ] ×Type D.ob[ c ]) → Type _
  FibBinProductsAtᴰ = LocalRightAdjointAtᴰ (Δᴰ D)

  FibBinProductsᴰ : Type _
  FibBinProductsᴰ = LocalRightAdjointᴰ (Δᴰ D)

  module BinProductsᴰNotation (bp : BinProducts' C) (bpᴰ : BinProductsᴰ bp)
    where
    open Notation C (RightAdjoint'ToBinProducts C bp)
    open UniversalElementᴰ

    _×ᴰ_ : ∀ {x y : C .ob} → D.ob[ x ] → D.ob[ y ] → D.ob[ x × y ]
    xᴰ ×ᴰ yᴰ = bpᴰ (xᴰ , yᴰ) .vertexᴰ

    π₁ᴰ : ∀ {x y : C .ob} {xᴰ : D.ob[ x ]}{yᴰ : D.ob[ y ]}
        → D [ π₁ ][ xᴰ ×ᴰ yᴰ , xᴰ ]
    π₁ᴰ {xᴰ = xᴰ}{yᴰ} = bpᴰ (xᴰ , yᴰ) .elementᴰ .fst

    π₂ᴰ : ∀ {x y : C .ob} {xᴰ : D.ob[ x ]}{yᴰ : D.ob[ y ]}
        → D [ π₂ ][ xᴰ ×ᴰ yᴰ , yᴰ ]
    π₂ᴰ {xᴰ = xᴰ}{yᴰ} = bpᴰ (xᴰ , yᴰ) .elementᴰ .snd

    _,ᴰ_ : ∀ {w x y : C .ob} {wᴰ : D.ob[ w ]}{xᴰ : D.ob[ x ]}{yᴰ : D.ob[ y ]}
         → {f : C [ w , x ]} {g : C [ w , y ]}
         → (fᴰ : D [ f ][ wᴰ , xᴰ ]) (gᴰ : D [ g ][ wᴰ , yᴰ ])
         → D [ f ,p g ][ wᴰ , xᴰ ×ᴰ yᴰ ]
    _,ᴰ_ {wᴰ = wᴰ}{xᴰ}{yᴰ}{f}{g} fᴰ gᴰ = invIsEq (bpᴰ _ .universalᴰ _)
      ( transport (λ i → D [ ×β₁ {f = f}{g = g} (~ i) ][ wᴰ , xᴰ ]) fᴰ
      , transport (λ i → D [ ×β₂ {f = f}{g = g} (~ i) ][ wᴰ , yᴰ ]) gᴰ)

    private
      ×β-raw : ∀ {w x y : C .ob} {wᴰ : D.ob[ w ]}{xᴰ : D.ob[ x ]}{yᴰ : D.ob[ y ]}
         → {f : C [ w , x ]} {g : C [ w , y ]}
         → {fᴰ : D [ f ][ wᴰ , xᴰ ]} {gᴰ : D [ g ][ wᴰ , yᴰ ]}
         → _
      ×β-raw {wᴰ = wᴰ}{xᴰ}{yᴰ}{f = f}{g = g}{fᴰ = fᴰ}{gᴰ = gᴰ} =
        secIsEq (bpᴰ _ .universalᴰ _)
        ( transport (λ i → D [ ×β₁ {f = f}{g = g} (~ i) ][ wᴰ , xᴰ ]) fᴰ
        , transport (λ i → D [ ×β₂ {f = f}{g = g} (~ i) ][ wᴰ , yᴰ ]) gᴰ)
        
    ×β₁ᴰ : ∀ {w x y : C .ob} {wᴰ : D.ob[ w ]}{xᴰ : D.ob[ x ]}{yᴰ : D.ob[ y ]}
         → {f : C [ w , x ]} {g : C [ w , y ]}
         → {fᴰ : D [ f ][ wᴰ , xᴰ ]} {gᴰ : D [ g ][ wᴰ , yᴰ ]}
         → (fᴰ ,ᴰ gᴰ) D.⋆ᴰ π₁ᴰ D.≡[ ×β₁ ] fᴰ
    ×β₁ᴰ {wᴰ = wᴰ}{xᴰ}{yᴰ}{f = f}{g = g}{fᴰ = fᴰ}{gᴰ = gᴰ} =
      (symP (toPathP (symP (congP (λ _ → fst) ×β-raw))))

    ×β₂ᴰ : ∀ {w x y : C .ob} {wᴰ : D.ob[ w ]}{xᴰ : D.ob[ x ]}{yᴰ : D.ob[ y ]}
         → {f : C [ w , x ]} {g : C [ w , y ]}
         → {fᴰ : D [ f ][ wᴰ , xᴰ ]} {gᴰ : D [ g ][ wᴰ , yᴰ ]}
         → (fᴰ ,ᴰ gᴰ) D.⋆ᴰ π₂ᴰ D.≡[ ×β₂ ] gᴰ
    ×β₂ᴰ {wᴰ = wᴰ}{xᴰ}{yᴰ}{f = f}{g = g}{fᴰ = fᴰ}{gᴰ = gᴰ} =
      (symP (toPathP (symP (congP (λ _ → snd) ×β-raw))))
          
