{-# OPTIONS --safe  --lossy-unification #-}
module Cubical.Categories.Displayed.Limits.BinProduct.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.FunctorComprehension
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions
open import Cubical.Categories.Displayed.Profunctor
open import Cubical.Categories.Displayed.Instances.Sets.Base
import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open UniversalElement
open UniversalElementᴰ
open UniversalElementⱽ
open isIsoOver

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓD ℓD') where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
    module R = HomᴰReasoning Cᴰ

  BinProductᴰ : ∀ {c12} → BinProduct' C c12
              → (Cᴰ.ob[ c12 .fst ] × Cᴰ.ob[ c12 .snd ])
              → Type _
  BinProductᴰ = RightAdjointAtᴰ (ΔCᴰ Cᴰ)

  hasAllBinProductᴰ : BinProducts' C → Type _
  hasAllBinProductᴰ = RightAdjointᴰ (ΔCᴰ Cᴰ)

  open Functorᴰ
  ProdWithAProfᴰ : ∀ {c} → Cᴰ.ob[ c ]
    → Profunctorᴰ (ProdWithAProf C c) Cᴰ Cᴰ ℓD'
  ProdWithAProfᴰ cᴰ = appLᴰ PshProdᴰ (YOᴰ .F-obᴰ cᴰ) ∘Fᴰ YOᴰ

  hasAllBinProductWithᴰ : ∀ {c} → hasAllBinProductWith C c → Cᴰ.ob[ c ]
    → Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD')
  hasAllBinProductWithᴰ c×- cᴰ = UniversalElementsᴰ c×- (ProdWithAProfᴰ cᴰ)

  a×-Fᴰ : ∀ {c}  {c×- : hasAllBinProductWith C c}
            {cᴰ} (cᴰ×ᴰ- : hasAllBinProductWithᴰ c×- cᴰ)
          → Functorᴰ (a×-F C c×-) Cᴰ Cᴰ
  a×-Fᴰ {cᴰ = cᴰ} cᴰ×ᴰ- = FunctorᴰComprehension {Pᴰ = ProdWithAProfᴰ cᴰ} cᴰ×ᴰ-

  BinProductⱽ : ∀ {c} → (Cᴰ.ob[ c ] × Cᴰ.ob[ c ]) → Type _
  BinProductⱽ = VerticalRightAdjointAtᴰ (Δᴰ Cᴰ)

  hasAllBinProductⱽ : Type _
  hasAllBinProductⱽ = VerticalRightAdjointᴰ (Δᴰ Cᴰ)

module hasAllBinProductᴰNotation
         {C : Category ℓC ℓC'}
         {Cᴰ : Categoryᴰ C ℓD ℓD'}
         {bp' : BinProducts' C}
         (bpᴰ : hasAllBinProductᴰ Cᴰ bp')
       where

  private
    module BP = BinProducts'Notation bp'
    module Cᴰ = Categoryᴰ Cᴰ
    module R = HomᴰReasoning Cᴰ

  open BP

  private
    variable
      c c' c₁ c₂ : C .ob
      d d' d₁ d₂ : Cᴰ.ob[ c ]

  _×ᴰ_ : Cᴰ.ob[ c₁ ] → Cᴰ.ob[ c₂ ] → Cᴰ.ob[ c₁ BP.× c₂ ]
  _×ᴰ_ d₁ d₂ = bpᴰ (d₁ , d₂) .vertexᴰ

  module _ {c₁ c₂} {d₁ : Cᴰ.ob[ c₁ ]} {d₂ : Cᴰ.ob[ c₂ ]} where

    π₁ᴰ : Cᴰ.Hom[ π₁ ][ d₁ ×ᴰ d₂ , d₁ ]
    π₁ᴰ = bpᴰ (d₁ , d₂) .elementᴰ .fst

    π₂ᴰ : Cᴰ.Hom[ π₂ ][ d₁ ×ᴰ d₂ , d₂ ]
    π₂ᴰ = bpᴰ (d₁ , d₂) .elementᴰ .snd

    _,pᴰ_ : {f₁ : C [ c , c₁ ]}{f₂ : C [ c , c₂ ]}
          → Cᴰ.Hom[ f₁ ][ d , d₁ ] → Cᴰ.Hom[ f₂ ][ d , d₂ ]
          → Cᴰ.Hom[ f₁ ,p f₂ ][ d , d₁ ×ᴰ d₂ ]
    _,pᴰ_{f₁ = f₁}{f₂ = f₂} f₁ᴰ f₂ᴰ =
      UniversalElementᴰNotation.introᴰ _ _ (bpᴰ (d₁ , d₂)) _ (f₁ᴰ , f₂ᴰ)

    module _ {f₁ : C [ c , c₁ ]}{f₂ : C [ c , c₂ ]}
             {f₁ᴰ : Cᴰ.Hom[ f₁ ][ d , d₁ ]}
             {f₂ᴰ : Cᴰ.Hom[ f₂ ][ d , d₂ ]}
           where
      open isIsoOver
      private
        ,pᴰ-isUniversalᴰ = bpᴰ (d₁ , d₂) .universalᴰ {xᴰ = d}
      opaque
        unfolding UniversalElementᴰNotation.βᴰ
        ×β₁ᴰ : ((f₁ᴰ ,pᴰ f₂ᴰ) Cᴰ.⋆ᴰ π₁ᴰ) Cᴰ.≡[ ×β₁ ] f₁ᴰ
        ×β₁ᴰ = λ i → UniversalElementᴰNotation.βᴰ _ _
          (bpᴰ (d₁ , d₂)) {pᴰ = (f₁ᴰ , f₂ᴰ)} i .fst

        ×β₂ᴰ : ((f₁ᴰ ,pᴰ f₂ᴰ) Cᴰ.⋆ᴰ π₂ᴰ) Cᴰ.≡[ ×β₂ ] f₂ᴰ
        ×β₂ᴰ = λ i → UniversalElementᴰNotation.βᴰ _ _
          (bpᴰ (d₁ , d₂)) {pᴰ = (f₁ᴰ , f₂ᴰ)} i .snd

    module _ {f : C [ c , c₁ BP.× c₂ ]}
             {fᴰ : Cᴰ.Hom[ f ][ d , d₁ ×ᴰ d₂ ]}
           where
      opaque
        unfolding UniversalElementᴰNotation.ηᴰ
        ×ηᴰ : fᴰ Cᴰ.≡[ ×η ] ((fᴰ Cᴰ.⋆ᴰ π₁ᴰ) ,pᴰ (fᴰ Cᴰ.⋆ᴰ π₂ᴰ))
        ×ηᴰ = UniversalElementᴰNotation.ηᴰ _ _ (bpᴰ (d₁ , d₂))

module _ {C  : Category ℓC ℓC'}{c : C .ob}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module R = HomᴰReasoning Cᴰ
  -- meant to be used as `module cᴰ∧cᴰ' = VerticalBinProductsAtNotation vbp`
  module BinProductⱽNotation {cᴰ cᴰ' : Cᴰ.ob[ c ]}
    (vbp : BinProductⱽ Cᴰ (cᴰ , cᴰ')) where

    private
      module vbp = UniversalElementⱽ vbp

    vert : Cᴰ.ob[ c ]
    vert = vbp .vertexⱽ

    -- shorthand for terminal vertical cone
    π₁₂ :
      Cᴰ.Hom[ C .id ][ vert , cᴰ ] × Cᴰ.Hom[ C .id ][ vert , cᴰ' ]
    π₁₂ = vbp .elementⱽ
    π₁ = π₁₂ .fst
    π₂ = π₁₂ .snd

    module _ {x : C .ob}{xᴰ : Cᴰ.ob[ x ]}{f : C [ x , c ]} where
      _,ⱽ_ : Cᴰ.Hom[ f ][ xᴰ , cᴰ ] →
        Cᴰ.Hom[ f ][ xᴰ , cᴰ' ] →
        Cᴰ.Hom[ f ][ xᴰ , vert ]
      (fᴰ ,ⱽ fᴰ') = vbp.introⱽ _ (fᴰ , fᴰ')

      ×βⱽ₁ : {fᴰ : Cᴰ.Hom[ f ][ xᴰ , cᴰ ]}
        → {fᴰ' : Cᴰ.Hom[ f ][ xᴰ , cᴰ' ]}
        → seqᴰⱽ Cᴰ (fᴰ ,ⱽ fᴰ') π₁ ≡ fᴰ
      ×βⱽ₁ = cong fst vbp.βⱽ

      ×βⱽ₂ : {fᴰ : Cᴰ.Hom[ f ][ xᴰ , cᴰ ]}
        → {fᴰ' : Cᴰ.Hom[ f ][ xᴰ , cᴰ' ]}
        → seqᴰⱽ Cᴰ (fᴰ ,ⱽ fᴰ') π₂ ≡ fᴰ'
      ×βⱽ₂ = cong snd vbp.βⱽ

      ×ηⱽ : {fᴰ : Cᴰ.Hom[ f ][ xᴰ , vert ]}
        → fᴰ ≡ (seqᴰⱽ Cᴰ fᴰ π₁ ,ⱽ seqᴰⱽ Cᴰ fᴰ π₂)
      ×ηⱽ = vbp.ηⱽ
