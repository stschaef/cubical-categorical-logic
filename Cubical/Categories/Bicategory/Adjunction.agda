{- Adjunctions in a bicategory (Street's formal adjunctions). -}
module Cubical.Categories.Bicategory.Adjunction where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Bicategory.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ (C : Bicategory ℓ ℓ' ℓ'') where
  private
    module C = Bicategory C

  record Adjunction : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
    field
      c d : C.0Cell
      f : C.1Cell c d
      u : C.1Cell d c
      η : C.2Cell C.id₁ (f C.⋆₁ u)
      ε : C.2Cell (u C.⋆₁ f) C.id₁

    field
      zigzagL :
          C.λ⁻ f
            C.⋆₂ ((η C.▷w f)
            C.⋆₂ (C.α⁺ f u f
            C.⋆₂ ((f C.◁w ε) C.⋆₂ C.ρ⁺ f)))
        ≡ C.id₂

      zigzagR :
          C.ρ⁻ u
            C.⋆₂ ((u C.◁w η)
            C.⋆₂ (C.α⁻ u f u
            C.⋆₂ ((ε C.▷w u) C.⋆₂ C.λ⁺ u)))
        ≡ C.id₂
