{- Biclosed monoidal structure: residuals as universal elements. -}
module Cubical.Categories.Monoidal.Biclosed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Adjoint.RightAdjoint

private
  variable
    ℓ ℓ' : Level

open Category
open Functor

module _ {C : Category ℓ ℓ'} (T : TensorStr C) where
  private
    module C = Category C
  open TensorStr T

  A⊗-F : C .ob → Functor C C
  A⊗-F A .F-ob X = A ⊗ X
  A⊗-F A .F-hom f = C.id ⊗ₕ f
  A⊗-F A .F-id = ─⊗─ .F-id
  A⊗-F A .F-seq f g =
    cong (λ k → ─⊗─ .F-hom (k , (f C.⋆ g))) (sym (C.⋆IdL C.id))
    ∙ ─⊗─ .F-seq (C.id , f) (C.id , g)

  -⊗AF : C .ob → Functor C C
  -⊗AF A .F-ob X = X ⊗ A
  -⊗AF A .F-hom f = f ⊗ₕ C.id
  -⊗AF A .F-id = ─⊗─ .F-id
  -⊗AF A .F-seq f g =
    cong (λ k → ─⊗─ .F-hom ((f C.⋆ g) , k)) (sym (C.⋆IdL C.id))
    ∙ ─⊗─ .F-seq (f , C.id) (g , C.id)

  -- `Δ ⊸ Θ` represents `X ↦ Hom(Δ ⊗ X , Θ)`.
  LeftResidual : (Δ Θ : C .ob) → Type (ℓ-max ℓ ℓ')
  LeftResidual Δ Θ = UniversalElement C (RPsh (A⊗-F Δ) Θ)

  -- `Θ ⟜ Δ` represents `X ↦ Hom(X ⊗ Δ , Θ)`.
  RightResidual : (Δ Θ : C .ob) → Type (ℓ-max ℓ ℓ')
  RightResidual Δ Θ = UniversalElement C (RPsh (-⊗AF Δ) Θ)

record BiclosedMonoidalStr (C : Category ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    monstr : MonoidalStr C
  open MonoidalStr monstr public
  field
    lres : ∀ Δ Θ → LeftResidual tenstr Δ Θ
    rres : ∀ Δ Θ → RightResidual tenstr Δ Θ

record BiclosedMonoidalCategory (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    C : Category ℓ ℓ'
    biclosedstr : BiclosedMonoidalStr C
  open BiclosedMonoidalStr biclosedstr public
