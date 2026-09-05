{-# OPTIONS --lossy-unification #-}
{- The classical unit-counit adjunction, recovered from an adjunction
   in `CAT`. -}
module Cubical.Categories.Bicategory.Instances.CAT.AdjointFunctor where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint

open import Cubical.Categories.Bicategory.Adjunction
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Instances.CAT.Adjunction

private
  variable
    ℓ ℓ' : Level

open Category
open Functor
open NatTrans
open UnitCounit
open UnitCounit._⊣_
open UnitCounit.TriangleIdentities

-- The unit and counit transfer by `refl`: CAT's `id₁` is `Id` and
-- `f ⋆₁ u` is `u ∘F f` on the nose.  The zigzags are 2-cells with
-- definitionally correct endpoints, so evaluating them pointwise
-- gives equations in the base categories in which the (identity)
-- unitor/associator components are absorbed by `⋆IdL`/`⋆IdR`.
module _ (adj : AdjointFunctorᴮ {ℓ} {ℓ'}) where
  private
    module A = Adjunction adj
    module c = Category A.c
    module d = Category A.d

  F : Functor A.c A.d
  F = A.f

  G : Functor A.d A.c
  G = A.u

  η⊣ : NatTrans 𝟙⟨ A.c ⟩ (G ∘F F)
  η⊣ = A.η

  ε⊣ : NatTrans (F ∘F G) 𝟙⟨ A.d ⟩
  ε⊣ = A.ε

  Δ₁⊣ : ∀ x → F .F-hom (η⊣ .N-ob x) ⋆⟨ A.d ⟩ ε⊣ .N-ob (F .F-ob x) ≡ A.d .id
  Δ₁⊣ x = sym simpl ∙ funExt⁻ (cong N-ob A.zigzagL) x
    where
      a = A.f .F-hom (A.η .N-ob x)
      b = A.ε .N-ob (A.f .F-ob x)
      -- The only extra content on the left zigzag.
      fu-id : A.f .F-hom (A.u .F-hom d.id) ≡ d.id
      fu-id = cong (A.f .F-hom) (A.u .F-id) ∙ A.f .F-id
      simpl :
          d.id d.⋆ ((a d.⋆ d.id)
                    d.⋆ (d.id d.⋆
                          (((A.f .F-hom (A.u .F-hom d.id)) d.⋆ b) d.⋆ d.id)))
        ≡ a d.⋆ b
      simpl =
          d.⋆IdL _
        ∙ cong₂ d._⋆_ (d.⋆IdR _)
            ( d.⋆IdL _
            ∙ d.⋆IdR _
            ∙ cong (d._⋆ b) fu-id
            ∙ d.⋆IdL _)

  Δ₂⊣ : ∀ x → η⊣ .N-ob (G .F-ob x) ⋆⟨ A.c ⟩ G .F-hom (ε⊣ .N-ob x) ≡ A.c .id
  Δ₂⊣ x = sym simpl ∙ funExt⁻ (cong N-ob A.zigzagR) x
    where
      a = A.η .N-ob (A.u .F-ob x)
      b = A.u .F-hom (A.ε .N-ob x)
      simpl :
          c.id c.⋆ ((c.id c.⋆ a)
                    c.⋆ (c.id c.⋆ ((b c.⋆ c.id) c.⋆ c.id)))
        ≡ a c.⋆ b
      simpl =
          c.⋆IdL _
        ∙ cong₂ c._⋆_ (c.⋆IdL _)
            ( c.⋆IdL _
            ∙ c.⋆IdR _
            ∙ c.⋆IdR _)

  AdjointFunctorᴮ→UnitCounit : F ⊣ G
  AdjointFunctorᴮ→UnitCounit .UnitCounit._⊣_.η = η⊣
  AdjointFunctorᴮ→UnitCounit .UnitCounit._⊣_.ε = ε⊣
  AdjointFunctorᴮ→UnitCounit .UnitCounit._⊣_.triangleIdentities .Δ₁ = Δ₁⊣
  AdjointFunctorᴮ→UnitCounit .UnitCounit._⊣_.triangleIdentities .Δ₂ = Δ₂⊣
