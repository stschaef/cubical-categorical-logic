{- Displayed biclosed monoidal categories, and the biclosed
   structure on a weakening. -}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Monoidal.Biclosed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Biclosed
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.Adjoint.RightAdjoint
import Cubical.Categories.Instances.Free.Monoidal.OnCategory as FM
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Instances.Fiber

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Monoidal.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Constructions.ReindexFunctor.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.Instances.Weaken.Monoidal
import Cubical.Categories.Displayed.Instances.Weaken.Base as Wk

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

open Category
open Functor
open NatTrans
open NatIso
open isIso
open UniversalElement
open StrongMonoidalFunctor
open StrongMonoidalStr
open LaxMonoidalStr
open Functorᴰ
open Section
open NatTransᴰ
open NatIsoᴰ
open isIsoᴰ
open UniversalElementᴰ

{- Displayed biclosed monoidal categories.  The residual halves are
   displayed universal elements of the reindexed representables, i.e.
   displayed right adjoints. -}
module _ {M : MonoidalCategory ℓD ℓD'} (Mᴰ : MonoidalCategoryᴰ M ℓE ℓE')
  where
  private
    module M = MonoidalCategory M
    module Mᴰ = MonoidalCategoryᴰ Mᴰ
    module Cᴰ = Fibers Mᴰ.Cᴰ

  A⊗ᴰ-F : ∀ {A} (Aᴰ : Mᴰ.ob[ A ]) → Functorᴰ (A⊗-F M.tenstr A) Mᴰ.Cᴰ Mᴰ.Cᴰ
  A⊗ᴰ-F Aᴰ .F-obᴰ Xᴰ = Aᴰ Mᴰ.⊗ᴰ Xᴰ
  A⊗ᴰ-F Aᴰ .F-homᴰ fᴰ = Mᴰ.idᴰ Mᴰ.⊗ₕᴰ fᴰ
  A⊗ᴰ-F Aᴰ .F-idᴰ = Mᴰ.─⊗ᴰ─ .F-idᴰ
  A⊗ᴰ-F Aᴰ .F-seqᴰ {f = f}{g = g} fᴰ gᴰ = Cᴰ.rectifyOut $
    (λ i → M.─⊗─ .F-hom (q i .fst , f M.⋆ g)
         , Mᴰ.─⊗ᴰ─ .F-homᴰ (q i .snd , fᴰ Mᴰ.⋆ᴰ gᴰ))
    ∙ Cᴰ.≡in (Mᴰ.─⊗ᴰ─ .F-seqᴰ (Mᴰ.idᴰ , fᴰ) (Mᴰ.idᴰ , gᴰ))
    where q = sym (Cᴰ.≡in (Mᴰ.⋆IdLᴰ Mᴰ.idᴰ))

  -⊗ᴰAF : ∀ {A} (Aᴰ : Mᴰ.ob[ A ]) → Functorᴰ (-⊗AF M.tenstr A) Mᴰ.Cᴰ Mᴰ.Cᴰ
  -⊗ᴰAF Aᴰ .F-obᴰ Xᴰ = Xᴰ Mᴰ.⊗ᴰ Aᴰ
  -⊗ᴰAF Aᴰ .F-homᴰ fᴰ = fᴰ Mᴰ.⊗ₕᴰ Mᴰ.idᴰ
  -⊗ᴰAF Aᴰ .F-idᴰ = Mᴰ.─⊗ᴰ─ .F-idᴰ
  -⊗ᴰAF Aᴰ .F-seqᴰ {f = f}{g = g} fᴰ gᴰ = Cᴰ.rectifyOut $
    (λ i → M.─⊗─ .F-hom (f M.⋆ g , q i .fst)
         , Mᴰ.─⊗ᴰ─ .F-homᴰ (fᴰ Mᴰ.⋆ᴰ gᴰ , q i .snd))
    ∙ Cᴰ.≡in (Mᴰ.─⊗ᴰ─ .F-seqᴰ (fᴰ , Mᴰ.idᴰ) (gᴰ , Mᴰ.idᴰ))
    where q = sym (Cᴰ.≡in (Mᴰ.⋆IdLᴰ Mᴰ.idᴰ))

  LeftResidualᴰ : ∀ {Δ Θ} (Δᴰ : Mᴰ.ob[ Δ ]) (Θᴰ : Mᴰ.ob[ Θ ])
    → LeftResidual M.tenstr Δ Θ → Type _
  LeftResidualᴰ Δᴰ Θᴰ lr = UniversalElementᴰ Mᴰ.Cᴰ lr
    (reindPshᴰFunctor (A⊗ᴰ-F Δᴰ) (Mᴰ.Cᴰ [-][-, Θᴰ ]))

  RightResidualᴰ : ∀ {Δ Θ} (Δᴰ : Mᴰ.ob[ Δ ]) (Θᴰ : Mᴰ.ob[ Θ ])
    → RightResidual M.tenstr Δ Θ → Type _
  RightResidualᴰ Δᴰ Θᴰ rr = UniversalElementᴰ Mᴰ.Cᴰ rr
    (reindPshᴰFunctor (-⊗ᴰAF Δᴰ) (Mᴰ.Cᴰ [-][-, Θᴰ ]))

BM→Mon : BiclosedMonoidalCategory ℓD ℓD' → MonoidalCategory ℓD ℓD'
BM→Mon B .MonoidalCategory.C = B .BiclosedMonoidalCategory.C
BM→Mon B .MonoidalCategory.monstr =
  B .BiclosedMonoidalCategory.biclosedstr .BiclosedMonoidalStr.monstr

record BiclosedMonoidalCategoryᴰ (B : BiclosedMonoidalCategory ℓD ℓD')
  (ℓE ℓE' : Level)
  : Type (ℓ-suc (ℓ-max (ℓ-max ℓD ℓD') (ℓ-max ℓE ℓE'))) where
  private module B = BiclosedMonoidalCategory B
  field
    Mᴰ : MonoidalCategoryᴰ (BM→Mon B) ℓE ℓE'
  open MonoidalCategoryᴰ Mᴰ public
  field
    lresᴰ : ∀ {Δ Θ} (Δᴰ : ob[ Δ ]) (Θᴰ : ob[ Θ ])
      → LeftResidualᴰ Mᴰ Δᴰ Θᴰ (B.lres Δ Θ)
    rresᴰ : ∀ {Δ Θ} (Δᴰ : ob[ Δ ]) (Θᴰ : ob[ Θ ])
      → RightResidualᴰ Mᴰ Δᴰ Θᴰ (B.rres Δ Θ)

open BiclosedMonoidalCategoryᴰ

{- The weakening of a biclosed monoidal category is biclosed
   displayed: the displayed presheaves are constant, so the universal
   property is the target's. -}
module _ (B : BiclosedMonoidalCategory ℓD ℓD')
         (N : BiclosedMonoidalCategory ℓE ℓE') where
  private
    module B = BiclosedMonoidalCategory B
    module N = BiclosedMonoidalCategory N
    module Nl (Δ Θ : N.C .ob) = UniversalElementNotation (N.lres Δ Θ)
    module Nr (Δ Θ : N.C .ob) = UniversalElementNotation (N.rres Δ Θ)

  weakenBiclosed : BiclosedMonoidalCategoryᴰ B ℓE ℓE'
  weakenBiclosed .Mᴰ = weaken (BM→Mon B) (BM→Mon N)
  weakenBiclosed .lresᴰ Δᴰ Θᴰ .vertexᴰ = Nl.vertex Δᴰ Θᴰ
  weakenBiclosed .lresᴰ Δᴰ Θᴰ .elementᴰ = Nl.element Δᴰ Θᴰ
  weakenBiclosed .lresᴰ Δᴰ Θᴰ .universalᴰ .isIsoOver.inv _ = Nl.intro Δᴰ Θᴰ
  weakenBiclosed .lresᴰ Δᴰ Θᴰ .universalᴰ .isIsoOver.rightInv _ _ =
    Nl.β Δᴰ Θᴰ
  weakenBiclosed .lresᴰ Δᴰ Θᴰ .universalᴰ .isIsoOver.leftInv _ _ =
    sym (Nl.η Δᴰ Θᴰ)
  weakenBiclosed .rresᴰ Δᴰ Θᴰ .vertexᴰ = Nr.vertex Δᴰ Θᴰ
  weakenBiclosed .rresᴰ Δᴰ Θᴰ .elementᴰ = Nr.element Δᴰ Θᴰ
  weakenBiclosed .rresᴰ Δᴰ Θᴰ .universalᴰ .isIsoOver.inv _ = Nr.intro Δᴰ Θᴰ
  weakenBiclosed .rresᴰ Δᴰ Θᴰ .universalᴰ .isIsoOver.rightInv _ _ =
    Nr.β Δᴰ Θᴰ
  weakenBiclosed .rresᴰ Δᴰ Θᴰ .universalᴰ .isIsoOver.leftInv _ _ =
    sym (Nr.η Δᴰ Θᴰ)
