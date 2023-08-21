{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Presheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Instances.Sets
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Constructions.Functors

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓP ℓP' : Level

open Category
open Functor
open Functorᴰ

-- equivalent to the data of a presheaf Pᴰ over ∫ D and a natural transformation
-- Pᴰ → P ∘ Fst
Presheafᴰ : {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
          → (P : Presheaf C ℓP) → (ℓP' : Level)
          → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD') (ℓ-suc ℓP))
                    (ℓ-suc ℓP'))
Presheafᴰ {ℓP = ℓP} D P ℓP' = Functorᴰ P (D ^opᴰ) (SETS ℓP ℓP')

PRESHEAFᴰ : {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
            (ℓP : Level) (ℓP' : Level)
          → Categoryᴰ (PresheafCategory C ℓP) _ _
PRESHEAFᴰ D ℓP ℓP' = FUNCTORᴰ (D ^opᴰ) (SETS ℓP ℓP')

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
         {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ D P ℓP') where

  -- equivalent to the data of a universal element of Pᴰ such that the
  -- projection preserves the universality
  record UniversalElementᴰ (ue : UniversalElement C P)
    : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD') ℓP') where
    open UniversalElement ue
    open UniversalElementNotation ue
    open Categoryᴰ D
    field
      vertexᴰ : ob[ vertex ]
      elementᴰ : ⟨ Pᴰ .F-obᴰ vertexᴰ element ⟩
      universalᴰ : ∀ {x} xᴰ {f : C [ x , vertex ]}
                 → isEquiv λ (fᴰ : Hom[ f ][ xᴰ , vertexᴰ ]) →
                     Pᴰ .F-homᴰ fᴰ _ elementᴰ
    introᴰ : ∀ {x xᴰ} {p : ⟨ P .F-ob x ⟩}
           → ⟨ Pᴰ .F-obᴰ xᴰ p ⟩
           → D [ intro p ][ xᴰ , vertexᴰ ]
    introᴰ {x}{xᴰ}{p} pᴰ  = invIsEq (universalᴰ xᴰ) pᴰ'
      where pᴰ' = transport (λ i → ⟨ Pᴰ .F-obᴰ xᴰ (β {p = p} (~ i)) ⟩) pᴰ

    βᴰ : ∀ {x xᴰ} {p : ⟨ P .F-ob x ⟩}
        → {pᴰ : ⟨ Pᴰ .F-obᴰ xᴰ p ⟩}
        → PathP (λ i → ⟨ Pᴰ .F-obᴰ xᴰ (β {x} {p} i) ⟩) (Pᴰ .F-homᴰ (introᴰ pᴰ) element elementᴰ) pᴰ
    βᴰ {x}{xᴰ}{p}{pᴰ} =
      symP (toPathP (sym (
        secIsEq (universalᴰ xᴰ) (transport (λ i → ⟨ Pᴰ .F-obᴰ xᴰ (β {x} {p} (~ i)) ⟩) pᴰ)))
      )

    -- ηᴰ : ∀ {c}{cᴰ : ob[ c ]}{f : C [ c , vertex ]} →
    --      {fᴰ : Hom[ f ][ cᴰ , vertexᴰ ]} →
    --      fᴰ ≡[ η ] introᴰ (Pᴰ .F-homᴰ fᴰ element elementᴰ)
    -- ηᴰ {c}{cᴰ}{f}{fᴰ} =
    --     symP (toPathP
    --     {A = λ i → Hom[ η (~ i) ][ cᴰ , vertexᴰ ]}
    --     {x = introᴰ (Pᴰ .F-homᴰ fᴰ element elementᴰ)}{y = fᴰ}
    --     (
    --     {!cong fst (
    --       (universalᴰ cᴰ) .equiv-proof (Pᴰ .F-homᴰ ? ? ?) .snd (fᴰ , ?j))!}
    --     -- {!!} ∙
    --     -- retIsEq (universalᴰ cᴰ) fᴰ)
    --     ))
    --   where
    --   the-B = D [_][ cᴰ , vertexᴰ ]

    -- weak-ηᴰ : idᴰ {p = vertexᴰ} ≡[ weak-η ] (introᴰ {p = element} elementᴰ)
    -- weak-ηᴰ =
    --   compPathP' {B = the-B} {!!} {!!}
    --   where
    --   the-B = D [_][ vertexᴰ , vertexᴰ ]
