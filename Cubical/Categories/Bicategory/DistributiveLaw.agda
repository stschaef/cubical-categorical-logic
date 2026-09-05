{-# OPTIONS --lossy-unification #-}
{- Beck distributive laws between formal monads on a shared 0-cell,
   and the data of the composite monad they induce. -}
module Cubical.Categories.Bicategory.DistributiveLaw where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Monad
open import Cubical.Categories.Bicategory.MonadMorphism

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ (C : Bicategory ℓ ℓ' ℓ'') (a : Bicategory.ob C) where
  private
    module C = Bicategory C

  open MonadOn

  -- Writing `s = t S` and `u = t T`, a distributive law of `S` over
  -- `T` is a 2-cell `Λ : u ⋆₁ s ⇒ s ⋆₁ u` (classically `TS ⇒ ST`)
  -- satisfying Beck's four laws.  Unitors mediate the `id₁` seams and
  -- associators the multiplication seams.
  record DistributiveLaw (S T : MonadOn C a)
    : Type (ℓ-max ℓ' ℓ'') where
    private
      s : C.1Cell a a
      s = S .t
      u : C.1Cell a a
      u = T .t
    field
      Λ : C.2Cell (u C.⋆₁ s) (s C.⋆₁ u)

      -- `u ⇒ s ⋆₁ u`, comparing `u ◁ ηS` with `ηS ▷ u`.
      unit-S :
          ((C.ρ⁻ u C.⋆₂ (u C.◁w S .η)) C.⋆₂ Λ)
        ≡ (C.λ⁻ u C.⋆₂ (S .η C.▷w u))

      -- `s ⇒ s ⋆₁ u`, comparing `ηT ▷ s` with `s ◁ ηT`.
      unit-T :
          ((C.λ⁻ s C.⋆₂ (T .η C.▷w s)) C.⋆₂ Λ)
        ≡ (C.ρ⁻ s C.⋆₂ (s C.◁w T .η))

      -- `(u ⋆₁ s) ⋆₁ s ⇒ s ⋆₁ u`: `Λ` transposed across `μS`.
      mult-S :
          ((C.α⁺ u s s C.⋆₂ (u C.◁w S .μ)) C.⋆₂ Λ)
        ≡ ((Λ C.▷w s) C.⋆₂
             ((C.α⁺ s u s C.⋆₂ (s C.◁w Λ)) C.⋆₂
               (C.α⁻ s s u C.⋆₂ (S .μ C.▷w u))))

      -- `(u ⋆₁ u) ⋆₁ s ⇒ s ⋆₁ u`: `Λ` transposed across `μT`.
      mult-T :
          ((T .μ C.▷w s) C.⋆₂ Λ)
        ≡ ((C.α⁺ u u s C.⋆₂ (u C.◁w Λ)) C.⋆₂
             ((C.α⁻ u s u C.⋆₂ (Λ C.▷w u)) C.⋆₂
               (C.α⁺ s u u C.⋆₂ (s C.◁w T .μ))))

  open DistributiveLaw

  -- The composite monad `ST`, with carrier `s ⋆₁ u`.
  module Composite (S T : MonadOn C a) (D : DistributiveLaw S T) where
    private
      s : C.1Cell a a
      s = S .t
      u : C.1Cell a a
      u = T .t
      Λ' : C.2Cell (u C.⋆₁ s) (s C.⋆₁ u)
      Λ' = D .Λ
      st : C.1Cell a a
      st = s C.⋆₁ u

    ηST : C.2Cell C.id₁ st
    ηST = (C.λ⁻ C.id₁ C.⋆₂ (S .η C.▷w C.id₁)) C.⋆₂ (s C.◁w T .η)

    -- The middle-four interchange, mediated by `Λ` on the inner `u s`.
    μST : C.2Cell (st C.⋆₁ st) st
    μST =
        (C.α⁺ s u (s C.⋆₁ u) C.⋆₂
          (s C.◁w (C.α⁻ u s u C.⋆₂
            ((Λ' C.▷w u) C.⋆₂ C.α⁺ s u u)))) C.⋆₂
        (C.α⁻ s s (u C.⋆₁ u) C.⋆₂
          ((S .μ C.▷w (u C.⋆₁ u)) C.⋆₂ (s C.◁w T .μ)))

    -- The three composite-monad coherences, stated here and supplied
    -- at instantiation.
    idL-ty : Type ℓ''
    idL-ty = ((ηST C.▷w st) C.⋆₂ μST) ≡ C.λ⁺ st

    idR-ty : Type ℓ''
    idR-ty = ((st C.◁w ηST) C.⋆₂ μST) ≡ C.ρ⁺ st

    μAssoc-ty : Type ℓ''
    μAssoc-ty =
      (C.α⁺ st st st C.⋆₂ ((st C.◁w μST) C.⋆₂ μST))
        ≡ ((μST C.▷w st) C.⋆₂ μST)

    compositeMonadOn : idL-ty → idR-ty → μAssoc-ty → MonadOn C a
    compositeMonadOn idL' idR' μAssoc' = record
      { t = st
      ; η = ηST
      ; μ = μST
      ; idL = idL'
      ; idR = idR'
      ; μAssoc = μAssoc'
      }
