{-# OPTIONS --lossy-unification #-}
{- Street's monad functors: morphisms of formal monads carried on
   possibly different 0-cells. -}
module Cubical.Categories.Bicategory.MonadFunctor where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Monad
open import Cubical.Categories.Bicategory.MonadMorphism

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ (C : Bicategory ℓ ℓ' ℓ'') where
  private
    module C = Bicategory C

  open MonadOn

  -- `(P , φ) : M ⇒ M'` for `M` on `a` and `M'` on `a'`: a 1-cell
  -- `P : a → a'` and a lax comparison `φ : t M ⋆₁ P ⇒ P ⋆₁ t M'`,
  -- compatible with the units (through the unitors) and with the
  -- multiplications (through the associators).
  record MonadFunctor {a a' : C.ob}
    (M : MonadOn C a) (M' : MonadOn C a')
    : Type (ℓ-max ℓ' ℓ'') where
    field
      P : C.1Cell a a'
      φ : C.2Cell (M .t C.⋆₁ P) (P C.⋆₁ M' .t)
      φ-η :
          ((M .η C.▷w P) C.⋆₂ φ)
        ≡ (C.λ⁺ P C.⋆₂ (C.ρ⁻ P C.⋆₂ (P C.◁w M' .η)))
      φ-μ :
          ((M .μ C.▷w P) C.⋆₂ φ)
        ≡ ( C.α⁺ (M .t) (M .t) P
        C.⋆₂ ((M .t C.◁w φ)
        C.⋆₂ (C.α⁻ (M .t) P (M' .t)
        C.⋆₂ ((φ C.▷w M' .t)
        C.⋆₂ (C.α⁺ P (M' .t) (M' .t)
        C.⋆₂ (P C.◁w M' .μ))))))

  open MonadFunctor

  MonadFunctor≡ : {a a' : C.ob}
    {M : MonadOn C a} {M' : MonadOn C a'}
    {F G : MonadFunctor M M'}
    → (pP : F .P ≡ G .P)
    → PathP (λ i → C.2Cell (M .t C.⋆₁ pP i) (pP i C.⋆₁ M' .t))
        (F .φ) (G .φ)
    → F ≡ G
  MonadFunctor≡ {a} {a'} {M} {M'} {F} {G} pP pφ i .P = pP i
  MonadFunctor≡ {a} {a'} {M} {M'} {F} {G} pP pφ i .φ = pφ i
  MonadFunctor≡ {a} {a'} {M} {M'} {F} {G} pP pφ i .φ-η =
    isProp→PathP
      (λ i → Bicategory.isSet2Cell C
        ((M .η C.▷w pP i) C.⋆₂ pφ i)
        (C.λ⁺ (pP i) C.⋆₂ (C.ρ⁻ (pP i) C.⋆₂ (pP i C.◁w M' .η))))
      (F .φ-η) (G .φ-η) i
  MonadFunctor≡ {a} {a'} {M} {M'} {F} {G} pP pφ i .φ-μ =
    isProp→PathP
      (λ i → Bicategory.isSet2Cell C
        ((M .μ C.▷w pP i) C.⋆₂ pφ i)
        ( C.α⁺ (M .t) (M .t) (pP i)
        C.⋆₂ ((M .t C.◁w pφ i)
        C.⋆₂ (C.α⁻ (M .t) (pP i) (M' .t)
        C.⋆₂ ((pφ i C.▷w M' .t)
        C.⋆₂ (C.α⁺ (pP i) (M' .t) (M' .t)
        C.⋆₂ (pP i C.◁w M' .μ)))))))
      (F .φ-μ) (G .φ-μ) i
