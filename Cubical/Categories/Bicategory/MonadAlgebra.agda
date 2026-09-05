{-# OPTIONS --lossy-unification #-}
{- Eilenberg-Moore algebras for a formal monad in a bicategory, and
   the `WildCat` they form. -}
module Cubical.Categories.Bicategory.MonadAlgebra where

open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Monad
open import Cubical.Categories.Bicategory.MonadMorphism

private
  variable
    ℓ ℓ' ℓ'' : Level

-- Algebras for the monad `M` on `a`, with carriers based at `b`.  The
-- action is whiskered on the right, since a carrier `x : b → a`
-- composes with `t : a → a` only as `x ⋆₁ t`.
module _ (C : Bicategory ℓ ℓ' ℓ'')
  (a : Bicategory.ob C) (M : MonadOn C a) (b : Bicategory.ob C)
  where
  private
    module C = Bicategory C
    module M = MonadOn M

  record Algebra : Type (ℓ-max ℓ' ℓ'') where
    field
      x : C.1Cell b a
      ξ : C.2Cell (x C.⋆₁ M.t) x

      α-unit : ((x C.◁w M.η) C.⋆₂ ξ) ≡ C.ρ⁺ x
      α-mult : (C.α⁺ x M.t M.t C.⋆₂ ((x C.◁w M.μ) C.⋆₂ ξ))
             ≡ ((ξ C.▷w M.t) C.⋆₂ ξ)

  open Algebra

  record AlgebraMor (P Q : Algebra) : Type ℓ'' where
    field
      f : C.2Cell (P .x) (Q .x)
      f-comm : (P .ξ C.⋆₂ f) ≡ ((f C.▷w M.t) C.⋆₂ Q .ξ)

  open AlgebraMor

  AlgebraMor≡ : {P Q : Algebra} {g h : AlgebraMor P Q}
    → g .f ≡ h .f → g ≡ h
  AlgebraMor≡ {P} {Q} {g} {h} p i .f = p i
  AlgebraMor≡ {P} {Q} {g} {h} p i .f-comm =
    isProp→PathP
      (λ i → Bicategory.isSet2Cell C (P .ξ C.⋆₂ p i) ((p i C.▷w M.t) C.⋆₂ Q .ξ))
      (g .f-comm) (h .f-comm) i

  idAlgMor : (P : Algebra) → AlgebraMor P P
  idAlgMor P .f = C.id₂
  idAlgMor P .f-comm =
    C.⋆₂IdR _ ∙ sym (C.⟨ C.▷wId M.t ⟩⋆₂⟨⟩ ∙ C.⋆₂IdL _)

  _∘A_ : {P Q R : Algebra}
    → AlgebraMor Q R → AlgebraMor P Q → AlgebraMor P R
  _∘A_ {P} {Q} {R} v u .f = u .f C.⋆₂ v .f
  _∘A_ {P} {Q} {R} v u .f-comm =
      sym (C.⋆₂Assoc _ _ _)
    ∙ C.⟨ u .f-comm ⟩⋆₂⟨⟩
    ∙ C.⋆₂Assoc _ _ _
    ∙ C.⟨⟩⋆₂⟨ v .f-comm ⟩
    ∙ sym (C.⋆₂Assoc _ _ _)
    ∙ C.⟨ sym (▷wSeq C (u .f) (v .f) M.t) ⟩⋆₂⟨⟩

  -- The Eilenberg-Moore WildCat; its laws are those of `Hom[ b , a ]`.
  EMWild : WildCat (ℓ-max ℓ' ℓ'') ℓ''
  EMWild .WildCat.ob = Algebra
  EMWild .WildCat.Hom[_,_] = AlgebraMor
  EMWild .WildCat.id {P} = idAlgMor P
  EMWild .WildCat._⋆_ u v = v ∘A u
  EMWild .WildCat.⋆IdL u = AlgebraMor≡ (C.⋆₂IdL (u .f))
  EMWild .WildCat.⋆IdR u = AlgebraMor≡ (C.⋆₂IdR (u .f))
  EMWild .WildCat.⋆Assoc u v w =
    AlgebraMor≡ (C.⋆₂Assoc (u .f) (v .f) (w .f))

module _ (C : Bicategory ℓ ℓ' ℓ'') where
  EMWildOfMonad : (M : Monad C) (b : Bicategory.ob C)
    → WildCat (ℓ-max ℓ' ℓ'') ℓ''
  EMWildOfMonad M b = EMWild C (Monad.a M) (fromMonad C M) b
