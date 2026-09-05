{-# OPTIONS --lossy-unification #-}
{- Monads on a fixed 0-cell of a bicategory, their morphisms, and the
   category they form. -}
module Cubical.Categories.Bicategory.Monad.Morphism where

open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Properties.Coherence
open import Cubical.Categories.Bicategory.Monad.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

-- Street's formal monad with the carrier 0-cell fixed, so that
-- morphisms carry no object-transport clutter.
module _ (C : Bicategory ℓ ℓ' ℓ'') (a : Bicategory.ob C) where
  private
    module C = Bicategory C

  record MonadOn : Type (ℓ-max ℓ' ℓ'') where
    field
      t : C.1Cell a a
      η : C.2Cell C.id₁ t
      μ : C.2Cell (t C.⋆₁ t) t

      idL    : ((η C.▷w t) C.⋆₂ μ) ≡ C.λ⁺ t
      idR    : ((t C.◁w η) C.⋆₂ μ) ≡ C.ρ⁺ t
      μAssoc : (C.α⁺ t t t C.⋆₂ ((t C.◁w μ) C.⋆₂ μ))
             ≡ ((μ C.▷w t) C.⋆₂ μ)

  open MonadOn

  -- A 2-cell between the carriers commuting with units and mults;
  -- the horizontal composite `φ ⋆₁ φ` is spelled by whiskering.
  record MonadMorphism (M M' : MonadOn) : Type ℓ'' where
    field
      φ : C.2Cell (M .t) (M' .t)
      φ-η : (M .η C.⋆₂ φ) ≡ M' .η
      φ-μ : (M .μ C.⋆₂ φ)
          ≡ (((φ C.▷w M .t) C.⋆₂ (M' .t C.◁w φ)) C.⋆₂ M' .μ)

  open MonadMorphism

  MonadMorphism≡ : {M M' : MonadOn} {f g : MonadMorphism M M'}
    → f .φ ≡ g .φ → f ≡ g
  MonadMorphism≡ {M} {M'} {f} {g} p i .φ = p i
  MonadMorphism≡ {M} {M'} {f} {g} p i .φ-η =
    isProp→PathP (λ i → Bicategory.isSet2Cell C (M .η C.⋆₂ p i) (M' .η))
      (f .φ-η) (g .φ-η) i
  MonadMorphism≡ {M} {M'} {f} {g} p i .φ-μ =
    isProp→PathP
      (λ i → Bicategory.isSet2Cell C (M .μ C.⋆₂ p i)
        (((p i C.▷w M .t) C.⋆₂ (M' .t C.◁w p i)) C.⋆₂ M' .μ))
      (f .φ-μ) (g .φ-μ) i

  idMonadMor : (M : MonadOn) → MonadMorphism M M
  idMonadMor M .φ = C.id₂
  idMonadMor M .φ-η = C.⋆₂IdR _
  idMonadMor M .φ-μ =
      C.⋆₂IdR _
    ∙ sym ( C.⟨ C.⟨ C.▷wId (M .t) ⟩⋆₂⟨ C.◁wId (M .t) ⟩ ∙ C.⋆₂IdL _ ⟩⋆₂⟨⟩
          ∙ C.⋆₂IdL _)

  _∘M_ : {M M' M'' : MonadOn}
    → MonadMorphism M' M'' → MonadMorphism M M'
    → MonadMorphism M M''
  _∘M_ {M} {M'} {M''} g f .φ = f .φ C.⋆₂ g .φ
  _∘M_ {M} {M'} {M''} g f .φ-η =
      sym (C.⋆₂Assoc _ _ _)
    ∙ C.⟨ f .φ-η ⟩⋆₂⟨⟩
    ∙ g .φ-η
  _∘M_ {M} {M'} {M''} g f .φ-μ =
      sym (C.⋆₂Assoc _ _ _)
    ∙ C.⟨ f .φ-μ ⟩⋆₂⟨⟩
    ∙ C.⋆₂Assoc _ _ _
    ∙ C.⟨⟩⋆₂⟨ g .φ-μ ⟩
    ∙ sym (C.⋆₂Assoc _ _ _)
    ∙ C.⟨ hcomp-square ⟩⋆₂⟨⟩
    where
    -- Interchange: composing horizontally then vertically agrees.
    hcomp-square :
        ((f .φ C.▷w M .t) C.⋆₂ (M' .t C.◁w f .φ))
          C.⋆₂ ((g .φ C.▷w M' .t) C.⋆₂ (M'' .t C.◁w g .φ))
      ≡ (((f .φ C.⋆₂ g .φ) C.▷w M .t)
          C.⋆₂ (M'' .t C.◁w (f .φ C.⋆₂ g .φ)))
    hcomp-square =
        C.⋆₂Assoc _ _ _
      ∙ C.⟨⟩⋆₂⟨ sym (C.⋆₂Assoc _ _ _)
              ∙ C.⟨ sym (▷◁exch C (g .φ) (f .φ)) ⟩⋆₂⟨⟩
              ∙ C.⋆₂Assoc _ _ _ ⟩
      ∙ sym (C.⋆₂Assoc _ _ _)
      ∙ C.⟨ sym (▷wSeq C (f .φ) (g .φ) (M .t)) ⟩⋆₂⟨
            sym (◁wSeq C (M'' .t) (f .φ) (g .φ)) ⟩

  -- A morphism is a 2-cell plus two equations between 2-cells, so the
  -- hom-types are sets and this is a category, not merely a WildCat.
  MonadMorphismΣ : (M M' : MonadOn) → Type ℓ''
  MonadMorphismΣ M M' =
    Σ[ φ ∈ C.2Cell (M .t) (M' .t) ]
      ((M .η C.⋆₂ φ) ≡ M' .η)
    × ((M .μ C.⋆₂ φ)
        ≡ (((φ C.▷w M .t) C.⋆₂ (M' .t C.◁w φ)) C.⋆₂ M' .μ))

  isoMonadMorphismΣ : (M M' : MonadOn)
    → Iso (MonadMorphism M M') (MonadMorphismΣ M M')
  isoMonadMorphismΣ M M' .Iso.fun u = u .φ , u .φ-η , u .φ-μ
  isoMonadMorphismΣ M M' .Iso.inv (g , p , q) =
    record { φ = g ; φ-η = p ; φ-μ = q }
  isoMonadMorphismΣ M M' .Iso.sec _ = refl
  isoMonadMorphismΣ M M' .Iso.ret _ = refl

  isSetMonadMorphism : (M M' : MonadOn) → isSet (MonadMorphism M M')
  isSetMonadMorphism M M' =
    isOfHLevelRetractFromIso 2 (isoMonadMorphismΣ M M')
      (isSetΣ C.isSet2Cell λ _ →
        isSet× (isProp→isSet (C.isSet2Cell _ _))
               (isProp→isSet (C.isSet2Cell _ _)))

  -- The category laws are those of the 2-cell category `Hom[ a , a ]`.
  MND : Category (ℓ-max ℓ' ℓ'') ℓ''
  MND .Category.ob = MonadOn
  MND .Category.Hom[_,_] = MonadMorphism
  MND .Category.id {M} = idMonadMor M
  MND .Category._⋆_ f g = g ∘M f
  MND .Category.⋆IdL f = MonadMorphism≡ (C.⋆₂IdL (f .φ))
  MND .Category.⋆IdR f = MonadMorphism≡ (C.⋆₂IdR (f .φ))
  MND .Category.⋆Assoc f g h =
    MonadMorphism≡ (C.⋆₂Assoc (f .φ) (g .φ) (h .φ))
  MND .Category.isSetHom {M} {M'} = isSetMonadMorphism M M'

-- A `Monad C` is a `MonadOn C` at its own carrier: the two records
-- have definitionally the same data and laws.
module _ (C : Bicategory ℓ ℓ' ℓ'') where
  fromMonad : (M : Monad C) → MonadOn C (Monad.a M)
  fromMonad M = record
    { t = M.t ; η = M.η ; μ = M.μ
    ; idL = M.idL ; idR = M.idR ; μAssoc = M.μAssoc }
    where module M = Monad M
