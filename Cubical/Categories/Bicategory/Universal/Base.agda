{-
  Biuniversal elements: `UniversalElement` one dimension up.  A vertex
  `a` and an element `e : P a` of a prestack whose comparison functor
  `⟨ e ⟩ x : Hom[ x , a ] → P x`, `h ↦ h ⋆ᴾ e`, is an equivalence at
  every probe.  Names follow `UniversalElementNotation`; everything
  that is an equation there is an isomorphism here.
-}
module Cubical.Categories.Bicategory.Universal.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Morphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.Base
open import Cubical.Categories.Equivalence.Properties
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Hom
open import Cubical.Categories.Bicategory.Prestack.Morphism
open import Cubical.Categories.Bicategory.Prestack.Yoneda

private
  variable
    ℓ ℓ' ℓ'' ℓp ℓp' : Level

open Functor
open NatIso
open isIso
open WeakInverse using (invFunc; ε)

module _ {B : Bicategory ℓ ℓ' ℓ''} (P : Prestack B ℓp ℓp') where
  private
    module B = Bicategory B
  open PrestackNotation P

  isBiuniversal : (a : B.0Cell) → p[ a ] → Type _
  isBiuniversal a e = (x : B.0Cell) → WeakInverse (⟨ e ⟩ x)

  record BiuniversalElement : Type (ℓ-max ℓ (ℓ-max (ℓ-max ℓ' ℓ'')
                                        (ℓ-max ℓp ℓp'))) where
    field
      vertex : B.0Cell
      element : p[ vertex ]
      universal : isBiuniversal vertex element

module BiuniversalElementNotation {B : Bicategory ℓ ℓ' ℓ''}
  {P : Prestack B ℓp ℓp'} (bue : BiuniversalElement P) where

  open BiuniversalElement bue public
  open PrestackNotation P public

  private
    module B = Bicategory B

  -- `isBiuniversal` is data, but everything derived from `ff` is
  -- canonical: `isFullyFaithful` is a proposition.
  ff : (x : B.0Cell) → isFullyFaithful (⟨ element ⟩ x)
  ff x = isEquiv→FullyFaithful ∣ universal x ∣₁

  intro : {x : B.0Cell} → p[ x ] → B.1Cell x vertex
  intro {x} e = universal x .invFunc .F-ob e

  β : {x : B.0Cell} (e : p[ x ]) → CatIso P⟨ x ⟩ (intro e ⋆ᴾ element) e
  β {x} e = isIso→CatIso (universal x .ε .nIso e)

  intro⟨_⟩ : {x : B.0Cell} {e e' : p[ x ]}
    → CatIso P⟨ x ⟩ e e' → CatIso B.Hom[ x , vertex ] (intro e) (intro e')
  intro⟨_⟩ {x} φ = F-Iso {F = universal x .invFunc} φ

  intro⟨⟩-seq : {x : B.0Cell} {e e' e'' : p[ x ]}
    (φ : CatIso P⟨ x ⟩ e e') (φ' : CatIso P⟨ x ⟩ e' e'')
    → intro⟨ ⋆Iso φ φ' ⟩ ≡ ⋆Iso intro⟨ φ ⟩ intro⟨ φ' ⟩
  intro⟨⟩-seq {x} φ φ' = F-Iso-Pres⋆ {F = universal x .invFunc} φ φ'

  intro⟨⟩-id : {x : B.0Cell} {e : p[ x ]}
    → intro⟨ idCatIso {x = e} ⟩ ≡ idCatIso
  intro⟨⟩-id {x} = F-Iso-PresId {F = universal x .invFunc}

  -- Lift the iso along the fully faithful `⟨ element ⟩ x` rather than
  -- conjugate with the weak inverse's unit: lifting has a β-rule.
  intro≡ : {x : B.0Cell} {h : B.1Cell x vertex} {e : p[ x ]}
    → CatIso P⟨ x ⟩ (h ⋆ᴾ element) e
    → CatIso B.Hom[ x , vertex ] h (intro e)
  intro≡ {x} {e = e} φ =
    liftIso {F = ⟨ element ⟩ x} (ff x) (⋆Iso φ (invIso (β e)))

  intro≡-β : {x : B.0Cell} {h : B.1Cell x vertex} {e : p[ x ]}
    (φ : CatIso P⟨ x ⟩ (h ⋆ᴾ element) e)
    → F-Iso {F = ⟨ element ⟩ x} (intro≡ φ) ≡ ⋆Iso φ (invIso (β e))
  intro≡-β {x} {e = e} φ =
    liftIso≡ {F = ⟨ element ⟩ x} (ff x) (⋆Iso φ (invIso (β e)))

  η : {x : B.0Cell} (h : B.1Cell x vertex)
    → CatIso B.Hom[ x , vertex ] h (intro (h ⋆ᴾ element))
  η h = intro≡ idCatIso

  weak-η : CatIso B.Hom[ vertex , vertex ] B.id₁ (intro element)
  weak-η = intro≡ (⋆ᴾIdL element)

  extensionality : {x : B.0Cell} {h k : B.1Cell x vertex}
    (α γ : B.2Cell h k)
    → ⟨ element ⟩ x .F-hom α ≡ ⟨ element ⟩ x .F-hom γ → α ≡ γ
  extensionality {x} α γ =
    isFullyFaithful→Faithful {F = ⟨ element ⟩ x} (ff x) _ _ α γ

  intro₂ : {x : B.0Cell} {h k : B.1Cell x vertex}
    → P⟨ x ⟩ [ h ⋆ᴾ element , k ⋆ᴾ element ] → B.2Cell h k
  intro₂ {x} ξ = invEq (_ , ff x _ _) ξ

  intro₂-β : {x : B.0Cell} {h k : B.1Cell x vertex}
    (ξ : P⟨ x ⟩ [ h ⋆ᴾ element , k ⋆ᴾ element ])
    → ⟨ element ⟩ x .F-hom (intro₂ ξ) ≡ ξ
  intro₂-β {x} ξ = secEq (_ , ff x _ _) ξ

  intro₂-η : {x : B.0Cell} {h k : B.1Cell x vertex} (α : B.2Cell h k)
    → intro₂ (⟨ element ⟩ x .F-hom α) ≡ α
  intro₂-η {x} α = retEq (_ , ff x _ _) α

  intro-natural : {x' x : B.0Cell} (k : B.1Cell x' x) (e : p[ x ])
    → CatIso B.Hom[ x' , vertex ] (k B.⋆₁ intro e) (intro (k ⋆ᴾ e))
  intro-natural k e =
    intro≡ (⋆Iso (invIso (⋆ᴾAssoc k (intro e) element))
                 (F-Iso {F = reind k} (β e)))

  intro-natural-β : {x' x : B.0Cell} (k : B.1Cell x' x) (e : p[ x ])
    → F-Iso {F = ⟨ element ⟩ x'} (intro-natural k e)
      ≡ ⋆Iso (⋆Iso (invIso (⋆ᴾAssoc k (intro e) element))
                   (F-Iso {F = reind k} (β e)))
             (invIso (β (k ⋆ᴾ e)))
  intro-natural-β k e =
    intro≡-β (⋆Iso (invIso (⋆ᴾAssoc k (intro e) element))
                   (F-Iso {F = reind k} (β e)))

-- `asPshIso` one dimension up.  It cannot be a member of
-- `BiuniversalElementNotation`: `PrestackHom` is homogeneous in
-- levels, so it forces `P` to live at the levels of B's hom-categories.
module _ {B : Bicategory ℓ ℓ' ℓ''} {P : Prestack B ℓ' ℓ''}
  (bue : BiuniversalElement P) where
  open BiuniversalElementNotation bue
  open PrestackIso

  asPrestackIso : PrestackIso (Hom B vertex) P
  asPrestackIso .trans = yoRecᴮᵖ P element
  asPrestackIso .nIso = universal
