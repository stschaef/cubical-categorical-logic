{- Prestacks: pseudofunctors B ^opᴮ → CAT, the bicategorical presheaves. -}
module Cubical.Categories.Bicategory.Prestack.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.BinProduct

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Constructions.Op
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo

private
  variable
    ℓ ℓ' ℓ'' ℓp ℓp' : Level

open Functor
open NatTrans
open NatIso
open isIso

module _ {C : Category ℓ ℓ'} {D : Category ℓp ℓp'} where
  evalAtF : D .Category.ob → Functor (FUNCTOR D C) C
  evalAtF d .F-ob F = F .F-ob d
  evalAtF d .F-hom α = α .N-ob d
  evalAtF d .F-id = refl
  evalAtF d .F-seq _ _ = refl

Prestack : (B : Bicategory ℓ ℓ' ℓ'') (ℓp ℓp' : Level) → Type _
Prestack B ℓp ℓp' = Pseudofunctor (B ^opᴮ) (CAT {ℓp} {ℓp'})

module PrestackNotation {B : Bicategory ℓ ℓ' ℓ''} (P : Prestack B ℓp ℓp') where
  private
    module B = Bicategory B
  module P = Pseudofunctor P

  P⟨_⟩ : B.0Cell → Category ℓp ℓp'
  P⟨ x ⟩ = P.F-ob x

  p[_] : B.0Cell → Type ℓp
  p[ x ] = P⟨ x ⟩ .Category.ob

  -- the hom-category's own notation (⋆IdL, ⋆Assoc, ⟨_⟩⋆⟨_⟩, ...)
  module Pᶜ {x : B.0Cell} = Category P⟨ x ⟩

  reind : {x y : B.0Cell} → B.1Cell x y → Functor P⟨ y ⟩ P⟨ x ⟩
  reind k = P.F-1cell k

  _⋆ᴾ_ : {x y : B.0Cell} → B.1Cell x y → p[ y ] → p[ x ]
  k ⋆ᴾ e = reind k .F-ob e

  ⟨_⟩ : {a : B.0Cell} → p[ a ] → (x : B.0Cell)
    → Functor B.Hom[ x , a ] P⟨ x ⟩
  ⟨ e ⟩ x = evalAtF e ∘F P.F-Hom

  ⋆ᴾIdL : {x : B.0Cell} (e : p[ x ]) → CatIso P⟨ x ⟩ (B.id₁ ⋆ᴾ e) e
  ⋆ᴾIdL e = invIso (P.F⁰ .N-ob e , F-PresIsIso {F = evalAtF e} (P.F-id-isIso _))

  ⋆ᴾAssoc : {x' x a : B.0Cell} (k : B.1Cell x' x) (f : B.1Cell x a)
    (e : p[ a ]) → CatIso P⟨ x' ⟩ (k ⋆ᴾ (f ⋆ᴾ e)) ((k B.⋆₁ f) ⋆ᴾ e)
  ⋆ᴾAssoc k f e .fst = P.F² f k .N-ob e
  ⋆ᴾAssoc k f e .snd = F-PresIsIso {F = evalAtF e} (P.F-seq-isIso (f , k))
