{- Lax functors between bicategories -}
module Cubical.Categories.Bicategory.Functor.Lax where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Terminal

open import Cubical.Categories.Bicategory.Base

private
  variable
    ℓb ℓb' ℓb'' ℓc ℓc' ℓc'' : Level

record LaxFunctor (B : Bicategory ℓb ℓb' ℓb'')
                  (C : Bicategory ℓc ℓc' ℓc'') :
                  Type (ℓ-max (ℓ-max ℓb (ℓ-max ℓb' ℓb''))
                              (ℓ-max ℓc (ℓ-max ℓc' ℓc''))) where
  no-eta-equality

  private
    module B = Bicategory B
    module C = Bicategory C

  field
    F-ob  : B.ob → C.ob
    F-Hom : ∀ {x y : B.ob}
      → Functor B.Hom[ x , y ] C.Hom[ F-ob x , F-ob y ]

  F-1cell : ∀ {x y} → B.1Cell x y → C.1Cell (F-ob x) (F-ob y)
  F-1cell {x}{y} f = Functor.F-ob (F-Hom {x}{y}) f

  F-2cell : ∀ {x y}{f g : B.1Cell x y}
    → B.2Cell f g → C.2Cell (F-1cell f) (F-1cell g)
  F-2cell {x}{y} α = Functor.F-hom (F-Hom {x}{y}) α

  field
    F-id : ∀ {x : B.ob}
      → NatTrans (C.id {F-ob x}) (F-Hom {x}{x} ∘F B.id {x})

    F-seq : ∀ {x y z : B.ob}
      → NatTrans
          (C.seq (F-ob x) (F-ob y) (F-ob z) ∘F (F-Hom {x}{y} ×F F-Hom {y}{z}))
          (F-Hom {x}{z} ∘F B.seq x y z)

  F⁰ : ∀ {x} → C.2Cell C.id₁ (F-1cell (B.id₁ {x}))
  F⁰ {x} = NatTrans.N-ob (F-id {x}) tt*

  F² : ∀ {x y z}
    (f : B.1Cell x y) (g : B.1Cell y z)
    → C.2Cell (F-1cell f C.⋆₁ F-1cell g) (F-1cell (f B.⋆₁ g))
  F² {x}{y}{z} f g = NatTrans.N-ob (F-seq {x}{y}{z}) (f , g)

  field
    lax-λ : (x y : B.ob) (f : B.1Cell x y)
      →   (F⁰ C.▷w F-1cell f) C.⋆₂ F² B.id₁ f C.⋆₂ F-2cell (B.λ⁺ f)
        ≡ C.λ⁺ (F-1cell f)

    lax-ρ : (x y : B.ob) (f : B.1Cell x y)
      →   (F-1cell f C.◁w F⁰) C.⋆₂ F² f B.id₁ C.⋆₂ F-2cell (B.ρ⁺ f)
        ≡ C.ρ⁺ (F-1cell f)

    lax-α : (x y z w : B.ob)
      (f : B.1Cell x y) (g : B.1Cell y z) (h : B.1Cell z w)
      →    (F² f g C.▷w F-1cell h) C.⋆₂ F² (f B.⋆₁ g) h
             C.⋆₂ F-2cell (B.α⁺ f g h)
        ≡  C.α⁺ (F-1cell f) (F-1cell g) (F-1cell h)
           C.⋆₂ (F-1cell f C.◁w F² g h)
           C.⋆₂ F² f (g B.⋆₁ h)
