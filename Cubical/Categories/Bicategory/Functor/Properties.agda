{- Derived properties of a lax functor. -}
module Cubical.Categories.Bicategory.Functor.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo

private
  variable
    ℓb ℓb' ℓb'' ℓc ℓc' ℓc'' : Level

open Functor

-- Naturality of a lax functor's composition constraint in each slot.
module _ {B : Bicategory ℓb ℓb' ℓb''} {C : Bicategory ℓc ℓc' ℓc''}
         (K : LaxFunctor B C) where
  private
    module B = Bicategory B
    module C = Bicategory C
    module K = LaxFunctor K

  F²nat▷ : ∀ {x y z}{a a' : B.1Cell x y} (α : B.2Cell a a')
    (b : B.1Cell y z)
    →   (K.F-2cell α C.▷w K.F-1cell b) C.⋆₂ K.F² a' b
      ≡ K.F² a b C.⋆₂ K.F-2cell (α B.▷w b)
  F²nat▷ α b =
      C.⟨ C.⟨⟩⋆ₕ⟨ sym (K.F-Hom .F-id) ⟩ ⟩⋆₂⟨⟩
    ∙ NatTrans.N-hom K.F-seq (α , B.id₂)

  F²nat◁ : ∀ {x y z} (a : B.1Cell x y){b b' : B.1Cell y z}
    (β : B.2Cell b b')
    →   (K.F-1cell a C.◁w K.F-2cell β) C.⋆₂ K.F² a b'
      ≡ K.F² a b C.⋆₂ K.F-2cell (a B.◁w β)
  F²nat◁ a β =
      C.⟨ C.⟨ sym (K.F-Hom .F-id) ⟩⋆ₕ⟨⟩ ⟩⋆₂⟨⟩
    ∙ NatTrans.N-hom K.F-seq (B.id₂ , β)

-- The laxity constraints of a pseudofunctor, as isomorphisms.
module _ {B : Bicategory ℓb ℓb' ℓb''} {C : Bicategory ℓc ℓc' ℓc''}
         (K : Pseudofunctor B C) where
  private
    module B = Bicategory B
    module C = Bicategory C
    module K = Pseudofunctor K

  κ⁰I : ∀ {x} → C.id₁ C.≅₂ K.F-1cell (B.id₁ {x})
  κ⁰I = K.F⁰ , K.F-id-isIso tt*

  κ⁰⁻ : ∀ {x} → C.2Cell (K.F-1cell (B.id₁ {x})) C.id₁
  κ⁰⁻ = κ⁰I .snd .isIso.inv

  κ²I : ∀ {x y z} (a : B.1Cell x y) (b : B.1Cell y z)
    → (K.F-1cell a C.⋆₁ K.F-1cell b) C.≅₂ K.F-1cell (a B.⋆₁ b)
  κ²I a b = K.F² a b , K.F-seq-isIso (a , b)

  κ²⁻ : ∀ {x y z} (a : B.1Cell x y) (b : B.1Cell y z)
    → C.2Cell (K.F-1cell (a B.⋆₁ b)) (K.F-1cell a C.⋆₁ K.F-1cell b)
  κ²⁻ a b = κ²I a b .snd .isIso.inv
