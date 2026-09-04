{-# OPTIONS --lossy-unification #-}
{- Lax and pseudo functors on opposite bicategories. -}
module Cubical.Categories.Bicategory.Functor.Op where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Morphism
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Constructions.Op
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo

private
  variable
    ℓa ℓa' ℓa'' ℓb ℓb' ℓb'' : Level

open Functor
open NatTrans
open NatIso
open isIso
open LaxFunctor
open Pseudofunctor

module _ {A : Bicategory ℓa ℓa' ℓa''} {B : Bicategory ℓb ℓb' ℓb''}
  (F : LaxFunctor A B) where
  private
    module A = Bicategory A
    module B = Bicategory B
    module F = LaxFunctor F

  OpLax : LaxFunctor (A ^opᴮ) (B ^opᴮ)
  OpLax .F-ob = F.F-ob
  OpLax .F-Hom {x} {y} = F.F-Hom {y} {x}
  OpLax .F-id {x} = F.F-id {x}
  OpLax .F-seq {x} {y} {z} .N-ob (k , l) = F.F-seq {z} {y} {x} .N-ob (l , k)
  OpLax .F-seq {x} {y} {z} .N-hom (σ , τ) =
    F.F-seq {z} {y} {x} .N-hom (τ , σ)
  OpLax .lax-λ x y f = F.lax-ρ y x f
  OpLax .lax-ρ x y f = F.lax-λ y x f
  OpLax .lax-α x y z w f g h =
    ⋆InvLMove Siso
      ( B.⟨⟩⋆₂⟨ sym (B.⋆₂Assoc _ _ _) ⟩
      ∙ sym (B.⋆₂Assoc _ _ _)
      ∙ B.⟨ sym (F.lax-α w z y x h g f) ⟩⋆₂⟨⟩
      ∙ B.⋆₂Assoc _ _ _
      ∙ B.⟨⟩⋆₂⟨ B.⋆₂Assoc _ _ _ ∙ B.⟨⟩⋆₂⟨ Rret ⟩ ∙ B.⋆₂IdR _ ⟩)
    where
    Siso = isIso→CatIso
      (B.α (F.F-ob w) (F.F-ob z) (F.F-ob y) (F.F-ob x)
         .nIso (F.F-1cell h , F.F-1cell g , F.F-1cell f))
    Rret : F.F-2cell (A.α⁺ h g f) B.⋆₂ F.F-2cell (A.α⁻ h g f) ≡ B.id₂
    Rret = F-PresIsIso {F = F.F-Hom} (A.α w z y x .nIso (h , g , f)) .ret

module _ {A : Bicategory ℓa ℓa' ℓa''} {B : Bicategory ℓb ℓb' ℓb''}
  (F : Pseudofunctor A B) where
  private
    module F = Pseudofunctor F

  OpPs : Pseudofunctor (A ^opᴮ) (B ^opᴮ)
  OpPs .laxFunctor = OpLax (F .laxFunctor)
  OpPs .F-id-isIso p = F.F-id-isIso p
  OpPs .F-seq-isIso (k , l) = F.F-seq-isIso (l , k)
