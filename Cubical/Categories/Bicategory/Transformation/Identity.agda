{-# OPTIONS --lossy-unification #-}
{- The identity lax natural transformation on a lax functor. -}
module Cubical.Categories.Bicategory.Transformation.Identity where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More hiding (α)

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Transformation

private
  variable
    ℓb ℓb' ℓb'' ℓc ℓc' ℓc'' : Level

open NatIso
open isIso
open LaxNatTrans

private
  module _ (C : Bicategory ℓc ℓc' ℓc'') where
    private
      module C = Bicategory C

    push : {w x : C.0Cell} {p q r s t u v : C.1Cell w x}
      (e₁ : C.2Cell p q) (e₂ : C.2Cell q r) (e₃ : C.2Cell r s)
      (e₄ : C.2Cell s t) (e₅ : C.2Cell t u) (e₆ : C.2Cell u v)
      →   e₁ C.⋆₂ e₂ C.⋆₂ e₃ C.⋆₂ e₄ C.⋆₂ e₅ C.⋆₂ e₆
        ≡ (e₁ C.⋆₂ e₂ C.⋆₂ e₃ C.⋆₂ e₄ C.⋆₂ e₅) C.⋆₂ e₆
    push e₁ e₂ e₃ e₄ e₅ e₆ =
        C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ sym (C.⋆₂Assoc e₄ e₅ e₆) ⟩
                      ∙ sym (C.⋆₂Assoc e₃ _ e₆) ⟩
              ∙ sym (C.⋆₂Assoc e₂ _ e₆) ⟩
      ∙ sym (C.⋆₂Assoc e₁ _ e₆)

    module _ {x y z : C.0Cell} (a : C.1Cell x y) (b : C.1Cell y z) where
      private
        u₁ = a C.◁w C.ρ⁺ b
        u₂ = a C.◁w C.λ⁻ b
        v₁ = C.ρ⁺ a C.▷w b
        v₂ = C.λ⁻ a C.▷w b
        A⁻ = C.α⁻ a C.id₁ b
        A⁺ = C.α⁺ C.id₁ a b
        L  = C.λ⁻ (a C.⋆₁ b)

        mid : u₂ C.⋆₂ (A⁻ C.⋆₂ v₁) ≡ C.id₂
        mid =
            C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ sym (C.triangle x y z a b) ⟩
                  ∙ sym (C.⋆₂Assoc _ _ _)
                  ∙ C.⟨ C.α x y y z .nIso (a , C.id₁ , b) .sec ⟩⋆₂⟨⟩
                  ∙ C.⋆₂IdL _ ⟩
          ∙ sym (◁wSeq C a (C.λ⁻ b) (C.λ⁺ b))
          ∙ a C.◁⟨ C.λU y z .nIso (tt* , b) .sec ⟩
          ∙ C.◁wId a

        tail : u₂ C.⋆₂ (A⁻ C.⋆₂ ((v₁ C.⋆₂ v₂) C.⋆₂ A⁺)) ≡ L
        tail =
            C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⋆₂Assoc v₁ v₂ A⁺ ⟩
                  ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ λ⁻⋆₁ C a b ⟩ ⟩
                  ∙ sym (C.⋆₂Assoc A⁻ v₁ L) ⟩
          ∙ sym (C.⋆₂Assoc u₂ (A⁻ C.⋆₂ v₁) L)
          ∙ C.⟨ mid ⟩⋆₂⟨⟩
          ∙ C.⋆₂IdL L

      -- The coherence underlying `lax-seq`: pure unitor/associator data.
      unitCoh :
          C.α⁺ a b C.id₁ C.⋆₂ (a C.◁w (C.ρ⁺ b C.⋆₂ C.λ⁻ b))
            C.⋆₂ C.α⁻ a C.id₁ b C.⋆₂ ((C.ρ⁺ a C.⋆₂ C.λ⁻ a) C.▷w b)
            C.⋆₂ C.α⁺ C.id₁ a b
        ≡ C.ρ⁺ (a C.⋆₁ b) C.⋆₂ C.λ⁻ (a C.⋆₁ b)
      unitCoh =
          C.⟨⟩⋆₂⟨ C.⟨ ◁wSeq C a (C.ρ⁺ b) (C.λ⁻ b) ⟩⋆₂⟨
                    C.⟨⟩⋆₂⟨ C.⟨ ▷wSeq C (C.ρ⁺ a) (C.λ⁻ a) b ⟩⋆₂⟨⟩ ⟩ ⟩ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⋆₂Assoc u₁ u₂ _ ⟩
        ∙ sym (C.⋆₂Assoc (C.α⁺ a b C.id₁) u₁ _)
        ∙ C.⟨ ρ⋆₁ C b a ⟩⋆₂⟨⟩
        ∙ C.⟨⟩⋆₂⟨ tail ⟩

module _ {B : Bicategory ℓb ℓb' ℓb''} {C : Bicategory ℓc ℓc' ℓc''}
  (F : LaxFunctor B C) where
  private
    module B = Bicategory B
    module C = Bicategory C
    module F = LaxFunctor F

  idLaxNatTrans : LaxNatTrans F F
  idLaxNatTrans .N-1cell x = C.id₁
  idLaxNatTrans .N-hom f = C.ρ⁺ (F.F-1cell f) C.⋆₂ C.λ⁻ (F.F-1cell f)
  idLaxNatTrans .N-natural θ =
      sym (C.⋆₂Assoc _ _ _)
    ∙ C.⟨ ρ-nat C (F.F-2cell θ) ⟩⋆₂⟨⟩
    ∙ C.⋆₂Assoc _ _ _
    ∙ C.⟨⟩⋆₂⟨ λ⁻-nat C (F.F-2cell θ) ⟩
    ∙ sym (C.⋆₂Assoc _ _ _)
  idLaxNatTrans .lax-id x =
      sym (C.⋆₂Assoc _ _ _)
    ∙ C.⟨ ρ-nat C F.F⁰ ⟩⋆₂⟨⟩
    ∙ C.⋆₂Assoc _ _ _
    ∙ C.⟨⟩⋆₂⟨ λ⁻-nat C F.F⁰ ⟩
    ∙ sym (C.⋆₂Assoc _ _ _)
    ∙ C.⟨ C.⟨ sym (λ⁺≡ρ⁺ C) ⟩⋆₂⟨ λ⁻≡ρ⁻ C ⟩ ⟩⋆₂⟨⟩
    ∙ C.⋆₂Assoc _ _ _
  idLaxNatTrans .lax-seq f g =
      sym (C.⋆₂Assoc _ _ _)
    ∙ C.⟨ ρ-nat C (F.F² f g) ⟩⋆₂⟨⟩
    ∙ C.⋆₂Assoc _ _ _
    ∙ C.⟨⟩⋆₂⟨ λ⁻-nat C (F.F² f g) ⟩
    ∙ sym (C.⋆₂Assoc _ _ _)
    ∙ C.⟨ sym (unitCoh C (F.F-1cell f) (F.F-1cell g)) ⟩⋆₂⟨⟩
    ∙ sym (push C _ _ _ _ _ _)

  -- the identity transformation is pseudonatural
  idIsPseudo : {x y : B.ob} (f : B.1Cell x y)
    → isIso C.Hom[ F.F-ob x , F.F-ob y ] (idLaxNatTrans .LaxNatTrans.N-hom f)
  idIsPseudo f =
    ⋆IsIso (C.ρU _ _ .nIso (_ , _))
           (invIso (_ , C.λU _ _ .nIso (_ , _)) .snd)
