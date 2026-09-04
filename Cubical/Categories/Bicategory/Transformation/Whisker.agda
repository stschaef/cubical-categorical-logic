{-# OPTIONS --lossy-unification #-}
{-
  Right whiskering of a lax natural transformation, and of a
  modification, by a lax functor.  Together these give a functor
  between hom-categories of lax functors.
-}
module Cubical.Categories.Bicategory.Transformation.Whisker where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Composition
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.Transformation.Properties

private
  variable
    ℓa ℓa' ℓa'' ℓb ℓb' ℓb'' ℓc ℓc' ℓc'' : Level

open Functor
open LaxFunctor
open LaxNatTrans
open Modification

module _ {A : Bicategory ℓa ℓa' ℓa''}
         {B : Bicategory ℓb ℓb' ℓb''}
         {C : Bicategory ℓc ℓc' ℓc''}
         {F G : LaxFunctor B C}
         (K : LaxFunctor A B) where
  private
    module A = Bicategory A
    module B = Bicategory B
    module C = Bicategory C
    module F = LaxFunctor F
    module G = LaxFunctor G
    module K = LaxFunctor K

  module _ (σ : LaxNatTrans F G) where
    private
      module σ = LaxNatTrans σ

      n : (x : A.ob) → C.1Cell (F.F-ob (K.F-ob x)) (G.F-ob (K.F-ob x))
      n x = σ.N-1cell (K.F-ob x)

      nh : ∀ {x y} (f : A.1Cell x y)
        → C.2Cell (F.F-1cell (K.F-1cell f) C.⋆₁ n y)
                  (n x C.⋆₁ G.F-1cell (K.F-1cell f))
      nh f = σ.N-hom (K.F-1cell f)

      wnat : ∀ {x y}{f g : A.1Cell x y} (θ : A.2Cell f g)
        →   (F.F-2cell (K.F-2cell θ) C.▷w n y) C.⋆₂ nh g
          ≡ nh f C.⋆₂ (n x C.◁w G.F-2cell (K.F-2cell θ))
      wnat θ = σ.N-natural (K.F-2cell θ)

      wid : (x : A.ob)
        →   ((F.F⁰ C.⋆₂ F.F-2cell K.F⁰) C.▷w n x) C.⋆₂ nh A.id₁
          ≡   C.λ⁺ (n x) C.⋆₂ C.ρ⁻ (n x)
            C.⋆₂ (n x C.◁w (G.F⁰ C.⋆₂ G.F-2cell K.F⁰))
      wid x =
          C.⟨ ▷wSeq C F.F⁰ (F.F-2cell K.F⁰) (n x) ⟩⋆₂⟨⟩
        ∙ C.⋆₂Assoc _ _ _
        ∙ C.⟨⟩⋆₂⟨ σ.N-natural K.F⁰ ⟩
        ∙ sym (C.⋆₂Assoc _ _ _)
        ∙ C.⟨ σ.lax-id (K.F-ob x) ⟩⋆₂⟨⟩
        ∙ C.⋆₂Assoc _ _ _
        ∙ C.⟨⟩⋆₂⟨ C.⋆₂Assoc _ _ _ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ sym (◁wSeq C (n x) G.F⁰ (G.F-2cell K.F⁰)) ⟩ ⟩

      wseq : ∀ {x y z} (f : A.1Cell x y) (g : A.1Cell y z)
        →   ((F.F² (K.F-1cell f) (K.F-1cell g) C.⋆₂ F.F-2cell (K.F² f g))
               C.▷w n z)
            C.⋆₂ nh (f A.⋆₁ g)
          ≡   C.α⁺ (F.F-1cell (K.F-1cell f)) (F.F-1cell (K.F-1cell g)) (n z)
            C.⋆₂ (F.F-1cell (K.F-1cell f) C.◁w nh g)
            C.⋆₂ C.α⁻ (F.F-1cell (K.F-1cell f)) (n y)
                      (G.F-1cell (K.F-1cell g))
            C.⋆₂ (nh f C.▷w G.F-1cell (K.F-1cell g))
            C.⋆₂ C.α⁺ (n x) (G.F-1cell (K.F-1cell f))
                      (G.F-1cell (K.F-1cell g))
            C.⋆₂ (n x C.◁w (G.F² (K.F-1cell f) (K.F-1cell g)
                              C.⋆₂ G.F-2cell (K.F² f g)))
      wseq f g =
          C.⟨ ▷wSeq C (F.F² (K.F-1cell f) (K.F-1cell g))
                      (F.F-2cell (K.F² f g)) (n _) ⟩⋆₂⟨⟩
        ∙ C.⋆₂Assoc _ _ _
        ∙ C.⟨⟩⋆₂⟨ σ.N-natural (K.F² f g) ⟩
        ∙ sym (C.⋆₂Assoc _ _ _)
        ∙ C.⟨ σ.lax-seq (K.F-1cell f) (K.F-1cell g) ⟩⋆₂⟨⟩
        ∙ C.⋆₂Assoc _ _ _
        ∙ C.⟨⟩⋆₂⟨ C.⋆₂Assoc _ _ _ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⋆₂Assoc _ _ _ ⟩ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⋆₂Assoc _ _ _ ⟩ ⟩ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⋆₂Assoc _ _ _ ⟩ ⟩ ⟩ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
            sym (◁wSeq C (n _) (G.F² (K.F-1cell f) (K.F-1cell g))
                              (G.F-2cell (K.F² f g))) ⟩ ⟩ ⟩ ⟩ ⟩

    whiskerR : LaxNatTrans (F ∘Lax K) (G ∘Lax K)
    whiskerR .N-1cell = n
    whiskerR .N-hom = nh
    whiskerR .N-natural = wnat
    whiskerR .lax-id = wid
    whiskerR .lax-seq = wseq

  whiskerRMod : {σ τ : LaxNatTrans F G}
    → Modification σ τ → Modification (whiskerR σ) (whiskerR τ)
  whiskerRMod Γ .M-ob x = Γ .M-ob (K.F-ob x)
  whiskerRMod Γ .M-hom f = Γ .M-hom (K.F-1cell f)

  whiskerRF : Functor (LaxNatTransCat {F = F} {G = G})
                      (LaxNatTransCat {F = F ∘Lax K} {G = G ∘Lax K})
  whiskerRF .F-ob = whiskerR
  whiskerRF .F-hom = whiskerRMod
  whiskerRF .F-id = makeModificationPath λ x → refl
  whiskerRF .F-seq Γ Δ = makeModificationPath λ x → refl
