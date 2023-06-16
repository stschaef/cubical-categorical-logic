{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.InternalPoset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base

open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.Preorders.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Preorders.Forgetful
open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Constructions.Subcategory

open import Cubical.Relation.Binary.Poset
open import Cubical.Relation.Binary.Preorder

open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More

private
  variable
    ℓC ℓC' : Level

open Category

-- Define some order theory internal to the category of presheaves.
module _ (C : Category ℓC ℓC' ) (ℓS : Level) where
  -- record InternalPreorder : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' ℓS))) where
  --   field
  --     P : PresheafCategory C ℓS .ob
  --     _≤_ : ∀ {Γ} → (x y : (P ⟅ Γ ⟆) .fst) → Set ℓS
  --     rel-is-poset : ∀ Γ → IsPreorder (_≤_ {Γ})
  --     naturally-monotone : {Γ Δ : C .ob} → (γ : C [ Δ , Γ ]) → (x y : (P ⟅ Γ ⟆) .fst) →
  --       x ≤ y → (C [ x ∘ᴾ⟨ P ⟩ γ ]) ≤ (C [ y ∘ᴾ⟨ P ⟩ γ ])

  record InternalPoset : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' ℓS))) where
    field
      P : PresheafCategory C ℓS .ob
      _≤_ : ∀ {Γ} → (x y : (P ⟅ Γ ⟆) .fst) → Set ℓS
      ≤-is-poset : ∀ Γ → IsPoset (_≤_ {Γ})
      naturally-monotone : {Γ Δ : C .ob} → (γ : C [ Δ , Γ ]) → (x y : (P ⟅ Γ ⟆) .fst) →
        x ≤ y → (C [ x ∘ᴾ⟨ P ⟩ γ ]) ≤ (C [ y ∘ᴾ⟨ P ⟩ γ ])

  open InternalPoset
  open PreorderStr
  open IsPoset


  IsPoset→Preorder : (C .ob) → InternalPoset → Preorder ℓS ℓS
  IsPoset→Preorder Γ X = 
    preorder ((X .P ⟅ Γ ⟆) .fst) (X ._≤_)
            (ispreorder ((X .P ⟅ Γ ⟆) .snd)
            (X .≤-is-poset Γ .is-prop-valued)
            (X .≤-is-poset Γ .is-refl)
            ((X .≤-is-poset Γ .is-trans)))

  record InternalPosetMonotone (X Y : InternalPoset) : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' ℓS))) where
    field
      fun : ∀ Γ → MonFun (IsPoset→Preorder Γ X) (IsPoset→Preorder Γ Y)
      commutes-with-reindexing : ∀ {Γ Δ} → (γ : C [ Δ , Γ ]) → (x : (X .P ⟅ Γ ⟆) .fst) →
        C [ fun Γ $ x ∘ᴾ⟨ Y .P ⟩ γ ] ≡ fun Δ $ (C [ x ∘ᴾ⟨ X .P ⟩ γ ])

  open MonFun

  FunctorToPoset≅InternalPoset : Iso (Functor (C ^op) (POSET' ℓS ℓS)) (InternalPoset)
  FunctorToPoset≅InternalPoset =
    iso
    (λ F → record
          { P = PREORDER→SET ℓS ℓS ∘F GrothendieckForgetful
                                   (PREORDER ℓS ℓS) {_}
                                   {DisplayedPoset→Cat (PREORDER ℓS ℓS) PosetDisplay} ∘F F ;
          _≤_ = λ {Γ} → (F ⟅ Γ ⟆) .fst .snd ._≤_ ;
          ≤-is-poset = λ Γ → (F ⟅ Γ ⟆) .snd ;
          naturally-monotone = λ γ x y x≤y → (F ⟪ γ ⟫) .fst .isMon x≤y })
    (λ X → record { F-ob = {!!} ; F-hom = {!!} ; F-id = {!!} ; F-seq = {!!} })
    {!!}
    {!!}
