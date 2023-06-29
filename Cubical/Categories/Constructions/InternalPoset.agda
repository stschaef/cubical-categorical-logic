{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.InternalPoset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Unit
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Exponentials
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.Preorders.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Preorders.Forgetful
open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Yoneda.More

open import Cubical.Categories.Constructions.DisplayedCategory
open import Cubical.Categories.Constructions.DisplayedCategory.DisplayedPoset
open import Cubical.Categories.Constructions.DisplayedCategory.Grothendieck
open import Cubical.Categories.Constructions.BinProduct.Redundant.Base
import Cubical.Categories.Constructions.BinProduct.Redundant.Base as R

open import Cubical.Relation.Binary.Poset
open import Cubical.Relation.Binary.Preorder

open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
import Cubical.Categories.Bifunctor.Redundant as R

open Category



-- Define some order theory internal to the category of presheaves.
module _ {ℓC ℓC' : Level} (C : Category ℓC ℓC' )
  (bp : BinProducts C)
  (bpPsh : BinProducts (PresheafCategory C (ℓ-max ℓC ℓC')))
  (expPsh : Exponentials (PresheafCategory C (ℓ-max ℓC ℓC')) bpPsh)
  where

  bpSET : BinProducts (SET (ℓ-max ℓC ℓC'))
  bpSET = λ x y →
    record {
    binProdOb = x .fst Cubical.Data.Sigma.× y .fst , λ p q e₁ e₂ i →
      ΣPathP
      (x .snd (p .fst) (q .fst) (cong fst e₁) (cong fst e₂) i ,
      y .snd (p .snd) (q .snd) (cong snd e₁) (cong snd e₂) i
      );
    binProdPr₁ = fst ;
    binProdPr₂ = snd ;
    univProp =
    λ {z} p₁ p₂ →
      ((λ a → p₁ a , p₂ a) , refl , refl) ,
      λ (mor , fstMor≡p₁ , sndMor≡p₂) →
        let q = (λ i z₀ → fstMor≡p₁ (~ i) z₀ , sndMor≡p₂ (~ i) z₀)
        in
        Σ≡Prop (λ f →
          isProp× (isSetHom (SET (ℓ-max ℓC ℓC')) {z}{x} (λ x → fst (f x)) p₁)
                  (isSetHom (SET (ℓ-max ℓC ℓC')) {z}{y} (λ x → snd (f x)) p₂))
          q
    }

  -- record InternalPreorder : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' ℓS))) where
  --   field
  --     P : PresheafCategory C ℓS .ob
  --     _≤_ : ∀ {Γ} → (x y : (P ⟅ Γ ⟆) .fst) → Set ℓS wv
  --     rel-is-poset : ∀ Γ → IsPreorder (_≤_ {Γ})
  --     naturally-monotone : {Γ Δ : C .ob} → (γ : C [ Δ , Γ ]) →
  --     (x y : (P ⟅ Γ ⟆) .fst) →
  --       x ≤ y → (C [ x ∘ᴾ⟨ P ⟩ γ ]) ≤ (C [ y ∘ᴾ⟨ P ⟩ γ ])

  record InternalPoset : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' ℓC'))) where
    field
      P : PresheafCategory C (ℓ-max ℓC ℓC') .ob
      _≤_ : ∀ {Γ} → (x y : (P ⟅ Γ ⟆) .fst) → Type (ℓ-max ℓC ℓC')
      ≤-is-poset : ∀ Γ → IsPoset (_≤_ {Γ})
      naturally-monotone : {Γ Δ : C .ob} → (γ : C [ Δ , Γ ]) →
        (x y : (P ⟅ Γ ⟆) .fst) →
        x ≤ y → (C [ x ∘ᴾ⟨ P ⟩ γ ]) ≤ (C [ y ∘ᴾ⟨ P ⟩ γ ])

  open InternalPoset
  open PreorderStr
  open IsPoset

  IsPoset→Preorder : (C .ob) → InternalPoset →
                     Preorder (ℓ-max ℓC ℓC') (ℓ-max ℓC ℓC')
  IsPoset→Preorder Γ X = 
    preorder ((X .P ⟅ Γ ⟆) .fst) (X ._≤_)
            (ispreorder ((X .P ⟅ Γ ⟆) .snd)
            (X .≤-is-poset Γ .is-prop-valued)
            (X .≤-is-poset Γ .is-refl)
            ((X .≤-is-poset Γ .is-trans)))

  record InternalPosetMonotone (X Y : InternalPoset) :
    Type (ℓ-suc (ℓ-max ℓC ℓC')) where
    field
      fun : ∀ Γ → MonFun (IsPoset→Preorder Γ X) (IsPoset→Preorder Γ Y)
      commutes-with-reindexing : ∀ {Γ Δ} → (γ : C [ Δ , Γ ]) →
        (x : (X .P ⟅ Γ ⟆) .fst) →
        C [ fun Γ $ x ∘ᴾ⟨ Y .P ⟩ γ ] ≡ fun Δ $ (C [ x ∘ᴾ⟨ X .P ⟩ γ ])

  open MonFun
  open Functor
  open ExpNotation
  open Notation
  open R.Bifunctor
  open NatTrans

  -- Lifted version of YONEDA from Cubical.Categories.Yoneda.More
  -- TODO: make this more universe polymorphic.
  Yon : Functor C (PresheafCategory C (ℓ-max ℓC ℓC'))
  Yon .F-ob a = LiftF {ℓC'}{ℓ-max ℓC ℓC'} ∘F (C [-, a ])
  Yon .F-hom f .N-ob b g = lift (lower g ⋆⟨ C ⟩ f)
  Yon .F-hom f .N-hom g = funExt (λ h i → lift (C .⋆Assoc g (lower h) f i))
  Yon .F-id =
    makeNatTransPath
      (funExt (λ a → funExt (λ f i → lift (C .⋆IdR (lower f) i ))))
  Yon .F-seq f g =
    makeNatTransPath
      (funExt (λ a → funExt (λ h i → lift (C .⋆Assoc (lower h) f g (~ i)))))


  -- Power : (X : InternalPoset) →
  --         (A : PresheafCategory C (ℓ-max ℓC ℓC') .ob) →
  --         InternalPoset
  -- Power X A .P =
  --   {! (PresheafCategory C (ℓ-max ℓC ℓC')) [-, (X .P)] !}
  -- Power X A ._≤_ {Γ} f g =
  --     (Δ : C .ob) →
  --     (γ : C [ Δ , Γ ]) →
  --     (a : (A ⟅ Δ ⟆) .fst) →
  --     X ._≤_ {Δ}
  --       {!!}
  --       {!!}

    -- (Δ : C .ob) → (γ : C [ Δ , Γ ]) →
    -- (a : (A ⟅ Δ ⟆) .fst ) →
    -- X ._≤_ {Δ}
      -- ((f .N-ob Δ) {!!})
      -- ((g .N-ob Δ) {!!})
  -- Power X A .≤-is-poset = {!!}
  -- Power X A .naturally-monotone = {!YONEDA!}

  -- X^A(Γ) = Set^{C ^op} (YΓ × A , X)
  Power : (X : InternalPoset) →
          (A : PresheafCategory C (ℓ-max ℓC ℓC') .ob) →
          InternalPoset
  Power X A .P =
    ((PresheafCategory C (ℓ-max ℓC ℓC')) [-, (X .P) ]) ∘F
    (((R.appR (×Bif (PresheafCategory C (ℓ-max ℓC ℓC')) bpPsh) A) ^opF)) ∘F
    (BinProductWithF (PresheafCategory C (ℓ-max ℓC ℓC')) (bpPsh A) ^opF) ∘F
    (Yon ^opF)
  Power X A ._≤_ {Γ} f g =
    (Δ : C .ob) → (γ : C [ Δ , Γ ]) →
    (a : (A ⟅ Δ ⟆) .fst ) →
    X ._≤_ {Δ}
      ((f .N-ob Δ) {!!})
      ((g .N-ob Δ) {!!})
  Power X A .≤-is-poset = {!!}
  Power X A .naturally-monotone = {!YONEDA!}

  -- FunctorToPoset≅InternalPoset : Iso (Functor (C ^op) (POSET' ℓS ℓS))
  --                                    InternalPoset
  -- FunctorToPoset≅InternalPoset =
  --   iso
  --   the-fun
  --   the-inv
  --   -- Either the definitional behavior of the-fun and the-inv aren't good enough
  --   -- or maybe its nicer to appeal to the fact that all of
  --   -- PREORDER→SET, GrothendieckForgetful, and DisplayedPoset→Cat are morally
  --   -- the indentity/forgetful and we are only forgetting trivial information
  --   (λ X → {!!})
  --   (λ F → Functor≡ (λ Γ → {!!}) {!!})
  --   where
  --     the-fun : (Functor (C ^op) (POSET' ℓS ℓS)) → InternalPoset
  --     the-fun F .P =
      --   PREORDER→SET ℓS ℓS
      --     ∘F Cubical.Categories.Constructions.DisplayedCategory.Grothendieck.Fst
      --        (PREORDER ℓS ℓS)
      --        {DisplayedPoset→Cat (PREORDER ℓS ℓS) PosetDisplay}
      --     ∘F F
      -- the-fun F ._≤_ {Γ} = (F ⟅ Γ ⟆) .fst .snd ._≤_
      -- the-fun F .≤-is-poset = λ Γ → (F ⟅ Γ ⟆) .snd
      -- the-fun F .naturally-monotone = λ γ x y x≤y → (F ⟪ γ ⟫) .fst .isMon x≤y

      -- the-mon-fun : {x y : C .ob} → (C ^op) [ x , y ] →
      --               (X : InternalPoset) →
      --               MonFun (IsPoset→Preorder x X) (IsPoset→Preorder y X)
      -- the-mon-fun f X .f = X .P ⟪ f ⟫
      -- the-mon-fun f X .isMon = X .naturally-monotone f _ _

      -- the-inv : InternalPoset → (Functor (C ^op) (POSET' ℓS ℓS))
      -- the-inv X .F-ob = λ Γ → IsPoset→Preorder Γ X , X .≤-is-poset Γ
      -- the-inv X .F-hom = λ f → the-mon-fun f X , tt*
      -- the-inv X .F-id =
      --   ΣPathP ((eqMon (the-mon-fun (C .id) X) MonId (X .P .F-id)) , refl)
      -- the-inv X .F-seq f g =
      --   ΣPathP (
      --   (eqMon
      --     (fst (the-inv X .F-hom (seq' (C ^op) f g)))
      --     (MonComp (the-mon-fun f X) (the-mon-fun g X))
      --     (X .P .F-seq f g)) , refl)
