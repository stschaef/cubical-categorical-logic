{-# OPTIONS --lossy-unification #-}
{-
  The 2-monad `T C = M ×C C` on CAT induced by a monoidal category M.

  `T` is a strict 2-functor and `η c = (unit , c)`,
  `μ (m , (n , c)) = (m ⊗ n , c)` are strict 2-natural; the three
  2-monad laws are the unitors and associator of M, which are honest
  morphisms of M, so no transports occur anywhere.  Strictness of M
  is not wanted here: it is exactly what would turn the three laws
  into transport squares.  See `Monoidal.Strict.Forded`.
-}
module Cubical.Categories.Bicategory.Instances.CAT.TwoMonads.Monoidal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Category.More
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Terminal
open import Cubical.Categories.Monoidal.Base

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Functor.Identity
open import Cubical.Categories.Bicategory.Functor.Composition
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.Transformation.Properties
open import Cubical.Categories.Bicategory.Transformation.Identity
open import Cubical.Categories.Bicategory.Transformation.Composition
open import Cubical.Categories.Bicategory.Transformation.Whisker
open import Cubical.Categories.Bicategory.Transformation.Coherence
open import Cubical.Categories.Bicategory.TwoMonad.Base

private
  variable
    ℓ ℓ' : Level

open Category
open Functor
open NatTrans
open isIso
open NatIso
open Modification

module _ {ℓ ℓ' : Level} (M : MonoidalCategory ℓ ℓ') where
  private
    module M = MonoidalCategory M

  T₁ : {C D : Category ℓ ℓ'} → Functor C D
     → Functor (M.C ×C C) (M.C ×C D)
  T₁ F .F-ob (m , c) = m , F .F-ob c
  T₁ F .F-hom (f , g) = f , F .F-hom g
  T₁ F .F-id = λ i → M.id , F .F-id i
  T₁ F .F-seq (f , g) (f' , g') = λ i → f M.⋆ f' , F .F-seq g g' i

  T₂ : {C D : Category ℓ ℓ'} {F G : Functor C D}
     → NatTrans F G → NatTrans (T₁ F) (T₁ G)
  T₂ α .N-ob (m , c) = M.id , α .N-ob c
  T₂ {D = D} α .N-hom (f , g) =
    ΣPathP (M.⋆IdR f ∙ sym (M.⋆IdL f) , α .N-hom g)

  TFun : {C D : Category ℓ ℓ'}
    → Functor (FUNCTOR C D) (FUNCTOR (M.C ×C C) (M.C ×C D))
  TFun .F-ob = T₁
  TFun .F-hom = T₂
  TFun .F-id = makeNatTransPath (funExt λ _ → refl)
  TFun {D = D} .F-seq α β =
    makeNatTransPath (funExt λ _ → ΣPathP (sym (M.⋆IdL M.id) , refl))

  -- `T₁` agrees with the identity/composite on objects and
  -- morphisms; only the (proof-irrelevant) functor laws differ, so
  -- the laxity cells below are identity components.
  ιId : {C : Category ℓ ℓ'} → NatTrans (Id {C = M.C ×C C}) (T₁ Id)
  ιId {C} .N-ob _ = (M.C ×C C) .id
  ιId {C} .N-hom f = (M.C ×C C) .⋆IdR _ ∙ sym ((M.C ×C C) .⋆IdL _)

  ιSeq : {C D E : Category ℓ ℓ'} (F : Functor C D) (G : Functor D E)
    → NatTrans (T₁ G ∘F T₁ F) (T₁ (G ∘F F))
  ιSeq {C} {D} {E} F G .N-ob _ = (M.C ×C E) .id
  ιSeq {C} {D} {E} F G .N-hom f =
    (M.C ×C E) .⋆IdR _ ∙ sym ((M.C ×C E) .⋆IdL _)


  MonLax : LaxFunctor (CAT {ℓ} {ℓ'}) (CAT {ℓ} {ℓ'})
  MonLax .LaxFunctor.F-ob C = M.C ×C C
  MonLax .LaxFunctor.F-Hom = TFun
  MonLax .LaxFunctor.F-id .N-ob _ = ιId
  MonLax .LaxFunctor.F-id .N-hom _ =
    makeNatTransPath (funExt λ _ → refl)
  MonLax .LaxFunctor.F-seq .N-ob (F , G) = ιSeq F G
  MonLax .LaxFunctor.F-seq {x} {y} {z} .N-hom (α , β) =
    makeNatTransPath (funExt λ _ →
      ΣPathP ( M.⋆IdR _
             , z .⋆IdR _ ∙ sym (z .⋆IdL _)))
  MonLax .LaxFunctor.lax-λ x y f =
    makeNatTransPath (funExt λ p →
        cong (λ m → (m ⋆⟨ Q ⟩ Q .id) ⋆⟨ Q ⟩ (Q .id ⋆⟨ Q ⟩ Q .id))
             (T₁ f .F-id)
      ∙ four Q)
    where Q = M.C ×C y
  MonLax .LaxFunctor.lax-ρ x y f =
    makeNatTransPath (funExt λ p → four (M.C ×C y))
  MonLax .LaxFunctor.lax-α x y z w f g h =
    makeNatTransPath (funExt λ p →
        ( cong (λ m → (m ⋆⟨ Q ⟩ Q .id) ⋆⟨ Q ⟩ (Q .id ⋆⟨ Q ⟩ Q .id))
               (T₁ h .F-id)
        ∙ four Q)
      ∙ sym ( cong (λ m → Q .id ⋆⟨ Q ⟩ ((m ⋆⟨ Q ⟩ Q .id) ⋆⟨ Q ⟩ Q .id))
                   (cong (T₁ h .F-hom) (T₁ g .F-id) ∙ T₁ h .F-id)
            ∙ four' Q))
    where Q = M.C ×C w

  ιId⁻ : {C : Category ℓ ℓ'} → NatTrans (T₁ Id) (Id {C = M.C ×C C})
  ιId⁻ {C} .N-ob _ = (M.C ×C C) .id
  ιId⁻ {C} .N-hom f = (M.C ×C C) .⋆IdR _ ∙ sym ((M.C ×C C) .⋆IdL _)

  ιSeq⁻ : {C D E : Category ℓ ℓ'} (F : Functor C D) (G : Functor D E)
    → NatTrans (T₁ (G ∘F F)) (T₁ G ∘F T₁ F)
  ιSeq⁻ {C} {D} {E} F G .N-ob _ = (M.C ×C E) .id
  ιSeq⁻ {C} {D} {E} F G .N-hom f =
    (M.C ×C E) .⋆IdR _ ∙ sym ((M.C ×C E) .⋆IdL _)

  MonPs : Pseudofunctor (CAT {ℓ} {ℓ'}) (CAT {ℓ} {ℓ'})
  MonPs .Pseudofunctor.laxFunctor = MonLax
  MonPs .Pseudofunctor.F-id-isIso {x} _ .inv = ιId⁻
  MonPs .Pseudofunctor.F-id-isIso {x} _ .sec =
    makeNatTransPath (funExt λ _ → (M.C ×C x) .⋆IdL _)
  MonPs .Pseudofunctor.F-id-isIso {x} _ .ret =
    makeNatTransPath (funExt λ _ → (M.C ×C x) .⋆IdL _)
  MonPs .Pseudofunctor.F-seq-isIso {z = z} (F , G) .inv = ιSeq⁻ F G
  MonPs .Pseudofunctor.F-seq-isIso {z = z} (F , G) .sec =
    makeNatTransPath (funExt λ _ → (M.C ×C z) .⋆IdL _)
  MonPs .Pseudofunctor.F-seq-isIso {z = z} (F , G) .ret =
    makeNatTransPath (funExt λ _ → (M.C ×C z) .⋆IdL _)

  ηF : (C : Category ℓ ℓ') → Functor C (M.C ×C C)
  ηF C .F-ob c = M.unit , c
  ηF C .F-hom g = M.id , g
  ηF C .F-id = refl
  ηF C .F-seq f g = λ i → M.⋆IdL M.id (~ i) , f ⋆⟨ C ⟩ g

  MonUnit : LaxNatTrans (LaxId (CAT {ℓ} {ℓ'})) MonLax
  MonUnit .LaxNatTrans.N-1cell = ηF
  MonUnit .LaxNatTrans.N-hom {y = D} F .N-ob _ = (M.C ×C D) .id
  MonUnit .LaxNatTrans.N-hom {y = D} F .N-hom f =
    (M.C ×C D) .⋆IdR _ ∙ sym ((M.C ×C D) .⋆IdL _)
  MonUnit .LaxNatTrans.N-natural {y = D} {f} θ =
    makeNatTransPath (funExt λ c →
        cong (λ m → m ⋆⟨ Q ⟩ Q .id) (Q .⋆IdR _) ∙ Q .⋆IdR _
      ∙ sym (Q .⋆IdL _ ∙ collapseL Q (T₁ f .F-id)))
    where Q = M.C ×C D
  MonUnit .LaxNatTrans.lax-id C =
    makeNatTransPath (funExt λ c →
        collapse Q (Q .⋆IdL _) refl
      ∙ sym (collapse Q refl (collapse Q refl (Q .⋆IdL _))))
    where Q = M.C ×C C
  MonUnit .LaxNatTrans.lax-seq {z = E} f g =
    makeNatTransPath (funExt λ c →
      let Q = M.C ×C E
          pb = Q .⋆IdR _ ∙ cong (ηF E .F-hom) (g .F-id)
          pd = Q .⋆IdR _ ∙ T₁ g .F-id
          pe = Q .⋆IdR _ ∙ cong (T₁ g .F-hom) (T₁ f .F-id) ∙ T₁ g .F-id
      in  collapse Q (Q .⋆IdL _) refl
        ∙ sym (collapse Q refl (collapse Q pb
                (collapse Q refl (collapse Q pd
                  (collapse Q refl pe))))))

  μF : (C : Category ℓ ℓ') → Functor (M.C ×C (M.C ×C C)) (M.C ×C C)
  μF C .F-ob (m , (n , c)) = m M.⊗ n , c
  μF C .F-hom (f , (g , h)) = f M.⊗ₕ g , h
  μF C .F-id = λ i → M.─⊗─ .F-id i , C .id
  μF C .F-seq (f , (g , h)) (f' , (g' , h')) =
    λ i → M.─⊗─ .F-seq (f , g) (f' , g') i , h ⋆⟨ C ⟩ h'

  MonMult : LaxNatTrans (MonLax ∘Lax MonLax) MonLax
  MonMult .LaxNatTrans.N-1cell = μF
  MonMult .LaxNatTrans.N-hom {y = D} F .N-ob _ = (M.C ×C D) .id
  MonMult .LaxNatTrans.N-hom {y = D} F .N-hom f =
    (M.C ×C D) .⋆IdR _ ∙ sym ((M.C ×C D) .⋆IdL _)
  MonMult .LaxNatTrans.N-natural {y = D} {f} θ =
    makeNatTransPath (funExt λ p →
      let Q = M.C ×C D in
        cong (λ m → m ⋆⟨ Q ⟩ Q .id) (Q .⋆IdR _) ∙ Q .⋆IdR _
      ∙ (λ i → M.─⊗─ .F-id i , θ .N-ob (p .snd .snd))
      ∙ sym (Q .⋆IdL _ ∙ collapseL Q (T₁ f .F-id)))
  MonMult .LaxNatTrans.lax-id C =
    makeNatTransPath (funExt λ p →
      let Q = M.C ×C C
          R = M.C ×C (M.C ×C C)
          pA = cong (μF C .F-hom) (R .⋆IdL _) ∙ μF C .F-id
      in  collapse Q (collapse Q pA refl) refl
        ∙ sym (collapse Q refl (collapse Q refl (Q .⋆IdL _))))
  MonMult .LaxNatTrans.lax-seq {y = D} {z = E} f g =
    makeNatTransPath (funExt λ p →
      let Q = M.C ×C E
          R = M.C ×C (M.C ×C E)
          pA = cong (μF E .F-hom) (R .⋆IdL _) ∙ μF E .F-id
          pB = Q .⋆IdR _ ∙ cong (μF E .F-hom) (T₁ (T₁ g) .F-id)
             ∙ μF E .F-id
          pD = Q .⋆IdR _ ∙ T₁ g .F-id
          pF = Q .⋆IdR _ ∙ cong (T₁ g .F-hom) (T₁ f .F-id) ∙ T₁ g .F-id
      in  collapse Q (collapse Q pA refl) refl
        ∙ sym (collapse Q refl (collapse Q pB
                (collapse Q refl (collapse Q pD
                  (collapse Q refl pF))))))

  ρN : (C : Category ℓ ℓ') (m : M.ob) (c : C .ob)
    → (M.C ×C C) [ (m M.⊗ M.unit , c) , (m , c) ]
  ρN C m c = M.ρ⟨ m ⟩ , C .id

  unitLMod : Modification (seqLaxNatTrans (whiskerL MonPs MonUnit) MonMult)
                          (ridLax MonLax)
  unitLMod .M-ob C .N-ob (m , c) = ρN C m c
  unitLMod .M-ob C .N-hom {y = y} (f , g) =
    ΣPathP (M.ρ .trans .N-hom f , C .⋆IdR g ∙ sym (C .⋆IdL g))
  unitLMod .M-hom {x = C} {y = D} f =
    makeNatTransPath (funExt λ p →
      let Q = M.C ×C D
          R = M.C ×C (M.C ×C D)
          pX1 = Q .⋆IdR _
              ∙ cong (μF D .F-hom) (R .⋆IdL _ ∙ R .⋆IdL _)
              ∙ μF D .F-id
          pX2 = Q .⋆IdR _
              ∙ cong (μF D .F-hom) (T₁ (T₁ f) .F-id) ∙ μF D .F-id
          pX3 = Q .⋆IdR _ ∙ (λ i → M.ρ⟨ p .fst ⟩ , f .F-id i)
          pY1 = collapseL Q (cong (μF D .F-hom) (T₁ (ηF D) .F-id)
                             ∙ μF D .F-id)
          L1 = collapse Q refl (collapse Q pX1
                 (collapse Q refl (collapse Q pX2 refl)))
          rho = ρN D (p .fst) (f .F-ob (p .snd))
      in  cong⋆ Q L1 pX3 ∙ Q .⋆IdL rho
        ∙ sym ( cong⋆ Q pY1 (Q .⋆IdL (Q .id))
              ∙ Q .⋆IdR rho))

  ηN : (C : Category ℓ ℓ') (m : M.ob) (c : C .ob)
    → (M.C ×C C) [ (M.unit M.⊗ m , c) , (m , c) ]
  ηN C m c = M.η⟨ m ⟩ , C .id

  unitRMod : Modification (seqLaxNatTrans (whiskerR MonLax MonUnit) MonMult)
                          (lidLax MonLax)
  unitRMod .M-ob C .N-ob (m , c) = ηN C m c
  unitRMod .M-ob C .N-hom (f , g) =
    ΣPathP (M.η .trans .N-hom f , C .⋆IdR g ∙ sym (C .⋆IdL g))
  unitRMod .M-hom {x = C} {y = D} f =
    makeNatTransPath (funExt λ p →
      let Q = M.C ×C D
          pX1 = Q .⋆IdR _ ∙ μF D .F-id
          pX2 = Q .⋆IdR _
              ∙ cong (μF D .F-hom) (T₁ (T₁ f) .F-id) ∙ μF D .F-id
          pX3 = Q .⋆IdR _ ∙ (λ i → M.η⟨ p .fst ⟩ , f .F-id i)
          pY1 = collapseL Q (cong (μF D .F-hom) (ηF (M.C ×C D) .F-id)
                             ∙ μF D .F-id)
          L1 = collapse Q refl (collapse Q pX1
                 (collapse Q refl (collapse Q pX2 refl)))
          eta = ηN D (p .fst) (f .F-ob (p .snd))
      in  cong⋆ Q L1 pX3 ∙ Q .⋆IdL eta
        ∙ sym ( cong⋆ Q pY1 (Q .⋆IdL (Q .id))
              ∙ Q .⋆IdR eta))

  αN : (C : Category ℓ ℓ') (k m n : M.ob) (c : C .ob)
    → (M.C ×C C) [ ((k M.⊗ m) M.⊗ n , c) , (k M.⊗ (m M.⊗ n) , c) ]
  αN C k m n c = M.α⁻¹⟨ k , m , n ⟩ , C .id

  assocMod' : Modification
    (seqLaxNatTrans (whiskerR MonLax MonMult) MonMult)
    (seqLaxNatTrans (assocLax MonLax MonLax MonLax)
      (seqLaxNatTrans (whiskerL MonPs MonMult) MonMult))
  assocMod' .M-ob C .N-ob (k , (m , (n , c))) = αN C k m n c
  assocMod' .M-ob C .N-hom (f , (g , (h , u))) =
    ΣPathP ( symNatIso M.α .trans .N-hom (f , (g , h))
           , C .⋆IdR u ∙ sym (C .⋆IdL u))
  assocMod' .M-hom {x = C} {y = D} f =
    makeNatTransPath (funExt λ p →
      let Q = M.C ×C D
          R = M.C ×C (M.C ×C D)
          S = M.C ×C (M.C ×C (M.C ×C D))
          Tμ₁ = T₁ (μF D)
          GD = μF D ∘F Tμ₁
          pX1 = Q .⋆IdR _ ∙ μF D .F-id
          pX2 = Q .⋆IdR _
              ∙ cong (μF D .F-hom) (T₁ (T₁ f) .F-id) ∙ μF D .F-id
          pX3 = Q .⋆IdR _
              ∙ (λ i → M.α⁻¹⟨ p .fst , p .snd .fst , p .snd .snd .fst ⟩
                     , f .F-id i)
          L1 = collapse Q refl (collapse Q pX1
                 (collapse Q refl (collapse Q pX2 refl)))
          pW = collapseL Q (cong (μF D .F-hom) (μF (M.C ×C D) .F-id)
                            ∙ μF D .F-id)
          pB1 = Q .⋆IdR _ ∙ cong (GD .F-hom) (S .⋆IdL (S .id))
              ∙ cong (μF D .F-hom) (Tμ₁ .F-id) ∙ μF D .F-id
          pZ1 = Q .⋆IdR _
              ∙ cong (μF D .F-hom) ( R .⋆IdL (R .id ⋆⟨ R ⟩ R .id)
                                   ∙ R .⋆IdL (R .id))
              ∙ μF D .F-id
          pZ2 = Q .⋆IdR _
              ∙ cong (μF D .F-hom) (T₁ (T₁ f) .F-id) ∙ μF D .F-id
          pB2a = cong (GD .F-hom) (T₁ (T₁ (T₁ f)) .F-id)
               ∙ cong (μF D .F-hom) (Tμ₁ .F-id) ∙ μF D .F-id
          pB2b = collapse Q refl (collapse Q pZ1
                   (collapse Q refl (collapse Q pZ2 refl)))
          R1 = collapse Q refl (collapse Q pB1
                 (collapse Q refl (collapse Q (collapse Q pB2a pB2b) refl)))
          al = αN D (p .fst) (p .snd .fst) (p .snd .snd .fst)
                 (f .F-ob (p .snd .snd .snd))
      in  cong⋆ Q L1 pX3 ∙ Q .⋆IdL al
        ∙ sym (cong⋆ Q pW R1 ∙ Q .⋆IdR al))

  private
    ρIso : (C : Category ℓ ℓ') (m : M.ob) (c : C .ob)
      → isIso (M.C ×C C) (ρN C m c)
    ρIso C m c .inv = M.ρ⁻¹⟨ m ⟩ , C .id
    ρIso C m c .sec = ΣPathP (M.ρ .nIso m .sec , C .⋆IdL (C .id))
    ρIso C m c .ret = ΣPathP (M.ρ .nIso m .ret , C .⋆IdL (C .id))

    ηIso : (C : Category ℓ ℓ') (m : M.ob) (c : C .ob)
      → isIso (M.C ×C C) (ηN C m c)
    ηIso C m c .inv = M.η⁻¹⟨ m ⟩ , C .id
    ηIso C m c .sec = ΣPathP (M.η .nIso m .sec , C .⋆IdL (C .id))
    ηIso C m c .ret = ΣPathP (M.η .nIso m .ret , C .⋆IdL (C .id))

    αIso : (C : Category ℓ ℓ') (k m n : M.ob) (c : C .ob)
      → isIso (M.C ×C C) (αN C k m n c)
    αIso C k m n c .inv = M.α⟨ k , m , n ⟩ , C .id
    αIso C k m n c .sec =
      ΣPathP (M.α .nIso (k , m , n) .ret , C .⋆IdL (C .id))
    αIso C k m n c .ret =
      ΣPathP (M.α .nIso (k , m , n) .sec , C .⋆IdL (C .id))

  MonoidalTwoMonad : TwoMonad (CAT {ℓ} {ℓ'})
  MonoidalTwoMonad .TwoMonad.T = MonPs
  MonoidalTwoMonad .TwoMonad.η = MonUnit
  MonoidalTwoMonad .TwoMonad.μ = MonMult
  MonoidalTwoMonad .TwoMonad.unitL =
    unitLMod , modIsIso unitLMod (λ C →
      FUNCTORIso (M.C ×C C) (M.C ×C C) _
        (λ p → ρIso C (p .fst) (p .snd)))
  MonoidalTwoMonad .TwoMonad.unitR =
    unitRMod , modIsIso unitRMod (λ C →
      FUNCTORIso (M.C ×C C) (M.C ×C C) _
        (λ p → ηIso C (p .fst) (p .snd)))
  MonoidalTwoMonad .TwoMonad.assoc =
    assocMod' , modIsIso assocMod' (λ C →
      FUNCTORIso (M.C ×C (M.C ×C (M.C ×C C))) (M.C ×C C) _
        (λ p → αIso C (p .fst) (p .snd .fst)
          (p .snd .snd .fst) (p .snd .snd .snd)))

-- An algebra for this 2-monad is a category `C` with a functor
-- `M ×C C → C` that is unital and associative up to coherent
-- isomorphism: an action of `M` on `C`, i.e. an `M`-actegory.
