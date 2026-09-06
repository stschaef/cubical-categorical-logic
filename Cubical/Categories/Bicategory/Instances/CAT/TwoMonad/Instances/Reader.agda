{-# OPTIONS --lossy-unification #-}
{-
  The reader 2-monad `T C = FUNCTOR A C` on CAT, for a fixed
  category `A`.

  Every object of a cartesian bicategory is a comonoid via its
  diagonal; `[A ,-]` is the 2-monad induced by that comonoid
  structure on `A`.  So `η` is restriction along `A → 1` and `μ` is
  currying followed by restriction along `Δ : A → A ×C A`; both are
  written out directly, since `λF⁻` composed with `Δ` would only
  reproduce `μF` with its functor laws packaged less usefully.

  Every laxity and coherence cell below has identity components: `T`
  is strictly functorial on 0- and 1-cells, and only the (invisible)
  functor laws differ, exactly as in `TwoMonads.Monoidal`.
-}
module Cubical.Categories.Bicategory.Instances.CAT.TwoMonad.Instances.Reader where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Category.More
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors

open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Identity
open import Cubical.Categories.Bicategory.Functor.Composition
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.Transformation.Properties
open import Cubical.Categories.Bicategory.Transformation.Composition
open import Cubical.Categories.Bicategory.Transformation.Whisker
open import Cubical.Categories.Bicategory.Transformation.Coherence
open import Cubical.Categories.Bicategory.TwoMonad.Base

open Category
open Functor
open NatTrans
open isIso
open Modification

module _ {ℓ : Level} (A : Category ℓ ℓ) where

  T₁ : {C D : Category ℓ ℓ} → Functor C D
     → Functor (FUNCTOR A C) (FUNCTOR A D)
  T₁ F .F-ob H = F ∘F H
  T₁ F .F-hom β .N-ob a = F .F-hom (β .N-ob a)
  T₁ {D = D} F .F-hom β .N-hom f =
      sym (F .F-seq _ _) ∙ cong (F .F-hom) (β .N-hom f) ∙ F .F-seq _ _
  T₁ F .F-id = makeNatTransPath (funExt λ a → F .F-id)
  T₁ F .F-seq β γ = makeNatTransPath (funExt λ a → F .F-seq _ _)

  T₂ : {C D : Category ℓ ℓ} {F G : Functor C D}
     → NatTrans F G → NatTrans (T₁ F) (T₁ G)
  T₂ α .N-ob H .N-ob a = α .N-ob (H .F-ob a)
  T₂ α .N-ob H .N-hom f = α .N-hom (H .F-hom f)
  T₂ α .N-hom β = makeNatTransPath (funExt λ a → α .N-hom (β .N-ob a))

  TFun : {C D : Category ℓ ℓ}
    → Functor (FUNCTOR C D) (FUNCTOR (FUNCTOR A C) (FUNCTOR A D))
  TFun .F-ob = T₁
  TFun .F-hom = T₂
  TFun .F-id = makeNatTransPath (funExt λ _ → makeNatTransPath refl)
  TFun .F-seq α β =
    makeNatTransPath (funExt λ _ → makeNatTransPath refl)

  -- `T₁` agrees with the identity/composite on objects and
  -- morphisms; only the functor laws differ, so the laxity cells are
  -- identity components.
  ιId-ob : {C : Category ℓ ℓ} (H : Functor A C)
    → NatTrans H (Id ∘F H)
  ιId-ob {C} H .N-ob a = C .id
  ιId-ob {C} H .N-hom f = C .⋆IdR _ ∙ sym (C .⋆IdL _)

  ιId : {C : Category ℓ ℓ} → NatTrans (Id {C = FUNCTOR A C}) (T₁ Id)
  ιId .N-ob = ιId-ob
  ιId {C} .N-hom β =
    makeNatTransPath (funExt λ a → C .⋆IdR _ ∙ sym (C .⋆IdL _))

  ιId⁻-ob : {C : Category ℓ ℓ} (H : Functor A C)
    → NatTrans (Id ∘F H) H
  ιId⁻-ob {C} H .N-ob a = C .id
  ιId⁻-ob {C} H .N-hom f = C .⋆IdR _ ∙ sym (C .⋆IdL _)

  ιId⁻ : {C : Category ℓ ℓ} → NatTrans (T₁ Id) (Id {C = FUNCTOR A C})
  ιId⁻ .N-ob = ιId⁻-ob
  ιId⁻ {C} .N-hom β =
    makeNatTransPath (funExt λ a → C .⋆IdR _ ∙ sym (C .⋆IdL _))

  ιSeq-ob : {C D E : Category ℓ ℓ} (F : Functor C D) (G : Functor D E)
    (H : Functor A C) → NatTrans (G ∘F (F ∘F H)) ((G ∘F F) ∘F H)
  ιSeq-ob {E = E} F G H .N-ob a = E .id
  ιSeq-ob {E = E} F G H .N-hom f = E .⋆IdR _ ∙ sym (E .⋆IdL _)

  ιSeq : {C D E : Category ℓ ℓ} (F : Functor C D) (G : Functor D E)
    → NatTrans (T₁ G ∘F T₁ F) (T₁ (G ∘F F))
  ιSeq F G .N-ob = ιSeq-ob F G
  ιSeq {E = E} F G .N-hom β =
    makeNatTransPath (funExt λ a → E .⋆IdR _ ∙ sym (E .⋆IdL _))

  ιSeq⁻-ob : {C D E : Category ℓ ℓ} (F : Functor C D) (G : Functor D E)
    (H : Functor A C) → NatTrans ((G ∘F F) ∘F H) (G ∘F (F ∘F H))
  ιSeq⁻-ob {E = E} F G H .N-ob a = E .id
  ιSeq⁻-ob {E = E} F G H .N-hom f = E .⋆IdR _ ∙ sym (E .⋆IdL _)

  ιSeq⁻ : {C D E : Category ℓ ℓ} (F : Functor C D) (G : Functor D E)
    → NatTrans (T₁ (G ∘F F)) (T₁ G ∘F T₁ F)
  ιSeq⁻ F G .N-ob = ιSeq⁻-ob F G
  ιSeq⁻ {E = E} F G .N-hom β =
    makeNatTransPath (funExt λ a → E .⋆IdR _ ∙ sym (E .⋆IdL _))


  RdLax : LaxFunctor (CAT {ℓ} {ℓ}) (CAT {ℓ} {ℓ})
  RdLax .LaxFunctor.F-ob C = FUNCTOR A C
  RdLax .LaxFunctor.F-Hom = TFun
  RdLax .LaxFunctor.F-id .N-ob _ = ιId
  RdLax .LaxFunctor.F-id .N-hom _ =
    makeNatTransPath (funExt λ _ → makeNatTransPath refl)
  RdLax .LaxFunctor.F-seq .N-ob (F , G) = ιSeq F G
  RdLax .LaxFunctor.F-seq {z = z} .N-hom (α , β) =
    makeNatTransPath (funExt λ _ → makeNatTransPath (funExt λ a →
      Q .⋆IdR _ ∙ sym (Q .⋆IdL _)))
    where Q = z
  RdLax .LaxFunctor.lax-λ x y f =
    makeNatTransPath (funExt λ p → makeNatTransPath (funExt λ a →
      collapse y (collapse y (f .F-id) refl) (y .⋆IdL _)))
  RdLax .LaxFunctor.lax-ρ x y f =
    makeNatTransPath (funExt λ p → makeNatTransPath (funExt λ a →
      four y))
  RdLax .LaxFunctor.lax-α x y z w f g h =
    makeNatTransPath (funExt λ p → makeNatTransPath (funExt λ a →
        collapse w (collapse w (h .F-id) refl) (w .⋆IdL _)
      ∙ sym (collapse w refl (collapse w
          (collapse w (cong (h .F-hom) (g .F-id) ∙ h .F-id) refl) refl))))

  RdPs : Pseudofunctor (CAT {ℓ} {ℓ}) (CAT {ℓ} {ℓ})
  RdPs .Pseudofunctor.laxFunctor = RdLax
  RdPs .Pseudofunctor.F-id-isIso {x} _ .inv = ιId⁻
  RdPs .Pseudofunctor.F-id-isIso {x} _ .sec =
    makeNatTransPath (funExt λ _ → makeNatTransPath (funExt λ a →
      x .⋆IdL _))
  RdPs .Pseudofunctor.F-id-isIso {x} _ .ret =
    makeNatTransPath (funExt λ _ → makeNatTransPath (funExt λ a →
      x .⋆IdL _))
  RdPs .Pseudofunctor.F-seq-isIso {z = z} (F , G) .inv = ιSeq⁻ F G
  RdPs .Pseudofunctor.F-seq-isIso {z = z} (F , G) .sec =
    makeNatTransPath (funExt λ _ → makeNatTransPath (funExt λ a →
      z .⋆IdL _))
  RdPs .Pseudofunctor.F-seq-isIso {z = z} (F , G) .ret =
    makeNatTransPath (funExt λ _ → makeNatTransPath (funExt λ a →
      z .⋆IdL _))

  constF : (C : Category ℓ ℓ) → C .ob → Functor A C
  constF C c .F-ob _ = c
  constF C c .F-hom _ = C .id
  constF C c .F-id = refl
  constF C c .F-seq _ _ = sym (C .⋆IdL _)

  ηF : (C : Category ℓ ℓ) → Functor C (FUNCTOR A C)
  ηF C .F-ob = constF C
  ηF C .F-hom g .N-ob _ = g
  ηF C .F-hom {c} {c'} g .N-hom f = C .⋆IdL _ ∙ sym (C .⋆IdR _)
  ηF C .F-id = makeNatTransPath refl
  ηF C .F-seq f g = makeNatTransPath refl

  -- The constant functor at `F c` is `F` after the constant functor
  -- at `c` only up to `F .F-id`.
  ηNat : {C D : Category ℓ ℓ} (F : Functor C D) (c : C .ob)
    → NatTrans (constF D (F .F-ob c)) (F ∘F constF C c)
  ηNat {D = D} F c .N-ob _ = D .id
  ηNat {D = D} F c .N-hom f = cong (λ m → D .id ⋆⟨ D ⟩ m) (sym (F .F-id))

  ReaderUnit : LaxNatTrans (LaxId (CAT {ℓ} {ℓ})) RdLax
  ReaderUnit .LaxNatTrans.N-1cell = ηF
  ReaderUnit .LaxNatTrans.N-hom F .N-ob = ηNat F
  ReaderUnit .LaxNatTrans.N-hom {y = D} F .N-hom g =
    makeNatTransPath (funExt λ a → D .⋆IdR _ ∙ sym (D .⋆IdL _))
  ReaderUnit .LaxNatTrans.N-natural {y = D} {f} θ =
    makeNatTransPath (funExt λ c → makeNatTransPath (funExt λ a →
        cong (λ m → m ⋆⟨ D ⟩ D .id) (D .⋆IdR _) ∙ D .⋆IdR _
      ∙ sym (D .⋆IdL _ ∙ collapseL D (f .F-id))))
  ReaderUnit .LaxNatTrans.lax-id C =
    makeNatTransPath (funExt λ c → makeNatTransPath (funExt λ a →
        collapse C (C .⋆IdL _) refl
      ∙ sym (collapse C refl (collapse C refl (C .⋆IdL _)))))
  ReaderUnit .LaxNatTrans.lax-seq {y = D} {z = E} f g =
    makeNatTransPath (funExt λ c → makeNatTransPath (funExt λ a →
      let pb = E .⋆IdR _ ∙ g .F-id
          pd = E .⋆IdR _ ∙ g .F-id
          pe = E .⋆IdR _ ∙ cong (g .F-hom) (f .F-id) ∙ g .F-id
      in  collapse E (E .⋆IdL _) refl
        ∙ sym (collapse E refl (collapse E pb
                (collapse E refl (collapse E pd
                  (collapse E refl pe)))))))


  μF : (C : Category ℓ ℓ)
    → Functor (FUNCTOR A (FUNCTOR A C)) (FUNCTOR A C)
  μF C .F-ob K .F-ob a = K .F-ob a .F-ob a
  μF C .F-ob K .F-hom {a} {a'} f =
    K .F-ob a .F-hom f ⋆⟨ C ⟩ K .F-hom f .N-ob a'
  μF C .F-ob K .F-id {a} =
    collapse C (K .F-ob a .F-id) (λ i → K .F-id i .N-ob a)
  μF C .F-ob K .F-seq {a} {a'} {a''} f g =
      cong₂ (λ m n → m ⋆⟨ C ⟩ n) (K .F-ob a .F-seq f g)
            (λ i → K .F-seq f g i .N-ob a'')
    ∙ exch C (K .F-ob a .F-hom f) (K .F-hom g .N-ob a'')
             (K .F-hom f .N-hom g)
  μF C .F-hom θ .N-ob a = θ .N-ob a .N-ob a
  μF C .F-hom {K} {L} θ .N-hom {a} {a'} f =
      C .⋆Assoc _ _ _
    ∙ cong (λ m → K .F-ob a .F-hom f ⋆⟨ C ⟩ m)
           (λ i → θ .N-hom f i .N-ob a')
    ∙ sym (C .⋆Assoc _ _ _)
    ∙ cong (λ m → m ⋆⟨ C ⟩ L .F-hom f .N-ob a') (θ .N-ob a .N-hom f)
    ∙ C .⋆Assoc _ _ _
  μF C .F-id = makeNatTransPath refl
  μF C .F-seq θ φ = makeNatTransPath refl

  μNat : {C D : Category ℓ ℓ} (F : Functor C D)
    (K : Functor A (FUNCTOR A C))
    → NatTrans (μF D .F-ob (T₁ F ∘F K)) (F ∘F μF C .F-ob K)
  μNat {D = D} F K .N-ob a = D .id
  μNat {D = D} F K .N-hom f =
    D .⋆IdR _ ∙ sym (F .F-seq _ _) ∙ sym (D .⋆IdL _)

  ReaderMult : LaxNatTrans (RdLax ∘Lax RdLax) RdLax
  ReaderMult .LaxNatTrans.N-1cell = μF
  ReaderMult .LaxNatTrans.N-hom F .N-ob = μNat F
  ReaderMult .LaxNatTrans.N-hom {y = D} F .N-hom θ =
    makeNatTransPath (funExt λ a → D .⋆IdR _ ∙ sym (D .⋆IdL _))
  ReaderMult .LaxNatTrans.N-natural {y = D} {f} θ =
    makeNatTransPath (funExt λ K → makeNatTransPath (funExt λ a →
        cong (λ m → m ⋆⟨ D ⟩ D .id) (D .⋆IdR _) ∙ D .⋆IdR _
      ∙ sym (D .⋆IdL _ ∙ collapseL D (f .F-id))))
  ReaderMult .LaxNatTrans.lax-id C =
    makeNatTransPath (funExt λ K → makeNatTransPath (funExt λ a →
        collapse C (collapse C (C .⋆IdL _) refl) refl
      ∙ sym (collapse C refl (collapse C refl (C .⋆IdL _)))))
  ReaderMult .LaxNatTrans.lax-seq {y = D} {z = E} f g =
    makeNatTransPath (funExt λ K → makeNatTransPath (funExt λ a →
      let pB = E .⋆IdR _ ∙ g .F-id
          pD = E .⋆IdR _ ∙ g .F-id
          pF = E .⋆IdR _ ∙ cong (g .F-hom) (f .F-id) ∙ g .F-id
      in  collapse E (collapse E (E .⋆IdL _) refl) refl
        ∙ sym (collapse E refl (collapse E pB
                (collapse E refl (collapse E pD
                  (collapse E refl pF)))))))

  private
    unitL-ob : (C : Category ℓ ℓ) (H : Functor A C)
      → NatTrans (μF C .F-ob (ηF C ∘F H)) H
    unitL-ob C H .N-ob a = C .id
    unitL-ob C H .N-hom f = C .⋆IdR _

  unitLMod : Modification
    (seqLaxNatTrans (whiskerL RdPs ReaderUnit) ReaderMult) (ridLax RdLax)
  unitLMod .M-ob C .N-ob = unitL-ob C
  unitLMod .M-ob C .N-hom θ =
    makeNatTransPath (funExt λ a → C .⋆IdR _ ∙ sym (C .⋆IdL _))
  unitLMod .M-hom {y = D} f =
    makeNatTransPath (funExt λ H → makeNatTransPath (funExt λ a →
      let pX1 = collapse D (collapse D refl (D .⋆IdL _)) refl
          pX2 = D .⋆IdR _ ∙ f .F-id
          pX3 = D .⋆IdR _ ∙ f .F-id
          L1 = collapse D refl (collapse D pX1
                 (collapse D refl (collapse D pX2 refl)))
      in  cong⋆ D L1 pX3 ∙ D .⋆IdL (D .id)
        ∙ sym (cong⋆ D (D .⋆IdL _) (D .⋆IdL (D .id)) ∙ D .⋆IdR (D .id))))

  private
    unitR-ob : (C : Category ℓ ℓ) (H : Functor A C)
      → NatTrans (μF C .F-ob (constF (FUNCTOR A C) H)) H
    unitR-ob C H .N-ob a = C .id
    unitR-ob C H .N-hom f =
      cong (λ m → m ⋆⟨ C ⟩ C .id) (C .⋆IdR _) ∙ C .⋆IdR _
      ∙ sym (C .⋆IdL _)

  unitRMod : Modification
    (seqLaxNatTrans (whiskerR RdLax ReaderUnit) ReaderMult) (lidLax RdLax)
  unitRMod .M-ob C .N-ob = unitR-ob C
  unitRMod .M-ob C .N-hom θ =
    makeNatTransPath (funExt λ a → C .⋆IdR _ ∙ sym (C .⋆IdL _))
  unitRMod .M-hom {y = D} f =
    makeNatTransPath (funExt λ H → makeNatTransPath (funExt λ a →
      let pX2 = D .⋆IdR _ ∙ f .F-id
          pX3 = D .⋆IdR _ ∙ f .F-id
          L1 = collapse D refl (collapse D (D .⋆IdL _)
                 (collapse D refl (collapse D pX2 refl)))
      in  cong⋆ D L1 pX3 ∙ D .⋆IdL (D .id)
        ∙ sym (cong⋆ D (D .⋆IdL _) (D .⋆IdL (D .id)) ∙ D .⋆IdR (D .id))))

  private
    assoc-ob : (C : Category ℓ ℓ) (K : Functor A (FUNCTOR A (FUNCTOR A C)))
      → NatTrans (μF C .F-ob (μF (FUNCTOR A C) .F-ob K))
                 (μF C .F-ob (μF C ∘F K))
    assoc-ob C K .N-ob a = C .id
    assoc-ob C K .N-hom f =
      C .⋆IdR _ ∙ sym (C .⋆Assoc _ _ _) ∙ sym (C .⋆IdL _)

  assocMod' : Modification
    (seqLaxNatTrans (whiskerR RdLax ReaderMult) ReaderMult)
    (seqLaxNatTrans (assocLax RdLax RdLax RdLax)
      (seqLaxNatTrans (whiskerL RdPs ReaderMult) ReaderMult))
  assocMod' .M-ob C .N-ob = assoc-ob C
  assocMod' .M-ob C .N-hom θ =
    makeNatTransPath (funExt λ a → C .⋆IdR _ ∙ sym (C .⋆IdL _))
  assocMod' .M-hom {y = D} f =
    makeNatTransPath (funExt λ K → makeNatTransPath (funExt λ a →
      let pX2 = D .⋆IdR _ ∙ f .F-id
          pX3 = D .⋆IdR _ ∙ f .F-id
          L1 = collapse D refl (collapse D (D .⋆IdL _)
                 (collapse D refl (collapse D pX2 refl)))
          pB1 = collapse D (D .⋆IdL _) refl
          pZ1 = collapse D (collapse D refl (D .⋆IdL _)) refl
          pZ2 = D .⋆IdR _ ∙ f .F-id
          pB2b = collapse D refl (collapse D pZ1
                   (collapse D refl (collapse D pZ2 refl)))
          R1 = collapse D refl (collapse D pB1
                 (collapse D refl
                   (collapse D (collapse D (f .F-id) pB2b) refl)))
      in  cong⋆ D L1 pX3 ∙ D .⋆IdL (D .id)
        ∙ sym (cong⋆ D (D .⋆IdL _) R1 ∙ D .⋆IdR (D .id))))

  private
    idIsIso : (C : Category ℓ ℓ) {x : C .ob} {g : C [ x , x ]}
      → g ≡ C .id → isIso C g
    idIsIso C p .inv = C .id
    idIsIso C p .sec = cong (λ m → C .id ⋆⟨ C ⟩ m) p ∙ C .⋆IdL _
    idIsIso C p .ret = cong (λ m → m ⋆⟨ C ⟩ C .id) p ∙ C .⋆IdL _

  ReaderTwoMonad : TwoMonad (CAT {ℓ} {ℓ})
  ReaderTwoMonad .TwoMonad.T = RdPs
  ReaderTwoMonad .TwoMonad.η = ReaderUnit
  ReaderTwoMonad .TwoMonad.μ = ReaderMult
  ReaderTwoMonad .TwoMonad.unitL =
    unitLMod , modIsIso unitLMod (λ C →
      FUNCTORIso (FUNCTOR A C) (FUNCTOR A C) _
        (λ H → FUNCTORIso A C (unitL-ob C H) (λ a → idIsIso C refl)))
  ReaderTwoMonad .TwoMonad.unitR =
    unitRMod , modIsIso unitRMod (λ C →
      FUNCTORIso (FUNCTOR A C) (FUNCTOR A C) _
        (λ H → FUNCTORIso A C (unitR-ob C H) (λ a → idIsIso C refl)))
  ReaderTwoMonad .TwoMonad.assoc =
    assocMod' , modIsIso assocMod' (λ C →
      FUNCTORIso (FUNCTOR A (FUNCTOR A (FUNCTOR A C))) (FUNCTOR A C) _
        (λ K → FUNCTORIso A C (assoc-ob C K) (λ a → idIsIso C refl)))

-- A pseudoalgebra is `a : FUNCTOR A C → C` with `a ∘F constF ≅ Id`
-- and `a ∘F T₁ a ≅ a ∘F μF C`: an A-ary rectangular band on `C`.
-- For `A` discrete on two objects that forces `C ≃ C₁ ×C C₂` with
-- `a (x , y) = (x .fst , y .snd)`; for `A` empty it forces `C ≃ 1`.
