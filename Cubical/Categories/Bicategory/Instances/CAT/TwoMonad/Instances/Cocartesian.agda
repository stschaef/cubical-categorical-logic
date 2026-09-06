{-# OPTIONS --lossy-unification #-}
{-
  The free cocartesian category 2-monad on CAT.

  Dual to the cartesian case, and built on the same underlying free
  construction: `|FreeCocartesianOn| C` is `|FreeCartesianOn| (C ^op)
  ^op`.  What the duality moves is the hypothesis of the two
  dimensional uniqueness principle: it is now the DOMAIN functor that
  must preserve the finite coproducts, since maps out of a coproduct
  are what get determined.
-}
module Cubical.Categories.Bicategory.Instances.CAT.TwoMonad.Instances.Cocartesian
  where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Category.More
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Instances.Functors

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Instances.CAT.Structured.Terminal
open import Cubical.Categories.Bicategory.Instances.CAT.Structured.Cartesian
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
open import Cubical.Categories.Bicategory.TwoMonad.Algebra
  using (PseudoAlgebra)

open import Cubical.Categories.Instances.Free.CartesianCategory.OnCategory
  using (|FreeCartesianOn|; FreeCartesianOn; ↑; ↑ₘ; ↑ₘId; ↑ₘSeq)
open import Cubical.Categories.Instances.Free.CocartesianCategory.OnCategory

private
  variable
    ℓ : Level

open Category
open Functor
open CartesianCategory renaming (C to Cat) using (term; bp)
open NatTrans
open NatIso
open isIso

module _ {ℓ : Level} where
  ιId : (C : Category ℓ ℓ)
    → NatTrans (Id {C = |FreeCocartesianOn| C}) (T₁ᶜ (Id {C = C}))
  ιId C = symNatIso (T₁ᶜ-id {C = C}) .trans

  ιSeq : {C D E : Category ℓ ℓ} (F : Functor C D) (G : Functor D E)
    → NatTrans (T₁ᶜ G ∘F T₁ᶜ F) (T₁ᶜ (G ∘F F))
  ιSeq F G = symNatIso (T₁ᶜ-seq F G) .trans

  -- Two transformations out of a coproduct preserving functor
  -- agreeing on the generators are equal.
  ext : {C : Category ℓ ℓ} {D : Category ℓ ℓ}
    {P Q : Functor (|FreeCocartesianOn| C) (|FreeCocartesianOn| D)}
    → preservesInitialOn C P → preservesBinCoproductsOn C P
    → (σ τ : NatTrans P Q)
    → (∀ c → σ .N-ob (↑ c) ≡ τ .N-ob (↑ c))
    → σ ≡ τ
  ext {C = C} P-0 P-+ = uniq₂ᶜ C P-0 P-+

  ∘Id≡ : {C D : Category ℓ ℓ} (Q : Functor C D) → Q ∘F Id ≡ Q
  ∘Id≡ Q = Functor≡ (λ _ → refl) (λ _ → refl)

  Id∘≡ : {C D : Category ℓ ℓ} (Q : Functor C D) → Id ∘F Q ≡ Q
  Id∘≡ Q = Functor≡ (λ _ → refl) (λ _ → refl)

  ext≡ : {C D : Category ℓ ℓ}
    {P P' Q : Functor (|FreeCocartesianOn| C) (|FreeCocartesianOn| D)}
    → P' ≡ P
    → preservesInitialOn C P → preservesBinCoproductsOn C P
    → (σ τ : NatTrans P' Q)
    → (∀ c → σ .N-ob (↑ c) ≡ τ .N-ob (↑ c))
    → σ ≡ τ
  ext≡ {C = C} p P-0 P-+ =
    ext (subst (preservesInitialOn C) (sym p) P-0)
        (subst (preservesBinCoproductsOn C) (sym p) P-+)

  Id-0 : (C : Category ℓ ℓ)
    → preservesInitialOn C (Id {C = |FreeCocartesianOn| C})
  Id-0 C = idPreservesTerminal' (FreeCartesianOn (C ^op) .term)

  Id-+ : (C : Category ℓ ℓ)
    → preservesBinCoproductsOn C (Id {C = |FreeCocartesianOn| C})
  Id-+ C = idPreservesBinProducts (FreeCartesianOn (C ^op) .bp)

  T-ext : {C D : Category ℓ ℓ}
    {Q : Functor (|FreeCocartesianOn| C) (|FreeCocartesianOn| D)}
    (G : Functor C D) (σ τ : NatTrans (T₁ᶜ G) Q)
    → (∀ c → σ .N-ob (↑ c) ≡ τ .N-ob (↑ c))
    → σ ≡ τ
  T-ext G = ext (T₁ᶜ-0 G) (T₁ᶜ-+ G)

  Tseq-0 : {C D E : Category ℓ ℓ} (F : Functor C D) (G : Functor D E)
    → preservesInitialOn C (T₁ᶜ G ∘F T₁ᶜ F)
  Tseq-0 {E = E} F G =
    recSeqᶜ-0 (FreeCartesianOn (E ^op)) (ηFreeᶜ _ ∘F F) (ηFreeᶜ E ∘F G)

  Tseq-+ : {C D E : Category ℓ ℓ} (F : Functor C D) (G : Functor D E)
    → preservesBinCoproductsOn C (T₁ᶜ G ∘F T₁ᶜ F)
  Tseq-+ {E = E} F G =
    recSeqᶜ-+ (FreeCartesianOn (E ^op)) (ηFreeᶜ _ ∘F F) (ηFreeᶜ E ∘F G)

  Tseq-ext : {C D E : Category ℓ ℓ}
    {F : Functor C D} {G : Functor D E}
    {Q : Functor (|FreeCocartesianOn| C) (|FreeCocartesianOn| E)}
    (σ τ : NatTrans (T₁ᶜ G ∘F T₁ᶜ F) Q)
    → (∀ c → σ .N-ob (↑ c) ≡ τ .N-ob (↑ c))
    → σ ≡ τ
  Tseq-ext {F = F} {G = G} = ext (Tseq-0 F G) (Tseq-+ F G)

  CocartLax : LaxFunctor (CAT {ℓ} {ℓ}) (CAT {ℓ} {ℓ})
  CocartLax .LaxFunctor.F-ob = |FreeCocartesianOn|
  CocartLax .LaxFunctor.F-Hom = TFunᶜ
  CocartLax .LaxFunctor.F-id {x = C} .N-ob _ = ιId C
  CocartLax .LaxFunctor.F-id {x = C} .N-hom _ =
    ext (Id-0 C) (Id-+ C) _ _ (λ c → FC.⟨ refl ⟩⋆⟨ sym ↑ₘId ⟩)
    where module FC = Category (|FreeCocartesianOn| C)
  CocartLax .LaxFunctor.F-seq .N-ob (F , G) = ιSeq F G
  CocartLax .LaxFunctor.F-seq {z = E} .N-hom (α , β) =
    Tseq-ext _ _ (λ c →
      FE.⋆IdR _ ∙ sym (↑ₘSeq _ _) ∙ sym (FE.⋆IdL _))
    where module FE = Category (|FreeCocartesianOn| E)
  CocartLax .LaxFunctor.lax-λ C D f =
    ext≡ (∘Id≡ (T₁ᶜ f)) (T₁ᶜ-0 f) (T₁ᶜ-+ f) _ _ (λ c →
      FD.⟨ FD.⋆IdL _ ⟩⋆⟨ FD.⋆IdL _ ∙ ↑ₘId ⟩ ∙ FD.⋆IdL _)
    where module FD = Category (|FreeCocartesianOn| D)
  CocartLax .LaxFunctor.lax-ρ C D f =
    ext≡ (Id∘≡ (T₁ᶜ f)) (T₁ᶜ-0 f) (T₁ᶜ-+ f) _ _ (λ c →
      FD.⟨ FD.⋆IdL _ ⟩⋆⟨ FD.⋆IdL _ ∙ ↑ₘId ⟩ ∙ FD.⋆IdL _)
    where module FD = Category (|FreeCocartesianOn| D)
  CocartLax .LaxFunctor.lax-α C D E W f g h =
    ext (compPreservesTerminal'
          {termC = FreeCartesianOn (C ^op) .term}
          {termD = FreeCartesianOn (E ^op) .term}
          (Tseq-0 f g) (T₁ᶜ-0 h))
        (compPreservesBinProducts
          {bpC = FreeCartesianOn (C ^op) .bp}
          {bpD = FreeCartesianOn (E ^op) .bp}
          (Tseq-+ f g) (T₁ᶜ-+ h))
      _ _ (λ c →
      (FW.⟨ FW.⋆IdL _ ⟩⋆⟨ FW.⋆IdL _ ∙ ↑ₘId ⟩ ∙ FW.⋆IdL _)
      ∙ sym (FW.⋆IdL _ ∙ FW.⟨ FW.⋆IdL _ ⟩⋆⟨ refl ⟩ ∙ FW.⋆IdL _))
    where module FW = Category (|FreeCocartesianOn| W)

  CocartPs : Pseudofunctor (CAT {ℓ} {ℓ}) (CAT {ℓ} {ℓ})
  CocartPs .Pseudofunctor.laxFunctor = CocartLax
  CocartPs .Pseudofunctor.F-id-isIso {x = C} _ =
    FUNCTORIso _ _ _ (symNatIso (T₁ᶜ-id {C = C}) .nIso)
  CocartPs .Pseudofunctor.F-seq-isIso (F , G) =
    FUNCTORIso _ _ _ (symNatIso (T₁ᶜ-seq F G) .nIso)

  -- The unit.  `ηFreeᶜ-nat` is a strict equality, so every naturality
  -- 2-cell is an identity.
  ηHom : {C D : Category ℓ ℓ} (F : Functor C D)
    → NatTrans (ηFreeᶜ D ∘F F) (T₁ᶜ F ∘F ηFreeᶜ C)
  ηHom {D = D} F .N-ob c = FD.id
    where module FD = Category (|FreeCocartesianOn| D)
  ηHom {D = D} F .N-hom f = FD.⋆IdR _ ∙ sym (FD.⋆IdL _)
    where module FD = Category (|FreeCocartesianOn| D)

  CocartUnit : LaxNatTrans (LaxId (CAT {ℓ} {ℓ})) CocartLax
  CocartUnit .LaxNatTrans.N-1cell = ηFreeᶜ
  CocartUnit .LaxNatTrans.N-hom = ηHom
  CocartUnit .LaxNatTrans.N-natural {y = D} θ =
    makeNatTransPath (funExt λ c →
      FD.⋆IdR _ ∙ FD.⋆IdR _ ∙ sym (FD.⋆IdL _ ∙ FD.⋆IdL _))
    where module FD = Category (|FreeCocartesianOn| D)
  CocartUnit .LaxNatTrans.lax-id C =
    makeNatTransPath (funExt λ c →
      FC.⋆IdR _ ∙ FC.⋆IdR _ ∙ ↑ₘId
      ∙ sym (FC.⋆IdL _ ∙ FC.⋆IdL _ ∙ FC.⋆IdL _))
    where module FC = Category (|FreeCocartesianOn| C)
  CocartUnit .LaxNatTrans.lax-seq {z = E} f g =
    makeNatTransPath (funExt λ c →
      FE.⋆IdR _ ∙ FE.⋆IdR _ ∙ ↑ₘId
      ∙ sym ( FE.⋆IdL _
            ∙ FE.⟨ FE.⋆IdR _
                 ∙ cong (ηFreeᶜ E .F-hom) (g .F-id) ∙ ↑ₘId ⟩⋆⟨ refl ⟩
            ∙ FE.⋆IdL _ ∙ FE.⋆IdL _
            ∙ FE.⟨ FE.⋆IdL _ ⟩⋆⟨ refl ⟩
            ∙ FE.⋆IdL _ ∙ FE.⋆IdL _ ∙ FE.⋆IdL _))
    where module FE = Category (|FreeCocartesianOn| E)

  -- The multiplication.
  private
    μ∘-0 : {C D : Category ℓ ℓ} (F : Functor C D)
      → preservesInitialOn (|FreeCocartesianOn| C)
          (μFreeᶜ D ∘F T₁ᶜ (T₁ᶜ F))
    μ∘-0 {C} {D} F = recSeqᶜ-0 (FreeCartesianOn (D ^op))
      (ηFreeᶜ (|FreeCocartesianOn| D) ∘F T₁ᶜ F) Id

    μ∘-+ : {C D : Category ℓ ℓ} (F : Functor C D)
      → preservesBinCoproductsOn (|FreeCocartesianOn| C)
          (μFreeᶜ D ∘F T₁ᶜ (T₁ᶜ F))
    μ∘-+ {C} {D} F = recSeqᶜ-+ (FreeCartesianOn (D ^op))
      (ηFreeᶜ (|FreeCocartesianOn| D) ∘F T₁ᶜ F) Id

  CocartMult : LaxNatTrans (CocartLax ∘Lax CocartLax) CocartLax
  CocartMult .LaxNatTrans.N-1cell = μFreeᶜ
  CocartMult .LaxNatTrans.N-hom F = μFreeᶜ-nat F .trans
  CocartMult .LaxNatTrans.N-natural {y = D} {f = F} θ =
    ext (μ∘-0 F) (μ∘-+ F) _ _ (λ x →
      FD.⋆IdR _ ∙ FD.⋆IdR _ ∙ sym (FD.⋆IdL _ ∙ FD.⋆IdL _))
    where module FD = Category (|FreeCocartesianOn| D)
  CocartMult .LaxNatTrans.lax-id C =
    ext≡ (∘Id≡ (μFreeᶜ C)) (μFreeᶜ-0 C) (μFreeᶜ-+ C) _ _ (λ x →
      FC.⋆IdR _ ∙ FC.⋆IdR _ ∙ FC.⋆IdL _
      ∙ sym (FC.⋆IdL _ ∙ FC.⋆IdL _ ∙ FC.⋆IdL _))
    where module FC = Category (|FreeCocartesianOn| C)
  CocartMult .LaxNatTrans.lax-seq {x = C} {z = E} f g =
    ext (compPreservesTerminal'
          {termC = FreeCartesianOn (|FreeCocartesianOn| C ^op) .term}
          {termD = FreeCartesianOn (|FreeCocartesianOn| E ^op) .term}
          (Tseq-0 (T₁ᶜ f) (T₁ᶜ g)) (μFreeᶜ-0 E))
        (compPreservesBinProducts
          {bpC = FreeCartesianOn (|FreeCocartesianOn| C ^op) .bp}
          {bpD = FreeCartesianOn (|FreeCocartesianOn| E ^op) .bp}
          (Tseq-+ (T₁ᶜ f) (T₁ᶜ g)) (μFreeᶜ-+ E))
      _ _ (λ x →
      FE.⋆IdR _ ∙ FE.⋆IdR _ ∙ FE.⋆IdL _
      ∙ sym ( FE.⋆IdL _
            ∙ FE.⟨ FE.⋆IdL _ ⟩⋆⟨ refl ⟩
            ∙ FE.⋆IdL _ ∙ FE.⋆IdL _
            ∙ FE.⟨ FE.⋆IdL _ ⟩⋆⟨ refl ⟩
            ∙ FE.⋆IdL _ ∙ FE.⋆IdL _ ∙ FE.⋆IdL _))
    where module FE = Category (|FreeCocartesianOn| E)

  private
    μηL-0 : (D : Category ℓ ℓ)
      → preservesInitialOn D (μFreeᶜ D ∘F T₁ᶜ (ηFreeᶜ D))
    μηL-0 D = recSeqᶜ-0 (FreeCartesianOn (D ^op))
      (ηFreeᶜ (|FreeCocartesianOn| D) ∘F ηFreeᶜ D) Id

    μηL-+ : (D : Category ℓ ℓ)
      → preservesBinCoproductsOn D (μFreeᶜ D ∘F T₁ᶜ (ηFreeᶜ D))
    μηL-+ D = recSeqᶜ-+ (FreeCartesianOn (D ^op))
      (ηFreeᶜ (|FreeCocartesianOn| D) ∘F ηFreeᶜ D) Id

  unitLMod : Modification
    (seqLaxNatTrans (whiskerL CocartPs CocartUnit) CocartMult)
    (ridLax CocartLax)
  unitLMod .Modification.M-ob C = μ-ηLᶜ C .trans
  unitLMod .Modification.M-hom {x = C} {y = D} f =
    ext (compPreservesTerminal'
          {termC = FreeCartesianOn (C ^op) .term}
          {termD = FreeCartesianOn (D ^op) .term}
          (T₁ᶜ-0 f) (μηL-0 D))
        (compPreservesBinProducts
          {bpC = FreeCartesianOn (C ^op) .bp}
          {bpD = FreeCartesianOn (D ^op) .bp}
          (T₁ᶜ-+ f) (μηL-+ D))
      _ _ (λ c →
        collapse Q
          (collapse Q refl
            (collapse Q
              (collapse Q (collapse Q refl (collapse Q refl refl)) refl)
              (collapse Q refl
                (collapse Q (collapse Q refl refl) refl))))
          (collapse Q refl refl)
      ∙ sym (four Q))
    where Q = |FreeCocartesianOn| D

  private
    ηRcell : (C : Category ℓ ℓ)
      → NatTrans (μFreeᶜ C ∘F ηFreeᶜ (|FreeCocartesianOn| C))
                 (Id {C = |FreeCocartesianOn| C})
    ηRcell C .N-ob x = FC.id
      where module FC = Category (|FreeCocartesianOn| C)
    ηRcell C .N-hom f = FC.⋆IdR _ ∙ sym (FC.⋆IdL _)
      where module FC = Category (|FreeCocartesianOn| C)

    μηR-0 : (D : Category ℓ ℓ)
      → preservesInitialOn D (μFreeᶜ D ∘F ηFreeᶜ (|FreeCocartesianOn| D))
    μηR-0 D = subst (preservesInitialOn D) (sym (μ-ηRᶜ D)) (Id-0 D)

    μηR-+ : (D : Category ℓ ℓ)
      → preservesBinCoproductsOn D
          (μFreeᶜ D ∘F ηFreeᶜ (|FreeCocartesianOn| D))
    μηR-+ D = subst (preservesBinCoproductsOn D) (sym (μ-ηRᶜ D)) (Id-+ D)

  unitRMod : Modification
    (seqLaxNatTrans (whiskerR CocartLax CocartUnit) CocartMult)
    (lidLax CocartLax)
  unitRMod .Modification.M-ob = ηRcell
  unitRMod .Modification.M-hom {x = C} {y = D} f =
    ext (compPreservesTerminal'
          {termC = FreeCartesianOn (C ^op) .term}
          {termD = FreeCartesianOn (D ^op) .term}
          (T₁ᶜ-0 f) (μηR-0 D))
        (compPreservesBinProducts
          {bpC = FreeCartesianOn (C ^op) .bp}
          {bpD = FreeCartesianOn (D ^op) .bp}
          (T₁ᶜ-+ f) (μηR-+ D))
      _ _ (λ c →
        collapse Q
          (collapse Q refl
            (collapse Q (collapse Q refl refl)
              (collapse Q refl
                (collapse Q (collapse Q refl refl) refl))))
          (collapse Q refl refl)
      ∙ sym (four Q))
    where Q = |FreeCocartesianOn| D

  private
    assocCell : (C : Category ℓ ℓ)
      → NatTrans (μFreeᶜ C ∘F μFreeᶜ (|FreeCocartesianOn| C))
                 ((μFreeᶜ C ∘F T₁ᶜ (μFreeᶜ C)) ∘F Id)
    assocCell C .N-ob x = symNatIso (μ-assocᶜ C) .trans .N-ob x
    assocCell C .N-hom f = symNatIso (μ-assocᶜ C) .trans .N-hom f

    μμ-0 : (D : Category ℓ ℓ)
      → preservesInitialOn (|FreeCocartesianOn| (|FreeCocartesianOn| D))
          (μFreeᶜ D ∘F μFreeᶜ (|FreeCocartesianOn| D))
    μμ-0 D = recSeqᶜ-0 (FreeCartesianOn (D ^op)) Id Id

    μμ-+ : (D : Category ℓ ℓ)
      → preservesBinCoproductsOn (|FreeCocartesianOn| (|FreeCocartesianOn| D))
          (μFreeᶜ D ∘F μFreeᶜ (|FreeCocartesianOn| D))
    μμ-+ D = recSeqᶜ-+ (FreeCartesianOn (D ^op)) Id Id

  assocMod' : Modification
    (seqLaxNatTrans (whiskerR CocartLax CocartMult) CocartMult)
    (seqLaxNatTrans (assocLax CocartLax CocartLax CocartLax)
      (seqLaxNatTrans (whiskerL CocartPs CocartMult) CocartMult))
  assocMod' .Modification.M-ob = assocCell
  assocMod' .Modification.M-hom {x = C} {y = D} f =
    ext {C = T²C}
      (compPreservesTerminal'
        {termC = FreeCartesianOn (T²C ^op) .term}
        {termD = FreeCartesianOn (T²D ^op) .term}
        (T₁ᶜ-0 (T₁ᶜ (T₁ᶜ f))) (μμ-0 D))
      (compPreservesBinProducts
        {bpC = FreeCartesianOn (T²C ^op) .bp}
        {bpD = FreeCartesianOn (T²D ^op) .bp}
        (T₁ᶜ-+ (T₁ᶜ (T₁ᶜ f))) (μμ-+ D))
      _ _ (λ c →
          ( FD.⟨ refl ⟩⋆⟨ FD.⋆IdL _ ⟩ ∙ FD.⋆IdR _
          ∙ FD.⋆IdL _
          ∙ collapseL QD (FD.⋆IdL _)
          ∙ FD.⋆IdL _ ∙ FD.⋆IdR _ ∙ FD.⋆IdL _)
        ∙ sym
          ( collapseL QD (FD.⋆IdL _)
          ∙ FD.⋆IdL _
          ∙ collapseL QD (collapse QD (collapse QD refl refl) refl)
          ∙ FD.⋆IdL _ ∙ FD.⋆IdR _ ∙ FD.⋆IdL _ ∙ FD.⋆IdL _
          ∙ FD.⟨ refl ⟩⋆⟨ collapse QD refl
              (collapse QD (collapse QD refl refl) refl) ⟩
          ∙ FD.⋆IdR _ ∙ FD.⋆IdR _ ∙ FD.⋆IdL _ ∙ FD.⋆IdR _))
    where
    QD = |FreeCocartesianOn| D
    module FD = Category QD
    T²C = |FreeCocartesianOn| (|FreeCocartesianOn| C)
    T²D = |FreeCocartesianOn| (|FreeCocartesianOn| D)

  CocartesianTwoMonad : TwoMonad (CAT {ℓ} {ℓ})
  CocartesianTwoMonad .TwoMonad.T = CocartPs
  CocartesianTwoMonad .TwoMonad.η = CocartUnit
  CocartesianTwoMonad .TwoMonad.μ = CocartMult
  CocartesianTwoMonad .TwoMonad.unitL =
    unitLMod , modIsIso unitLMod (λ C →
      FUNCTORIso _ _ _ (μ-ηLᶜ C .nIso))
  CocartesianTwoMonad .TwoMonad.unitR =
    unitRMod , modIsIso unitRMod (λ C →
      FUNCTORIso _ _ _ (λ x → idCatIso .snd))
  CocartesianTwoMonad .TwoMonad.assoc =
    assocMod' , modIsIso assocMod' (λ C →
      FUNCTORIso _ _ _ (symNatIso (μ-assocᶜ C) .nIso))

{- A pseudoalgebra is a category with a coherent choice of finite
   coproducts: the structure map interprets the formal coproducts.
   Every cocartesian category — presented as `CC .Cat ^op` for a
   cartesian CC — is one, with the extension of the identity as the
   action. -}
module _ {ℓ : Level} (CC : CartesianCategory ℓ ℓ) where
  private
    B = CC .Cat ^op
    module B = Category B
    a : Functor (|FreeCocartesianOn| B) B
    a = recᶜ B CC Id

    unitCell : NatTrans (a ∘F ηFreeᶜ B) (Id {C = B})
    unitCell .N-ob x = B.id
    unitCell .N-hom f = B.⋆IdR _ ∙ sym (B.⋆IdL _)

    multCell : NatIso (a ∘F T₁ᶜ a) (a ∘F μFreeᶜ B)
    multCell = uniqᶜ (|FreeCocartesianOn| B) (a ∘F T₁ᶜ a) (a ∘F μFreeᶜ B)
      (recSeqᶜ-0 CC (ηFreeᶜ B ∘F a) Id) (recSeqᶜ-+ CC (ηFreeᶜ B ∘F a) Id)
      (recSeqᶜ-0 CC Id Id) (recSeqᶜ-+ CC Id Id) ı≅
      where
      ı≅ : NatIso ((a ∘F T₁ᶜ a) ∘F ηFreeᶜ (|FreeCocartesianOn| B))
                  ((a ∘F μFreeᶜ B) ∘F ηFreeᶜ (|FreeCocartesianOn| B))
      ı≅ .trans .N-ob x = B.id
      ı≅ .trans .N-hom f = B.⋆IdR _ ∙ sym (B.⋆IdL _)
      ı≅ .nIso x = idCatIso .snd

  CocartesianPseudoAlgebra : PseudoAlgebra (CocartesianTwoMonad {ℓ})
  CocartesianPseudoAlgebra .PseudoAlgebra.carrier = B
  CocartesianPseudoAlgebra .PseudoAlgebra.act = a
  CocartesianPseudoAlgebra .PseudoAlgebra.actUnit = unitCell
  CocartesianPseudoAlgebra .PseudoAlgebra.actMult = multCell .trans
  CocartesianPseudoAlgebra .PseudoAlgebra.actUnitIso =
    FUNCTORIso _ _ _ (λ x → idCatIso .snd)
  CocartesianPseudoAlgebra .PseudoAlgebra.actMultIso =
    FUNCTORIso _ _ _ (multCell .nIso)
