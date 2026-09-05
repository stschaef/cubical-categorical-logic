{-# OPTIONS --lossy-unification #-}
{-
  The free cartesian category 2-monad on CAT.

  Every law is an equation between natural transformations whose
  codomain is a `rec`-generated, hence product preserving, functor, so
  `uniq₂` reduces it to the generators.  There all the laxity cells
  and comparisons are identities, and the two sides differ only in how
  they are bracketed.
-}
module Cubical.Categories.Bicategory.Instances.CAT.TwoMonads.Cartesian
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
    → NatTrans (Id {C = |FreeCartesianOn| C}) (T₁ (Id {C = C}))
  ιId C = symNatIso (T₁-id {C = C}) .trans

  ιSeq : {C D E : Category ℓ ℓ} (F : Functor C D) (G : Functor D E)
    → NatTrans (T₁ G ∘F T₁ F) (T₁ (G ∘F F))
  ιSeq F G = symNatIso (T₁-seq F G) .trans

  -- Two transformations into a product preserving functor agreeing
  -- on the generators are equal.
  ext : {C : Category ℓ ℓ} {D : Category ℓ ℓ}
    {P Q : Functor (|FreeCartesianOn| C) D}
    → preservesTerminalOn C Q → preservesBinProductsOn C Q
    → (σ τ : NatTrans P Q)
    → (∀ c → σ .N-ob (↑ c) ≡ τ .N-ob (↑ c))
    → σ ≡ τ
  ext {C = C} Q-1 Q-× = TwoDim.uniq₂ C _ _ Q-1 Q-×

  ∘Id≡ : {C D : Category ℓ ℓ} (Q : Functor C D) → Q ∘F Id ≡ Q
  ∘Id≡ Q = Functor≡ (λ _ → refl) (λ _ → refl)

  ext∘Id : {C D : Category ℓ ℓ}
    {P Q : Functor (|FreeCartesianOn| C) (|FreeCartesianOn| D)}
    → preservesTerminalOn C Q → preservesBinProductsOn C Q
    → (σ τ : NatTrans P (Q ∘F Id))
    → (∀ c → σ .N-ob (↑ c) ≡ τ .N-ob (↑ c))
    → σ ≡ τ
  ext∘Id {C = C} {Q = Q} Q-1 Q-× = ext
    (subst (preservesTerminalOn C) (sym (∘Id≡ Q)) Q-1)
    (subst (preservesBinProductsOn C) (sym (∘Id≡ Q)) Q-×)

  T-ext : {C D : Category ℓ ℓ}
    {P : Functor (|FreeCartesianOn| C) (|FreeCartesianOn| D)}
    (G : Functor C D) (σ τ : NatTrans P (T₁ G))
    → (∀ c → σ .N-ob (↑ c) ≡ τ .N-ob (↑ c))
    → σ ≡ τ
  T-ext G = ext (T₁-1 G) (T₁-× G)

  CartLax : LaxFunctor (CAT {ℓ} {ℓ}) (CAT {ℓ} {ℓ})
  CartLax .LaxFunctor.F-ob = |FreeCartesianOn|
  CartLax .LaxFunctor.F-Hom = TFun
  CartLax .LaxFunctor.F-id {x = C} .N-ob _ = ιId C
  CartLax .LaxFunctor.F-id {x = C} .N-hom _ =
    T-ext Id _ _ (λ c → FC.⟨ refl ⟩⋆⟨ sym ↑ₘId ⟩)
    where module FC = Category (|FreeCartesianOn| C)
  CartLax .LaxFunctor.F-seq .N-ob (F , G) = ιSeq F G
  CartLax .LaxFunctor.F-seq {z = E} .N-hom (α , β) =
    T-ext _ _ _ (λ c →
      FE.⋆IdR _ ∙ sym (↑ₘSeq _ _) ∙ sym (FE.⋆IdL _))
    where module FE = Category (|FreeCartesianOn| E)
  CartLax .LaxFunctor.lax-λ C D f =
    T-ext f _ _ (λ c →
      FD.⟨ FD.⋆IdL _ ⟩⋆⟨ FD.⋆IdL _ ∙ ↑ₘId ⟩ ∙ FD.⋆IdL _)
    where module FD = Category (|FreeCartesianOn| D)
  CartLax .LaxFunctor.lax-ρ C D f =
    T-ext f _ _ (λ c →
      FD.⟨ FD.⋆IdL _ ⟩⋆⟨ FD.⋆IdL _ ∙ ↑ₘId ⟩ ∙ FD.⋆IdL _)
    where module FD = Category (|FreeCartesianOn| D)
  CartLax .LaxFunctor.lax-α C D E W f g h =
    T-ext _ _ _ (λ c →
      (FW.⟨ FW.⋆IdL _ ⟩⋆⟨ FW.⋆IdL _ ∙ ↑ₘId ⟩ ∙ FW.⋆IdL _)
      ∙ sym (FW.⋆IdL _ ∙ FW.⟨ FW.⋆IdL _ ⟩⋆⟨ refl ⟩ ∙ FW.⋆IdL _))
    where module FW = Category (|FreeCartesianOn| W)

  CartPs : Pseudofunctor (CAT {ℓ} {ℓ}) (CAT {ℓ} {ℓ})
  CartPs .Pseudofunctor.laxFunctor = CartLax
  CartPs .Pseudofunctor.F-id-isIso {x = C} _ =
    FUNCTORIso _ _ _ (symNatIso (T₁-id {C = C}) .nIso)
  CartPs .Pseudofunctor.F-seq-isIso {x = C} {z = E} (F , G) =
    FUNCTORIso _ _ _ (symNatIso (T₁-seq F G) .nIso)

  -- The unit.  `ηFree-nat` is a strict equality, so every naturality
  -- 2-cell is an identity.
  ηHom : {C D : Category ℓ ℓ} (F : Functor C D)
    → NatTrans (ηFree D ∘F F) (T₁ F ∘F ηFree C)
  ηHom {D = D} F .N-ob c = FD.id
    where module FD = Category (|FreeCartesianOn| D)
  ηHom {D = D} F .N-hom f = FD.⋆IdR _ ∙ sym (FD.⋆IdL _)
    where module FD = Category (|FreeCartesianOn| D)

  CartUnit : LaxNatTrans (LaxId (CAT {ℓ} {ℓ})) CartLax
  CartUnit .LaxNatTrans.N-1cell = ηFree
  CartUnit .LaxNatTrans.N-hom = ηHom
  CartUnit .LaxNatTrans.N-natural {y = D} θ =
    makeNatTransPath (funExt λ c →
      FD.⋆IdR _ ∙ FD.⋆IdR _ ∙ sym (FD.⋆IdL _ ∙ FD.⋆IdL _))
    where module FD = Category (|FreeCartesianOn| D)
  CartUnit .LaxNatTrans.lax-id C =
    makeNatTransPath (funExt λ c →
      FC.⋆IdR _ ∙ FC.⋆IdR _ ∙ ↑ₘId
      ∙ sym (FC.⋆IdL _ ∙ FC.⋆IdL _ ∙ FC.⋆IdL _))
    where module FC = Category (|FreeCartesianOn| C)
  CartUnit .LaxNatTrans.lax-seq {z = E} f g =
    makeNatTransPath (funExt λ c →
      FE.⋆IdR _ ∙ FE.⋆IdR _ ∙ ↑ₘId
      ∙ sym ( FE.⋆IdL _
            ∙ FE.⟨ FE.⋆IdR _
                 ∙ cong (ηFree E .F-hom) (g .F-id) ∙ ↑ₘId ⟩⋆⟨ refl ⟩
            ∙ FE.⋆IdL _ ∙ FE.⋆IdL _
            ∙ FE.⟨ FE.⋆IdL _ ⟩⋆⟨ refl ⟩
            ∙ FE.⋆IdL _ ∙ FE.⋆IdL _ ∙ FE.⋆IdL _))
    where module FE = Category (|FreeCartesianOn| E)

  -- The multiplication.
  private
    μ∘-1 : {C D : Category ℓ ℓ} (G : Functor C D)
      → preservesTerminalOn (|FreeCartesianOn| C) (T₁ G ∘F μFree C)
    μ∘-1 {C} {D} G = recSeq-1 (FreeCartesianOn D) Id (ηFree D ∘F G)

    μ∘-× : {C D : Category ℓ ℓ} (G : Functor C D)
      → preservesBinProductsOn (|FreeCartesianOn| C) (T₁ G ∘F μFree C)
    μ∘-× {C} {D} G = recSeq-× (FreeCartesianOn D) Id (ηFree D ∘F G)

  CartMult : LaxNatTrans (CartLax ∘Lax CartLax) CartLax
  CartMult .LaxNatTrans.N-1cell = μFree
  CartMult .LaxNatTrans.N-hom F = μFree-nat F .trans
  CartMult .LaxNatTrans.N-natural {y = D} {g = G} θ =
    ext (μ∘-1 G) (μ∘-× G) _ _ (λ x →
      FD.⋆IdR _ ∙ FD.⋆IdR _ ∙ sym (FD.⋆IdL _ ∙ FD.⋆IdL _))
    where module FD = Category (|FreeCartesianOn| D)
  CartMult .LaxNatTrans.lax-id C =
    ext (μ∘-1 (Id {C = C})) (μ∘-× (Id {C = C})) _ _ (λ x →
      FC.⋆IdR _ ∙ FC.⋆IdR _ ∙ FC.⋆IdL _
      ∙ sym (FC.⋆IdL _ ∙ FC.⋆IdL _ ∙ FC.⋆IdL _))
    where module FC = Category (|FreeCartesianOn| C)
  CartMult .LaxNatTrans.lax-seq {z = E} f g =
    ext (μ∘-1 (g ∘F f)) (μ∘-× (g ∘F f)) _ _ (λ x →
      FE.⋆IdR _ ∙ FE.⋆IdR _ ∙ FE.⋆IdL _
      ∙ sym ( FE.⋆IdL _
            ∙ FE.⟨ FE.⋆IdL _ ⟩⋆⟨ refl ⟩
            ∙ FE.⋆IdL _ ∙ FE.⋆IdL _
            ∙ FE.⟨ FE.⋆IdL _ ⟩⋆⟨ refl ⟩
            ∙ FE.⋆IdL _ ∙ FE.⋆IdL _ ∙ FE.⋆IdL _))
    where module FE = Category (|FreeCartesianOn| E)

  unitLMod : Modification
    (seqLaxNatTrans (whiskerL CartPs CartUnit) CartMult) (ridLax CartLax)
  unitLMod .Modification.M-ob C = μ-ηL C .trans
  unitLMod .Modification.M-hom {y = D} f =
    ext∘Id (T₁-1 f) (T₁-× f) _ _ (λ c →
        collapse Q
          (collapse Q refl
            (collapse Q
              (collapse Q (collapse Q refl (collapse Q refl refl)) refl)
              (collapse Q refl
                (collapse Q (collapse Q refl refl) refl))))
          (collapse Q refl refl)
      ∙ sym (four Q))
    where Q = |FreeCartesianOn| D

  private
    ηRcell : (C : Category ℓ ℓ)
      → NatTrans (μFree C ∘F ηFree (|FreeCartesianOn| C))
                 (Id {C = |FreeCartesianOn| C})
    ηRcell C .N-ob x = FC.id where module FC = Category (|FreeCartesianOn| C)
    ηRcell C .N-hom f = FC.⋆IdR _ ∙ sym (FC.⋆IdL _)
      where module FC = Category (|FreeCartesianOn| C)

  unitRMod : Modification
    (seqLaxNatTrans (whiskerR CartLax CartUnit) CartMult) (lidLax CartLax)
  unitRMod .Modification.M-ob = ηRcell
  unitRMod .Modification.M-hom {y = D} f =
    ext∘Id (T₁-1 f) (T₁-× f) _ _ (λ c →
        collapse Q
          (collapse Q refl
            (collapse Q (collapse Q refl refl)
              (collapse Q refl
                (collapse Q (collapse Q refl refl) refl))))
          (collapse Q refl refl)
      ∙ sym (four Q))
    where Q = |FreeCartesianOn| D

  private
    assocCell : (C : Category ℓ ℓ)
      → NatTrans (μFree C ∘F μFree (|FreeCartesianOn| C))
                 ((μFree C ∘F T₁ (μFree C)) ∘F Id)
    assocCell C .N-ob x = symNatIso (μ-assoc C) .trans .N-ob x
    assocCell C .N-hom f = symNatIso (μ-assoc C) .trans .N-hom f

  assocMod' : Modification
    (seqLaxNatTrans (whiskerR CartLax CartMult) CartMult)
    (seqLaxNatTrans (assocLax CartLax CartLax CartLax)
      (seqLaxNatTrans (whiskerL CartPs CartMult) CartMult))
  assocMod' .Modification.M-ob = assocCell
  assocMod' .Modification.M-hom {x = C} {y = D} f =
    ext {C = T²C}
      (compPreservesTerminal' {F = Y} {G = T₁ f}
        {termC = FreeCartesianOn T²C .term} {termD = FreeCartesianOn C .term}
        Yp1 (T₁-1 f))
      (compPreservesBinProducts {F = Y} {G = T₁ f}
        {bpC = FreeCartesianOn T²C .bp} {bpD = FreeCartesianOn C .bp}
        Yp× (T₁-× f))
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
    QD = |FreeCartesianOn| D
    module FD = Category QD
    T²C = |FreeCartesianOn| (|FreeCartesianOn| C)
    Z : Functor (|FreeCartesianOn| T²C) (|FreeCartesianOn| C)
    Z = μFree C ∘F T₁ (μFree C)
    Y : Functor (|FreeCartesianOn| T²C) (|FreeCartesianOn| C)
    Y = Z ∘F Id
    Yp1 : preservesTerminalOn T²C Y
    Yp1 = compPreservesTerminal' {F = Id} {G = Z}
      {termC = FreeCartesianOn T²C .term} {termD = FreeCartesianOn T²C .term}
      (idPreservesTerminal' (FreeCartesianOn T²C .term))
      (recSeq-1 (FreeCartesianOn C)
        (ηFree (|FreeCartesianOn| C) ∘F μFree C) Id)
    Yp× : preservesBinProductsOn T²C Y
    Yp× = compPreservesBinProducts {F = Id} {G = Z}
      {bpC = FreeCartesianOn T²C .bp} {bpD = FreeCartesianOn T²C .bp}
      (idPreservesBinProducts (FreeCartesianOn T²C .bp))
      (recSeq-× (FreeCartesianOn C)
        (ηFree (|FreeCartesianOn| C) ∘F μFree C) Id)

  CartesianTwoMonad : TwoMonad (CAT {ℓ} {ℓ})
  CartesianTwoMonad .TwoMonad.T = CartPs
  CartesianTwoMonad .TwoMonad.η = CartUnit
  CartesianTwoMonad .TwoMonad.μ = CartMult
  CartesianTwoMonad .TwoMonad.unitL =
    unitLMod , modIsIso unitLMod (λ C →
      FUNCTORIso _ _ _ (μ-ηL C .nIso))
  CartesianTwoMonad .TwoMonad.unitR =
    unitRMod , modIsIso unitRMod (λ C →
      FUNCTORIso _ _ _ (λ x → idCatIso .snd))
  CartesianTwoMonad .TwoMonad.assoc =
    assocMod' , modIsIso assocMod' (λ C →
      FUNCTORIso _ _ _ (symNatIso (μ-assoc C) .nIso))

{- A pseudoalgebra is a category with a coherent choice of finite
   products: the structure map interprets the formal products.  Every
   cartesian category is one, with the extension of the identity as
   the action; its unit constraint is `rec-β` and its multiplication
   constraint compares two `recSeq`s. -}
module _ {ℓ : Level} (CC : CartesianCategory ℓ ℓ) where
  private
    B = CC .Cat
    module B = Category B
    a : Functor (|FreeCartesianOn| B) B
    a = rec B CC Id

    unitCell : NatTrans (a ∘F ηFree B) (Id {C = B})
    unitCell .N-ob x = B.id
    unitCell .N-hom f = B.⋆IdR _ ∙ sym (B.⋆IdL _)

    multCell : NatIso (a ∘F T₁ a) (a ∘F μFree B)
    multCell = uniq (|FreeCartesianOn| B) (a ∘F T₁ a) (a ∘F μFree B)
      (recSeq-1 CC (ηFree B ∘F a) Id) (recSeq-× CC (ηFree B ∘F a) Id)
      (recSeq-1 CC Id Id) (recSeq-× CC Id Id) ı≅
      where
      ı≅ : NatIso ((a ∘F T₁ a) ∘F ηFree (|FreeCartesianOn| B))
                  ((a ∘F μFree B) ∘F ηFree (|FreeCartesianOn| B))
      ı≅ .NatIso.trans .N-ob x = B.id
      ı≅ .NatIso.trans .N-hom f = B.⋆IdR _ ∙ sym (B.⋆IdL _)
      ı≅ .NatIso.nIso x = idCatIso .snd

  CartesianPseudoAlgebra : PseudoAlgebra (CartesianTwoMonad {ℓ})
  CartesianPseudoAlgebra .PseudoAlgebra.carrier = B
  CartesianPseudoAlgebra .PseudoAlgebra.act = a
  CartesianPseudoAlgebra .PseudoAlgebra.actUnit = unitCell
  CartesianPseudoAlgebra .PseudoAlgebra.actMult = multCell .trans
  CartesianPseudoAlgebra .PseudoAlgebra.actUnitIso =
    FUNCTORIso _ _ _ (λ x → idCatIso .snd)
  CartesianPseudoAlgebra .PseudoAlgebra.actMultIso =
    FUNCTORIso _ _ _ (multCell .nIso)
