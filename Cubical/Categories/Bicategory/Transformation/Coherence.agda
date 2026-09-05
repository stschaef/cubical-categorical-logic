{-# OPTIONS --lossy-unification #-}
{-
  Unitors and associators, in the two directions they are needed.

  For `∘Lax` of lax functors: `ridLax`/`lidLax`/`assocLax`.  Those
  comparisons all have identity components, so their coherence is that
  of `idLaxNatTrans` once the two laxity cells have been compared.

  For `seqLaxNatTrans` of lax transformations: `lamMod`/`rhoMod`/
  `assocMod`, generic in the target bicategory.
-}
module Cubical.Categories.Bicategory.Transformation.Coherence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More hiding (α)

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Properties.Coherence
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Identity
open import Cubical.Categories.Bicategory.Functor.Composition
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.Transformation.Properties
open import Cubical.Categories.Bicategory.Transformation.Identity
open import Cubical.Categories.Bicategory.Transformation.Composition

private
  variable
    ℓa ℓa' ℓa'' ℓb ℓb' ℓb'' ℓc ℓc' ℓc'' ℓd ℓd' ℓd'' : Level

open Functor
open NatIso
open isIso
open LaxFunctor
open LaxNatTrans
open Modification

module _ {B : Bicategory ℓb ℓb' ℓb''} {C : Bicategory ℓc ℓc' ℓc''}
         (H : LaxFunctor B C) where
  private
    module B = Bicategory B
    module C = Bicategory C
    module H = LaxFunctor H
    module ι = LaxNatTrans (idLaxNatTrans H)

  ridLax : LaxNatTrans (H ∘Lax LaxId B) H
  ridLax .N-1cell x = C.id₁
  ridLax .N-hom = ι.N-hom
  ridLax .N-natural = ι.N-natural
  ridLax .lax-id x =
      C.⟨ C.⟨ C.⟨⟩⋆₂⟨ H.F-Hom .F-id ⟩ ∙ C.⋆₂IdR _ ⟩▷ C.id₁ ⟩⋆₂⟨⟩
    ∙ ι.lax-id x
  ridLax .lax-seq f g =
      C.⟨ C.⟨ C.⟨⟩⋆₂⟨ H.F-Hom .F-id ⟩ ∙ C.⋆₂IdR _ ⟩▷ C.id₁ ⟩⋆₂⟨⟩
    ∙ ι.lax-seq f g

  lidLax : LaxNatTrans (LaxId C ∘Lax H) H
  lidLax .N-1cell x = C.id₁
  lidLax .N-hom = ι.N-hom
  lidLax .N-natural = ι.N-natural
  lidLax .lax-id x = C.⟨ C.⟨ C.⋆₂IdL _ ⟩▷ C.id₁ ⟩⋆₂⟨⟩ ∙ ι.lax-id x
  lidLax .lax-seq f g = C.⟨ C.⟨ C.⋆₂IdL _ ⟩▷ C.id₁ ⟩⋆₂⟨⟩ ∙ ι.lax-seq f g

module _ {A : Bicategory ℓa ℓa' ℓa''} {B : Bicategory ℓb ℓb' ℓb''}
         {C : Bicategory ℓc ℓc' ℓc''} {D : Bicategory ℓd ℓd' ℓd''}
         (H₃ : LaxFunctor C D) (H₂ : LaxFunctor B C)
         (H₁ : LaxFunctor A B) where
  private
    module D = Bicategory D
    module H₃ = LaxFunctor H₃
    module ι = LaxNatTrans (idLaxNatTrans (H₃ ∘Lax (H₂ ∘Lax H₁)))

  assocLax : LaxNatTrans ((H₃ ∘Lax H₂) ∘Lax H₁) (H₃ ∘Lax (H₂ ∘Lax H₁))
  assocLax .N-1cell x = D.id₁
  assocLax .N-hom = ι.N-hom
  assocLax .N-natural = ι.N-natural
  assocLax .lax-id x =
      D.⟨ D.⟨ D.⋆₂Assoc _ _ _
            ∙ D.⟨⟩⋆₂⟨ sym (H₃.F-Hom .F-seq _ _) ⟩ ⟩▷ D.id₁ ⟩⋆₂⟨⟩
    ∙ ι.lax-id x
  assocLax .lax-seq f g =
      D.⟨ D.⟨ D.⋆₂Assoc _ _ _
            ∙ D.⟨⟩⋆₂⟨ sym (H₃.F-Hom .F-seq _ _) ⟩ ⟩▷ D.id₁ ⟩⋆₂⟨⟩
    ∙ ι.lax-seq f g

-- Unitors and associator for `seqLaxNatTrans`.
module _ {B : Bicategory ℓb ℓb' ℓb''} {C : Bicategory ℓc ℓc' ℓc''}
         {F G : LaxFunctor B C} (α : LaxNatTrans F G) where
  private
    module B = Bicategory B
    module C = Bicategory C
    module F = LaxFunctor F
    module G = LaxFunctor G

    lamHom : {x y : B.ob} (f : B.1Cell x y)
      →   seqLaxNatTrans (idLaxNatTrans F) α .N-hom f
            C.⋆₂ (C.λ⁺ (α .N-1cell x) C.▷w G.F-1cell f)
        ≡ (F.F-1cell f C.◁w C.λ⁺ (α .N-1cell y)) C.⋆₂ α .N-hom f
    lamHom {x} {y} f =
        aR5 C _ _ _ _ _ _
      ∙ C.⟨⟩⋆₂⟨ C.⟨ ▷wSeq C (C.ρ⁺ Pf) (C.λ⁻ Pf) Ay ⟩⋆₂⟨⟩
              ∙ aR2 C _ _ _ ⟩
      ∙ pushn C (α⁻ρ▷ C Pf Ay) _
      ∙ C.⟨⟩⋆₂⟨ pushn C (λ⁻⋆₁ C Pf Ay) _ ⟩
      ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ λ⋆₁ C Ax Qf ⟩ ⟩ ⟩
      ∙ C.⟨⟩⋆₂⟨ pushr C (sym (λ⁻-nat C N)) _
              ∙ C.⟨⟩⋆₂⟨ C.λU _ _ .nIso (tt* , Ax C.⋆₁ Qf) .sec ⟩
              ∙ C.⋆₂IdR _ ⟩
      where
      Pf = F.F-1cell f
      Qf = G.F-1cell f
      Ax = α .N-1cell x
      Ay = α .N-1cell y
      N  = α .N-hom f

    rhoHom : {x y : B.ob} (f : B.1Cell x y)
      →   seqLaxNatTrans α (idLaxNatTrans G) .N-hom f
            C.⋆₂ (C.ρ⁺ (α .N-1cell x) C.▷w G.F-1cell f)
        ≡ (F.F-1cell f C.◁w C.ρ⁺ (α .N-1cell y)) C.⋆₂ α .N-hom f
    rhoHom {x} {y} f =
        aR5 C _ _ _ _ _ _
      ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
          C.⟨ ◁wSeq C Ax (C.ρ⁺ Qf) (C.λ⁻ Qf) ⟩⋆₂⟨⟩
          ∙ aR2 C _ _ _ ⟩ ⟩ ⟩
      ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ pushn C (ρ⋆₁ C Qf Ax) _ ⟩ ⟩
      ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
          C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ α⁻ρ▷ C Ax Qf ⟩
                ∙ sym (◁wSeq C Ax (C.λ⁻ Qf) (C.λ⁺ Qf))
                ∙ Ax C.◁⟨ C.λU _ _ .nIso (tt* , Qf) .sec ⟩
                ∙ C.◁wId Ax ⟩
          ∙ C.⋆₂IdR _ ⟩ ⟩
      ∙ C.⟨⟩⋆₂⟨ ρ-nat C N ⟩
      ∙ pushn C (α⁻ρ◁ C Pf Ay) _
      where
      Pf = F.F-1cell f
      Qf = G.F-1cell f
      Ax = α .N-1cell x
      Ay = α .N-1cell y
      N  = α .N-hom f

  lamMod : Modification (seqLaxNatTrans (idLaxNatTrans F) α) α
  lamMod .M-ob x = C.λ⁺ (α .N-1cell x)
  lamMod .M-hom = lamHom

  lamModInv : Modification α (seqLaxNatTrans (idLaxNatTrans F) α)
  lamModInv = invMod lamMod (λ x → C.λU _ _ .nIso (tt* , α .N-1cell x))

  rhoMod : Modification (seqLaxNatTrans α (idLaxNatTrans G)) α
  rhoMod .M-ob x = C.ρ⁺ (α .N-1cell x)
  rhoMod .M-hom = rhoHom

  rhoModInv : Modification α (seqLaxNatTrans α (idLaxNatTrans G))
  rhoModInv = invMod rhoMod (λ x → C.ρU _ _ .nIso (α .N-1cell x , tt*))

module _ {B : Bicategory ℓb ℓb' ℓb''} {C : Bicategory ℓc ℓc' ℓc''}
         {F₁ F₂ F₃ F₄ : LaxFunctor B C}
         (α : LaxNatTrans F₁ F₂) (β : LaxNatTrans F₂ F₃)
         (γ : LaxNatTrans F₃ F₄) where
  private
    module B = Bicategory B
    module C = Bicategory C
    module F₁ = LaxFunctor F₁
    module F₂ = LaxFunctor F₂
    module F₃ = LaxFunctor F₃
    module F₄ = LaxFunctor F₄

    module _ {x y : B.ob} (f : B.1Cell x y) where
      private
        fP = F₁.F-1cell f
        fQ = F₂.F-1cell f
        fR = F₃.F-1cell f
        fS = F₄.F-1cell f
        ax = α .N-1cell x
        ay = α .N-1cell y
        bx = β .N-1cell x
        by = β .N-1cell y
        cx = γ .N-1cell x
        cy = γ .N-1cell y
        hA = α .N-hom f
        hB = β .N-hom f
        hC = γ .N-hom f

      claimA :
          C.α⁻ fP (ay C.⋆₁ by) cy
            C.⋆₂ (C.α⁻ fP ay by C.▷w cy)
            C.⋆₂ ((hA C.▷w by) C.▷w cy)
        ≡   (fP C.◁w C.α⁺ ay by cy)
            C.⋆₂ C.α⁻ fP ay (by C.⋆₁ cy)
            C.⋆₂ (hA C.▷w (by C.⋆₁ cy))
            C.⋆₂ C.α⁻ (ax C.⋆₁ fQ) by cy
      claimA =
          sym (C.⋆₂Assoc _ _ _)
        ∙ C.⟨ ⋆InvRMove (αI C (fP C.⋆₁ ay) by cy)
                (C.⋆₂Assoc _ _ _ ∙ pentP1 C fP ay by cy) ⟩⋆₂⟨⟩
        ∙ C.⋆₂Assoc _ _ _
        ∙ C.⟨⟩⋆₂⟨ sym (α⁻natL C hA by cy) ⟩
        ∙ C.⋆₂Assoc _ _ _

      assocHom :
          seqLaxNatTrans (seqLaxNatTrans α β) γ .N-hom f
            C.⋆₂ (C.α⁺ ax bx cx C.▷w fS)
        ≡   (fP C.◁w C.α⁺ ay by cy)
            C.⋆₂ seqLaxNatTrans α (seqLaxNatTrans β γ) .N-hom f
      assocHom =
          aR5 C _ _ _ _ _ _
        ∙ C.⟨⟩⋆₂⟨ C.⟨ ▷5 C _ _ _ _ _ cy ⟩⋆₂⟨⟩ ∙ aR5 C _ _ _ _ _ _ ⟩
        ∙ sym (aR3 C _ _ _ _) ∙ C.⟨ claimA ⟩⋆₂⟨⟩ ∙ aR4 C _ _ _ _ _
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
            sym (aR2 C _ _ _)
            ∙ C.⟨ pentP3 C ax fQ by cy ⟩⋆₂⟨⟩
            ∙ aR3 C _ _ _ _ ⟩ ⟩ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
            pushr C (sym (α⁻natM C ax hB cy)) _ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
            rep3 C (pentP1 C ax bx fR cy) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
            pushr C (sym (α⁻natR C ax bx hC)) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
            C.⟨⟩⋆₂⟨
              sym (aR2 C _ _ _)
              ∙ C.⟨ sym (pentP2 C ax bx cx fS) ⟩⋆₂⟨⟩
              ∙ aR3 C _ _ _ _
              ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ sym (▷wSeq C _ _ fS)
                               ∙ C.⟨ C.α _ _ _ _ .nIso (ax , bx , cx) .sec
                                 ⟩▷ fS
                               ∙ C.▷wId fS ⟩
                      ∙ C.⋆₂IdR _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ sym ( C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
                  C.⟨ ◁5 C ax _ _ _ _ _ ⟩⋆₂⟨⟩
                  ∙ aR5 C _ _ _ _ _ _ ⟩ ⟩ ⟩ ⟩ )

  assocMod : Modification (seqLaxNatTrans (seqLaxNatTrans α β) γ)
                          (seqLaxNatTrans α (seqLaxNatTrans β γ))
  assocMod .M-ob x =
    C.α⁺ (α .N-1cell x) (β .N-1cell x) (γ .N-1cell x)
  assocMod .M-hom f = assocHom f

  assocModInv : Modification (seqLaxNatTrans α (seqLaxNatTrans β γ))
                             (seqLaxNatTrans (seqLaxNatTrans α β) γ)
  assocModInv = invMod assocMod
    (λ x → C.α _ _ _ _
      .nIso (α .N-1cell x , β .N-1cell x , γ .N-1cell x))
