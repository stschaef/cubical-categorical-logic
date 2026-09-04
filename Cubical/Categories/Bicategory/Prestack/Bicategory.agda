{-# OPTIONS --lossy-unification #-}
{- The bicategory of prestacks: prestacks, pseudonatural
   transformations and modifications. -}
module Cubical.Categories.Bicategory.Prestack.Bicategory where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More hiding (α)
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Terminal
open import Cubical.Categories.Instances.FullSubcategory

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Constructions.Op
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.Transformation.Properties
open import Cubical.Categories.Bicategory.Transformation.Identity
open import Cubical.Categories.Bicategory.Transformation.Composition
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Morphism

private
  variable
    ℓ ℓ' ℓ'' ℓp ℓp' : Level

open Functor
open NatTrans
open NatIso
open isIso
open LaxNatTrans
open Modification
open Pseudofunctor

module _ (B : Bicategory ℓ ℓ' ℓ'') (ℓp ℓp' : Level) where
  private
    C : Bicategory (ℓ-suc (ℓ-max ℓp ℓp')) (ℓ-max ℓp ℓp') (ℓ-max ℓp ℓp')
    C = CAT {ℓp} {ℓp'}

    module C = Bicategory C

    isoα⁻ : {w x y z : C.0Cell}
      (p : C.1Cell w x) (q : C.1Cell x y) (r : C.1Cell y z)
      → isIso C.Hom[ w , z ] (C.α⁻ p q r)
    isoα⁻ p q r = invIso (_ , C.α _ _ _ _ .nIso (p , q , r)) .snd

    isoα⁺ : {w x y z : C.0Cell}
      (p : C.1Cell w x) (q : C.1Cell x y) (r : C.1Cell y z)
      → isIso C.Hom[ w , z ] (C.α⁺ p q r)
    isoα⁺ p q r = C.α _ _ _ _ .nIso (p , q , r)

    -- triangle, read with the associator on the other side
    ▷5 : {x y z : C.0Cell} {f₀ f₁ f₂ f₃ f₄ f₅ : C.1Cell x y}
      (p : C.2Cell f₀ f₁) (q : C.2Cell f₁ f₂) (r : C.2Cell f₂ f₃)
      (s : C.2Cell f₃ f₄) (u : C.2Cell f₄ f₅) (h : C.1Cell y z)
      →   ((p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ u) C.▷w h)
        ≡ (p C.▷w h) C.⋆₂ (q C.▷w h) C.⋆₂ (r C.▷w h)
            C.⋆₂ (s C.▷w h) C.⋆₂ (u C.▷w h)
    ▷5 p q r s u h =
        ▷wSeq C p _ h
      ∙ C.⟨⟩⋆₂⟨ ▷wSeq C q _ h ∙ C.⟨⟩⋆₂⟨ ▷3 C r s u h ⟩ ⟩

    ◁5 : {x y z : C.0Cell} (e : C.1Cell x y)
      {f₀ f₁ f₂ f₃ f₄ f₅ : C.1Cell y z}
      (p : C.2Cell f₀ f₁) (q : C.2Cell f₁ f₂) (r : C.2Cell f₂ f₃)
      (s : C.2Cell f₃ f₄) (u : C.2Cell f₄ f₅)
      →   (e C.◁w (p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ u))
        ≡ (e C.◁w p) C.⋆₂ (e C.◁w q) C.⋆₂ (e C.◁w r)
            C.⋆₂ (e C.◁w s) C.⋆₂ (e C.◁w u)
    ◁5 e p q r s u =
        ◁wSeq C e p _
      ∙ C.⟨⟩⋆₂⟨ ◁wSeq C e q _ ∙ C.⟨⟩⋆₂⟨ ◁3 C e r s u ⟩ ⟩

  -- Step 1: the composite of two pseudonatural transformations is
  -- pseudonatural.
  seqIsPseudo : (P Q R : Prestack B ℓp ℓp')
    (σ : PrestackHom P Q) (τ : PrestackHom Q R)
    → isPseudoNat P Q σ → isPseudoNat Q R τ
    → isPseudoNat P R (seqLaxNatTrans σ τ)
  seqIsPseudo P Q R σ τ pσ pτ f =
    ⋆IsIso (isoα⁻ _ _ _)
      (⋆IsIso (▷wIsIso C _ (pσ f))
        (⋆IsIso (isoα⁺ _ _ _)
          (⋆IsIso (◁wIsIso C _ (pτ f)) (isoα⁻ _ _ _))))

  PRESTACKseq : (P Q R : Prestack B ℓp ℓp')
    → Functor (PrestackHomCat {B = B} P Q ×C PrestackHomCat {B = B} Q R)
              (PrestackHomCat {B = B} P R)
  PRESTACKseq P Q R =
    ToFullSubcategory _ _ _
      (seqLaxNatTransF ∘F (FullInclusion _ _ ×F FullInclusion _ _))
      (λ pr → seqIsPseudo P Q R (pr .fst .fst) (pr .snd .fst)
                          (pr .fst .snd) (pr .snd .snd))

  -- Step 2: the identity pseudonatural transformation.
  PRESTACKid : (P : Prestack B ℓp ℓp')
    → Functor 𝟙C (PrestackHomCat {B = B} P P)
  PRESTACKid P = FunctorFromTerminal
    (idLaxNatTrans (P .laxFunctor) , idIsPseudo (P .laxFunctor))

  -- Step 3: the left unitor.
  module _ (P Q : Prestack B ℓp ℓp') (α : PrestackHom P Q) where
    private
      module Bo = Bicategory (B ^opᴮ)
      module Pl = LaxFunctor (P .laxFunctor)
      module Ql = LaxFunctor (Q .laxFunctor)

      idα : PrestackHom P P
      idα = idLaxNatTrans (P .laxFunctor)

      lamHom : {x y : Bo.ob} (f : Bo.1Cell x y)
        →   seqLaxNatTrans idα α .N-hom f
              C.⋆₂ (C.λ⁺ (α .N-1cell x) C.▷w Ql.F-1cell f)
          ≡ (Pl.F-1cell f C.◁w C.λ⁺ (α .N-1cell y)) C.⋆₂ α .N-hom f
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
        Pf = Pl.F-1cell f
        Qf = Ql.F-1cell f
        Ax = α .N-1cell x
        Ay = α .N-1cell y
        N  = α .N-hom f

    lamMod : Modification (seqLaxNatTrans idα α) α
    lamMod .M-ob x = C.λ⁺ (α .N-1cell x)
    lamMod .M-hom = lamHom

    lamModInv : Modification α (seqLaxNatTrans idα α)
    lamModInv = invMod lamMod
      (λ x → C.λU _ _ .nIso (tt* , α .N-1cell x))

  PRESTACKλ : (P Q : Prestack B ℓp ℓp')
    → NatIso (PRESTACKseq P P Q
                ∘F (PRESTACKid P ×F 𝟙⟨ PrestackHomCat {B = B} P Q ⟩))
             (Snd 𝟙C (PrestackHomCat {B = B} P Q))
  PRESTACKλ P Q .trans .N-ob (_ , α , _) = lamMod P Q α
  PRESTACKλ P Q .trans .N-hom (_ , Γ) =
    makeModificationPath (λ x → λ-nat C (Γ .M-ob x))
  PRESTACKλ P Q .nIso (_ , α , _) .inv = lamModInv P Q α
  PRESTACKλ P Q .nIso (_ , α , _) .sec =
    makeModificationPath (λ x → C.λU _ _ .nIso (tt* , α .N-1cell x) .sec)
  PRESTACKλ P Q .nIso (_ , α , _) .ret =
    makeModificationPath (λ x → C.λU _ _ .nIso (tt* , α .N-1cell x) .ret)

  -- Step 4: the right unitor.
  module _ (P Q : Prestack B ℓp ℓp') (α : PrestackHom P Q) where
    private
      module Bo = Bicategory (B ^opᴮ)
      module Pl = LaxFunctor (P .laxFunctor)
      module Ql = LaxFunctor (Q .laxFunctor)

      idβ : PrestackHom Q Q
      idβ = idLaxNatTrans (Q .laxFunctor)

      rhoHom : {x y : Bo.ob} (f : Bo.1Cell x y)
        →   seqLaxNatTrans α idβ .N-hom f
              C.⋆₂ (C.ρ⁺ (α .N-1cell x) C.▷w Ql.F-1cell f)
          ≡ (Pl.F-1cell f C.◁w C.ρ⁺ (α .N-1cell y)) C.⋆₂ α .N-hom f
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
        Pf = Pl.F-1cell f
        Qf = Ql.F-1cell f
        Ax = α .N-1cell x
        Ay = α .N-1cell y
        N  = α .N-hom f

    rhoMod : Modification (seqLaxNatTrans α idβ) α
    rhoMod .M-ob x = C.ρ⁺ (α .N-1cell x)
    rhoMod .M-hom = rhoHom

    rhoModInv : Modification α (seqLaxNatTrans α idβ)
    rhoModInv = invMod rhoMod
      (λ x → C.ρU _ _ .nIso (α .N-1cell x , tt*))

  PRESTACKρ : (P Q : Prestack B ℓp ℓp')
    → NatIso (PRESTACKseq P Q Q
                ∘F (𝟙⟨ PrestackHomCat {B = B} P Q ⟩ ×F PRESTACKid Q))
             (Fst (PrestackHomCat {B = B} P Q) 𝟙C)
  PRESTACKρ P Q .trans .N-ob ((α , _) , _) = rhoMod P Q α
  PRESTACKρ P Q .trans .N-hom (Γ , _) =
    makeModificationPath (λ x → ρ-nat C (Γ .M-ob x))
  PRESTACKρ P Q .nIso ((α , _) , _) .inv = rhoModInv P Q α
  PRESTACKρ P Q .nIso ((α , _) , _) .sec =
    makeModificationPath (λ x → C.ρU _ _ .nIso (α .N-1cell x , tt*) .sec)
  PRESTACKρ P Q .nIso ((α , _) , _) .ret =
    makeModificationPath (λ x → C.ρU _ _ .nIso (α .N-1cell x , tt*) .ret)

  -- Step 5: the associator.
  module _ (P Q R S : Prestack B ℓp ℓp')
    (α : PrestackHom P Q) (β : PrestackHom Q R) (γ : PrestackHom R S)
    where
    private
      module Bo = Bicategory (B ^opᴮ)
      module Pl = LaxFunctor (P .laxFunctor)
      module Ql = LaxFunctor (Q .laxFunctor)
      module Rl = LaxFunctor (R .laxFunctor)
      module Sl = LaxFunctor (S .laxFunctor)

      module _ {x y : Bo.ob} (f : Bo.1Cell x y) where
        private
          fP = Pl.F-1cell f
          fQ = Ql.F-1cell f
          fR = Rl.F-1cell f
          fS = Sl.F-1cell f
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
          ∙ C.⟨⟩⋆₂⟨ C.⟨ ▷5 _ _ _ _ _ cy ⟩⋆₂⟨⟩ ∙ aR5 C _ _ _ _ _ _ ⟩
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
                    C.⟨ ◁5 ax _ _ _ _ _ ⟩⋆₂⟨⟩
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

  PRESTACKα : (P Q R S : Prestack B ℓp ℓp')
    → NatIso (PRESTACKseq P R S
                ∘F (PRESTACKseq P Q R ×F 𝟙⟨ PrestackHomCat {B = B} R S ⟩)
                ∘F ×C-assoc (PrestackHomCat {B = B} P Q)
                            (PrestackHomCat {B = B} Q R)
                            (PrestackHomCat {B = B} R S))
             (PRESTACKseq P Q S
                ∘F (𝟙⟨ PrestackHomCat {B = B} P Q ⟩ ×F PRESTACKseq Q R S))
  PRESTACKα P Q R S .trans .N-ob ((α , _) , (β , _) , (γ , _)) =
    assocMod P Q R S α β γ
  PRESTACKα P Q R S .trans .N-hom (Γ , Δ , Θ) =
    makeModificationPath
      (λ x → α⁺nat C (Γ .M-ob x) (Δ .M-ob x) (Θ .M-ob x))
  PRESTACKα P Q R S .nIso ((α , _) , (β , _) , (γ , _)) .inv =
    assocModInv P Q R S α β γ
  PRESTACKα P Q R S .nIso ((α , _) , (β , _) , (γ , _)) .sec =
    makeModificationPath (λ x → C.α _ _ _ _
      .nIso (α .N-1cell x , β .N-1cell x , γ .N-1cell x) .sec)
  PRESTACKα P Q R S .nIso ((α , _) , (β , _) , (γ , _)) .ret =
    makeModificationPath (λ x → C.α _ _ _ _
      .nIso (α .N-1cell x , β .N-1cell x , γ .N-1cell x) .ret)

  -- Steps 6 and 7: the two axioms, and the assembled bicategory.
  PRESTACK : Bicategory _ _ _
  PRESTACK .Bicategory.ob = Prestack B ℓp ℓp'
  PRESTACK .Bicategory.Hom[_,_] = PrestackHomCat {B = B}
  PRESTACK .Bicategory.id = PRESTACKid _
  PRESTACK .Bicategory.seq = PRESTACKseq
  PRESTACK .Bicategory.λU = PRESTACKλ
  PRESTACK .Bicategory.ρU = PRESTACKρ
  PRESTACK .Bicategory.α = PRESTACKα
  PRESTACK .Bicategory.triangle P Q R (α , _) (β , _) =
    makeModificationPath
      (λ x → C.triangle _ _ _ (α .N-1cell x) (β .N-1cell x))
  PRESTACK .Bicategory.pentagon P Q R S T (α , _) (β , _) (γ , _) (δ , _) =
    makeModificationPath
      (λ x → C.pentagon _ _ _ _ _ (α .N-1cell x) (β .N-1cell x)
                                  (γ .N-1cell x) (δ .N-1cell x))
