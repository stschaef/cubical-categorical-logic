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
open import Cubical.Categories.Bicategory.Properties.Coherence
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.Transformation.Properties
open import Cubical.Categories.Bicategory.Transformation.Identity
open import Cubical.Categories.Bicategory.Transformation.Composition
open import Cubical.Categories.Bicategory.Transformation.Coherence
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

  -- Steps 3-5: the unitors and the associator, componentwise the
  -- generic ones for `seqLaxNatTrans`.
  PRESTACKλ : (P Q : Prestack B ℓp ℓp')
    → NatIso (PRESTACKseq P P Q
                ∘F (PRESTACKid P ×F 𝟙⟨ PrestackHomCat {B = B} P Q ⟩))
             (Snd 𝟙C (PrestackHomCat {B = B} P Q))
  PRESTACKλ P Q .trans .N-ob (_ , α , _) = lamMod α
  PRESTACKλ P Q .trans .N-hom (_ , Γ) =
    makeModificationPath (λ x → λ-nat C (Γ .M-ob x))
  PRESTACKλ P Q .nIso (_ , α , _) .inv = lamModInv α
  PRESTACKλ P Q .nIso (_ , α , _) .sec =
    makeModificationPath (λ x → C.λU _ _ .nIso (tt* , α .N-1cell x) .sec)
  PRESTACKλ P Q .nIso (_ , α , _) .ret =
    makeModificationPath (λ x → C.λU _ _ .nIso (tt* , α .N-1cell x) .ret)

  PRESTACKρ : (P Q : Prestack B ℓp ℓp')
    → NatIso (PRESTACKseq P Q Q
                ∘F (𝟙⟨ PrestackHomCat {B = B} P Q ⟩ ×F PRESTACKid Q))
             (Fst (PrestackHomCat {B = B} P Q) 𝟙C)
  PRESTACKρ P Q .trans .N-ob ((α , _) , _) = rhoMod α
  PRESTACKρ P Q .trans .N-hom (Γ , _) =
    makeModificationPath (λ x → ρ-nat C (Γ .M-ob x))
  PRESTACKρ P Q .nIso ((α , _) , _) .inv = rhoModInv α
  PRESTACKρ P Q .nIso ((α , _) , _) .sec =
    makeModificationPath (λ x → C.ρU _ _ .nIso (α .N-1cell x , tt*) .sec)
  PRESTACKρ P Q .nIso ((α , _) , _) .ret =
    makeModificationPath (λ x → C.ρU _ _ .nIso (α .N-1cell x , tt*) .ret)

  PRESTACKα : (P Q R S : Prestack B ℓp ℓp')
    → NatIso (PRESTACKseq P R S
                ∘F (PRESTACKseq P Q R ×F 𝟙⟨ PrestackHomCat {B = B} R S ⟩)
                ∘F ×C-assoc (PrestackHomCat {B = B} P Q)
                            (PrestackHomCat {B = B} Q R)
                            (PrestackHomCat {B = B} R S))
             (PRESTACKseq P Q S
                ∘F (𝟙⟨ PrestackHomCat {B = B} P Q ⟩ ×F PRESTACKseq Q R S))
  PRESTACKα P Q R S .trans .N-ob ((α , _) , (β , _) , (γ , _)) =
    assocMod α β γ
  PRESTACKα P Q R S .trans .N-hom (Γ , Δ , Θ) =
    makeModificationPath
      (λ x → α⁺nat C (Γ .M-ob x) (Δ .M-ob x) (Θ .M-ob x))
  PRESTACKα P Q R S .nIso ((α , _) , (β , _) , (γ , _)) .inv =
    assocModInv α β γ
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
