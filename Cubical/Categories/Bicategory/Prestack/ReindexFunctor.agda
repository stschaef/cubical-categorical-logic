{-# OPTIONS --lossy-unification #-}
{- Reindexing of prestacks is a pseudofunctor
   PRESTACK B → PRESTACK A. -}
module Cubical.Categories.Bicategory.Prestack.ReindexFunctor where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.FullSubcategory

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Constructions.Op
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Functor.Op
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.Transformation.Properties
open import Cubical.Categories.Bicategory.Transformation.Identity
open import Cubical.Categories.Bicategory.Transformation.Composition
open import Cubical.Categories.Bicategory.Transformation.Whisker
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Morphism
open import Cubical.Categories.Bicategory.Prestack.Bicategory
open import Cubical.Categories.Bicategory.Prestack.Reindex

private
  variable
    ℓa ℓa' ℓa'' ℓb ℓb' ℓb'' ℓp ℓp' : Level

open Functor
open NatTrans
open isIso
open LaxFunctor
open LaxNatTrans
open Modification
open Pseudofunctor

module _ {A : Bicategory ℓa ℓa' ℓa''} {B : Bicategory ℓb ℓb' ℓb''}
  (F : Pseudofunctor A B) (ℓp ℓp' : Level) where
  private
    C : Bicategory (ℓ-suc (ℓ-max ℓp ℓp')) (ℓ-max ℓp ℓp') (ℓ-max ℓp ℓp')
    C = CAT {ℓp} {ℓp'}
    module C = Bicategory C

    K : LaxFunctor (A ^opᴮ) (B ^opᴮ)
    K = OpLax (F .laxFunctor)
    module K = LaxFunctor K

    R : Prestack B ℓp ℓp' → Prestack A ℓp ℓp'
    R = reindexPrestack F

    Hom₀ : (P Q : Prestack B ℓp ℓp')
      → Functor (PrestackHomCat {B = B} P Q)
                (PrestackHomCat {B = A} (R P) (R Q))
    Hom₀ P Q =
      MapFullSubcategory _ _ _ _ (whiskerRF K) (λ σ pσ f → pσ (K.F-1cell f))

    εMod : (P : Prestack B ℓp ℓp')
      → Modification (idLaxNatTrans ((R P) .laxFunctor))
                     (whiskerR K (idLaxNatTrans (P .laxFunctor)))
    εMod P .M-ob x = C.id₂
    εMod P .M-hom f =
        C.⟨⟩⋆₂⟨ C.▷wId _ ⟩
      ∙ C.⋆₂IdR _
      ∙ sym (C.⋆₂IdL _)
      ∙ C.⟨ sym (C.◁wId _) ⟩⋆₂⟨⟩

    εMod⁻ : (P : Prestack B ℓp ℓp')
      → Modification (whiskerR K (idLaxNatTrans (P .laxFunctor)))
                     (idLaxNatTrans ((R P) .laxFunctor))
    εMod⁻ P .M-ob x = C.id₂
    εMod⁻ P .M-hom f =
        C.⟨⟩⋆₂⟨ C.▷wId _ ⟩
      ∙ C.⋆₂IdR _
      ∙ sym (C.⋆₂IdL _)
      ∙ C.⟨ sym (C.◁wId _) ⟩⋆₂⟨⟩

    module _ (P Q S : Prestack B ℓp ℓp')
      (σ : PrestackHom P Q) (τ : PrestackHom Q S) where

      μMod : Modification (seqLaxNatTrans (whiskerR K σ) (whiskerR K τ))
                          (whiskerR K (seqLaxNatTrans σ τ))
      μMod .M-ob x = C.id₂
      μMod .M-hom f =
          C.⟨⟩⋆₂⟨ C.▷wId _ ⟩
        ∙ C.⋆₂IdR _
        ∙ sym (C.⋆₂IdL _)
        ∙ C.⟨ sym (C.◁wId _) ⟩⋆₂⟨⟩

      μMod⁻ : Modification (whiskerR K (seqLaxNatTrans σ τ))
                           (seqLaxNatTrans (whiskerR K σ) (whiskerR K τ))
      μMod⁻ .M-ob x = C.id₂
      μMod⁻ .M-hom f =
          C.⟨⟩⋆₂⟨ C.▷wId _ ⟩
        ∙ C.⋆₂IdR _
        ∙ sym (C.⋆₂IdL _)
        ∙ C.⟨ sym (C.◁wId _) ⟩⋆₂⟨⟩

  reindexLax : LaxFunctor (PRESTACK B ℓp ℓp') (PRESTACK A ℓp ℓp')
  reindexLax .F-ob = R
  reindexLax .F-Hom {P} {Q} = Hom₀ P Q
  reindexLax .F-id {P} .N-ob _ = εMod P
  reindexLax .F-id {P} .N-hom _ = makeModificationPath (λ x → refl)
  reindexLax .F-seq {P} {Q} {S} .N-ob (σ , τ) = μMod P Q S (σ .fst) (τ .fst)
  reindexLax .F-seq .N-hom (Γ , Δ) =
    makeModificationPath (λ x → C.⋆₂IdR _ ∙ sym (C.⋆₂IdL _))
  reindexLax .lax-λ P Q f =
    makeModificationPath
      (λ x → C.⟨ C.⋆ₕId ⟩⋆₂⟨ C.⋆₂IdL _ ⟩ ∙ C.⋆₂IdL _)
  reindexLax .lax-ρ P Q f =
    makeModificationPath
      (λ x → C.⟨ C.⋆ₕId ⟩⋆₂⟨ C.⋆₂IdL _ ⟩ ∙ C.⋆₂IdL _)
  reindexLax .lax-α P Q S T f g h =
    makeModificationPath
      (λ x → C.⟨ C.⋆ₕId ⟩⋆₂⟨ C.⋆₂IdL _ ⟩ ∙ C.⋆₂IdL _
           ∙ sym ( C.⟨⟩⋆₂⟨ C.⟨ C.⋆ₕId ⟩⋆₂⟨⟩ ∙ C.⋆₂IdL _ ⟩
                 ∙ C.⋆₂IdR _))

  reindexPs : Pseudofunctor (PRESTACK B ℓp ℓp') (PRESTACK A ℓp ℓp')
  reindexPs .laxFunctor = reindexLax
  reindexPs .F-id-isIso {P} _ .inv = εMod⁻ P
  reindexPs .F-id-isIso {P} _ .sec = makeModificationPath (λ x → C.⋆₂IdL _)
  reindexPs .F-id-isIso {P} _ .ret = makeModificationPath (λ x → C.⋆₂IdL _)
  reindexPs .F-seq-isIso {P} {Q} {S} (σ , τ) .inv =
    μMod⁻ P Q S (σ .fst) (τ .fst)
  reindexPs .F-seq-isIso {P} {Q} {S} (σ , τ) .sec =
    makeModificationPath (λ x → C.⋆₂IdL _)
  reindexPs .F-seq-isIso {P} {Q} {S} (σ , τ) .ret =
    makeModificationPath (λ x → C.⋆₂IdL _)
