{-# OPTIONS --lossy-unification #-}
{- The representable prestack B [-, a ]: precomposition,
   with F⁰ = λ and F² = α. -}
module Cubical.Categories.Bicategory.Prestack.Hom where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Functors.Currying
open import Cubical.Categories.Instances.BinProduct

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Constructions.Op
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Prestack.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

open Functor
open NatTrans
open NatIso
open isIso
open LaxFunctor
open Pseudofunctor

module _ (B : Bicategory ℓ ℓ' ℓ'') (a : Bicategory.0Cell B) where
  private
    module B = Bicategory B

  private
    precomp : {x y : Bicategory.0Cell B}
      → Functor B.Hom[ y , x ] (FUNCTOR B.Hom[ x , a ] B.Hom[ y , a ])
    precomp {x} {y} =
      λF B.Hom[ x , a ] B.Hom[ y , a ] B.Hom[ y , x ] (B.seq y x a)

    ι : (x : Bicategory.0Cell B)
      → NatTrans Id (precomp {x} {x} .F-ob B.id₁)
    ι x .N-ob f = B.λ⁻ f
    ι x .N-hom α =
        symNatIso (B.λU x a) .trans .N-hom (_ , α)
      ∙ B.⟨⟩⋆₂⟨ B.⟨ B.id {x} .F-id ⟩⋆ₕ⟨⟩ ⟩

    ν : {x y z : Bicategory.0Cell B} (k : B.1Cell y x) (l : B.1Cell z y)
      → NatTrans (seqCAT B.Hom[ x , a ] B.Hom[ y , a ] B.Hom[ z , a ]
                    .F-ob (precomp .F-ob k , precomp .F-ob l))
                 (precomp .F-ob (l B.⋆₁ k))
    ν {x} {y} {z} k l .N-ob f = B.α⁻ l k f
    ν {x} {y} {z} k l .N-hom α =
        symNatIso (B.α z y x a) .trans .N-hom (B.id₂ , B.id₂ , α)
      ∙ B.⟨⟩⋆₂⟨ B.⟨ B.⋆ₕId ⟩⋆ₕ⟨⟩ ⟩

  HomLax : LaxFunctor (B ^opᴮ) (CAT {ℓ'} {ℓ''})
  HomLax .F-ob x = B.Hom[ x , a ]
  HomLax .F-Hom {x} {y} = precomp {x} {y}
  HomLax .F-id {x} .N-ob _ = ι x
  HomLax .F-id {x} .N-hom _ = makeNatTransPath (funExt λ f →
      B.⋆₂IdL _
    ∙ sym (B.⋆₂IdR _)
    ∙ B.⟨⟩⋆₂⟨ sym seq-id ⟩)
    where
    seq-id : {f : B.1Cell x a}
      → B.seq x x a .F-hom (B.id {x} .F-hom refl , B.id₂ {f = f}) ≡ B.id₂
    seq-id = B.⟨ B.id {x} .F-id ⟩⋆ₕ⟨⟩
           ∙ B.⋆ₕId
  HomLax .F-seq {x} {y} {z} .N-ob (k , l) = ν k l
  HomLax .F-seq {x} {y} {z} .N-hom {k , l} {k' , l'} (σ , τ) =
    makeNatTransPath (funExt λ f →
        B.⟨ reduce f ⟩⋆₂⟨⟩
      ∙ symNatIso (B.α z y x a) .trans .N-hom (τ , σ , B.id₂))
    where
    reduce : (f : B.1Cell x a)
      → (l B.◁w (σ B.▷w f)) B.⋆₂ (τ B.▷w (k' B.⋆₁ f))
        ≡ B.seq z y a .F-hom (τ , B.seq y x a .F-hom (σ , B.id₂))
    reduce f =
        sym (B.⋆ₕSeq B.id₂ τ (σ B.▷w f) B.id₂)
      ∙ B.⟨ B.⋆₂IdL τ ⟩⋆ₕ⟨ B.⋆₂IdR _ ⟩
  HomLax .lax-λ x y f = makeNatTransPath (funExt λ g →
      cong (B._⋆₂ (B.α⁻ f B.id₁ g B.⋆₂ (B.ρ⁺ f B.▷w g)))
           (B.⋆₂IdR _)
    ∙ cong (λ m → (f B.◁w B.λ⁻ g) B.⋆₂ (B.α⁻ f B.id₁ g B.⋆₂ m))
           (sym (B.triangle y x a f g))
    ∙ cong ((f B.◁w B.λ⁻ g) B.⋆₂_)
           ( sym (B.⋆₂Assoc _ _ _)
           ∙ B.⟨ B.α y x x a .nIso (f , B.id₁ , g) .sec ⟩⋆₂⟨⟩
           ∙ B.⋆₂IdL _)
    ∙ sym (B.⋆ₕSeq B.id₂ B.id₂ (B.λ⁻ g) (B.λ⁺ g))
    ∙ B.⟨ B.⋆₂IdL B.id₂ ⟩⋆ₕ⟨ B.λU x a .nIso (_ , g) .sec ⟩
    ∙ B.⋆ₕId)
  HomLax .lax-ρ x y f = makeNatTransPath (funExt λ p →
      cong (B._⋆₂ (B.α⁻ B.id₁ f p B.⋆₂ (B.λ⁺ f B.▷w p)))
           (B.⋆₂IdL _)
    ∙ B.⟨⟩⋆₂⟨ λ⋆₁ B f p ⟩
    ∙ B.λU y a .nIso (tt* , f B.⋆₁ p) .sec)
  HomLax .lax-α x y z w f g h = makeNatTransPath (funExt λ p →
      cong (B._⋆₂ (B.α⁻ h (g B.⋆₁ f) p B.⋆₂ (B.α⁻ h g f B.▷w p)))
           (B.⋆₂IdR _)
    ∙ Bicategory.pentagon (B ^opᴮ) a x y z w p f g h
    ∙ sym ( B.⋆₂IdL _
          ∙ cong (B._⋆₂ B.α⁻ (h B.⋆₁ g) f p)
                 ( cong (B._⋆₂ B.α⁻ h g (f B.⋆₁ p))
                        ( h B.◁⟨ B.⋆ₕId ⟩
                        ∙ B.⋆ₕId)
                 ∙ B.⋆₂IdL _)))

  private
    ι⁻ : (x : Bicategory.0Cell B)
      → NatTrans (precomp {x} {x} .F-ob B.id₁) Id
    ι⁻ x .N-ob f = B.λ⁺ f
    ι⁻ x .N-hom α =
        B.⟨ B.⟨ sym (B.id {x} .F-id) ⟩⋆ₕ⟨⟩ ⟩⋆₂⟨⟩
      ∙ B.λU x a .trans .N-hom (_ , α)

    ν⁻ : {x y z : Bicategory.0Cell B} (k : B.1Cell y x) (l : B.1Cell z y)
      → NatTrans (precomp .F-ob (l B.⋆₁ k))
                 (seqCAT B.Hom[ x , a ] B.Hom[ y , a ] B.Hom[ z , a ]
                    .F-ob (precomp .F-ob k , precomp .F-ob l))
    ν⁻ {x} {y} {z} k l .N-ob f = B.α⁺ l k f
    ν⁻ {x} {y} {z} k l .N-hom α =
        B.⟨ B.⟨ sym B.⋆ₕId ⟩⋆ₕ⟨⟩ ⟩⋆₂⟨⟩
      ∙ B.α z y x a .trans .N-hom (B.id₂ , B.id₂ , α)

  Hom : Prestack B ℓ' ℓ''
  Hom .laxFunctor = HomLax
  Hom .F-id-isIso {x} _ .inv = ι⁻ x
  Hom .F-id-isIso {x} _ .sec =
    makeNatTransPath (funExt λ f → B.λU x a .nIso (_ , f) .ret)
  Hom .F-id-isIso {x} _ .ret =
    makeNatTransPath (funExt λ f → B.λU x a .nIso (_ , f) .sec)
  Hom .F-seq-isIso {x} {y} {z} (k , l) .inv = ν⁻ k l
  Hom .F-seq-isIso {x} {y} {z} (k , l) .sec =
    makeNatTransPath (funExt λ f → B.α z y x a .nIso (l , k , f) .ret)
  Hom .F-seq-isIso {x} {y} {z} (k , l) .ret =
    makeNatTransPath (funExt λ f → B.α z y x a .nIso (l , k , f) .sec)
