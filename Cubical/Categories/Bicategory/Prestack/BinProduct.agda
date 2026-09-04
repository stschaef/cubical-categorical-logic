{-# OPTIONS --lossy-unification #-}
{- Pointwise binary product of prestacks: everything is componentwise. -}
module Cubical.Categories.Bicategory.Prestack.BinProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More hiding (α)
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.BinProduct

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Prestack.Base

private
  variable
    ℓ ℓ' ℓ'' ℓp ℓp' : Level
    ℓa ℓa' ℓb ℓb' ℓc ℓc' ℓd ℓd' : Level

open Functor
open NatTrans
open isIso
open LaxFunctor
open Pseudofunctor

module _ {A : Category ℓa ℓa'} {B : Category ℓb ℓb'}
         {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} where
  ×NT : {F F' : Functor A B} {G G' : Functor C D}
    → NatTrans F F' → NatTrans G G' → NatTrans (F ×F G) (F' ×F G')
  ×NT α β .N-ob (a , c) = α .N-ob a , β .N-ob c
  ×NT α β .N-hom (f , g) = ≡-× (α .N-hom f) (β .N-hom g)

  -- `_×F_` is only the object part of this functor.
  ×FF : Functor (FUNCTOR A B ×C FUNCTOR C D) (FUNCTOR (A ×C C) (B ×C D))
  ×FF .F-ob (F , G) = F ×F G
  ×FF .F-hom (α , β) = ×NT α β
  ×FF .F-id = makeNatTransPath refl
  ×FF .F-seq _ _ = makeNatTransPath refl

module _ {A : Bicategory ℓ ℓ' ℓ''}
         (P Q : Pseudofunctor A (CAT {ℓp} {ℓp'})) where
  private
    module A = Bicategory A
    module P = Pseudofunctor P
    module Q = Pseudofunctor Q

    R⟨_⟩ : A.ob → Category ℓp ℓp'
    R⟨ x ⟩ = P.F-ob x ×C Q.F-ob x

    ι : (x : A.ob) → NatTrans (Id {C = R⟨ x ⟩})
      (P.F-1cell (A.id₁ {x}) ×F Q.F-1cell (A.id₁ {x}))
    ι x .N-ob (e , e') = P.F⁰ .N-ob e , Q.F⁰ .N-ob e'
    ι x .N-hom (g , g') = ≡-× (P.F⁰ .N-hom g) (Q.F⁰ .N-hom g')

    ι⁻ : (x : A.ob)
      → NatTrans (P.F-1cell (A.id₁ {x}) ×F Q.F-1cell (A.id₁ {x}))
                 (Id {C = R⟨ x ⟩})
    ι⁻ x .N-ob (e , e') =
      P.F-id-isIso tt* .inv .N-ob e , Q.F-id-isIso tt* .inv .N-ob e'
    ι⁻ x .N-hom (g , g') =
      ≡-× (P.F-id-isIso tt* .inv .N-hom g)
          (Q.F-id-isIso tt* .inv .N-hom g')

    ν : {x y z : A.ob} (k : A.1Cell x y) (l : A.1Cell y z)
      → NatTrans (seqCAT R⟨ x ⟩ R⟨ y ⟩ R⟨ z ⟩ .F-ob
                   ( P.F-1cell k ×F Q.F-1cell k
                   , P.F-1cell l ×F Q.F-1cell l))
                 (P.F-1cell (k A.⋆₁ l) ×F Q.F-1cell (k A.⋆₁ l))
    ν k l .N-ob (e , e') = P.F² k l .N-ob e , Q.F² k l .N-ob e'
    ν k l .N-hom (g , g') = ≡-× (P.F² k l .N-hom g) (Q.F² k l .N-hom g')

    ν⁻ : {x y z : A.ob} (k : A.1Cell x y) (l : A.1Cell y z)
      → NatTrans (P.F-1cell (k A.⋆₁ l) ×F Q.F-1cell (k A.⋆₁ l))
                 (seqCAT R⟨ x ⟩ R⟨ y ⟩ R⟨ z ⟩ .F-ob
                   ( P.F-1cell k ×F Q.F-1cell k
                   , P.F-1cell l ×F Q.F-1cell l))
    ν⁻ k l .N-ob (e , e') =
      P.F-seq-isIso (k , l) .inv .N-ob e , Q.F-seq-isIso (k , l) .inv .N-ob e'
    ν⁻ k l .N-hom (g , g') =
      ≡-× (P.F-seq-isIso (k , l) .inv .N-hom g)
          (Q.F-seq-isIso (k , l) .inv .N-hom g')

  ×PsLax : LaxFunctor A (CAT {ℓp} {ℓp'})
  ×PsLax .F-ob x = R⟨ x ⟩
  ×PsLax .F-Hom {x} {y} =
    ×FF {A = P.F-ob x} {B = P.F-ob y} {C = Q.F-ob x} {D = Q.F-ob y}
    ∘F (P.F-Hom ,F Q.F-Hom)
  ×PsLax .F-id {x} .N-ob _ = ι x
  ×PsLax .F-id {x} .N-hom f = makeNatTransPath (funExt λ e →
    ≡-× (N-obPath (P.F-id .N-hom f) (e .fst))
        (N-obPath (Q.F-id .N-hom f) (e .snd)))
  ×PsLax .F-seq .N-ob (k , l) = ν k l
  ×PsLax .F-seq .N-hom στ = makeNatTransPath (funExt λ e →
    ≡-× (N-obPath (P.F-seq .N-hom στ) (e .fst))
        (N-obPath (Q.F-seq .N-hom στ) (e .snd)))
  ×PsLax .lax-λ x y f = makeNatTransPath (funExt λ e →
    ≡-× (N-obPath (P.lax-λ x y f) (e .fst))
        (N-obPath (Q.lax-λ x y f) (e .snd)))
  ×PsLax .lax-ρ x y f = makeNatTransPath (funExt λ e →
    ≡-× (N-obPath (P.lax-ρ x y f) (e .fst))
        (N-obPath (Q.lax-ρ x y f) (e .snd)))
  ×PsLax .lax-α x y z w f g h = makeNatTransPath (funExt λ e →
    ≡-× (N-obPath (P.lax-α x y z w f g h) (e .fst))
        (N-obPath (Q.lax-α x y z w f g h) (e .snd)))

  ×Ps : Pseudofunctor A (CAT {ℓp} {ℓp'})
  ×Ps .laxFunctor = ×PsLax
  ×Ps .F-id-isIso {x} p .inv = ι⁻ x
  ×Ps .F-id-isIso {x} p .sec = makeNatTransPath (funExt λ e →
    ≡-× (N-obPath (P.F-id-isIso p .sec) (e .fst))
        (N-obPath (Q.F-id-isIso p .sec) (e .snd)))
  ×Ps .F-id-isIso {x} p .ret = makeNatTransPath (funExt λ e →
    ≡-× (N-obPath (P.F-id-isIso p .ret) (e .fst))
        (N-obPath (Q.F-id-isIso p .ret) (e .snd)))
  ×Ps .F-seq-isIso (k , l) .inv = ν⁻ k l
  ×Ps .F-seq-isIso (k , l) .sec = makeNatTransPath (funExt λ e →
    ≡-× (N-obPath (P.F-seq-isIso (k , l) .sec) (e .fst))
        (N-obPath (Q.F-seq-isIso (k , l) .sec) (e .snd)))
  ×Ps .F-seq-isIso (k , l) .ret = makeNatTransPath (funExt λ e →
    ≡-× (N-obPath (P.F-seq-isIso (k , l) .ret) (e .fst))
        (N-obPath (Q.F-seq-isIso (k , l) .ret) (e .snd)))

infixr 6 _×Pre_

_×Pre_ : {B : Bicategory ℓ ℓ' ℓ''}
  → Prestack B ℓp ℓp' → Prestack B ℓp ℓp' → Prestack B ℓp ℓp'
P ×Pre Q = ×Ps P Q

module _ {B : Bicategory ℓ ℓ' ℓ''} (P Q : Prestack B ℓp ℓp') where
  private
    module B = Bicategory B
    module P = PrestackNotation P
    module Q = PrestackNotation Q
    module PQ = PrestackNotation (P ×Pre Q)

  pFst : {x : B.0Cell} → PQ.p[ x ] → P.p[ x ]
  pFst = fst

  pSnd : {x : B.0Cell} → PQ.p[ x ] → Q.p[ x ]
  pSnd = snd

  pPair : {x : B.0Cell} → P.p[ x ] → Q.p[ x ] → PQ.p[ x ]
  pPair e e' = e , e'

  test-p[] : {x : B.0Cell} → PQ.p[ x ] ≡ (P.p[ x ] ×Σ Q.p[ x ])
  test-p[] = refl

  test-⋆ᴾ : {x y : B.0Cell} (k : B.1Cell x y) (e : P.p[ y ]) (e' : Q.p[ y ])
    → PQ._⋆ᴾ_ k (e , e') ≡ (P._⋆ᴾ_ k e , Q._⋆ᴾ_ k e')
  test-⋆ᴾ k e e' = refl
