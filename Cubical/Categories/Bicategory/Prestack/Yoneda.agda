{-# OPTIONS --lossy-unification #-}
{- Bicategorical Yoneda recursion into a prestack. -}
module Cubical.Categories.Bicategory.Prestack.Yoneda where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.BinProduct

open import Cubical.Categories.Equivalence.Base

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Constructions.Op
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.Transformation.Properties
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Hom
open import Cubical.Categories.Bicategory.Prestack.Morphism

private
  variable
    ℓ ℓ' ℓ'' : Level

open Functor
open NatTrans
open NatIso
open isIso
open LaxFunctor
open Pseudofunctor
open LaxNatTrans
open Modification

module _ {B : Bicategory ℓ ℓ' ℓ''} (P : Prestack B ℓ' ℓ'') where
  private
    module B = Bicategory B
  open PrestackNotation P

  module _ {a : B.0Cell} (e : p[ a ]) where

    private
      module Ha = Pseudofunctor (Hom B a)

      -- Naturality of P's F-seq, read off at the element e.
      fsq : {x y : B.0Cell} {h h' : B.1Cell x a} {k k' : B.1Cell y x}
        (α : B.2Cell h h') (τ : B.2Cell k k')
        →  (reind k .F-hom (⟨ e ⟩ x .F-hom α)
              ⋆⟨ P⟨ y ⟩ ⟩ ⟨ h' ⋆ᴾ e ⟩ y .F-hom τ)
             ⋆⟨ P⟨ y ⟩ ⟩ ⋆ᴾAssoc k' h' e .fst
        ≡ ⋆ᴾAssoc k h e .fst
             ⋆⟨ P⟨ y ⟩ ⟩ ⟨ e ⟩ y .F-hom (τ B.⋆ₕ α)
      fsq {x} {y} α τ =
        N-obPath (P.F-seq {a} {x} {y} .N-hom (α , τ)) e

      fsqL : {x y : B.0Cell} {h h' : B.1Cell x a} (k : B.1Cell y x)
        (α : B.2Cell h h')
        → reind k .F-hom (⟨ e ⟩ x .F-hom α) ⋆⟨ P⟨ y ⟩ ⟩ ⋆ᴾAssoc k h' e .fst
        ≡ ⋆ᴾAssoc k h e .fst ⋆⟨ P⟨ y ⟩ ⟩ ⟨ e ⟩ y .F-hom (k B.◁w α)
      fsqL {x} {y} {h' = h'} k α =
          Pᶜ.⟨ sym (Pᶜ.⋆IdR _)
               ∙ Pᶜ.⟨⟩⋆⟨ sym (⟨ h' ⋆ᴾ e ⟩ y .F-id) ⟩ ⟩⋆⟨⟩
        ∙ fsq α B.id₂

      fsqR : {x y : B.0Cell} (h : B.1Cell x a) {k k' : B.1Cell y x}
        (τ : B.2Cell k k')
        → ⟨ h ⋆ᴾ e ⟩ y .F-hom τ ⋆⟨ P⟨ y ⟩ ⟩ ⋆ᴾAssoc k' h e .fst
        ≡ ⋆ᴾAssoc k h e .fst ⋆⟨ P⟨ y ⟩ ⟩ ⟨ e ⟩ y .F-hom (τ B.▷w h)
      fsqR {x} {y} h {k} {k'} τ =
          Pᶜ.⟨ sym (Pᶜ.⋆IdL _)
               ∙ Pᶜ.⟨ sym (cong (reind k .F-hom) (⟨ e ⟩ x .F-id)
                           ∙ reind k .F-id) ⟩⋆⟨⟩ ⟩⋆⟨⟩
        ∙ fsq B.id₂ τ

      -- P's lax-ρ, read off at e: this is what makes lax-id hold.
      key : {x : B.0Cell} (h : B.1Cell x a)
        → P.F⁰ .N-ob (h ⋆ᴾ e) ⋆⟨ P⟨ x ⟩ ⟩ ⋆ᴾAssoc B.id₁ h e .fst
        ≡ ⟨ e ⟩ x .F-hom (B.λ⁻ h)
      key {x} h =
          ⋆InvRMove (_ , F-PresIsIso {F = ⟨ e ⟩ x} (B.λU x a .nIso (tt* , h)))
            ( Pᶜ.⋆Assoc _ _ _
            ∙ Pᶜ.⟨ sym (Pᶜ.⋆IdL _) ⟩⋆⟨⟩
            ∙ N-obPath (P.lax-ρ a x h) e)
        ∙ Pᶜ.⋆IdL _

      -- P's lax-α, read off at e, with the identities cleared.
      cln : {x y z : B.0Cell} (k : B.1Cell y x) (l : B.1Cell z y)
        (h : B.1Cell x a)
        → reind l .F-hom (⋆ᴾAssoc k h e .fst)
            ⋆⟨ P⟨ z ⟩ ⟩ ( ⋆ᴾAssoc l (k B.⋆₁ h) e .fst
                          ⋆⟨ P⟨ z ⟩ ⟩ ⟨ e ⟩ z .F-hom (B.α⁻ l k h))
        ≡ P.F² k l .N-ob (h ⋆ᴾ e)
            ⋆⟨ P⟨ z ⟩ ⟩ ⋆ᴾAssoc (l B.⋆₁ k) h e .fst
      cln {x} {y} {z} k l h =
          Pᶜ.⟨ sym (Pᶜ.⋆IdR _) ⟩⋆⟨⟩
        ∙ N-obPath (P.lax-α a x y z h k l) e
        ∙ Pᶜ.⋆IdL _
        ∙ Pᶜ.⟨ Pᶜ.⟨ (reind l ∘F reind k) .F-id ⟩⋆⟨⟩
               ∙ Pᶜ.⋆IdL _ ⟩⋆⟨⟩

      sq3 : {x y z : B.0Cell} (k : B.1Cell y x) (l : B.1Cell z y)
        (h : B.1Cell x a)
        → ⟨ e ⟩ z .F-hom (B.α⁻ l k h)
            ⋆⟨ P⟨ z ⟩ ⟩ ⋆ᴾAssoc (l B.⋆₁ k) h e .snd .inv
        ≡ ⋆ᴾAssoc l (k B.⋆₁ h) e .snd .inv
            ⋆⟨ P⟨ z ⟩ ⟩ ( reind l .F-hom (⋆ᴾAssoc k h e .snd .inv)
                          ⋆⟨ P⟨ z ⟩ ⟩ P.F² k l .N-ob (h ⋆ᴾ e))
      sq3 {x} {y} {z} k l h =
        sym (⋆InvRMove (⋆ᴾAssoc (l B.⋆₁ k) h e)
          ( Pᶜ.⋆Assoc _ _ _
          ∙ Pᶜ.⟨⟩⋆⟨ Pᶜ.⋆Assoc _ _ _
                 ∙ Pᶜ.⟨⟩⋆⟨ sym (cln k l h) ⟩
                 ∙ sym (Pᶜ.⋆Assoc _ _ _)
                 ∙ Pᶜ.⟨ F-Iso {F = reind l} (⋆ᴾAssoc k h e) .snd .sec ⟩⋆⟨⟩
                 ∙ Pᶜ.⋆IdL _ ⟩
          ∙ sym (Pᶜ.⋆Assoc _ _ _)
          ∙ Pᶜ.⟨ ⋆ᴾAssoc l (k B.⋆₁ h) e .snd .sec ⟩⋆⟨⟩
          ∙ Pᶜ.⋆IdL _))

      rhsRed : {x y z : B.0Cell} (k : B.1Cell y x) (l : B.1Cell z y)
        (h : B.1Cell x a)
        →   Pᶜ.id
            ⋆⟨ P⟨ z ⟩ ⟩
            ( ( (⟨ e ⟩ z ∘F Ha.F-1cell {y} {z} l)
                  .F-hom (B.id₂)
                ⋆⟨ P⟨ z ⟩ ⟩ ⋆ᴾAssoc l (k B.⋆₁ h) e .snd .inv)
              ⋆⟨ P⟨ z ⟩ ⟩
              ( Pᶜ.id
                ⋆⟨ P⟨ z ⟩ ⟩
                ( (reind l .F-hom (⋆ᴾAssoc k h e .snd .inv)
                    ⋆⟨ P⟨ z ⟩ ⟩ Pᶜ.id)
                  ⋆⟨ P⟨ z ⟩ ⟩
                  ( Pᶜ.id
                    ⋆⟨ P⟨ z ⟩ ⟩
                    ( (reind l ∘F reind k) .F-hom (Pᶜ.id)
                      ⋆⟨ P⟨ z ⟩ ⟩ P.F² k l .N-ob (h ⋆ᴾ e))))))
        ≡ ⋆ᴾAssoc l (k B.⋆₁ h) e .snd .inv
            ⋆⟨ P⟨ z ⟩ ⟩ ( reind l .F-hom (⋆ᴾAssoc k h e .snd .inv)
                          ⋆⟨ P⟨ z ⟩ ⟩ P.F² k l .N-ob (h ⋆ᴾ e))
      rhsRed {x} {y} {z} k l h =
          cong₂ (λ p q → Pᶜ.id
                   ⋆⟨ P⟨ z ⟩ ⟩
                   ( (p ⋆⟨ P⟨ z ⟩ ⟩ ⋆ᴾAssoc l (k B.⋆₁ h) e .snd .inv)
                     ⋆⟨ P⟨ z ⟩ ⟩
                     ( Pᶜ.id
                       ⋆⟨ P⟨ z ⟩ ⟩
                       ( (reind l .F-hom (⋆ᴾAssoc k h e .snd .inv)
                           ⋆⟨ P⟨ z ⟩ ⟩ Pᶜ.id)
                         ⋆⟨ P⟨ z ⟩ ⟩
                         ( Pᶜ.id
                           ⋆⟨ P⟨ z ⟩ ⟩
                           (q ⋆⟨ P⟨ z ⟩ ⟩ P.F² k l .N-ob (h ⋆ᴾ e)))))))
                ((⟨ e ⟩ z ∘F Ha.F-1cell {y} {z} l) .F-id)
                ((reind l ∘F reind k) .F-id)
        ∙ Pᶜ.⋆IdL _
        ∙ Pᶜ.⟨ Pᶜ.⋆IdL _ ⟩⋆⟨⟩
        ∙ Pᶜ.⟨⟩⋆⟨ Pᶜ.⋆IdL _
               ∙ Pᶜ.⟨ Pᶜ.⋆IdR _ ⟩⋆⟨⟩
               ∙ Pᶜ.⟨⟩⋆⟨ Pᶜ.⋆IdL _
                      ∙ Pᶜ.⋆IdL _ ⟩ ⟩

      ζ : {x y : B.0Cell} (k : B.1Cell y x)
        → NatTrans (⟨ e ⟩ y ∘F Ha.F-1cell {x} {y} k)
                   (reind k ∘F ⟨ e ⟩ x)
      ζ k .N-ob h = ⋆ᴾAssoc k h e .snd .inv
      ζ {x} {y} k .N-hom {h} {h'} α =
        ⋆InvsFlipSq {C = P⟨ y ⟩} (⋆ᴾAssoc k h e) (⋆ᴾAssoc k h' e)
          (sym (fsqL k α))

    yoRecᴮ : PrestackHom (Hom B a) P
    yoRecᴮ .N-1cell x = ⟨ e ⟩ x
    yoRecᴮ .N-hom k = ζ k
    yoRecᴮ .N-natural {x} {y} {k} {k'} τ = makeNatTransPath (funExt λ h →
        Pᶜ.⟨ Pᶜ.⋆IdR _ ⟩⋆⟨⟩
      ∙ ⋆InvsFlipSq {C = P⟨ y ⟩} (⋆ᴾAssoc k h e) (⋆ᴾAssoc k' h e)
            (sym (fsqR h τ))
      ∙ Pᶜ.⟨⟩⋆⟨ sym ( Pᶜ.⟨ reind k .F-id ⟩⋆⟨⟩
                  ∙ Pᶜ.⋆IdL _) ⟩)
    yoRecᴮ .lax-id x = makeNatTransPath (funExt λ h →
        Pᶜ.⟨ Pᶜ.⋆IdR _ ⟩⋆⟨⟩
      ∙ sym (⋆InvRMove (⋆ᴾAssoc B.id₁ h e) (key h))
      ∙ sym ( Pᶜ.⋆IdL _
            ∙ Pᶜ.⋆IdL _
            ∙ Pᶜ.⋆IdL _))
    yoRecᴮ .lax-seq {x} {y} {z} k l = makeNatTransPath (funExt λ h →
        Pᶜ.⟨ Pᶜ.⋆IdR _ ⟩⋆⟨⟩
      ∙ sq3 k l h
      ∙ sym (rhsRed k l h))

    yoRecᴮ-pseudo : isPseudoNat (Hom B a) P yoRecᴮ
    yoRecᴮ-pseudo {x} {y} k = FUNCTORIso B.Hom[ x , a ] P⟨ y ⟩ (ζ k)
      (λ h → invIso (⋆ᴾAssoc k h e) .snd)

    yoRecᴮᵖ : PrestackPseudoHom (Hom B a) P
    yoRecᴮᵖ = yoRecᴮ , yoRecᴮ-pseudo

    yoRecβᴮ : CatIso P⟨ a ⟩ (⟨ e ⟩ a .F-ob B.id₁) e
    yoRecβᴮ = ⋆ᴾIdL e

  module _ {a : B.0Cell} (β : PrestackPseudoHom (Hom B a) P) where
    yoRecηᴮ-vertex : p[ a ]
    yoRecηᴮ-vertex = β .fst .N-1cell a .F-ob B.id₁

    yoRecηᴮ-elt : {x : B.0Cell} (h : B.1Cell x a)
      → CatIso P⟨ x ⟩ (β .fst .N-1cell x .F-ob h)
                      (yoRecᴮ yoRecηᴮ-vertex .N-1cell x .F-ob h)
    yoRecηᴮ-elt {x} h =
      ⋆Iso (F-Iso {F = β .fst .N-1cell x}
             (invIso (B.ρ⁺ h , B.ρU x a .nIso (h , tt*))))
           ( _
           , FUNCTORIso' B.Hom[ a , a ] P⟨ x ⟩
               (β .fst .N-hom h) (β .snd h) B.id₁)

    yoRecηᴮ-trans : (x : B.0Cell)
      → NatTrans (β .fst .N-1cell x) (yoRecᴮ yoRecηᴮ-vertex .N-1cell x)
    yoRecηᴮ-trans x .N-ob h = yoRecηᴮ-elt h .fst
    yoRecηᴮ-trans x .N-hom {h} {h'} α =
        sym (Pᶜ.⋆Assoc _ _ _)
      ∙ Pᶜ.⟨ sym (β .fst .N-1cell x .F-seq α (B.ρ⁻ h'))
             ∙ cong (β .fst .N-1cell x .F-hom) (ρ⁻-nat B α)
             ∙ β .fst .N-1cell x .F-seq (B.ρ⁻ h) (α B.▷w B.id₁) ⟩⋆⟨⟩
      ∙ Pᶜ.⋆Assoc _ _ _
      ∙ Pᶜ.⟨⟩⋆⟨ Pᶜ.⟨ sym (Pᶜ.⋆IdR _) ⟩⋆⟨⟩
             ∙ N-obPath (β .fst .N-natural α) B.id₁
             ∙ Pᶜ.⟨⟩⋆⟨ Pᶜ.⟨ reind h .F-id ⟩⋆⟨⟩
                    ∙ Pᶜ.⋆IdL _ ⟩ ⟩
      ∙ sym (Pᶜ.⋆Assoc _ _ _)

    yoRecηᴮ : (x : B.0Cell)
      → NatIso (β .fst .N-1cell x) (yoRecᴮ yoRecηᴮ-vertex .N-1cell x)
    yoRecηᴮ x .trans = yoRecηᴮ-trans x
    yoRecηᴮ x .nIso h = yoRecηᴮ-elt h .snd

module _ {B : Bicategory ℓ ℓ' ℓ''} {P Q : Prestack B ℓ' ℓ''}
  (β : PrestackHom P Q) where
  private
    module B = Bicategory B
    module PN = PrestackNotation P
    module QN = PrestackNotation Q

  yoRec-naturalᴮ-elt : {a x : B.0Cell} (e : PN.p[ a ]) (h : B.1Cell x a)
    → QN.P⟨ x ⟩ [ β .N-1cell x .F-ob (yoRecᴮ P e .N-1cell x .F-ob h)
                , yoRecᴮ Q (β .N-1cell a .F-ob e) .N-1cell x .F-ob h ]
  yoRec-naturalᴮ-elt e h = β .N-hom h .N-ob e

  yoRec-naturalᴮ : isPseudoNat P Q β → {a x : B.0Cell}
    (e : PN.p[ a ]) (h : B.1Cell x a)
    → CatIso QN.P⟨ x ⟩ (β .N-1cell x .F-ob (yoRecᴮ P e .N-1cell x .F-ob h))
                       (yoRecᴮ Q (β .N-1cell a .F-ob e) .N-1cell x .F-ob h)
  yoRec-naturalᴮ pf {a} {x} e h =
    _ , FUNCTORIso' PN.P⟨ a ⟩ QN.P⟨ x ⟩ (β .N-hom h) (pf h) e

module _ {B : Bicategory ℓ ℓ' ℓ''} (P : Prestack B ℓ' ℓ'') where
  private
    module B = Bicategory B
  open PrestackNotation P

  module _ (a : B.0Cell) where
    evalId₁ : Functor (PrestackHomCat (Hom B a) P) P⟨ a ⟩
    evalId₁ .F-ob β = β .fst .N-1cell a .F-ob B.id₁
    evalId₁ .F-hom Γ = Γ .M-ob a .N-ob B.id₁
    evalId₁ .F-id = refl
    evalId₁ .F-seq _ _ = refl

    private
      yoMor : {e e' : p[ a ]} (m : P⟨ a ⟩ [ e , e' ]) (x : B.0Cell)
        → NatTrans (⟨ e ⟩ x) (⟨ e' ⟩ x)
      yoMor m x .N-ob h = reind h .F-hom m
      yoMor m x .N-hom α = sym (P.F-Hom .F-hom α .N-hom m)

      yoRecMod : {e e' : p[ a ]} (m : P⟨ a ⟩ [ e , e' ])
        → Modification (yoRecᴮ P e) (yoRecᴮ P e')
      yoRecMod m .M-ob x = yoMor m x
      yoRecMod {e} {e'} m .M-hom {x} {y} k = makeNatTransPath (funExt λ h →
          Pᶜ.⟨⟩⋆⟨ Pᶜ.⋆IdR _ ⟩
        ∙ sym (⋆InvsFlipSq {C = P⟨ y ⟩} (⋆ᴾAssoc k h e) (⋆ᴾAssoc k h e')
                 (sym (P.F² h k .N-hom m)))
        ∙ Pᶜ.⟨ sym (Pᶜ.⋆IdL _)
               ∙ Pᶜ.⟨ sym (⟨ e ⟩ y .F-id) ⟩⋆⟨⟩ ⟩⋆⟨⟩)

    yoRecFunc : Functor P⟨ a ⟩ (PrestackHomCat (Hom B a) P)
    yoRecFunc .F-ob e = yoRecᴮᵖ P e
    yoRecFunc .F-hom m = yoRecMod m
    yoRecFunc .F-id = makeModificationPath λ x →
      makeNatTransPath (funExt λ h → reind h .F-id)
    yoRecFunc .F-seq m n = makeModificationPath λ x →
      makeNatTransPath (funExt λ h → reind h .F-seq m n)


    private
      module Ha = Pseudofunctor (Hom B a)

      -- The mate of `ρ⋆₁`: ρ⁻ splits along the associator.
      MH : {β γ : PrestackPseudoHom (Hom B a) P}
        (Γ : Modification (β .fst) (γ .fst))
        {x : B.0Cell} (h : B.1Cell x a)
        →   β .fst .N-hom h .N-ob B.id₁
              ⋆⟨ P⟨ x ⟩ ⟩ reind h .F-hom (Γ .M-ob a .N-ob B.id₁)
          ≡   Γ .M-ob x .N-ob (h B.⋆₁ B.id₁)
              ⋆⟨ P⟨ x ⟩ ⟩ γ .fst .N-hom h .N-ob B.id₁
      MH {β} Γ {x} h =
          Pᶜ.⟨⟩⋆⟨ sym (Pᶜ.⋆IdR _) ⟩
        ∙ N-obPath (Γ .M-hom h) B.id₁
        ∙ Pᶜ.⟨ Pᶜ.⟨ β .fst .N-1cell x .F-id ⟩⋆⟨⟩ ∙ Pᶜ.⋆IdL _ ⟩⋆⟨⟩

      idIso : (e : p[ a ]) → CatIso P⟨ a ⟩ e (B.id₁ ⋆ᴾ e)
      idIso e = invIso (⋆ᴾIdL e)

    module _ (β : PrestackPseudoHom (Hom B a) P) where
      private
        vtx : p[ a ]
        vtx = yoRecηᴮ-vertex P β

        Θ : (x : B.0Cell)
          → NatTrans (β .fst .N-1cell x) (yoRecᴮ P vtx .N-1cell x)
        Θ = yoRecηᴮ-trans P β

        -- β's lax-seq, read off at id₁ with the CAT identities cleared.
        LS : {x y : B.0Cell} (h : B.1Cell x a) (k : B.1Cell y x)
          →   β .fst .N-1cell y .F-hom (B.α⁻ k h B.id₁)
                ⋆⟨ P⟨ y ⟩ ⟩ β .fst .N-hom (k B.⋆₁ h) .N-ob B.id₁
            ≡   β .fst .N-hom k .N-ob (h B.⋆₁ B.id₁)
                ⋆⟨ P⟨ y ⟩ ⟩ ( reind k .F-hom (β .fst .N-hom h .N-ob B.id₁)
                              ⋆⟨ P⟨ y ⟩ ⟩ ⋆ᴾAssoc k h vtx .fst)
        LS {x} {y} h k =
            Pᶜ.⟨ sym (Pᶜ.⋆IdR _) ⟩⋆⟨⟩
          ∙ N-obPath (β .fst .lax-seq h k) B.id₁
          ∙ sym
            ( Pᶜ.⟨ sym (Pᶜ.⋆IdL _)
                 ∙ Pᶜ.⟨ sym ((β .fst .N-1cell y ∘F Ha.F-1cell {x} {y} k)
                               .F-id) ⟩⋆⟨⟩ ⟩⋆⟨⟩
            ∙ Pᶜ.⟨⟩⋆⟨ Pᶜ.⟨⟩⋆⟨ sym (Pᶜ.⋆IdL _)
                            ∙ Pᶜ.⟨ sym ((reind k ∘F reind h) .F-id) ⟩⋆⟨⟩ ⟩
                    ∙ Pᶜ.⟨ sym (Pᶜ.⋆IdR _) ⟩⋆⟨⟩ ⟩
            ∙ Pᶜ.⟨⟩⋆⟨ Pᶜ.⟨⟩⋆⟨ sym (Pᶜ.⋆IdL _) ⟩ ∙ sym (Pᶜ.⋆IdL _) ⟩
            ∙ sym (Pᶜ.⋆IdL _))

        -- The cylinder coherence for yoRecηᴮ, componentwise.
        star : {x y : B.0Cell} (h : B.1Cell x a) (k : B.1Cell y x)
          →   Θ y .N-ob (k B.⋆₁ h)
                ⋆⟨ P⟨ y ⟩ ⟩ ⋆ᴾAssoc k h vtx .snd .inv
            ≡   β .fst .N-hom k .N-ob h
                ⋆⟨ P⟨ y ⟩ ⟩ reind k .F-hom (Θ x .N-ob h)
        star {x} {y} h k =
            Pᶜ.⟨ Pᶜ.⟨ cong (β .fst .N-1cell y .F-hom) (ρ⁻⋆₁ B k h)
                    ∙ β .fst .N-1cell y .F-seq _ _ ⟩⋆⟨⟩ ⟩⋆⟨⟩
          ∙ Pᶜ.⟨ Pᶜ.⋆Assoc _ _ _ ⟩⋆⟨⟩
          ∙ Pᶜ.⟨ Pᶜ.⟨⟩⋆⟨ LS h k ⟩ ⟩⋆⟨⟩
          ∙ Pᶜ.⟨ sym (Pᶜ.⋆Assoc _ _ _) ⟩⋆⟨⟩
          ∙ Pᶜ.⟨ Pᶜ.⟨ β .fst .N-hom k .N-hom (B.ρ⁻ h) ⟩⋆⟨⟩ ⟩⋆⟨⟩
          ∙ Pᶜ.⟨ Pᶜ.⋆Assoc _ _ _ ⟩⋆⟨⟩
          ∙ Pᶜ.⋆Assoc _ _ _
          ∙ Pᶜ.⟨⟩⋆⟨ Pᶜ.⋆Assoc _ _ _
                  ∙ Pᶜ.⟨⟩⋆⟨ Pᶜ.⋆Assoc _ _ _
                          ∙ Pᶜ.⟨⟩⋆⟨ ⋆ᴾAssoc k h vtx .snd .ret ⟩
                          ∙ Pᶜ.⋆IdR _ ⟩
                  ∙ sym (reind k .F-seq _ _) ⟩

      ηMod : Modification (β .fst) (yoRecᴮ P (yoRecηᴮ-vertex P β))
      ηMod .M-ob x = Θ x
      ηMod .M-hom {x} {y} k = makeNatTransPath (funExt λ h →
          Pᶜ.⟨⟩⋆⟨ Pᶜ.⋆IdR _ ⟩
        ∙ sym (star h k)
        ∙ Pᶜ.⟨ sym (Pᶜ.⋆IdL _)
             ∙ Pᶜ.⟨ sym (β .fst .N-1cell y .F-id) ⟩⋆⟨⟩ ⟩⋆⟨⟩)

    private
      ηIsIso : (β : PrestackPseudoHom (Hom B a) P) (x : B.0Cell)
        → isIso (FUNCTOR B.Hom[ x , a ] P⟨ x ⟩) (ηMod β .M-ob x)
      ηIsIso β x = FUNCTORIso B.Hom[ x , a ] P⟨ x ⟩ (yoRecηᴮ-trans P β x)
        (λ h → yoRecηᴮ-elt P β h .snd)

    ηᴮ : NatIso 𝟙⟨ PrestackHomCat (Hom B a) P ⟩ (yoRecFunc ∘F evalId₁)
    ηᴮ .trans .N-ob β = ηMod β
    ηᴮ .trans .N-hom {β} {γ} Γ = makeModificationPath λ x →
      makeNatTransPath (funExt λ h →
          sym (Pᶜ.⋆Assoc _ _ _)
        ∙ Pᶜ.⟨ sym (Γ .M-ob x .N-hom (B.ρ⁻ h)) ⟩⋆⟨⟩
        ∙ Pᶜ.⋆Assoc _ _ _
        ∙ Pᶜ.⟨⟩⋆⟨ sym (MH {β} {γ} Γ h) ⟩
        ∙ sym (Pᶜ.⋆Assoc _ _ _))
    ηᴮ .nIso β .inv = invMod (ηMod β) (ηIsIso β)
    ηᴮ .nIso β .sec = makeModificationPath λ x → ηIsIso β x .sec
    ηᴮ .nIso β .ret = makeModificationPath λ x → ηIsIso β x .ret

    εᴮ : NatIso (evalId₁ ∘F yoRecFunc) 𝟙⟨ P⟨ a ⟩ ⟩
    εᴮ .trans .N-ob e = ⋆ᴾIdL e .fst
    εᴮ .trans .N-hom {e} {e'} m =
      ⋆InvsFlipSq {C = P⟨ a ⟩} (idIso e) (idIso e') (sym (P.F⁰ .N-hom m))
    εᴮ .nIso e = ⋆ᴾIdL e .snd

    -- The prestack Yoneda lemma: evaluation at id₁ is an equivalence
    -- between the prestack morphisms out of B [-, a ] and P a.
    yonedaᴮ : WeakInverse evalId₁
    yonedaᴮ .WeakInverse.invFunc = yoRecFunc
    yonedaᴮ .WeakInverse.η = ηᴮ
    yonedaᴮ .WeakInverse.ε = εᴮ
