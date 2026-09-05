{-# OPTIONS --lossy-unification #-}
{- Modifications form the hom-categories of the bicategory of lax
   functors: paths, sethood, invertibility and the category. -}
module Cubical.Categories.Bicategory.Transformation.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Isomorphism.More

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Transformation

private
  variable
    ℓb ℓb' ℓb'' ℓc ℓc' ℓc'' : Level

open Functor
open LaxFunctor
open LaxNatTrans
open Modification
open Category
open isIso

module _ {B : Bicategory ℓb ℓb' ℓb''} {C : Bicategory ℓc ℓc' ℓc''}
  {F G : LaxFunctor B C} where
  private
    module B = Bicategory B
    module C = Bicategory C
    module F = LaxFunctor F
    module G = LaxFunctor G

  -- Pseudonaturality: the naturality cell is invertible.  This is what
  -- makes componentwise equivalence imply invertibility.
  isPseudoNatTrans : LaxNatTrans F G → Type (ℓ-max ℓb (ℓ-max ℓb' ℓc''))
  isPseudoNatTrans α = {x y : B.ob} (f : B.1Cell x y)
    → Cubical.Categories.Category.isIso
        C.Hom[ F.F-ob x , G.F-ob y ] (α .N-hom f)

  makeModificationPath : {α β : LaxNatTrans F G} {Γ Δ : Modification α β}
    → ((x : B.0Cell) → Γ .M-ob x ≡ Δ .M-ob x)
    → Γ ≡ Δ
  makeModificationPath {α} {β} {Γ} {Δ} p i .M-ob x = p x i
  makeModificationPath {α} {β} {Γ} {Δ} p i .M-hom {x} {y} f =
    isProp→PathP
      (λ i → C.Hom[ F.F-ob x , G.F-ob y ] .isSetHom
               (α .N-hom f C.⋆₂ (p x i C.▷w G.F-1cell f))
               ((F.F-1cell f C.◁w p y i) C.⋆₂ β .N-hom f))
      (Γ .M-hom f) (Δ .M-hom f) i

  private
    ModΣ : (α β : LaxNatTrans F G) → Type _
    ModΣ α β =
      Σ[ o ∈ ((x : B.0Cell) → C.2Cell (α .N-1cell x) (β .N-1cell x)) ]
        ({x y : B.0Cell} (f : B.1Cell x y)
          →   α .N-hom f C.⋆₂ (o x C.▷w G.F-1cell f)
            ≡ (F.F-1cell f C.◁w o y) C.⋆₂ β .N-hom f)

    ModIso : (α β : LaxNatTrans F G) → Iso (Modification α β) (ModΣ α β)
    ModIso α β .Iso.fun Γ = Γ .M-ob , Γ .M-hom
    ModIso α β .Iso.inv q .M-ob = q .fst
    ModIso α β .Iso.inv q .M-hom = q .snd
    ModIso α β .Iso.sec _ = refl
    ModIso α β .Iso.ret Γ i .M-ob = Γ .M-ob
    ModIso α β .Iso.ret Γ i .M-hom = Γ .M-hom

  isSetModification : {α β : LaxNatTrans F G} → isSet (Modification α β)
  isSetModification {α} {β} =
    isOfHLevelRetractFromIso 2 (ModIso α β)
      (isSetΣ (isSetΠ λ x → C.Hom[ _ , _ ] .isSetHom)
        (λ o → isProp→isSet (isPropImplicitΠ2 λ x y → isPropΠ λ f →
          C.Hom[ _ , _ ] .isSetHom _ _)))

  idMod : (α : LaxNatTrans F G) → Modification α α
  idMod α .M-ob x = C.id₂
  idMod α .M-hom {x} {y} f =
      C.⟨⟩⋆₂⟨ C.▷wId (G.F-1cell f) ⟩
    ∙ C.⋆₂IdR _
    ∙ sym (C.⋆₂IdL _)
    ∙ C.⟨ sym (C.◁wId (F.F-1cell f)) ⟩⋆₂⟨⟩

  seqMod : {α β γ : LaxNatTrans F G}
    → Modification α β → Modification β γ → Modification α γ
  seqMod Γ Δ .M-ob x = Γ .M-ob x C.⋆₂ Δ .M-ob x
  seqMod {α} {β} {γ} Γ Δ .M-hom {x} {y} f =
      C.⟨⟩⋆₂⟨ ▷wSeq C (Γ .M-ob x) (Δ .M-ob x) (G.F-1cell f) ⟩
    ∙ sym (C.⋆₂Assoc _ _ _)
    ∙ C.⟨ Γ .M-hom f ⟩⋆₂⟨⟩
    ∙ C.⋆₂Assoc _ _ _
    ∙ C.⟨⟩⋆₂⟨ Δ .M-hom f ⟩
    ∙ sym (C.⋆₂Assoc _ _ _)
    ∙ C.⟨ sym (◁wSeq C (F.F-1cell f) (Γ .M-ob y) (Δ .M-ob y)) ⟩⋆₂⟨⟩

  -- A componentwise-invertible modification is invertible: conjugate
  -- the cylinder by the whiskered inverses.
  invMod : {α β : LaxNatTrans F G} (Γ : Modification α β)
    → ((x : B.0Cell) → isIso C.Hom[ F.F-ob x , G.F-ob x ] (Γ .M-ob x))
    → Modification β α
  invMod Γ isI .M-ob x = isI x .inv
  invMod {α} {β} Γ isI .M-hom {x} {y} f =
    ⋆InvsFlipSq {C = C.Hom[ F.F-ob x , G.F-ob y ]}
      (F.F-1cell f C.◁w Γ .M-ob y , ◁wIsIso C (F.F-1cell f) (isI y))
      (Γ .M-ob x C.▷w G.F-1cell f , ▷wIsIso C (G.F-1cell f) (isI x))
      (sym (Γ .M-hom f))

  LaxNatTransCat : Category
    (ℓ-max (ℓ-max ℓb (ℓ-max ℓb' ℓb'')) (ℓ-max ℓc (ℓ-max ℓc' ℓc'')))
    (ℓ-max (ℓ-max ℓb (ℓ-max ℓb' ℓb'')) (ℓ-max ℓc (ℓ-max ℓc' ℓc'')))
  LaxNatTransCat .ob = LaxNatTrans F G
  LaxNatTransCat .Hom[_,_] = Modification
  LaxNatTransCat .id = idMod _
  LaxNatTransCat ._⋆_ = seqMod
  LaxNatTransCat .⋆IdL Γ = makeModificationPath λ x → C.⋆₂IdL _
  LaxNatTransCat .⋆IdR Γ = makeModificationPath λ x → C.⋆₂IdR _
  LaxNatTransCat .⋆Assoc Γ Δ Θ = makeModificationPath λ x → C.⋆₂Assoc _ _ _
  LaxNatTransCat .isSetHom = isSetModification

  -- A componentwise invertible modification is an iso in
  -- `LaxNatTransCat`.
  modIsIso : {α β : LaxNatTrans F G} (Γ : Modification α β)
    → ((x : B.0Cell) → isIso C.Hom[ F.F-ob x , G.F-ob x ] (Γ .M-ob x))
    → isIso LaxNatTransCat Γ
  modIsIso Γ isI .inv = invMod Γ isI
  modIsIso Γ isI .sec = makeModificationPath λ x → isI x .sec
  modIsIso Γ isI .ret = makeModificationPath λ x → isI x .ret
