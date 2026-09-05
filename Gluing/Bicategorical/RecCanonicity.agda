{-# OPTIONS --lossy-unification #-}
{-
  Canonicity attempted through the RECURSOR of the free cartesian
  closed category applied to the comma category itself.

  `GLUE` is the Artin glue of `Gluing.Bicategorical.BoolNatCanonicity`
  -- a plain `CartesianClosedCategory` whose underlying category is
  `ArtinGlue Pts`, which `Gluing.Bicategorical.Artin` proves equal to
  the `CAT` comma object `Commaᴮ` on the nose.  So `rec` into it uses
  the bicategorical limit directly: no displayed category, no
  `Section`, no `SETᴰ`, no `reindex` anywhere below.
-}
module Gluing.Bicategorical.RecCanonicity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Data.Bool
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Nat
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd; ΣPathP)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base

open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Forded
  as FreeCCC

open import Gluing.Bicategorical.BoolNatCanonicity
import Gluing.Canonicity as GC

open Category
open Functor
open NatIso
open NatTrans
open CartesianClosedCategory

module GLUE = CartesianClosedCategory GLUE

fromBool : Bool → [bool]
fromBool b = if b then [t] else [f]

-- the interpretation lands in the comma category: a set, a syntactic
-- object, and the map picking out the canonical forms
S : Functor FREECCC.C GLUE.C
S = rec ×⇒QUIVER GLUE (mkElimInterpᴰ
  (λ { bool → ((Bool , isSetBool) , ↑ bool) , fromBool
     ; nat → ((ℕ , isSetℕ) , ↑ nat) , ＂_＂ })
  (λ { tr → ((λ _ → true) , [t])
             , funExt (λ u → cong₂ _⋆ₑ_ (GC.⊤→⊤IsId FREECCC.term u) refl
                           ∙ FREECCC.⋆IdL _)
     ; fl → ((λ _ → false) , [f])
             , funExt (λ u → cong₂ _⋆ₑ_ (GC.⊤→⊤IsId FREECCC.term u) refl
                           ∙ FREECCC.⋆IdL _)
     ; ze → ((λ _ → 0) , [ze])
             , funExt (λ u → cong₂ _⋆ₑ_ (GC.⊤→⊤IsId FREECCC.term u) refl
                           ∙ FREECCC.⋆IdL _)
     ; su → (suc , [su]) , funExt (λ n → refl) }))

-- the comma object's second projection, back to the syntax
projSyn : Functor GLUE.C FREECCC.C
projSyn .F-ob g = g .fst .snd
projSyn .F-hom m = m .fst .snd
projSyn .F-id = refl
projSyn .F-seq _ _ = refl

T : Functor FREECCC.C FREECCC.C
T = projSyn ∘F S

-- On OBJECTS initiality is immediate: `obExpr` is an ordinary
-- inductive type, and `S`'s object action is the glue's chosen
-- structure, whose syntactic component is the corresponding
-- constructor.  Every case below is `refl` at the leaves.
objEq : (A : FREECCC.C .ob) → T ⟅ A ⟆ ≡ A
objEq (↑ bool) = refl
objEq (↑ nat) = refl
objEq ⊤ = refl
objEq (A × B) = cong₂ CCCExpr._×_ (objEq A) (objEq B)
objEq (A ⇒ B) = cong₂ CCCExpr._⇒_ (objEq A) (objEq B)

-- the standard-model interpretation, also by `rec`
⟦-⟧SET : Functor FREECCC.C (SET ℓ-zero)
⟦-⟧SET = rec ×⇒QUIVER SETCCC (mkElimInterpᴰ
  (λ { bool → Bool , isSetBool ; nat → ℕ , isSetℕ })
  (λ { tr → λ _ → true ; fl → λ _ → false
     ; ze → λ _ → 0 ; su → suc }))

evalBool : [bool] → Bool
evalBool e = ⟦-⟧SET .F-hom e tt*

evalNat : [nat] → ℕ
evalNat e = ⟦-⟧SET .F-hom e tt*

evalNat-＂_＂ : (n : ℕ) → evalNat ＂ n ＂ ≡ n
evalNat-＂ zero ＂ = refl
evalNat-＂ suc n ＂ = cong suc evalNat-＂ n ＂

{-
  What initiality is needed for, and all it is needed for.  Given the
  natural isomorphism `T ≅ Id` that a uniqueness principle for the
  free CCC should supply, canonicity follows: naturality at the
  generators pins the component at `↑ nat` down to something that
  fixes every numeral, and at `↑ bool` to something that fixes both
  booleans (`numeralsFixed` / `booleansFixed`).
-}
module _ (η : NatIso T (Id {C = FREECCC.C})) where
  private
    ηnat = η .trans .N-ob (↑ nat)
    ηbool = η .trans .N-ob (↑ bool)

    η⊤≡id : η .trans .N-ob ⊤ ≡ FREECCC.id
    η⊤≡id = GC.⊤→⊤IsId FREECCC.term _

    natAt : {X : FREECCC.C .ob} (e : FREECCC.Hom[ ⊤ , X ])
      → (T ⟪ e ⟫) ⋆ₑ η .trans .N-ob X ≡ e
    natAt e = η .trans .N-hom e
            ∙ cong₂ _⋆ₑ_ η⊤≡id refl ∙ FREECCC.⋆IdL e

    numAt : (e : [nat])
      → ＂ (S ⟪ e ⟫) .fst .fst FREECCC.id ＂ ≡ (T ⟪ e ⟫)
    numAt e = sym (funExt⁻ ((S ⟪ e ⟫) .snd) FREECCC.id)
            ∙ FREECCC.⋆IdL ((T ⟪ e ⟫))

    boolAt : (e : [bool])
      → fromBool ((S ⟪ e ⟫) .fst .fst FREECCC.id) ≡ (T ⟪ e ⟫)
    boolAt e = sym (funExt⁻ ((S ⟪ e ⟫) .snd) FREECCC.id)
             ∙ FREECCC.⋆IdL ((T ⟪ e ⟫))

  canonicalize-nat : (e : [nat]) → fiber ＂_＂ e
  canonicalize-nat e = (S ⟪ e ⟫) .fst .fst FREECCC.id
    , sym (numeralsFixed ηnat (natAt [ze]) (η .trans .N-hom [su]) _)
    ∙ cong₂ _⋆ₑ_ (numAt e) refl ∙ natAt e

  canonicalize-bool : (e : [bool]) → (e ≡ [t]) ⊎ (e ≡ [f])
  canonicalize-bool e = go ((S ⟪ e ⟫) .fst .fst FREECCC.id) refl
    where
    key : (b : Bool) → (S ⟪ e ⟫) .fst .fst FREECCC.id ≡ b
      → e ≡ fromBool b
    key b p = sym (natAt e)
      ∙ cong₂ _⋆ₑ_ (sym (sym (cong fromBool p) ∙ boolAt e)) refl
      ∙ booleansFixed ηbool (natAt [t]) (natAt [f]) b

    go : (b : Bool) → (S ⟪ e ⟫) .fst .fst FREECCC.id ≡ b
      → (e ≡ [t]) ⊎ (e ≡ [f])
    go true p = inl (key true p)
    go false p = inr (key false p)

  canonicity-bool : Iso [bool] Bool
  canonicity-bool = GC.BoolIso.canonicity-bool [t] [f] evalBool refl refl
    canonicalize-bool

  canonicity-nat : Iso [nat] ℕ
  canonicity-nat = GC.NatIso.canonicity-nat ＂_＂ evalNat evalNat-＂_＂
    canonicalize-nat

{-
  Can the library's uniqueness principle supply that `NatIso`?
  `FreeCCCFunctor≅` asks for `⇒-lam`, reproduced below at `F := T`,
  `G := Id`.  Note that its left-hand side does not mention `γ` while
  its right-hand side does, and that `γ` is universally quantified
  over ALL isos `T Γ ≅ Γ` -- it is not the component of the natural
  isomorphism being built.  So the obligation collapses.
-}
module _ (⇒iso : {A B : FREECCC.C .ob}
  → CatIso FREECCC.C (T ⟅ A ⟆) A
  → CatIso FREECCC.C (T ⟅ B ⟆) B
  → CatIso FREECCC.C (T ⟅ CCCExpr._⇒_ A B ⟆) (CCCExpr._⇒_ A B)) where

  ⇒LamObligation : Type ℓ-zero
  ⇒LamObligation = {A B Γ : FREECCC.C .ob}
    (f : CatIso FREECCC.C (T ⟅ A ⟆) A)
    (g : CatIso FREECCC.C (T ⟅ B ⟆) B)
    (γ : CatIso FREECCC.C (T ⟅ Γ ⟆) Γ)
    (h : Expr ×⇒QUIVER (CCCExpr._×_ Γ A) B)
    → (T ⟪ lam' ×⇒QUIVER h ⟫) ⋆ₑ ⇒iso f g .fst
    ≡ γ .fst ⋆ₑ lam' ×⇒QUIVER h

  -- it forces `γ ⋆ lam' h` to be independent of `γ`
  ⇒LamCollapse : ⇒LamObligation
    → {A B Γ : FREECCC.C .ob}
      (f : CatIso FREECCC.C (T ⟅ A ⟆) A)
      (g : CatIso FREECCC.C (T ⟅ B ⟆) B)
      (γ γ' : CatIso FREECCC.C (T ⟅ Γ ⟆) Γ)
      (h : Expr ×⇒QUIVER (CCCExpr._×_ Γ A) B)
    → γ .fst ⋆ₑ lam' ×⇒QUIVER h ≡ γ' .fst ⋆ₑ lam' ×⇒QUIVER h
  ⇒LamCollapse hyp f g γ γ' h = sym (hyp f g γ h) ∙ hyp f g γ' h

  {-
    Concretely: `↑ bool × ↑ bool` has the swap automorphism, and
    `T` fixes it on the nose, so `id` and `swap` are both isos
    `T Γ ≅ Γ`.  The obligation therefore asserts that precomposing any
    λ-abstraction out of `↑ bool × ↑ bool` with `swap` changes nothing.
  -}
  private
    BB : FREECCC.C .ob
    BB = CCCExpr._×_ (↑ bool) (↑ bool)

    sw : FREECCC.Hom[ BB , BB ]
    sw = FREECCC._,p_ {a = ↑ bool} {b = ↑ bool}
      (FREECCC.π₂ {a = ↑ bool} {b = ↑ bool})
      (FREECCC.π₁ {a = ↑ bool} {b = ↑ bool})

    sw⋆sw : sw ⋆ₑ sw ≡ FREECCC.id
    sw⋆sw = FREECCC.,p-extensionality
      ( FREECCC.⋆Assoc _ _ _
      ∙ cong (sw ⋆ₑ_) FREECCC.×β₁ ∙ FREECCC.×β₂
      ∙ sym (FREECCC.⋆IdL _))
      ( FREECCC.⋆Assoc _ _ _
      ∙ cong (sw ⋆ₑ_) FREECCC.×β₂ ∙ FREECCC.×β₁
      ∙ sym (FREECCC.⋆IdL _))

    swIso : CatIso FREECCC.C BB BB
    swIso = sw , isiso sw sw⋆sw sw⋆sw

  ⇒LamSwap : ⇒LamObligation
    → (h : Expr ×⇒QUIVER (CCCExpr._×_ BB (↑ nat)) (↑ bool))
    → lam' ×⇒QUIVER h ≡ sw ⋆ₑ lam' ×⇒QUIVER h
  ⇒LamSwap hyp h = sym (FREECCC.⋆IdL _)
    ∙ ⇒LamCollapse hyp idCatIso idCatIso idCatIso swIso h

  {-
    And that is false.  Take `h` to project the first `bool`; in the
    standard model the two sides evaluate to `true` and `false`.  So
    `FreeCCCFunctor≅` cannot be applied to `T`, for any `⇒iso`.
  -}
  private
    hh : FREECCC.Hom[ CCCExpr._×_ BB (↑ nat) , ↑ bool ]
    hh = FREECCC.π₁ {a = BB} {b = ↑ nat}
       ⋆ₑ FREECCC.π₁ {a = ↑ bool} {b = ↑ bool}

  ⇒LamRefuted : ⇒LamObligation → ⊥
  ⇒LamRefuted hyp = true≢false
    (cong (λ m → ⟦-⟧SET .F-hom m (true , false) 0) (⇒LamSwap hyp hh))
