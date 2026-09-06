{-# OPTIONS --lossy-unification #-}
{-
  Canonicity through the RECURSOR of the free cartesian closed
  category applied to the comma category itself, plus the free CCC's
  uniqueness principle `FreeCCCFunctor≅` for the natural isomorphism
  `T ≅ Id`.  `canonicity-bool` and `canonicity-nat` are unconditional.

  `GLUE` is the Artin glue of `Gluing.Bicategorical.BoolNatCanonicity`
  -- a plain `CartesianClosedCategory` whose underlying category is
  `ArtinGlue Pts`, which `Gluing.Bicategorical.Artin` proves equal to
  the `CAT` comma object `Commaᴮ` on the nose.  So `rec` into it uses
  the bicategorical limit directly: no displayed category, no
  `Section`, no `SETᴰ`, no `reindex` anywhere below.

  The doctrine-generic half of the argument lives in
  `Gluing.Bicategorical.CanonicityCore`; what remains here is the
  interpretation, the strictness of `T` for each former, and the
  refutation of the uniqueness principle's old `⇒-lam`.
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
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.CartesianClosed.Base

open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Forded
  as FreeCCC

open import Gluing.Bicategorical.BoolNatCanonicity
open import Gluing.Bicategorical.CanonicityCore
import Gluing.Canonicity as GC

open Category
open Functor
open NatIso
open NatTrans
open CartesianClosedCategory
open UniversalElement

module GLUE = CartesianClosedCategory GLUE

-- the cartesian closed lemmas the uniqueness principle consumes,
-- instantiated at the syntax
module CORE = Exp FREECCC
open CORE using (pl; pb; plId; pbId; module ⇒At)
module TERM = BoolNat {C = FREECCC.C} FREECCC.term

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
  natural isomorphism `T ≅ Id`, naturality at `⊤` and the comma
  category's first projection reify every global point at a generating
  sort; `CanonicityCore`'s `Canonicity` then concludes.  `ηT`, below,
  supplies the isomorphism.
-}
module Canonicity (η : NatIso T (Id {C = FREECCC.C})) where
  private
    ηnat = η .trans .N-ob (↑ nat)
    ηbool = η .trans .N-ob (↑ bool)

    η⊤≡id : η .trans .N-ob ⊤ ≡ FREECCC.id
    η⊤≡id = GC.⊤→⊤IsId FREECCC.term _

    natAt : {X : FREECCC.C .ob} (e : FREECCC.Hom[ ⊤ , X ])
      → (T ⟪ e ⟫) ⋆ₑ η .trans .N-ob X ≡ e
    natAt e = η .trans .N-hom e
            ∙ cong₂ _⋆ₑ_ η⊤≡id refl ∙ FREECCC.⋆IdL e

    reifyNat : (e : [nat]) → Σ[ n ∈ ℕ ] ＂ n ＂ ⋆ₑ ηnat ≡ e
    reifyNat e = (S ⟪ e ⟫) .fst .fst FREECCC.id
      , cong₂ _⋆ₑ_ (sym (funExt⁻ ((S ⟪ e ⟫) .snd) FREECCC.id)
                    ∙ FREECCC.⋆IdL (T ⟪ e ⟫)) refl
      ∙ natAt e

    reifyBool : (e : [bool]) → Σ[ b ∈ Bool ] fromBool b ⋆ₑ ηbool ≡ e
    reifyBool e = (S ⟪ e ⟫) .fst .fst FREECCC.id
      , cong₂ _⋆ₑ_ (sym (funExt⁻ ((S ⟪ e ⟫) .snd) FREECCC.id)
                    ∙ FREECCC.⋆IdL (T ⟪ e ⟫)) refl
      ∙ natAt e

  open GENS.Canonicity ηnat ηbool (natAt [ze]) (η .trans .N-hom [su])
    (natAt [t]) (natAt [f]) reifyNat reifyBool
    evalBool refl refl evalNat evalNat-＂_＂ public


-- `T` preserves the whole cartesian closed structure DEFINITIONALLY:
-- `S`'s object action is the glue's chosen structure and `projSyn`
-- reads off its syntactic component, which is the corresponding
-- syntactic former.  This is what lets the generic lemmas of
-- `CanonicityCore` be applied at `T ⟅ - ⟆` with no comparison map.
private
  T-⊤ : T ⟅ CCCExpr.⊤ ⟆ ≡ CCCExpr.⊤
  T-⊤ = refl

  T-⇒ : ∀ {A B} → T ⟅ CCCExpr._⇒_ A B ⟆
                ≡ CCCExpr._⇒_ (T ⟅ A ⟆) (T ⟅ B ⟆)
  T-⇒ = refl

  T-lam : ∀ {Γ A B} (h : Expr ×⇒QUIVER (CCCExpr._×_ Γ A) B)
    → T ⟪ lam' ×⇒QUIVER h ⟫ ≡ lam' ×⇒QUIVER (T ⟪ h ⟫)
  T-lam h = refl

  T-lda : ∀ {Γ A B} (h : FREECCC.Hom[ CCCExpr._×_ Γ A , B ])
    → T ⟪ FREECCC.lda {c = A} {d = B} h ⟫
      ≡ FREECCC.lda {c = T ⟅ A ⟆} {d = T ⟅ B ⟆} (T ⟪ h ⟫)
  T-lda h = refl

  T-app : ∀ {A B} → T ⟪ FREECCC.app {c = A} {d = B} ⟫
                  ≡ FREECCC.app {c = T ⟅ A ⟆} {d = T ⟅ B ⟆}
  T-app = refl

  T-,p : ∀ {Γ A B} (f : FREECCC.Hom[ Γ , A ]) (g : FREECCC.Hom[ Γ , B ])
    → T ⟪ FREECCC._,p_ {a = A} {b = B} f g ⟫
      ≡ FREECCC._,p_ {a = T ⟅ A ⟆} {b = T ⟅ B ⟆} (T ⟪ f ⟫) (T ⟪ g ⟫)
  T-,p f g = refl

  T-bp : preservesProvidedBinProducts T FREECCC.bp
  T-bp c c' = FREECCC.bp (T ⟅ c ⟆ , T ⟅ c' ⟆) .universal

  TCart : CartesianFunctor (FREECCC .CC) FREECCC.C
  TCart = T , T-bp

  IdCart : CartesianFunctor (FREECCC .CC) FREECCC.C
  IdCart = Id , λ c c' → FREECCC.bp (c , c') .universal

  FREECCC1 : Terminal FREECCC.C
  FREECCC1 = Terminal'ToTerminal FREECCC.term

  T-1 : preservesTerminal FREECCC.C FREECCC.C T
  T-1 = preserveOnePreservesAll FREECCC.C FREECCC.C T
    FREECCC1 (FREECCC1 .snd)

  Id-1 : preservesTerminal FREECCC.C FREECCC.C Id
  Id-1 = preserveOnePreservesAll FREECCC.C FREECCC.C Id
    FREECCC1 (FREECCC1 .snd)

  ⇒-isoT : ∀ {A B} → CatIso FREECCC.C (T ⟅ A ⟆) A
         → CatIso FREECCC.C (T ⟅ B ⟆) B
         → CatIso FREECCC.C (T ⟅ CCCExpr._⇒_ A B ⟆) (CCCExpr._⇒_ A B)
  ⇒-isoT f g = ⇒At.expIso f g

-- The uniqueness principle, discharged for `T`.
ηT : NatIso T (Id {C = FREECCC.C})
ηT = FreeCCCFunctor≅ ×⇒QUIVER TCart IdCart T-1 Id-1 ⇒-isoT
  (λ f g → ⇒At.evalSq f g)
  (λ f g γ h sq → ⇒At.lamSq f g γ h (T ⟪ h ⟫) sq)
  (mkElimInterpᴰ
    (λ { bool → idCatIso ; nat → idCatIso })
    (λ { tr → TERM.genSq⊤ _ (↑ₑ ×⇒QUIVER tr) , tt
       ; fl → TERM.genSq⊤ _ (↑ₑ ×⇒QUIVER fl) , tt
       ; ze → TERM.genSq⊤ _ (↑ₑ ×⇒QUIVER ze) , tt
       ; su → (FREECCC.⋆IdR _ ∙ sym (FREECCC.⋆IdL _)) , tt }))

-- ... so the canonicity theorems are unconditional.
canonicalize-nat : (e : [nat]) → fiber ＂_＂ e
canonicalize-nat = Canonicity.canonicalize-nat ηT

canonicalize-bool : (e : [bool]) → (e ≡ [t]) ⊎ (e ≡ [f])
canonicalize-bool = Canonicity.canonicalize-bool ηT

canonicity-bool : Iso [bool] Bool
canonicity-bool = Canonicity.canonicity-bool ηT

canonicity-nat : Iso [nat] ℕ
canonicity-nat = Canonicity.canonicity-nat ηT


{-
  The bug this file's `⇒-lam` used to have, and why the corrected
  hypothesis is not refutable the same way.  The old `⇒-lam`, at
  `F := T` and `G := Id`, is `⇒LamObligation` below: its left-hand
  side does not mention `γ`, while `γ` is universally quantified over
  ALL isos `T Γ ≅ Γ`.  That forces `γ ⋆ lam h` to be independent of
  `γ`, and `⇒LamRefuted` derives `⊥`.

  `Forded`'s `⇒-lam` now carries the displayed morphism over `h` --
  the induction hypothesis -- as a premise, reproduced as `⇒LamFixed`.
  The refutation breaks at exactly one step, `⇒LamCollapse`: it uses
  `hyp f g γ h` and `hyp f g γ' h`, and each now demands a premise
  whose TYPE mentions its own `γ`.  Nothing produces both.  And the
  two it would need are genuinely inconsistent, not merely unavailable
  -- `premisesIncompatible`.
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
    the OLD `⇒-lam` was not dischargeable for `T`, for any `⇒iso`.
  -}
  private
    hh : FREECCC.Hom[ CCCExpr._×_ BB (↑ nat) , ↑ bool ]
    hh = FREECCC.π₁ {a = BB} {b = ↑ nat}
       ⋆ₑ FREECCC.π₁ {a = ↑ bool} {b = ↑ bool}

  ⇒LamRefuted : ⇒LamObligation → ⊥
  ⇒LamRefuted hyp = true≢false
    (cong (λ m → ⟦-⟧SET .F-hom m (true , false) 0) (⇒LamSwap hyp hh))

  -- `Forded`'s corrected `⇒-lam`, at `F := T` and `G := Id`.  The new
  -- premise is the displayed morphism over `h` that the use site used
  -- to discard, and its type mentions `γ`.
  ⇒LamFixed : Type ℓ-zero
  ⇒LamFixed = {A B Γ : FREECCC.C .ob}
    (f : CatIso FREECCC.C (T ⟅ A ⟆) A)
    (g : CatIso FREECCC.C (T ⟅ B ⟆) B)
    (γ : CatIso FREECCC.C (T ⟅ Γ ⟆) Γ)
    (h : Expr ×⇒QUIVER (CCCExpr._×_ Γ A) B)
    → T ⟪ h ⟫ ⋆ₑ g .fst ≡ pb (γ .fst) (f .fst) ⋆ₑ h
    → (T ⟪ lam' ×⇒QUIVER h ⟫) ⋆ₑ ⇒iso f g .fst
      ≡ γ .fst ⋆ₑ lam' ×⇒QUIVER h

  -- the premise `⇒LamCollapse` would need, at a given `γ`
  Premise : CatIso FREECCC.C (T ⟅ BB ⟆) BB
    → FREECCC.Hom[ CCCExpr._×_ BB (↑ nat) , ↑ bool ] → Type ℓ-zero
  Premise γ h = T ⟪ h ⟫ ⋆ₑ FREECCC.id
              ≡ pb (γ .fst) FREECCC.id ⋆ₑ h

  -- the two instantiations `⇒LamCollapse` takes are inconsistent, so
  -- it cannot be reconstructed for `⇒LamFixed`
  premisesIncompatible : Premise idCatIso hh → Premise swIso hh → ⊥
  premisesIncompatible p q = true≢false
    (cong (λ m → ⟦-⟧SET .F-hom m ((true , false) , 0)) hh≡sw⋆hh)
    where
    hh≡sw⋆hh : hh ≡ pl sw ⋆ₑ hh
    hh≡sw⋆hh =
        sym (FREECCC.⋆IdL _)
      ∙ cong₂ _⋆ₑ_ (sym (pbId FREECCC.id ∙ plId)) refl
      ∙ sym p ∙ q
      ∙ cong₂ _⋆ₑ_ (pbId sw) refl

-- ... and the corrected obligation is not merely unrefuted: this is
-- the instance `ηT` runs on.
private
  ⇒LamHolds : ⇒LamFixed ⇒-isoT
  ⇒LamHolds f g γ h sq = ⇒At.lamSq f g γ h (T ⟪ h ⟫) sq
