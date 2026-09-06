{-# OPTIONS --lossy-unification #-}
{-
  Canonicity for the free CARTESIAN category, through the RECURSOR
  applied to the Artin comma category, plus `FreeCartesianCatFunctor≅`
  for the natural isomorphism `T ≅ Id`.

  The third instance of `Gluing.Bicategorical.CanonicityCore`, and the
  cheapest: with no exponentials and no sums the uniqueness principle
  asks for nothing beyond the generators, so this file uses only the
  `BoolNat` half of the core.  Compare
  `Gluing.Bicategorical.CartesianCanonicity`, which proves the same
  two theorems through the displayed route and `elim`.
-}
module Gluing.Bicategorical.CartesianRecCanonicity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd)
open import Cubical.Data.Unit
open import Cubical.Data.Quiver.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Cartesian.More
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Instances.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Instances.Free.CartesianCategory.Forded

import Gluing.Bicategorical.Artin as Artin
open import Gluing.Bicategorical.CanonicityCore
import Gluing.Canonicity as GC

open Category
open Functor
open NatIso
open NatTrans
open QuiverOver
open UniversalElement
open CartesianCategory using (C; term; bp)

data OB : Type ℓ-zero where
  bool nat : OB

data MOR : Type ℓ-zero where
  tr fl ze su : MOR

×QUIVER : ×Quiver ℓ-zero ℓ-zero
×QUIVER .×Quiver.ob = OB
×QUIVER .×Quiver.Q .mor = MOR
×QUIVER .×Quiver.Q .dom tr = ⊤
×QUIVER .×Quiver.Q .dom fl = ⊤
×QUIVER .×Quiver.Q .dom ze = ⊤
×QUIVER .×Quiver.Q .dom su = ↑ nat
×QUIVER .×Quiver.Q .cod tr = ↑ bool
×QUIVER .×Quiver.Q .cod fl = ↑ bool
×QUIVER .×Quiver.Q .cod ze = ↑ nat
×QUIVER .×Quiver.Q .cod su = ↑ nat

FREECC : CartesianCategory ℓ-zero ℓ-zero
FREECC = FreeCartesianCategory ×QUIVER

module FREECC = CartesianCategory FREECC

-- the syntactic data the canonicity statements are about
[bool] : Type ℓ-zero
[bool] = FREECC.Hom[ ⊤ , ↑ bool ]

[t] [f] : [bool]
[t] = ↑ₑ ×QUIVER tr
[f] = ↑ₑ ×QUIVER fl

[nat] : Type ℓ-zero
[nat] = FREECC.Hom[ ⊤ , ↑ nat ]

[ze] : [nat]
[ze] = ↑ₑ ×QUIVER ze

[su] : FREECC.Hom[ ↑ nat , ↑ nat ]
[su] = ↑ₑ ×QUIVER su

module TERM = BoolNat {C = FREECC.C} FREECC.term
module GENS = BoolNat.Gens {C = FREECC.C} FREECC.term
  (↑ nat) (↑ bool) [t] [f] [ze] [su]
open GENS using (＂_＂; fromBool)

-- `Pts` preserves finite products because `⊤` is terminal
PtsCart : CartesianFunctor FREECC (SET ℓ-zero)
PtsCart = CorepCartesian FREECC ⊤

Pts : Functor FREECC.C (SET ℓ-zero)
Pts = PtsCart .fst

-- the glue is the comma category `SET ↓ Pts`, cartesian
GLUE : CartesianCategory (ℓ-suc ℓ-zero) ℓ-zero
GLUE .C = Artin.ArtinGlue Pts
GLUE .term = Artin.glueTerminal' Pts FREECC.term
GLUE .bp =
  Artin.glueBinProducts Pts FREECC.bp BinProductsSET (PtsCart .snd)

module GLUE = CartesianCategory GLUE

-- the interpretation lands in the comma category
S : Functor FREECC.C GLUE.C
S = rec ×QUIVER GLUE (mkElimInterpᴰ
  (λ { bool → ((Bool , isSetBool) , ↑ bool) , fromBool
     ; nat → ((ℕ , isSetℕ) , ↑ nat) , ＂_＂ })
  (λ { tr → ((λ _ → true) , [t])
             , funExt (λ u → cong₂ _⋆ₑ_ (GC.⊤→⊤IsId FREECC.term u) refl
                           ∙ FREECC.⋆IdL _)
     ; fl → ((λ _ → false) , [f])
             , funExt (λ u → cong₂ _⋆ₑ_ (GC.⊤→⊤IsId FREECC.term u) refl
                           ∙ FREECC.⋆IdL _)
     ; ze → ((λ _ → 0) , [ze])
             , funExt (λ u → cong₂ _⋆ₑ_ (GC.⊤→⊤IsId FREECC.term u) refl
                           ∙ FREECC.⋆IdL _)
     ; su → (suc , [su]) , funExt (λ n → refl) }))

-- the comma object's second projection, back to the syntax
projSyn : Functor GLUE.C FREECC.C
projSyn .F-ob g = g .fst .snd
projSyn .F-hom m = m .fst .snd
projSyn .F-id = refl
projSyn .F-seq _ _ = refl

T : Functor FREECC.C FREECC.C
T = projSyn ∘F S

objEq : (A : FREECC.C .ob) → T ⟅ A ⟆ ≡ A
objEq (↑ bool) = refl
objEq (↑ nat) = refl
objEq ⊤ = refl
objEq (A × B) = cong₂ ProdExpr._×_ (objEq A) (objEq B)

-- the standard-model interpretation, also by `rec`
⟦-⟧SET : Functor FREECC.C (SET ℓ-zero)
⟦-⟧SET = rec ×QUIVER SETCC (mkElimInterpᴰ
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

module Canonicity (η : NatIso T (Id {C = FREECC.C})) where
  private
    ηnat = η .trans .N-ob (↑ nat)
    ηbool = η .trans .N-ob (↑ bool)

    η⊤≡id : η .trans .N-ob ⊤ ≡ FREECC.id
    η⊤≡id = GC.⊤→⊤IsId FREECC.term _

    natAt : {X : FREECC.C .ob} (e : FREECC.Hom[ ⊤ , X ])
      → (T ⟪ e ⟫) ⋆ₑ η .trans .N-ob X ≡ e
    natAt e = η .trans .N-hom e
            ∙ cong₂ _⋆ₑ_ η⊤≡id refl ∙ FREECC.⋆IdL e

    reifyNat : (e : [nat]) → Σ[ n ∈ ℕ ] ＂ n ＂ ⋆ₑ ηnat ≡ e
    reifyNat e = (S ⟪ e ⟫) .fst .fst FREECC.id
      , cong₂ _⋆ₑ_ (sym (funExt⁻ ((S ⟪ e ⟫) .snd) FREECC.id)
                    ∙ FREECC.⋆IdL (T ⟪ e ⟫)) refl
      ∙ natAt e

    reifyBool : (e : [bool]) → Σ[ b ∈ Bool ] fromBool b ⋆ₑ ηbool ≡ e
    reifyBool e = (S ⟪ e ⟫) .fst .fst FREECC.id
      , cong₂ _⋆ₑ_ (sym (funExt⁻ ((S ⟪ e ⟫) .snd) FREECC.id)
                    ∙ FREECC.⋆IdL (T ⟪ e ⟫)) refl
      ∙ natAt e

  open GENS.Canonicity ηnat ηbool (natAt [ze]) (η .trans .N-hom [su])
    (natAt [t]) (natAt [f]) reifyNat reifyBool
    evalBool refl refl evalNat evalNat-＂_＂ public

-- `T` preserves the cartesian structure DEFINITIONALLY
private
  T-⊤ : T ⟅ ProdExpr.⊤ ⟆ ≡ ProdExpr.⊤
  T-⊤ = refl

  T-,p : ∀ {Γ A B} (f : FREECC.Hom[ Γ , A ]) (g : FREECC.Hom[ Γ , B ])
    → T ⟪ FREECC._,p_ {a = A} {b = B} f g ⟫
      ≡ FREECC._,p_ {a = T ⟅ A ⟆} {b = T ⟅ B ⟆} (T ⟪ f ⟫) (T ⟪ g ⟫)
  T-,p f g = refl

  T-bp : preservesProvidedBinProducts T FREECC.bp
  T-bp c c' = FREECC.bp (T ⟅ c ⟆ , T ⟅ c' ⟆) .universal

  TCart : CartesianFunctor FREECC FREECC.C
  TCart = T , T-bp

  IdCart : CartesianFunctor FREECC FREECC.C
  IdCart = Id , λ c c' → FREECC.bp (c , c') .universal

  FREECC1 : Terminal FREECC.C
  FREECC1 = Terminal'ToTerminal FREECC.term

  T-1 : preservesTerminal FREECC.C FREECC.C T
  T-1 = preserveOnePreservesAll FREECC.C FREECC.C T
    FREECC1 (FREECC1 .snd)

  Id-1 : preservesTerminal FREECC.C FREECC.C Id
  Id-1 = preserveOnePreservesAll FREECC.C FREECC.C Id
    FREECC1 (FREECC1 .snd)

-- The uniqueness principle, discharged for `T`.  Its first argument
-- is an unused ambient cartesian category, only there to fix levels.
ηT : NatIso T (Id {C = FREECC.C})
ηT = FreeCartesianCatFunctor≅ ×QUIVER FREECC TCart IdCart T-1 Id-1
  (mkElimInterpᴰ
    (λ { bool → idCatIso ; nat → idCatIso })
    (λ { tr → TERM.genSq⊤ _ (↑ₑ ×QUIVER tr) , tt
       ; fl → TERM.genSq⊤ _ (↑ₑ ×QUIVER fl) , tt
       ; ze → TERM.genSq⊤ _ (↑ₑ ×QUIVER ze) , tt
       ; su → (FREECC.⋆IdR _ ∙ sym (FREECC.⋆IdL _)) , tt }))

-- ... so the canonicity theorems are unconditional.
canonicalize-nat : (e : [nat]) → fiber ＂_＂ e
canonicalize-nat = Canonicity.canonicalize-nat ηT

canonicalize-bool : (e : [bool]) → (e ≡ [t]) ⊎ (e ≡ [f])
canonicalize-bool = Canonicity.canonicalize-bool ηT

canonicity-bool : Iso [bool] Bool
canonicity-bool = Canonicity.canonicity-bool ηT

canonicity-nat : Iso [nat] ℕ
canonicity-nat = Canonicity.canonicity-nat ηT
