{-# OPTIONS --lossy-unification #-}
{-
  Canonicity for the free BICARTESIAN closed category, through the
  RECURSOR applied to the Artin comma category, plus the free BiCCC's
  uniqueness principle `FreeBiCCCFunctor≅` for the natural
  isomorphism `T ≅ Id`.

  This is `Gluing.Bicategorical.RecCanonicity` with coproducts added,
  and the two share `Gluing.Bicategorical.CanonicityCore`: the
  exponential comparison, the coproduct comparison and the canonicity
  argument are all generic.  What is specific to this doctrine is the
  glue's structure, the strictness of `T` for each former, and the
  refutations.  No `Categoryᴰ`, `Section`, `elim`, `SETᴰ` or `reindex`
  below: the glue is a plain `BiCartesianClosedCategory` whose
  underlying category is `ArtinGlue Pts`.
-}
module Gluing.Bicategorical.BiCCCRecCanonicity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Data.Bool
open import Cubical.Data.Nat hiding (_+_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
import Cubical.Data.Empty as Empty
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
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.BiCartesianClosed.Base
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Forded

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
open CartesianClosedCategory using (CC; exps)
open BiCartesianClosedCategory using (CCC; sums; init)

data OB : Type ℓ-zero where
  bool nat : OB

data MOR : Type ℓ-zero where
  tr fl ze su : MOR

+×⇒QUIVER : +×⇒Quiver ℓ-zero ℓ-zero
+×⇒QUIVER .+×⇒Quiver.ob = OB
+×⇒QUIVER .+×⇒Quiver.Q .mor = MOR
+×⇒QUIVER .+×⇒Quiver.Q .dom tr = ⊤
+×⇒QUIVER .+×⇒Quiver.Q .dom fl = ⊤
+×⇒QUIVER .+×⇒Quiver.Q .dom ze = ⊤
+×⇒QUIVER .+×⇒Quiver.Q .dom su = ↑ nat
+×⇒QUIVER .+×⇒Quiver.Q .cod tr = ↑ bool
+×⇒QUIVER .+×⇒Quiver.Q .cod fl = ↑ bool
+×⇒QUIVER .+×⇒Quiver.Q .cod ze = ↑ nat
+×⇒QUIVER .+×⇒Quiver.Q .cod su = ↑ nat

FREEBICCC : BiCartesianClosedCategory ℓ-zero ℓ-zero
FREEBICCC = FreeBiCartesianClosedCategory +×⇒QUIVER

module FBC = BiCartesianClosedCategory FREEBICCC

-- the syntactic data the canonicity statements are about
[bool] : Type ℓ-zero
[bool] = FBC.Hom[ ⊤ , ↑ bool ]

[t] [f] : [bool]
[t] = ↑ₑ +×⇒QUIVER tr
[f] = ↑ₑ +×⇒QUIVER fl

[nat] : Type ℓ-zero
[nat] = FBC.Hom[ ⊤ , ↑ nat ]

[ze] : [nat]
[ze] = ↑ₑ +×⇒QUIVER ze

[su] : FBC.Hom[ ↑ nat , ↑ nat ]
[su] = ↑ₑ +×⇒QUIVER su

-- numerals, `fromBool`, the two "fixed" lemmas and the canonicity
-- argument are generic in the category and its generators
module TERM = BoolNat {C = FBC.C} FBC.term
module GENS = BoolNat.Gens {C = FBC.C} FBC.term
  (↑ nat) (↑ bool) [t] [f] [ze] [su]
open GENS using (＂_＂; fromBool)

-- the exponential and coproduct comparisons, at this syntax
module CORE = Exp (FREEBICCC .CCC)
module CORE+ = Sum FREEBICCC
open CORE using (module ⇒At)
open CORE+ using (module +At)

-- `Pts` preserves finite products because `⊤` is terminal
PtsCart : CartesianFunctor (FREEBICCC .CCC .CC) (SET ℓ-zero)
PtsCart = CorepCartesian (FREEBICCC .CCC .CC) ⊤

Pts : Functor FBC.C (SET ℓ-zero)
Pts = PtsCart .fst

-- The glue is the comma category `SET ↓ Pts`, bicartesian closed.
-- Only the exponential and the binary product use `PtsCart .snd`;
-- coproducts and the initial object need nothing of `Pts`.
GLUE : BiCartesianClosedCategory (ℓ-suc ℓ-zero) ℓ-zero
GLUE .CCC .CC .C = Artin.ArtinGlue Pts
GLUE .CCC .CC .term = Artin.glueTerminal' Pts FBC.term
GLUE .CCC .CC .bp =
  Artin.glueBinProducts Pts FBC.bp BinProductsSET (PtsCart .snd)
GLUE .CCC .exps =
  Artin.glueExponentials Pts FBC.bp FBC.exps (PtsCart .snd)
GLUE .sums = Artin.glueBinCoProducts Pts FBC.sums BinCoProductsSET
GLUE .init = Artin.glueInitial Pts FBC.init InitialSET

module GLUE = BiCartesianClosedCategory GLUE

-- the interpretation lands in the comma category
S : Functor FBC.C GLUE.C
S = rec +×⇒QUIVER GLUE (mkElimInterpᴰ
  (λ { bool → ((Bool , isSetBool) , ↑ bool) , fromBool
     ; nat → ((ℕ , isSetℕ) , ↑ nat) , ＂_＂ })
  (λ { tr → ((λ _ → true) , [t])
             , funExt (λ u → cong₂ _⋆ₑ_ (GC.⊤→⊤IsId FBC.term u) refl
                           ∙ FBC.⋆IdL _)
     ; fl → ((λ _ → false) , [f])
             , funExt (λ u → cong₂ _⋆ₑ_ (GC.⊤→⊤IsId FBC.term u) refl
                           ∙ FBC.⋆IdL _)
     ; ze → ((λ _ → 0) , [ze])
             , funExt (λ u → cong₂ _⋆ₑ_ (GC.⊤→⊤IsId FBC.term u) refl
                           ∙ FBC.⋆IdL _)
     ; su → (suc , [su]) , funExt (λ n → refl) }))

-- the comma object's second projection, back to the syntax
projSyn : Functor GLUE.C FBC.C
projSyn .F-ob g = g .fst .snd
projSyn .F-hom m = m .fst .snd
projSyn .F-id = refl
projSyn .F-seq _ _ = refl

T : Functor FBC.C FBC.C
T = projSyn ∘F S

-- On objects initiality is immediate; every leaf is `refl`.
objEq : (A : FBC.C .ob) → T ⟅ A ⟆ ≡ A
objEq (↑ bool) = refl
objEq (↑ nat) = refl
objEq ⊤ = refl
objEq ⊥ = refl
objEq (A × B) = cong₂ BiCCCExpr._×_ (objEq A) (objEq B)
objEq (A + B) = cong₂ BiCCCExpr._+_ (objEq A) (objEq B)
objEq (A ⇒ B) = cong₂ BiCCCExpr._⇒_ (objEq A) (objEq B)

-- the standard-model interpretation, also by `rec`
⟦-⟧SET : Functor FBC.C (SET ℓ-zero)
⟦-⟧SET = rec +×⇒QUIVER SETBiCCC (mkElimInterpᴰ
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

module Canonicity (η : NatIso T (Id {C = FBC.C})) where
  private
    ηnat = η .trans .N-ob (↑ nat)
    ηbool = η .trans .N-ob (↑ bool)

    η⊤≡id : η .trans .N-ob ⊤ ≡ FBC.id
    η⊤≡id = GC.⊤→⊤IsId FBC.term _

    natAt : {X : FBC.C .ob} (e : FBC.Hom[ ⊤ , X ])
      → (T ⟪ e ⟫) ⋆ₑ η .trans .N-ob X ≡ e
    natAt e = η .trans .N-hom e
            ∙ cong₂ _⋆ₑ_ η⊤≡id refl ∙ FBC.⋆IdL e

    reifyNat : (e : [nat]) → Σ[ n ∈ ℕ ] ＂ n ＂ ⋆ₑ ηnat ≡ e
    reifyNat e = (S ⟪ e ⟫) .fst .fst FBC.id
      , cong₂ _⋆ₑ_ (sym (funExt⁻ ((S ⟪ e ⟫) .snd) FBC.id)
                    ∙ FBC.⋆IdL (T ⟪ e ⟫)) refl
      ∙ natAt e

    reifyBool : (e : [bool]) → Σ[ b ∈ Bool ] fromBool b ⋆ₑ ηbool ≡ e
    reifyBool e = (S ⟪ e ⟫) .fst .fst FBC.id
      , cong₂ _⋆ₑ_ (sym (funExt⁻ ((S ⟪ e ⟫) .snd) FBC.id)
                    ∙ FBC.⋆IdL (T ⟪ e ⟫)) refl
      ∙ natAt e

  open GENS.Canonicity ηnat ηbool (natAt [ze]) (η .trans .N-hom [su])
    (natAt [t]) (natAt [f]) reifyNat reifyBool
    evalBool refl refl evalNat evalNat-＂_＂ public

-- `T` preserves the whole bicartesian closed structure
-- DEFINITIONALLY: `S`'s object action is the glue's chosen structure
-- and `projSyn` reads off its syntactic component, which is the
-- corresponding syntactic former.  This is what lets the generic
-- lemmas of `CanonicityCore` be applied at `T ⟅ - ⟆`.
private
  T-⊤ : T ⟅ BiCCCExpr.⊤ ⟆ ≡ BiCCCExpr.⊤
  T-⊤ = refl

  T-⇒ : ∀ {A B} → T ⟅ BiCCCExpr._⇒_ A B ⟆
                ≡ BiCCCExpr._⇒_ (T ⟅ A ⟆) (T ⟅ B ⟆)
  T-⇒ = refl

  T-lam : ∀ {Γ A B} (h : Expr +×⇒QUIVER (BiCCCExpr._×_ Γ A) B)
    → T ⟪ lam' +×⇒QUIVER h ⟫ ≡ lam' +×⇒QUIVER (T ⟪ h ⟫)
  T-lam h = refl

  T-lda : ∀ {Γ A B} (h : FBC.Hom[ BiCCCExpr._×_ Γ A , B ])
    → T ⟪ FBC.lda {c = A} {d = B} h ⟫
      ≡ FBC.lda {c = T ⟅ A ⟆} {d = T ⟅ B ⟆} (T ⟪ h ⟫)
  T-lda h = refl

  T-app : ∀ {A B} → T ⟪ FBC.app {c = A} {d = B} ⟫
                  ≡ FBC.app {c = T ⟅ A ⟆} {d = T ⟅ B ⟆}
  T-app = refl

  T-,p : ∀ {Γ A B} (f : FBC.Hom[ Γ , A ]) (g : FBC.Hom[ Γ , B ])
    → T ⟪ FBC._,p_ {a = A} {b = B} f g ⟫
      ≡ FBC._,p_ {a = T ⟅ A ⟆} {b = T ⟅ B ⟆} (T ⟪ f ⟫) (T ⟪ g ⟫)
  T-,p f g = refl

  T-+ : ∀ {A B} → T ⟅ BiCCCExpr._+_ A B ⟆
                ≡ BiCCCExpr._+_ (T ⟅ A ⟆) (T ⟅ B ⟆)
  T-+ = refl

  T-⊥ : T ⟅ BiCCCExpr.⊥ ⟆ ≡ BiCCCExpr.⊥
  T-⊥ = refl

  T-σ₁ : ∀ {A B} → T ⟪ FBC.σ₁ {a = A} {b = B} ⟫
                 ≡ FBC.σ₁ {a = T ⟅ A ⟆} {b = T ⟅ B ⟆}
  T-σ₁ = refl

  T-cocase : ∀ {A B Γ} (h₁ : FBC.Hom[ A , Γ ]) (h₂ : FBC.Hom[ B , Γ ])
    → T ⟪ FBC.[_,p_] {a = A} {b = B} h₁ h₂ ⟫
      ≡ FBC.[_,p_] {a = T ⟅ A ⟆} {b = T ⟅ B ⟆} (T ⟪ h₁ ⟫) (T ⟪ h₂ ⟫)
  T-cocase h₁ h₂ = refl

  T-bp : preservesProvidedBinProducts T FBC.bp
  T-bp c c' = FBC.bp (T ⟅ c ⟆ , T ⟅ c' ⟆) .universal

  TCart : CartesianFunctor (FREEBICCC .CCC .CC) FBC.C
  TCart = T , T-bp

  IdCart : CartesianFunctor (FREEBICCC .CCC .CC) FBC.C
  IdCart = Id , λ c c' → FBC.bp (c , c') .universal

  FBC1 : Terminal FBC.C
  FBC1 = Terminal'ToTerminal FBC.term

  T-1 : preservesTerminal FBC.C FBC.C T
  T-1 = preserveOnePreservesAll FBC.C FBC.C T FBC1 (FBC1 .snd)

  Id-1 : preservesTerminal FBC.C FBC.C Id
  Id-1 = preserveOnePreservesAll FBC.C FBC.C Id FBC1 (FBC1 .snd)

  FBC0 : Terminal (FBC.C ^op)
  FBC0 = Terminal'ToTerminal FBC.init

  T-0 : isTerminal (FBC.C ^op) (T ⟅ BiCCCExpr.⊥ ⟆)
  T-0 = FBC0 .snd

  Id-0 : isTerminal (FBC.C ^op) (Id {C = FBC.C} ⟅ BiCCCExpr.⊥ ⟆)
  Id-0 = FBC0 .snd

  ⇒-isoT : ∀ {A B} → CatIso FBC.C (T ⟅ A ⟆) A
         → CatIso FBC.C (T ⟅ B ⟆) B
         → CatIso FBC.C (T ⟅ BiCCCExpr._⇒_ A B ⟆) (BiCCCExpr._⇒_ A B)
  ⇒-isoT f g = ⇒At.expIso f g

  +-isoT : ∀ {A B} → CatIso FBC.C (T ⟅ A ⟆) A
         → CatIso FBC.C (T ⟅ B ⟆) B
         → CatIso FBC.C (T ⟅ BiCCCExpr._+_ A B ⟆) (BiCCCExpr._+_ A B)
  +-isoT f g = +At.sumIso f g

-- The uniqueness principle, discharged for `T`.
ηT : NatIso T (Id {C = FBC.C})
ηT = FreeBiCCCFunctor≅ +×⇒QUIVER TCart IdCart T-1 Id-1 T-0 Id-0
  ⇒-isoT +-isoT
  (λ f g → FBC.+β₁)
  (λ f g → FBC.+β₂)
  (λ f g γ h₁ h₂ → +At.cocaseSq f g γ h₁ h₂ (T ⟪ h₁ ⟫) (T ⟪ h₂ ⟫))
  (λ f g → ⇒At.evalSq f g)
  (λ f g γ h sq → ⇒At.lamSq f g γ h (T ⟪ h ⟫) sq)
  (mkElimInterpᴰ
    (λ { bool → idCatIso ; nat → idCatIso })
    (λ { tr → TERM.genSq⊤ _ (↑ₑ +×⇒QUIVER tr) , tt
       ; fl → TERM.genSq⊤ _ (↑ₑ +×⇒QUIVER fl) , tt
       ; ze → TERM.genSq⊤ _ (↑ₑ +×⇒QUIVER ze) , tt
       ; su → (FBC.⋆IdR _ ∙ sym (FBC.⋆IdL _)) , tt }))

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
  `+-cocase` had the same defect as `⇒-lam`: the use site discarded
  the displayed data, so the hypothesis quantified `γ` over all isos
  while `γ` was absent from the left-hand side.  Below is the OLD
  obligation at `F := T` and `G := Id`; it forces every automorphism
  of `A + B` to be `+iso f g`, and `+CocaseRefuted` derives `⊥`.
  The corrected `+-cocase` instead takes the pair of squares over
  `h₁` and `h₂` -- the induction hypotheses -- as premises, and
  concludes only about their copairing; that is `+At.cocaseSq`, which
  `ηT` runs on.
-}
module _ (+iso : {A B : FBC.C .ob}
  → CatIso FBC.C (T ⟅ A ⟆) A
  → CatIso FBC.C (T ⟅ B ⟆) B
  → CatIso FBC.C (T ⟅ BiCCCExpr._+_ A B ⟆) (BiCCCExpr._+_ A B)) where

  +CocaseObligation : Type ℓ-zero
  +CocaseObligation = {A B Γ : FBC.C .ob}
    (f : CatIso FBC.C (T ⟅ A ⟆) A)
    (g : CatIso FBC.C (T ⟅ B ⟆) B)
    (γ : CatIso FBC.C (T ⟅ Γ ⟆) Γ)
    (h : Expr +×⇒QUIVER (BiCCCExpr._+_ A B) Γ)
    → T ⟪ h ⟫ ⋆ₑ γ .fst ≡ +iso f g .fst ⋆ₑ h

  -- taking `h := id` forces `γ` to be `+iso f g`, for every `γ`
  +CocaseCollapse : +CocaseObligation → {A B : FBC.C .ob}
    (f : CatIso FBC.C (T ⟅ A ⟆) A)
    (g : CatIso FBC.C (T ⟅ B ⟆) B)
    (γ : CatIso FBC.C (T ⟅ BiCCCExpr._+_ A B ⟆) (BiCCCExpr._+_ A B))
    → γ .fst ≡ +iso f g .fst
  +CocaseCollapse hyp f g γ =
      sym (FBC.⋆IdL _)
    ∙ cong (_⋆ₑ γ .fst) (sym (T .F-id))
    ∙ hyp f g γ FBC.id
    ∙ FBC.⋆IdR _

  private
    U+U : FBC.C .ob
    U+U = BiCCCExpr._+_ ⊤ ⊤

    sw : FBC.Hom[ U+U , U+U ]
    sw = FBC.[_,p_] {a = ⊤} {b = ⊤}
      (FBC.σ₂ {a = ⊤} {b = ⊤}) (FBC.σ₁ {a = ⊤} {b = ⊤})

    sw⋆sw : sw ⋆ₑ sw ≡ FBC.id
    sw⋆sw = FBC.[-,p-]-extensionality
      ( sym (FBC.⋆Assoc _ _ _) ∙ FBC.⟨ FBC.+β₁ ⟩⋆⟨ refl ⟩
      ∙ FBC.+β₂ ∙ sym (FBC.⋆IdR _))
      ( sym (FBC.⋆Assoc _ _ _) ∙ FBC.⟨ FBC.+β₂ ⟩⋆⟨ refl ⟩
      ∙ FBC.+β₁ ∙ sym (FBC.⋆IdR _))

    swIso : CatIso FBC.C (T ⟅ U+U ⟆) U+U
    swIso = sw , isiso sw sw⋆sw sw⋆sw

    tf : FBC.Hom[ U+U , ↑ bool ]
    tf = FBC.[_,p_] {a = ⊤} {b = ⊤} [t] [f]

  +CocaseRefuted : +CocaseObligation → Empty.⊥
  +CocaseRefuted hyp = true≢false (cong evalBool [t]≡[f])
    where
    sw≡id : sw ≡ FBC.id
    sw≡id = +CocaseCollapse hyp idCatIso idCatIso swIso
          ∙ sym (+CocaseCollapse hyp idCatIso idCatIso idCatIso)

    σ₂≡σ₁ : FBC.σ₂ {a = ⊤} {b = ⊤} ≡ FBC.σ₁ {a = ⊤} {b = ⊤}
    σ₂≡σ₁ = sym FBC.+β₁ ∙ cong (FBC.σ₁ {a = ⊤} {b = ⊤} ⋆ₑ_) sw≡id
          ∙ FBC.⋆IdR _

    [t]≡[f] : [t] ≡ [f]
    [t]≡[f] = sym FBC.+β₁ ∙ cong (_⋆ₑ tf) (sym σ₂≡σ₁) ∙ FBC.+β₂
