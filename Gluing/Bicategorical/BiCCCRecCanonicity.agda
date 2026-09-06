{-# OPTIONS --lossy-unification #-}
{-
  Canonicity for the free BICARTESIAN closed category, through the
  RECURSOR applied to the Artin comma category, plus the free BiCCC's
  uniqueness principle `FreeBiCCCFunctor≅` for the natural
  isomorphism `T ≅ Id`.

  This is `Gluing.Bicategorical.RecCanonicity` with coproducts added.
  No `Categoryᴰ`, `Section`, `elim`, `SETᴰ` or `reindex` below: the
  glue is a plain `BiCartesianClosedCategory` whose underlying
  category is `ArtinGlue Pts`.
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

＂_＂ : ℕ → [nat]
＂ zero ＂ = [ze]
＂ suc n ＂ = ＂ n ＂ ⋆ₑ [su]

fromBool : Bool → [bool]
fromBool b = if b then [t] else [f]

-- naturality at the generators is all the uniqueness principle is
-- needed for
module _ (η : FBC.Hom[ ↑ nat , ↑ nat ])
  (ηze : [ze] ⋆ₑ η ≡ [ze])
  (ηsu : [su] ⋆ₑ η ≡ η ⋆ₑ [su]) where

  numeralsFixed : (n : ℕ) → ＂ n ＂ ⋆ₑ η ≡ ＂ n ＂
  numeralsFixed zero = ηze
  numeralsFixed (suc n) =
      FBC.⋆Assoc _ _ _
    ∙ cong (＂ n ＂ ⋆ₑ_) ηsu
    ∙ sym (FBC.⋆Assoc _ _ _)
    ∙ cong (_⋆ₑ [su]) (numeralsFixed n)

module _ (θ : FBC.Hom[ ↑ bool , ↑ bool ])
  (θtr : [t] ⋆ₑ θ ≡ [t]) (θfl : [f] ⋆ₑ θ ≡ [f]) where

  booleansFixed : (b : Bool) → fromBool b ⋆ₑ θ ≡ fromBool b
  booleansFixed true = θtr
  booleansFixed false = θfl

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

    numAt : (e : [nat])
      → ＂ (S ⟪ e ⟫) .fst .fst FBC.id ＂ ≡ (T ⟪ e ⟫)
    numAt e = sym (funExt⁻ ((S ⟪ e ⟫) .snd) FBC.id)
            ∙ FBC.⋆IdL ((T ⟪ e ⟫))

    boolAt : (e : [bool])
      → fromBool ((S ⟪ e ⟫) .fst .fst FBC.id) ≡ (T ⟪ e ⟫)
    boolAt e = sym (funExt⁻ ((S ⟪ e ⟫) .snd) FBC.id)
             ∙ FBC.⋆IdL ((T ⟪ e ⟫))

  canonicalize-nat : (e : [nat]) → fiber ＂_＂ e
  canonicalize-nat e = (S ⟪ e ⟫) .fst .fst FBC.id
    , sym (numeralsFixed ηnat (natAt [ze]) (η .trans .N-hom [su]) _)
    ∙ cong₂ _⋆ₑ_ (numAt e) refl ∙ natAt e

  canonicalize-bool : (e : [bool]) → (e ≡ [t]) ⊎ (e ≡ [f])
  canonicalize-bool e = go ((S ⟪ e ⟫) .fst .fst FBC.id) refl
    where
    key : (b : Bool) → (S ⟪ e ⟫) .fst .fst FBC.id ≡ b
      → e ≡ fromBool b
    key b p = sym (natAt e)
      ∙ cong₂ _⋆ₑ_ (sym (sym (cong fromBool p) ∙ boolAt e)) refl
      ∙ booleansFixed ηbool (natAt [t]) (natAt [f]) b

    go : (b : Bool) → (S ⟪ e ⟫) .fst .fst FBC.id ≡ b
      → (e ≡ [t]) ⊎ (e ≡ [f])
    go true p = inl (key true p)
    go false p = inr (key false p)

  canonicity-bool : Iso [bool] Bool
  canonicity-bool = GC.BoolIso.canonicity-bool [t] [f] evalBool refl refl
    canonicalize-bool

  canonicity-nat : Iso [nat] ℕ
  canonicity-nat = GC.NatIso.canonicity-nat ＂_＂ evalNat evalNat-＂_＂
    canonicalize-nat
-- `T` preserves the whole cartesian closed structure DEFINITIONALLY:
-- `S`'s object action is the glue's chosen structure and `projSyn`
-- reads off its syntactic component, which is the corresponding
-- syntactic former.
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

  T-bp : preservesProvidedBinProducts T FBC.bp
  T-bp c c' = FBC.bp (T ⟅ c ⟆ , T ⟅ c' ⟆) .universal

  TCart : CartesianFunctor (FREEBICCC .CCC .CC) FBC.C
  TCart = T , T-bp

  IdCart : CartesianFunctor (FREEBICCC .CCC .CC) FBC.C
  IdCart = Id , λ c c' → FBC.bp (c , c') .universal

  FBC1 : Terminal FBC.C
  FBC1 = Terminal'ToTerminal FBC.term

  T-1 : preservesTerminal FBC.C FBC.C T
  T-1 = preserveOnePreservesAll FBC.C FBC.C T
    FBC1 (FBC1 .snd)

  Id-1 : preservesTerminal FBC.C FBC.C Id
  Id-1 = preserveOnePreservesAll FBC.C FBC.C Id
    FBC1 (FBC1 .snd)

  -- the two half-maps out of a product, and the presheaf action on
  -- the exponential presheaf, spelled out
  pl : ∀ {X Y A} → FBC.Hom[ X , Y ]
     → FBC.Hom[ BiCCCExpr._×_ X A , BiCCCExpr._×_ Y A ]
  pl {X = X} {Y = Y} {A = A} m = FBC._,p_ {a = Y} {b = A}
    (FBC.π₁ {a = X} {b = A} ⋆ₑ m) (FBC.π₂ {a = X} {b = A})

  pr : ∀ {X A B} → FBC.Hom[ A , B ]
     → FBC.Hom[ BiCCCExpr._×_ X A , BiCCCExpr._×_ X B ]
  pr {X = X} {A = A} {B = B} n = FBC._,p_ {a = X} {b = B}
    (FBC.π₁ {a = X} {b = A}) (FBC.π₂ {a = X} {b = A} ⋆ₑ n)

  pb : ∀ {X Y A B} → FBC.Hom[ X , Y ] → FBC.Hom[ A , B ]
     → FBC.Hom[ BiCCCExpr._×_ X A , BiCCCExpr._×_ Y B ]
  pb {X = X} {Y = Y} {A = A} {B = B} m n = FBC._,p_ {a = Y} {b = B}
    (FBC.π₁ {a = X} {b = A} ⋆ₑ m) (FBC.π₂ {a = X} {b = A} ⋆ₑ n)

  pl⋆pl : ∀ {X Y Z A} (m : FBC.Hom[ X , Y ]) (m' : FBC.Hom[ Y , Z ])
    → pl {A = A} m ⋆ₑ pl {A = A} m' ≡ pl {A = A} (m ⋆ₑ m')
  pl⋆pl m m' = FBC.,p-extensionality
    ( FBC.⋆Assoc _ _ _ ∙ FBC.⟨ refl ⟩⋆⟨ FBC.×β₁ ⟩
    ∙ sym (FBC.⋆Assoc _ _ _) ∙ FBC.⟨ FBC.×β₁ ⟩⋆⟨ refl ⟩
    ∙ FBC.⋆Assoc _ _ _ ∙ sym FBC.×β₁)
    ( FBC.⋆Assoc _ _ _ ∙ FBC.⟨ refl ⟩⋆⟨ FBC.×β₂ ⟩
    ∙ FBC.×β₂ ∙ sym FBC.×β₂)

  pr⋆pr : ∀ {X A B C} (u : FBC.Hom[ A , B ]) (v : FBC.Hom[ B , C ])
    → pr {X = X} u ⋆ₑ pr {X = X} v ≡ pr {X = X} (u ⋆ₑ v)
  pr⋆pr u v = FBC.,p-extensionality
    ( FBC.⋆Assoc _ _ _ ∙ FBC.⟨ refl ⟩⋆⟨ FBC.×β₁ ⟩
    ∙ FBC.×β₁ ∙ sym FBC.×β₁)
    ( FBC.⋆Assoc _ _ _ ∙ FBC.⟨ refl ⟩⋆⟨ FBC.×β₂ ⟩
    ∙ sym (FBC.⋆Assoc _ _ _) ∙ FBC.⟨ FBC.×β₂ ⟩⋆⟨ refl ⟩
    ∙ FBC.⋆Assoc _ _ _ ∙ sym FBC.×β₂)

  plId : ∀ {X A} → pl {X = X} {A = A} FBC.id ≡ FBC.id
  plId = FBC.,p-extensionality
    (FBC.×β₁ ∙ FBC.⋆IdR _ ∙ sym (FBC.⋆IdL _))
    (FBC.×β₂ ∙ sym (FBC.⋆IdL _))

  prId : ∀ {X A} → pr {X = X} {A = A} FBC.id ≡ FBC.id
  prId = FBC.,p-extensionality
    (FBC.×β₁ ∙ sym (FBC.⋆IdL _))
    (FBC.×β₂ ∙ FBC.⋆IdR _ ∙ sym (FBC.⋆IdL _))

  pl⋆pr : ∀ {X Y A B} (m : FBC.Hom[ X , Y ]) (n : FBC.Hom[ A , B ])
    → pl {A = A} m ⋆ₑ pr {X = Y} n ≡ pb m n
  pl⋆pr m n = FBC.,p-extensionality
    ( FBC.⋆Assoc _ _ _ ∙ FBC.⟨ refl ⟩⋆⟨ FBC.×β₁ ⟩
    ∙ FBC.×β₁ ∙ sym FBC.×β₁)
    ( FBC.⋆Assoc _ _ _ ∙ FBC.⟨ refl ⟩⋆⟨ FBC.×β₂ ⟩
    ∙ sym (FBC.⋆Assoc _ _ _) ∙ FBC.⟨ FBC.×β₂ ⟩⋆⟨ refl ⟩
    ∙ sym FBC.×β₂)

  pr⋆pl : ∀ {X Y A B} (m : FBC.Hom[ X , Y ]) (n : FBC.Hom[ A , B ])
    → pr {X = X} n ⋆ₑ pl {A = B} m ≡ pb m n
  pr⋆pl m n = FBC.,p-extensionality
    ( FBC.⋆Assoc _ _ _ ∙ FBC.⟨ refl ⟩⋆⟨ FBC.×β₁ ⟩
    ∙ sym (FBC.⋆Assoc _ _ _) ∙ FBC.⟨ FBC.×β₁ ⟩⋆⟨ refl ⟩
    ∙ sym FBC.×β₁)
    ( FBC.⋆Assoc _ _ _ ∙ FBC.⟨ refl ⟩⋆⟨ FBC.×β₂ ⟩
    ∙ FBC.×β₂ ∙ sym FBC.×β₂)

  pr⋆pb : ∀ {X Y A B C} (m : FBC.Hom[ X , Y ])
    (n : FBC.Hom[ A , B ]) (n' : FBC.Hom[ B , C ])
    → pr {X = X} n ⋆ₑ pb m n' ≡ pb m (n ⋆ₑ n')
  pr⋆pb m n n' = FBC.,p-extensionality
    ( FBC.⋆Assoc _ _ _ ∙ FBC.⟨ refl ⟩⋆⟨ FBC.×β₁ ⟩
    ∙ sym (FBC.⋆Assoc _ _ _) ∙ FBC.⟨ FBC.×β₁ ⟩⋆⟨ refl ⟩
    ∙ sym FBC.×β₁)
    ( FBC.⋆Assoc _ _ _ ∙ FBC.⟨ refl ⟩⋆⟨ FBC.×β₂ ⟩
    ∙ sym (FBC.⋆Assoc _ _ _) ∙ FBC.⟨ FBC.×β₂ ⟩⋆⟨ refl ⟩
    ∙ FBC.⋆Assoc _ _ _ ∙ sym FBC.×β₂)

  pbId : ∀ {X Y A} (m : FBC.Hom[ X , Y ])
    → pb {A = A} m FBC.id ≡ pl m
  pbId m = FBC.,p-extensionality
    (FBC.×β₁ ∙ sym FBC.×β₁)
    (FBC.×β₂ ∙ FBC.⋆IdR _ ∙ sym FBC.×β₂)

  appOf : ∀ {X A B} → FBC.Hom[ X , BiCCCExpr._⇒_ A B ]
        → FBC.Hom[ BiCCCExpr._×_ X A , B ]
  appOf m = pl m ⋆ₑ FBC.app

  ldaβ : ∀ {X A B} (h : FBC.Hom[ BiCCCExpr._×_ X A , B ])
    → appOf (FBC.lda {c = A} {d = B} h) ≡ h
  ldaβ {A = A} {B = B} h = FBC.⇒ue.β A B

  ldaExt : ∀ {X A B} {m n : FBC.Hom[ X , BiCCCExpr._⇒_ A B ]}
    → appOf m ≡ appOf n → m ≡ n
  ldaExt {A = A} {B = B} = FBC.⇒ue.extensionality A B

  appOfSeq : ∀ {X Y A B} (m : FBC.Hom[ X , Y ])
    (n : FBC.Hom[ Y , BiCCCExpr._⇒_ A B ])
    → appOf (m ⋆ₑ n) ≡ pl m ⋆ₑ appOf n
  appOfSeq m n = cong (FBC._⋆ FBC.app) (sym (pl⋆pl m n))
               ∙ FBC.⋆Assoc _ _ _

  -- the action of the internal hom on a pair of maps
  conj : ∀ {A B A' B'} → FBC.Hom[ A' , A ] → FBC.Hom[ B , B' ]
       → FBC.Hom[ BiCCCExpr._⇒_ A B , BiCCCExpr._⇒_ A' B' ]
  conj {A = A} {B = B} {A' = A'} {B' = B'} u v =
    FBC.lda {c = A'} {d = B'}
      ((pr {X = BiCCCExpr._⇒_ A B} u ⋆ₑ FBC.app {c = A} {d = B}) ⋆ₑ v)

  conj⋆conj : ∀ {A B A' B' A'' B''}
    (u : FBC.Hom[ A' , A ]) (v : FBC.Hom[ B , B' ])
    (u' : FBC.Hom[ A'' , A' ]) (v' : FBC.Hom[ B' , B'' ])
    → conj u v ⋆ₑ conj u' v' ≡ conj (u' ⋆ₑ u) (v ⋆ₑ v')
  conj⋆conj u v u' v' = ldaExt
    ( appOfSeq (conj u v) (conj u' v')
    ∙ FBC.⟨ refl ⟩⋆⟨ ldaβ _ ⟩
    ∙ sym (FBC.⋆Assoc _ _ _)
    ∙ FBC.⟨ sym (FBC.⋆Assoc _ _ _) ⟩⋆⟨ refl ⟩
    ∙ FBC.⟨ FBC.⟨ pl⋆pr (conj u v) u'
                        ∙ sym (pr⋆pl (conj u v) u') ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩
    ∙ FBC.⟨ FBC.⋆Assoc _ _ _ ⟩⋆⟨ refl ⟩
    ∙ FBC.⟨ FBC.⟨ refl ⟩⋆⟨ ldaβ _ ⟩ ⟩⋆⟨ refl ⟩
    ∙ FBC.⟨ sym (FBC.⋆Assoc _ _ _) ⟩⋆⟨ refl ⟩
    ∙ FBC.⟨ FBC.⟨ sym (FBC.⋆Assoc _ _ _) ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩
    ∙ FBC.⟨ FBC.⟨ FBC.⟨ pr⋆pr u' u ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩
    ∙ FBC.⋆Assoc _ _ _
    ∙ sym (ldaβ _))

  conjId : ∀ {A B} → conj (FBC.id {x = A}) (FBC.id {x = B})
                   ≡ FBC.id
  conjId = ldaExt
    ( ldaβ _ ∙ FBC.⋆IdR _ ∙ FBC.⟨ prId ⟩⋆⟨ refl ⟩ ∙ FBC.⋆IdL _
    ∙ sym (FBC.⋆IdL _) ∙ FBC.⟨ sym plId ⟩⋆⟨ refl ⟩)

  module ⇒At {A B : FBC.C .ob}
    (f : CatIso FBC.C (T ⟅ A ⟆) A)
    (g : CatIso FBC.C (T ⟅ B ⟆) B) where

    TA = T ⟅ A ⟆
    TB = T ⟅ B ⟆
    ff = f .fst
    fi = f .snd .isIso.inv
    gf = g .fst
    gi = g .snd .isIso.inv

    E : FBC.Hom[ BiCCCExpr._⇒_ TA TB , BiCCCExpr._⇒_ A B ]
    E = conj fi gf

    Einv : FBC.Hom[ BiCCCExpr._⇒_ A B , BiCCCExpr._⇒_ TA TB ]
    Einv = conj ff gi

    expIso : CatIso FBC.C (T ⟅ BiCCCExpr._⇒_ A B ⟆) (BiCCCExpr._⇒_ A B)
    expIso = E , isiso Einv
      ( conj⋆conj ff gi fi gf
      ∙ cong₂ (conj {A = A} {B = B} {A' = A} {B' = B})
          (f .snd .isIso.sec) (g .snd .isIso.sec)
      ∙ conjId)
      ( conj⋆conj fi gf ff gi
      ∙ cong₂ (conj {A = TA} {B = TB} {A' = TA} {B' = TB})
          (f .snd .isIso.ret) (g .snd .isIso.ret)
      ∙ conjId)

    evalSq : FBC.app {c = TA} {d = TB} ⋆ₑ gf
           ≡ pb E ff ⋆ₑ FBC.app {c = A} {d = B}
    evalSq =
        FBC.⟨ sym (FBC.⋆IdL _) ⟩⋆⟨ refl ⟩
      ∙ FBC.⟨ FBC.⟨ sym prId ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩
      ∙ FBC.⟨ FBC.⟨ cong prTA (sym (f .snd .isIso.ret)) ⟩⋆⟨ refl ⟩
                ⟩⋆⟨ refl ⟩
      ∙ FBC.⟨ FBC.⟨ sym (pr⋆pr ff fi) ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩
      ∙ FBC.⟨ FBC.⋆Assoc _ _ _ ⟩⋆⟨ refl ⟩
      ∙ FBC.⋆Assoc _ _ _
      ∙ FBC.⟨ refl ⟩⋆⟨ sym (ldaβ _) ⟩
      ∙ sym (FBC.⋆Assoc _ _ _)
      ∙ FBC.⟨ pr⋆pl E ff ⟩⋆⟨ refl ⟩
      where
      prTA : FBC.Hom[ TA , TA ]
        → FBC.Hom[ BiCCCExpr._×_ (BiCCCExpr._⇒_ TA TB) TA
                     , BiCCCExpr._×_ (BiCCCExpr._⇒_ TA TB) TA ]
      prTA = pr {X = BiCCCExpr._⇒_ TA TB} {A = TA} {B = TA}

    lamSq : ∀ {Γ} (γ : CatIso FBC.C (T ⟅ Γ ⟆) Γ)
      (h : FBC.Hom[ BiCCCExpr._×_ Γ A , B ])
      → T ⟪ h ⟫ ⋆ₑ gf ≡ pb (γ .fst) ff ⋆ₑ h
      → T ⟪ FBC.lda {c = A} {d = B} h ⟫ ⋆ₑ E
        ≡ γ .fst ⋆ₑ FBC.lda {c = A} {d = B} h
    lamSq {Γ = Γ} γ h sq = ldaExt
      ( appOfSeq (FBC.lda {c = TA} {d = TB} (T ⟪ h ⟫)) E
      ∙ FBC.⟨ refl ⟩⋆⟨ ldaβ _ ⟩
      ∙ sym (FBC.⋆Assoc _ _ _)
      ∙ FBC.⟨ sym (FBC.⋆Assoc _ _ _) ⟩⋆⟨ refl ⟩
      ∙ FBC.⟨ FBC.⟨ pl⋆pr _ fi ∙ sym (pr⋆pl _ fi) ⟩⋆⟨ refl ⟩
                ⟩⋆⟨ refl ⟩
      ∙ FBC.⟨ FBC.⋆Assoc _ _ _ ⟩⋆⟨ refl ⟩
      ∙ FBC.⟨ FBC.⟨ refl ⟩⋆⟨ ldaβ (T ⟪ h ⟫) ⟩ ⟩⋆⟨ refl ⟩
      ∙ FBC.⋆Assoc _ _ _
      ∙ FBC.⟨ refl ⟩⋆⟨ sq ⟩
      ∙ sym (FBC.⋆Assoc _ _ _)
      ∙ FBC.⟨ pr⋆pb (γ .fst) fi ff ⟩⋆⟨ refl ⟩
      ∙ FBC.⟨ cong pbγ (f .snd .isIso.sec) ⟩⋆⟨ refl ⟩
      ∙ FBC.⟨ pbId (γ .fst) ⟩⋆⟨ refl ⟩
      ∙ FBC.⟨ refl ⟩⋆⟨ sym (ldaβ h) ⟩
      ∙ sym (appOfSeq (γ .fst) (FBC.lda {c = A} {d = B} h)))
      where
      pbγ : FBC.Hom[ A , A ]
        → FBC.Hom[ BiCCCExpr._×_ (T ⟅ Γ ⟆) A , BiCCCExpr._×_ Γ A ]
      pbγ z = pb (γ .fst) z

  ⇒-isoT : ∀ {A B} → CatIso FBC.C (T ⟅ A ⟆) A
         → CatIso FBC.C (T ⟅ B ⟆) B
         → CatIso FBC.C (T ⟅ BiCCCExpr._⇒_ A B ⟆) (BiCCCExpr._⇒_ A B)
  ⇒-isoT f g = ⇒At.expIso f g

  genSq⊤ : (u : FBC.Hom[ BiCCCExpr.⊤ , BiCCCExpr.⊤ ]) {X : FBC.C .ob}
    (e : FBC.Hom[ BiCCCExpr.⊤ , X ])
    → e ⋆ₑ FBC.id ≡ u ⋆ₑ e
  genSq⊤ u e = FBC.⋆IdR _
    ∙ sym (cong₂ _⋆ₑ_ (GC.⊤→⊤IsId FBC.term u) refl ∙ FBC.⋆IdL e)

  -- `T` preserves the coproduct structure definitionally too, for
  -- the same reason: `rec` picks the glue's chosen coproduct and
  -- Artin's chosen coproduct has the syntactic one as its syntactic
  -- component.
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

  FBC0 : Terminal (FBC.C ^op)
  FBC0 = Terminal'ToTerminal FBC.init

  T-0 : isTerminal (FBC.C ^op) (T ⟅ BiCCCExpr.⊥ ⟆)
  T-0 = FBC0 .snd

  Id-0 : isTerminal (FBC.C ^op) (Id {C = FBC.C} ⟅ BiCCCExpr.⊥ ⟆)
  Id-0 = FBC0 .snd

  module +At {A B : FBC.C .ob}
    (f : CatIso FBC.C (T ⟅ A ⟆) A)
    (g : CatIso FBC.C (T ⟅ B ⟆) B) where

    ff = f .fst
    fi = f .snd .isIso.inv
    gf = g .fst
    gi = g .snd .isIso.inv

    fwd : FBC.Hom[ BiCCCExpr._+_ (T ⟅ A ⟆) (T ⟅ B ⟆)
                 , BiCCCExpr._+_ A B ]
    fwd = FBC.[_,p_] {a = T ⟅ A ⟆} {b = T ⟅ B ⟆}
      (ff ⋆ₑ FBC.σ₁ {a = A} {b = B}) (gf ⋆ₑ FBC.σ₂ {a = A} {b = B})

    bwd : FBC.Hom[ BiCCCExpr._+_ A B
                 , BiCCCExpr._+_ (T ⟅ A ⟆) (T ⟅ B ⟆) ]
    bwd = FBC.[_,p_] {a = A} {b = B}
      (fi ⋆ₑ FBC.σ₁ {a = T ⟅ A ⟆} {b = T ⟅ B ⟆})
      (gi ⋆ₑ FBC.σ₂ {a = T ⟅ A ⟆} {b = T ⟅ B ⟆})

    +isoSec : bwd ⋆ₑ fwd ≡ FBC.id
    +isoSec = FBC.[-,p-]-extensionality
      ( sym (FBC.⋆Assoc _ _ _)
      ∙ FBC.⟨ FBC.+β₁ ⟩⋆⟨ refl ⟩
      ∙ FBC.⋆Assoc _ _ _
      ∙ FBC.⟨ refl ⟩⋆⟨ FBC.+β₁ ⟩
      ∙ sym (FBC.⋆Assoc _ _ _)
      ∙ FBC.⟨ f .snd .isIso.sec ⟩⋆⟨ refl ⟩
      ∙ FBC.⋆IdL _ ∙ sym (FBC.⋆IdR _))
      ( sym (FBC.⋆Assoc _ _ _)
      ∙ FBC.⟨ FBC.+β₂ ⟩⋆⟨ refl ⟩
      ∙ FBC.⋆Assoc _ _ _
      ∙ FBC.⟨ refl ⟩⋆⟨ FBC.+β₂ ⟩
      ∙ sym (FBC.⋆Assoc _ _ _)
      ∙ FBC.⟨ g .snd .isIso.sec ⟩⋆⟨ refl ⟩
      ∙ FBC.⋆IdL _ ∙ sym (FBC.⋆IdR _))

    +isoRet : fwd ⋆ₑ bwd ≡ FBC.id
    +isoRet = FBC.[-,p-]-extensionality
      ( sym (FBC.⋆Assoc _ _ _)
      ∙ FBC.⟨ FBC.+β₁ ⟩⋆⟨ refl ⟩
      ∙ FBC.⋆Assoc _ _ _
      ∙ FBC.⟨ refl ⟩⋆⟨ FBC.+β₁ ⟩
      ∙ sym (FBC.⋆Assoc _ _ _)
      ∙ FBC.⟨ f .snd .isIso.ret ⟩⋆⟨ refl ⟩
      ∙ FBC.⋆IdL _ ∙ sym (FBC.⋆IdR _))
      ( sym (FBC.⋆Assoc _ _ _)
      ∙ FBC.⟨ FBC.+β₂ ⟩⋆⟨ refl ⟩
      ∙ FBC.⋆Assoc _ _ _
      ∙ FBC.⟨ refl ⟩⋆⟨ FBC.+β₂ ⟩
      ∙ sym (FBC.⋆Assoc _ _ _)
      ∙ FBC.⟨ g .snd .isIso.ret ⟩⋆⟨ refl ⟩
      ∙ FBC.⋆IdL _ ∙ sym (FBC.⋆IdR _))

    sumIso : CatIso FBC.C (T ⟅ BiCCCExpr._+_ A B ⟆) (BiCCCExpr._+_ A B)
    sumIso = fwd , isiso bwd +isoSec +isoRet

    cocaseSq : ∀ {Γ} (γ : CatIso FBC.C (T ⟅ Γ ⟆) Γ)
      (h₁ : FBC.Hom[ A , Γ ]) (h₂ : FBC.Hom[ B , Γ ])
      → T ⟪ h₁ ⟫ ⋆ₑ γ .fst ≡ ff ⋆ₑ h₁
      → T ⟪ h₂ ⟫ ⋆ₑ γ .fst ≡ gf ⋆ₑ h₂
      → T ⟪ FBC.[_,p_] {a = A} {b = B} h₁ h₂ ⟫ ⋆ₑ γ .fst
        ≡ fwd ⋆ₑ FBC.[_,p_] {a = A} {b = B} h₁ h₂
    cocaseSq γ h₁ h₂ sq₁ sq₂ = FBC.[-,p-]-extensionality
      ( sym (FBC.⋆Assoc _ _ _)
      ∙ FBC.⟨ FBC.+β₁ ⟩⋆⟨ refl ⟩
      ∙ sq₁
      ∙ FBC.⟨ refl ⟩⋆⟨ sym FBC.+β₁ ⟩
      ∙ sym (FBC.⋆Assoc _ _ _)
      ∙ FBC.⟨ sym FBC.+β₁ ⟩⋆⟨ refl ⟩
      ∙ FBC.⋆Assoc _ _ _)
      ( sym (FBC.⋆Assoc _ _ _)
      ∙ FBC.⟨ FBC.+β₂ ⟩⋆⟨ refl ⟩
      ∙ sq₂
      ∙ FBC.⟨ refl ⟩⋆⟨ sym FBC.+β₂ ⟩
      ∙ sym (FBC.⋆Assoc _ _ _)
      ∙ FBC.⟨ sym FBC.+β₂ ⟩⋆⟨ refl ⟩
      ∙ FBC.⋆Assoc _ _ _)

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
  (λ f g γ h₁ h₂ → +At.cocaseSq f g γ h₁ h₂)
  (λ f g → ⇒At.evalSq f g)
  (λ f g γ h sq → ⇒At.lamSq f g γ h sq)
  (mkElimInterpᴰ
    (λ { bool → idCatIso ; nat → idCatIso })
    (λ { tr → genSq⊤ _ (↑ₑ +×⇒QUIVER tr) , tt
       ; fl → genSq⊤ _ (↑ₑ +×⇒QUIVER fl) , tt
       ; ze → genSq⊤ _ (↑ₑ +×⇒QUIVER ze) , tt
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
