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
import Gluing.Canonicity as GC

open Category
open Functor
open NatIso
open NatTrans
open CartesianClosedCategory
open UniversalElement

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
  natural isomorphism `T ≅ Id`, canonicity follows: naturality at the
  generators pins the component at `↑ nat` down to something that
  fixes every numeral, and at `↑ bool` to something that fixes both
  booleans (`numeralsFixed` / `booleansFixed`).  `ηT`, below, supplies
  it.
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


-- `T` preserves the whole cartesian closed structure DEFINITIONALLY:
-- `S`'s object action is the glue's chosen structure and `projSyn`
-- reads off its syntactic component, which is the corresponding
-- syntactic former.
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

  -- the two half-maps out of a product, and the presheaf action on
  -- the exponential presheaf, spelled out
  pl : ∀ {X Y A} → FREECCC.Hom[ X , Y ]
     → FREECCC.Hom[ CCCExpr._×_ X A , CCCExpr._×_ Y A ]
  pl {X = X} {Y = Y} {A = A} m = FREECCC._,p_ {a = Y} {b = A}
    (FREECCC.π₁ {a = X} {b = A} ⋆ₑ m) (FREECCC.π₂ {a = X} {b = A})

  pr : ∀ {X A B} → FREECCC.Hom[ A , B ]
     → FREECCC.Hom[ CCCExpr._×_ X A , CCCExpr._×_ X B ]
  pr {X = X} {A = A} {B = B} n = FREECCC._,p_ {a = X} {b = B}
    (FREECCC.π₁ {a = X} {b = A}) (FREECCC.π₂ {a = X} {b = A} ⋆ₑ n)

  pb : ∀ {X Y A B} → FREECCC.Hom[ X , Y ] → FREECCC.Hom[ A , B ]
     → FREECCC.Hom[ CCCExpr._×_ X A , CCCExpr._×_ Y B ]
  pb {X = X} {Y = Y} {A = A} {B = B} m n = FREECCC._,p_ {a = Y} {b = B}
    (FREECCC.π₁ {a = X} {b = A} ⋆ₑ m) (FREECCC.π₂ {a = X} {b = A} ⋆ₑ n)

  pl⋆pl : ∀ {X Y Z A} (m : FREECCC.Hom[ X , Y ]) (m' : FREECCC.Hom[ Y , Z ])
    → pl {A = A} m ⋆ₑ pl {A = A} m' ≡ pl {A = A} (m ⋆ₑ m')
  pl⋆pl m m' = FREECCC.,p-extensionality
    ( FREECCC.⋆Assoc _ _ _ ∙ FREECCC.⟨ refl ⟩⋆⟨ FREECCC.×β₁ ⟩
    ∙ sym (FREECCC.⋆Assoc _ _ _) ∙ FREECCC.⟨ FREECCC.×β₁ ⟩⋆⟨ refl ⟩
    ∙ FREECCC.⋆Assoc _ _ _ ∙ sym FREECCC.×β₁)
    ( FREECCC.⋆Assoc _ _ _ ∙ FREECCC.⟨ refl ⟩⋆⟨ FREECCC.×β₂ ⟩
    ∙ FREECCC.×β₂ ∙ sym FREECCC.×β₂)

  pr⋆pr : ∀ {X A B C} (u : FREECCC.Hom[ A , B ]) (v : FREECCC.Hom[ B , C ])
    → pr {X = X} u ⋆ₑ pr {X = X} v ≡ pr {X = X} (u ⋆ₑ v)
  pr⋆pr u v = FREECCC.,p-extensionality
    ( FREECCC.⋆Assoc _ _ _ ∙ FREECCC.⟨ refl ⟩⋆⟨ FREECCC.×β₁ ⟩
    ∙ FREECCC.×β₁ ∙ sym FREECCC.×β₁)
    ( FREECCC.⋆Assoc _ _ _ ∙ FREECCC.⟨ refl ⟩⋆⟨ FREECCC.×β₂ ⟩
    ∙ sym (FREECCC.⋆Assoc _ _ _) ∙ FREECCC.⟨ FREECCC.×β₂ ⟩⋆⟨ refl ⟩
    ∙ FREECCC.⋆Assoc _ _ _ ∙ sym FREECCC.×β₂)

  plId : ∀ {X A} → pl {X = X} {A = A} FREECCC.id ≡ FREECCC.id
  plId = FREECCC.,p-extensionality
    (FREECCC.×β₁ ∙ FREECCC.⋆IdR _ ∙ sym (FREECCC.⋆IdL _))
    (FREECCC.×β₂ ∙ sym (FREECCC.⋆IdL _))

  prId : ∀ {X A} → pr {X = X} {A = A} FREECCC.id ≡ FREECCC.id
  prId = FREECCC.,p-extensionality
    (FREECCC.×β₁ ∙ sym (FREECCC.⋆IdL _))
    (FREECCC.×β₂ ∙ FREECCC.⋆IdR _ ∙ sym (FREECCC.⋆IdL _))

  pl⋆pr : ∀ {X Y A B} (m : FREECCC.Hom[ X , Y ]) (n : FREECCC.Hom[ A , B ])
    → pl {A = A} m ⋆ₑ pr {X = Y} n ≡ pb m n
  pl⋆pr m n = FREECCC.,p-extensionality
    ( FREECCC.⋆Assoc _ _ _ ∙ FREECCC.⟨ refl ⟩⋆⟨ FREECCC.×β₁ ⟩
    ∙ FREECCC.×β₁ ∙ sym FREECCC.×β₁)
    ( FREECCC.⋆Assoc _ _ _ ∙ FREECCC.⟨ refl ⟩⋆⟨ FREECCC.×β₂ ⟩
    ∙ sym (FREECCC.⋆Assoc _ _ _) ∙ FREECCC.⟨ FREECCC.×β₂ ⟩⋆⟨ refl ⟩
    ∙ sym FREECCC.×β₂)

  pr⋆pl : ∀ {X Y A B} (m : FREECCC.Hom[ X , Y ]) (n : FREECCC.Hom[ A , B ])
    → pr {X = X} n ⋆ₑ pl {A = B} m ≡ pb m n
  pr⋆pl m n = FREECCC.,p-extensionality
    ( FREECCC.⋆Assoc _ _ _ ∙ FREECCC.⟨ refl ⟩⋆⟨ FREECCC.×β₁ ⟩
    ∙ sym (FREECCC.⋆Assoc _ _ _) ∙ FREECCC.⟨ FREECCC.×β₁ ⟩⋆⟨ refl ⟩
    ∙ sym FREECCC.×β₁)
    ( FREECCC.⋆Assoc _ _ _ ∙ FREECCC.⟨ refl ⟩⋆⟨ FREECCC.×β₂ ⟩
    ∙ FREECCC.×β₂ ∙ sym FREECCC.×β₂)

  pr⋆pb : ∀ {X Y A B C} (m : FREECCC.Hom[ X , Y ])
    (n : FREECCC.Hom[ A , B ]) (n' : FREECCC.Hom[ B , C ])
    → pr {X = X} n ⋆ₑ pb m n' ≡ pb m (n ⋆ₑ n')
  pr⋆pb m n n' = FREECCC.,p-extensionality
    ( FREECCC.⋆Assoc _ _ _ ∙ FREECCC.⟨ refl ⟩⋆⟨ FREECCC.×β₁ ⟩
    ∙ sym (FREECCC.⋆Assoc _ _ _) ∙ FREECCC.⟨ FREECCC.×β₁ ⟩⋆⟨ refl ⟩
    ∙ sym FREECCC.×β₁)
    ( FREECCC.⋆Assoc _ _ _ ∙ FREECCC.⟨ refl ⟩⋆⟨ FREECCC.×β₂ ⟩
    ∙ sym (FREECCC.⋆Assoc _ _ _) ∙ FREECCC.⟨ FREECCC.×β₂ ⟩⋆⟨ refl ⟩
    ∙ FREECCC.⋆Assoc _ _ _ ∙ sym FREECCC.×β₂)

  pbId : ∀ {X Y A} (m : FREECCC.Hom[ X , Y ])
    → pb {A = A} m FREECCC.id ≡ pl m
  pbId m = FREECCC.,p-extensionality
    (FREECCC.×β₁ ∙ sym FREECCC.×β₁)
    (FREECCC.×β₂ ∙ FREECCC.⋆IdR _ ∙ sym FREECCC.×β₂)

  appOf : ∀ {X A B} → FREECCC.Hom[ X , CCCExpr._⇒_ A B ]
        → FREECCC.Hom[ CCCExpr._×_ X A , B ]
  appOf m = pl m ⋆ₑ FREECCC.app

  ldaβ : ∀ {X A B} (h : FREECCC.Hom[ CCCExpr._×_ X A , B ])
    → appOf (FREECCC.lda {c = A} {d = B} h) ≡ h
  ldaβ {A = A} {B = B} h = FREECCC.⇒ue.β A B

  ldaExt : ∀ {X A B} {m n : FREECCC.Hom[ X , CCCExpr._⇒_ A B ]}
    → appOf m ≡ appOf n → m ≡ n
  ldaExt {A = A} {B = B} = FREECCC.⇒ue.extensionality A B

  appOfSeq : ∀ {X Y A B} (m : FREECCC.Hom[ X , Y ])
    (n : FREECCC.Hom[ Y , CCCExpr._⇒_ A B ])
    → appOf (m ⋆ₑ n) ≡ pl m ⋆ₑ appOf n
  appOfSeq m n = cong (FREECCC._⋆ FREECCC.app) (sym (pl⋆pl m n))
               ∙ FREECCC.⋆Assoc _ _ _

  -- the action of the internal hom on a pair of maps
  conj : ∀ {A B A' B'} → FREECCC.Hom[ A' , A ] → FREECCC.Hom[ B , B' ]
       → FREECCC.Hom[ CCCExpr._⇒_ A B , CCCExpr._⇒_ A' B' ]
  conj {A = A} {B = B} {A' = A'} {B' = B'} u v =
    FREECCC.lda {c = A'} {d = B'}
      ((pr {X = CCCExpr._⇒_ A B} u ⋆ₑ FREECCC.app {c = A} {d = B}) ⋆ₑ v)

  conj⋆conj : ∀ {A B A' B' A'' B''}
    (u : FREECCC.Hom[ A' , A ]) (v : FREECCC.Hom[ B , B' ])
    (u' : FREECCC.Hom[ A'' , A' ]) (v' : FREECCC.Hom[ B' , B'' ])
    → conj u v ⋆ₑ conj u' v' ≡ conj (u' ⋆ₑ u) (v ⋆ₑ v')
  conj⋆conj u v u' v' = ldaExt
    ( appOfSeq (conj u v) (conj u' v')
    ∙ FREECCC.⟨ refl ⟩⋆⟨ ldaβ _ ⟩
    ∙ sym (FREECCC.⋆Assoc _ _ _)
    ∙ FREECCC.⟨ sym (FREECCC.⋆Assoc _ _ _) ⟩⋆⟨ refl ⟩
    ∙ FREECCC.⟨ FREECCC.⟨ pl⋆pr (conj u v) u'
                        ∙ sym (pr⋆pl (conj u v) u') ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩
    ∙ FREECCC.⟨ FREECCC.⋆Assoc _ _ _ ⟩⋆⟨ refl ⟩
    ∙ FREECCC.⟨ FREECCC.⟨ refl ⟩⋆⟨ ldaβ _ ⟩ ⟩⋆⟨ refl ⟩
    ∙ FREECCC.⟨ sym (FREECCC.⋆Assoc _ _ _) ⟩⋆⟨ refl ⟩
    ∙ FREECCC.⟨ FREECCC.⟨ sym (FREECCC.⋆Assoc _ _ _) ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩
    ∙ FREECCC.⟨ FREECCC.⟨ FREECCC.⟨ pr⋆pr u' u ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩
    ∙ FREECCC.⋆Assoc _ _ _
    ∙ sym (ldaβ _))

  conjId : ∀ {A B} → conj (FREECCC.id {x = A}) (FREECCC.id {x = B})
                   ≡ FREECCC.id
  conjId = ldaExt
    ( ldaβ _ ∙ FREECCC.⋆IdR _ ∙ FREECCC.⟨ prId ⟩⋆⟨ refl ⟩ ∙ FREECCC.⋆IdL _
    ∙ sym (FREECCC.⋆IdL _) ∙ FREECCC.⟨ sym plId ⟩⋆⟨ refl ⟩)

  module ⇒At {A B : FREECCC.C .ob}
    (f : CatIso FREECCC.C (T ⟅ A ⟆) A)
    (g : CatIso FREECCC.C (T ⟅ B ⟆) B) where

    TA = T ⟅ A ⟆
    TB = T ⟅ B ⟆
    ff = f .fst
    fi = f .snd .isIso.inv
    gf = g .fst
    gi = g .snd .isIso.inv

    E : FREECCC.Hom[ CCCExpr._⇒_ TA TB , CCCExpr._⇒_ A B ]
    E = conj fi gf

    Einv : FREECCC.Hom[ CCCExpr._⇒_ A B , CCCExpr._⇒_ TA TB ]
    Einv = conj ff gi

    expIso : CatIso FREECCC.C (T ⟅ CCCExpr._⇒_ A B ⟆) (CCCExpr._⇒_ A B)
    expIso = E , isiso Einv
      ( conj⋆conj ff gi fi gf
      ∙ cong₂ (conj {A = A} {B = B} {A' = A} {B' = B})
          (f .snd .isIso.sec) (g .snd .isIso.sec)
      ∙ conjId)
      ( conj⋆conj fi gf ff gi
      ∙ cong₂ (conj {A = TA} {B = TB} {A' = TA} {B' = TB})
          (f .snd .isIso.ret) (g .snd .isIso.ret)
      ∙ conjId)

    evalSq : FREECCC.app {c = TA} {d = TB} ⋆ₑ gf
           ≡ pb E ff ⋆ₑ FREECCC.app {c = A} {d = B}
    evalSq =
        FREECCC.⟨ sym (FREECCC.⋆IdL _) ⟩⋆⟨ refl ⟩
      ∙ FREECCC.⟨ FREECCC.⟨ sym prId ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩
      ∙ FREECCC.⟨ FREECCC.⟨ cong prTA (sym (f .snd .isIso.ret)) ⟩⋆⟨ refl ⟩
                ⟩⋆⟨ refl ⟩
      ∙ FREECCC.⟨ FREECCC.⟨ sym (pr⋆pr ff fi) ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩
      ∙ FREECCC.⟨ FREECCC.⋆Assoc _ _ _ ⟩⋆⟨ refl ⟩
      ∙ FREECCC.⋆Assoc _ _ _
      ∙ FREECCC.⟨ refl ⟩⋆⟨ sym (ldaβ _) ⟩
      ∙ sym (FREECCC.⋆Assoc _ _ _)
      ∙ FREECCC.⟨ pr⋆pl E ff ⟩⋆⟨ refl ⟩
      where
      prTA : FREECCC.Hom[ TA , TA ]
        → FREECCC.Hom[ CCCExpr._×_ (CCCExpr._⇒_ TA TB) TA
                     , CCCExpr._×_ (CCCExpr._⇒_ TA TB) TA ]
      prTA = pr {X = CCCExpr._⇒_ TA TB} {A = TA} {B = TA}

    lamSq : ∀ {Γ} (γ : CatIso FREECCC.C (T ⟅ Γ ⟆) Γ)
      (h : FREECCC.Hom[ CCCExpr._×_ Γ A , B ])
      → T ⟪ h ⟫ ⋆ₑ gf ≡ pb (γ .fst) ff ⋆ₑ h
      → T ⟪ FREECCC.lda {c = A} {d = B} h ⟫ ⋆ₑ E
        ≡ γ .fst ⋆ₑ FREECCC.lda {c = A} {d = B} h
    lamSq {Γ = Γ} γ h sq = ldaExt
      ( appOfSeq (FREECCC.lda {c = TA} {d = TB} (T ⟪ h ⟫)) E
      ∙ FREECCC.⟨ refl ⟩⋆⟨ ldaβ _ ⟩
      ∙ sym (FREECCC.⋆Assoc _ _ _)
      ∙ FREECCC.⟨ sym (FREECCC.⋆Assoc _ _ _) ⟩⋆⟨ refl ⟩
      ∙ FREECCC.⟨ FREECCC.⟨ pl⋆pr _ fi ∙ sym (pr⋆pl _ fi) ⟩⋆⟨ refl ⟩
                ⟩⋆⟨ refl ⟩
      ∙ FREECCC.⟨ FREECCC.⋆Assoc _ _ _ ⟩⋆⟨ refl ⟩
      ∙ FREECCC.⟨ FREECCC.⟨ refl ⟩⋆⟨ ldaβ (T ⟪ h ⟫) ⟩ ⟩⋆⟨ refl ⟩
      ∙ FREECCC.⋆Assoc _ _ _
      ∙ FREECCC.⟨ refl ⟩⋆⟨ sq ⟩
      ∙ sym (FREECCC.⋆Assoc _ _ _)
      ∙ FREECCC.⟨ pr⋆pb (γ .fst) fi ff ⟩⋆⟨ refl ⟩
      ∙ FREECCC.⟨ cong pbγ (f .snd .isIso.sec) ⟩⋆⟨ refl ⟩
      ∙ FREECCC.⟨ pbId (γ .fst) ⟩⋆⟨ refl ⟩
      ∙ FREECCC.⟨ refl ⟩⋆⟨ sym (ldaβ h) ⟩
      ∙ sym (appOfSeq (γ .fst) (FREECCC.lda {c = A} {d = B} h)))
      where
      pbγ : FREECCC.Hom[ A , A ]
        → FREECCC.Hom[ CCCExpr._×_ (T ⟅ Γ ⟆) A , CCCExpr._×_ Γ A ]
      pbγ z = pb (γ .fst) z

  ⇒-isoT : ∀ {A B} → CatIso FREECCC.C (T ⟅ A ⟆) A
         → CatIso FREECCC.C (T ⟅ B ⟆) B
         → CatIso FREECCC.C (T ⟅ CCCExpr._⇒_ A B ⟆) (CCCExpr._⇒_ A B)
  ⇒-isoT f g = ⇒At.expIso f g

  genSq⊤ : (u : FREECCC.Hom[ CCCExpr.⊤ , CCCExpr.⊤ ]) {X : FREECCC.C .ob}
    (e : FREECCC.Hom[ CCCExpr.⊤ , X ])
    → e ⋆ₑ FREECCC.id ≡ u ⋆ₑ e
  genSq⊤ u e = FREECCC.⋆IdR _
    ∙ sym (cong₂ _⋆ₑ_ (GC.⊤→⊤IsId FREECCC.term u) refl ∙ FREECCC.⋆IdL e)

-- The uniqueness principle, discharged for `T`.
ηT : NatIso T (Id {C = FREECCC.C})
ηT = FreeCCCFunctor≅ ×⇒QUIVER TCart IdCart T-1 Id-1 ⇒-isoT
  (λ f g → ⇒At.evalSq f g)
  (λ f g γ h sq → ⇒At.lamSq f g γ h sq)
  (mkElimInterpᴰ
    (λ { bool → idCatIso ; nat → idCatIso })
    (λ { tr → genSq⊤ _ (↑ₑ ×⇒QUIVER tr) , tt
       ; fl → genSq⊤ _ (↑ₑ ×⇒QUIVER fl) , tt
       ; ze → genSq⊤ _ (↑ₑ ×⇒QUIVER ze) , tt
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
  ⇒LamHolds f g γ h sq = ⇒At.lamSq f g γ h sq
