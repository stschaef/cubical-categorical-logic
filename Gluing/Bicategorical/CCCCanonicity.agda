{-# OPTIONS --lossy-unification #-}
{-
  Canonicity for the free CARTESIAN CLOSED category, run on the comma
  glue `SET ↓ Pts` of `Gluing.Bicategorical.Artin` -- the category the
  `CAT` comma object supplies -- rather than on `reindex SETᴰ Pts`.

  The glue's terminal object, binary products and exponentials are the
  classical Artin ones; only their base component is forded away, in
  `Gluing.Bicategorical.Section`, so that the free CCC's eliminator
  produces a section that is strictly over the identity.
-}
module Gluing.Bicategorical.CCCCanonicity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Quiver.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Cartesian.More
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.CartesianClosedV

open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Forded
  as FreeCCC

open import Gluing.Bicategorical.Section
open import Gluing.Canonicity

open Category
open Functor
open QuiverOver
open CartesianCategory
open CartesianCategoryᴰ
open CartesianClosedCategory
open CartesianClosedCategoryᴰ
open Section

data OB : Type ℓ-zero where
  bool nat : OB

data MOR : Type ℓ-zero where
  tr fl ze su : MOR

×⇒QUIVER : ×⇒Quiver ℓ-zero ℓ-zero
×⇒QUIVER .×⇒Quiver.ob = OB
×⇒QUIVER .×⇒Quiver.Q .mor = MOR
×⇒QUIVER .×⇒Quiver.Q .dom tr = ⊤
×⇒QUIVER .×⇒Quiver.Q .dom fl = ⊤
×⇒QUIVER .×⇒Quiver.Q .dom ze = ⊤
×⇒QUIVER .×⇒Quiver.Q .dom su = ↑ nat
×⇒QUIVER .×⇒Quiver.Q .cod tr = ↑ bool
×⇒QUIVER .×⇒Quiver.Q .cod fl = ↑ bool
×⇒QUIVER .×⇒Quiver.Q .cod ze = ↑ nat
×⇒QUIVER .×⇒Quiver.Q .cod su = ↑ nat

FREECCC : CartesianClosedCategory ℓ-zero ℓ-zero
FREECCC = FreeCartesianClosedCategory ×⇒QUIVER

module FREECCC = CartesianClosedCategory FREECCC

[bool] : Type ℓ-zero
[bool] = FREECCC.Hom[ ⊤ , ↑ bool ]

[t] [f] : [bool]
[t] = ↑ₑ ×⇒QUIVER tr
[f] = ↑ₑ ×⇒QUIVER fl

[nat] : Type ℓ-zero
[nat] = FREECCC.Hom[ ⊤ , ↑ nat ]

[ze] : [nat]
[ze] = ↑ₑ ×⇒QUIVER ze

[su] : FREECCC.Hom[ ↑ nat , ↑ nat ]
[su] = ↑ₑ ×⇒QUIVER su

＂_＂ : ℕ → [nat]
＂ zero ＂ = [ze]
＂ suc n ＂ = ＂ n ＂ ⋆ₑ [su]

fromBool : Bool → [bool]
fromBool true = [t]
fromBool false = [f]

-- `Pts` preserves finite products because `⊤` is terminal
PtsCart : CartesianFunctor (FREECCC .CC) (SET ℓ-zero)
PtsCart = CorepCartesian (FREECCC .CC) ⊤

Pts : Functor FREECCC.C (SET ℓ-zero)
Pts = PtsCart .fst

-- the comma glue, displayed over the syntax, with the Artin
-- terminal object, binary products and exponentials
GLᴰ : Categoryᴰ FREECCC.C (ℓ-suc ℓ-zero) ℓ-zero
GLᴰ = Glᴰ Pts

GLUEᴰ : CartesianClosedCategoryᴰ FREECCC (ℓ-suc ℓ-zero) ℓ-zero
GLUEᴰ .CCᴰ .Cᴰ = GLᴰ
GLUEᴰ .CCᴰ .termᴰ = glTermᴰ Pts FREECCC.term
GLUEᴰ .CCᴰ .bpᴰ = glBpᴰ Pts FREECCC.bp (PtsCart .snd)
GLUEᴰ .expᴰ = glExpᴰ Pts FREECCC.bp (PtsCart .snd) FREECCC.exps

-- the fundamental lemma: canonical forms for the generators
INTERP : ElimInterpᴰ ×⇒QUIVER GLUEᴰ
INTERP = mkElimInterpᴰ
  (λ { bool → (Bool , isSetBool) , fromBool
     ; nat → (ℕ , isSetℕ) , ＂_＂ })
  (λ { tr → (λ _ → true)
             , λ u → cong₂ _⋆ₑ_ (⊤→⊤IsId FREECCC.term u) refl
                   ∙ FREECCC.⋆IdL _
     ; fl → (λ _ → false)
             , λ u → cong₂ _⋆ₑ_ (⊤→⊤IsId FREECCC.term u) refl
                   ∙ FREECCC.⋆IdL _
     ; ze → (λ _ → 0)
             , λ u → cong₂ _⋆ₑ_ (⊤→⊤IsId FREECCC.term u) refl
                   ∙ FREECCC.⋆IdL _
     ; su → suc , λ n → refl })

{-
  The section is strictly over the identity -- a `GlobalSection GLᴰ`
  -- which is what makes the canonical form land at `e` itself rather
  than at some `π₂ (S e)`.  The `NatIso` route of
  `Gluing.Bicategorical.BoolNatCanonicity` is not used.
-}
SEC : GlobalSection GLᴰ
SEC = FreeCCC.elim ×⇒QUIVER GLUEᴰ INTERP

canonicalize-nat : (e : [nat]) → fiber ＂_＂ e
canonicalize-nat e =
  SEC .F-homᴰ e .fst FREECCC.id
  , sym (SEC .F-homᴰ e .snd FREECCC.id) ∙ FREECCC.⋆IdL e

canonicalize-bool : (e : [bool]) → (e ≡ [t]) ⊎ (e ≡ [f])
canonicalize-bool e =
  go (SEC .F-homᴰ e .fst FREECCC.id) (SEC .F-homᴰ e .snd FREECCC.id)
  where
  go : (b : Bool) → Pts .F-hom e FREECCC.id ≡ fromBool b
    → (e ≡ [t]) ⊎ (e ≡ [f])
  go true p = inl (sym (FREECCC.⋆IdL e) ∙ p)
  go false p = inr (sym (FREECCC.⋆IdL e) ∙ p)

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

canonicity-bool : Iso [bool] Bool
canonicity-bool =
  BoolIso.canonicity-bool [t] [f] evalBool refl refl canonicalize-bool

canonicity-nat : Iso [nat] ℕ
canonicity-nat =
  NatIso.canonicity-nat ＂_＂ evalNat evalNat-＂_＂ canonicalize-nat
