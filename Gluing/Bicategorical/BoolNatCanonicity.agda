{-# OPTIONS --lossy-unification #-}
{-
  The canonicity glue of the free cartesian closed category, built as
  the Artin gluing of `Pts = C [ ⊤ ,-]` and shown cartesian closed by
  `Gluing.Bicategorical.Artin`.  Nothing displayed is used.
-}
module Gluing.Bicategorical.BoolNatCanonicity where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Quiver.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Cartesian.More
open import Cubical.Categories.Limits.CartesianClosed.Base

open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Forded

open import Gluing.Bicategorical.Artin

open Category
open QuiverOver
open CartesianCategory
open CartesianClosedCategory

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

-- `Pts` preserves finite products because `⊤` is terminal; this is
-- the hypothesis the Artin exponential needs, so it is an argument.
PtsCart : CartesianFunctor (FREECCC .CC) (SET ℓ-zero)
PtsCart = CorepCartesian (FREECCC .CC) ⊤

Pts : Functor FREECCC.C (SET ℓ-zero)
Pts = PtsCart .fst

-- The glue is the comma category `SET ↓ Pts`, cartesian closed.
GLUE : CartesianClosedCategory (ℓ-suc ℓ-zero) ℓ-zero
GLUE .CC .C = ArtinGlue Pts
GLUE .CC .term = glueTerminal' Pts FREECCC.term
GLUE .CC .bp =
  glueBinProducts Pts FREECCC.bp BinProductsSET (PtsCart .snd)
GLUE .exps =
  glueExponentials Pts FREECCC.bp FREECCC.exps (PtsCart .snd)

-- Why this glue is NOT obtained from `Commaᴮ`: every 0-cell of
-- `CAT ℓ ℓ'` has the same object level, and the two here do not.
_ : Category ℓ-zero ℓ-zero
_ = FREECCC.C

_ : Category (ℓ-suc ℓ-zero) ℓ-zero
_ = SET ℓ-zero

-- Canonicity over this glue is run in
-- `Gluing.Bicategorical.CCCCanonicity`, through the same structure
-- forded over the syntax in `Gluing.Bicategorical.Section`.
--
-- It does not follow from `rec` with plain categories alone:
-- `FreeCartesianClosedCategory`'s recursor produces a functor into
-- `GLUE`, but the only uniqueness principle for functors out of it
-- (`FreeCCCFunctor≅`) yields a `NatIso`, not the equality
-- `π₂ ∘F S ≡ Id` that reading canonical forms back off the glue
-- needs.  A strict section exists only through `elimLocal`, whose
-- statement is displayed.

-- The syntactic data the canonicity statements are about.
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

{-
  What a natural isomorphism `π₂ ∘F S ≅ Id` would buy.  Its component
  at `⊤` is the identity, and its component `η` at `↑ nat` satisfies
  the two naturality squares below; those already force `η` to fix
  every numeral, so canonicity transfers through a `NatIso` and does
  not need the strict equality `π₂ ∘F S ≡ Id`.
-}
module _ (η : FREECCC.Hom[ ↑ nat , ↑ nat ])
  (ηze : [ze] ⋆ₑ η ≡ [ze])
  (ηsu : [su] ⋆ₑ η ≡ η ⋆ₑ [su]) where

  numeralsFixed : (n : ℕ) → ＂ n ＂ ⋆ₑ η ≡ ＂ n ＂
  numeralsFixed zero = ηze
  numeralsFixed (suc n) =
      FREECCC.⋆Assoc _ _ _
    ∙ cong (＂ n ＂ ⋆ₑ_) ηsu
    ∙ sym (FREECCC.⋆Assoc _ _ _)
    ∙ cong (_⋆ₑ [su]) (numeralsFixed n)

module _ (θ : FREECCC.Hom[ ↑ bool , ↑ bool ])
  (θtr : [t] ⋆ₑ θ ≡ [t]) (θfl : [f] ⋆ₑ θ ≡ [f]) where

  booleansFixed : (b : Bool) → (if b then [t] else [f]) ⋆ₑ θ
                             ≡ (if b then [t] else [f])
  booleansFixed true = θtr
  booleansFixed false = θfl
