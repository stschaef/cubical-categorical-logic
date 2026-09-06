{-# OPTIONS --lossy-unification #-}
{- Does the normalizer compute?  A one-object, one-generator quiver,
   and a handful of `refl` checks on concrete morphisms. -}
module Gluing.Bicategorical.NormTest where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Quiver.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base

import Cubical.Categories.Instances.Free.CartesianClosedCategory.Forded
  as FCCC
open import
  Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
  using (Quiver→×⇒Quiver ; ↑_ ; CCCExpr)
open CCCExpr renaming (_×_ to _×ᵗ_ ; ⊤ to ⊤ᵗ ; _⇒_ to _⇒ᵗ_)

open import Gluing.Bicategorical.NormalForms
open import Gluing.Bicategorical.RecNormalization

-- the walking arrow quiver: objects {a}, one morphism g : a → a
Ob : Type
Ob = Unit

Mor : Type
Mor = Unit

Q : Quiver ℓ-zero ℓ-zero
Q = Ob , record { mor = Mor ; dom = λ _ → tt ; cod = λ _ → tt }

isSetOb : isSet (Q .fst)
isSetOb = isSetUnit

isSetMor : isSet (QuiverOver.mor (Q .snd))
isSetMor = isSetUnit

open NF Q isSetOb

private
  module 𝒞 = CartesianClosedCategory FREECCC

  A : Ty
  A = ↑ tt

  g : 𝒞.Hom[ A , A ]
  g = FCCC.↑ₑ (Quiver→×⇒Quiver Q) tt

  -- normalize the generator `g : a → a`
  nfG : Nf (A ∷ []) A
  nfG = normalizeAt Q isSetOb isSetMor tt tt g

  -- expected: the neutral `g` applied to the variable
  _ : nfG ≡ ne (genₙ tt (ne (var (inl refl))))
  _ = refl

  -- a beta redex: <g , id> then pi1.  Must REDUCE to g's normal form,
  -- not merely embed.
  redex : 𝒞.Hom[ A , A ]
  redex = 𝒞._,p_ g (𝒞.id) 𝒞.⋆ 𝒞.π₁

  _ : normalizeAt Q isSetOb isSetMor tt tt redex ≡ nfG
  _ = refl

  -- the identity normalizes to the variable
  _ : normalizeAt Q isSetOb isSetMor tt tt (𝒞.id) ≡ ne (var (inl refl))
  _ = refl

  -- HIGHER ORDER: twice = lam f. lam x. f (f x), at (A ⇒ A) ⇒ A ⇒ A.
  -- Forces `reify` under two binders, which is where `liftRen` runs.
  fx : 𝒞.Hom[ (A ⇒ᵗ A) ×ᵗ A , A ]
  fx = 𝒞.app

  ffx : 𝒞.Hom[ (A ⇒ᵗ A) ×ᵗ A , A ]
  ffx = 𝒞._,p_ 𝒞.π₁ fx 𝒞.⋆ 𝒞.app

  twice : 𝒞.Hom[ A ⇒ᵗ A , A ⇒ᵗ A ]
  twice = 𝒞.lda ffx

  Tob : Ty → Ty
  Tob X = Functor.F-ob (T Q isSetOb isSetMor) X

  nfTwice : Nf (Tob (A ⇒ᵗ A) ∷ []) (Tob (A ⇒ᵗ A))
  nfTwice = normalize Q isSetOb isSetMor twice

  -- does `T` compute on objects?
  _ : Tob A ≡ A
  _ = refl

  -- at a compound type?
  _ : Tob (A ⇒ᵗ A) ≡ A ⇒ᵗ A
  _ = refl

  -- HIGHER ORDER DOES NOT REDUCE, and the obstruction is precise.
  -- `nfTwice` is well-typed, and `T` computes on objects at every
  -- type (both probes above are `refl`), but asking for its value
  -- gets stuck at
  --
  --   PullbackNotation.pbIntro (Artin.PSHPullbacks Ren _)
  --
  -- The exponential's glue object is a pullback in presheaves, and
  -- `PSHPullbacks`'s `universal` is given as
  -- `isIsoToIsEquiv (inv , sec , ret)` fully inlined -- which it has
  -- to be, since a `where`-block joins the same mutual block and the
  -- termination checker rejects it.  That packaging is opaque, so
  -- `pbIntro` never unfolds.
  --
  -- In `SET` the Artin exponential's pullback degenerates to a
  -- Σ-type over a proposition, which does compute; the generic
  -- construction over an abstract `Pullbacks` does not.  A pointwise
  -- presheaf pullback with a transparent `pbIntro` should restore it.
