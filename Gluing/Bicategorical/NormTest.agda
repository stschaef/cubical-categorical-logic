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

  -- higher order: `twice` normalizes to `\f. \x. f (f x)`
  _ : nfTwice
    ≡ lamₙ (ne (appₙ (var (inr (inl refl)))
             (ne (appₙ (var (inr (inl refl)))
               (ne (var (inl refl)))))))
  _ = refl

  -- Church one, at the same type: a DIFFERENT normal form, so the
  -- check above is discriminating and not vacuous.
  once : 𝒞.Hom[ A ⇒ᵗ A , A ⇒ᵗ A ]
  once = 𝒞.lda fx

  nfOnce : Nf (Tob (A ⇒ᵗ A) ∷ []) (Tob (A ⇒ᵗ A))
  nfOnce = normalize Q isSetOb isSetMor once

  _ : nfOnce
    ≡ lamₙ (ne (appₙ (var (inr (inl refl))) (ne (var (inl refl)))))
  _ = refl

  -- a generator under a binder: `\f. g (f x)` -- eta-expanded, so
  -- the argument is the bound variable
  gafter : 𝒞.Hom[ A ⇒ᵗ A , A ⇒ᵗ A ]
  gafter = 𝒞.lda (fx 𝒞.⋆ g)

  _ : normalize Q isSetOb isSetMor gafter
    ≡ lamₙ (ne (genₙ tt
        (ne (appₙ (var (inr (inl refl))) (ne (var (inl refl)))))))
  _ = refl

  -- two nested binders: `K = \x. \y. x`, reaching under both
  konst : 𝒞.Hom[ A , A ⇒ᵗ (A ⇒ᵗ A) ]
  konst = 𝒞.lda (𝒞.lda (𝒞.π₁ 𝒞.⋆ 𝒞.π₁))

  _ : normalize Q isSetOb isSetMor konst
    ≡ lamₙ (lamₙ (ne (var (inr (inr (inl refl))))))
  _ = refl
