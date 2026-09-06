{-# OPTIONS --lossy-unification #-}
{-
  Equations solved in an ARBITRARY cartesian closed category.

  The first group is discharged by the macro: the user writes
  `solveCCC! 𝕊` and nothing else.  The second is the same solver
  called by hand, for the one equation whose two normal forms Agda's
  conversion checker will not compare directly.
-}
module Cubical.Tactics.CCCSolver.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Quiver.Base
open import Cubical.Data.Sum
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.CartesianClosed.Base

open import
  Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
  using (↑_ ; CCCExpr ; Quiver→×⇒Quiver)
open CCCExpr renaming (_×_ to _×ᵗ_ ; ⊤ to ⊤ᵗ ; _⇒_ to _⇒ᵗ_)
import Cubical.Categories.Instances.Free.CartesianClosedCategory.Forded
  as FCCC

open import Gluing.Bicategorical.NormalForms
open import Cubical.Tactics.CCCSolver.Solver
open import Cubical.Tactics.CCCSolver.Reflection

private
  variable ℓD ℓD' : Level

--------------------------------------------------------------------
-- Solved by the macro
--------------------------------------------------------------------

module Examples (𝕊 : SolvableCCC ℓD ℓD') where
  open CartesianClosedCategory (SolvableCCC.ccc 𝕊)

  -- product beta
  _ : ∀ {a b} {f : Hom[ a , b ]} → (f ,p id) ⋆ π₁ ≡ f
  _ = solveCCC! 𝕊

  -- product eta
  _ : ∀ {a b} → (π₁ ,p π₂) ≡ id {x = a × b}
  _ = solveCCC! 𝕊

  -- exponential eta
  _ : ∀ {a b} → lda app ≡ id {x = a ⇒ b}
  _ = solveCCC! 𝕊

  -- the swap is an involution
  _ : ∀ {a} → (π₂ ,p π₁) ⋆ (π₂ ,p π₁) ≡ id {x = a × a}
  _ = solveCCC! 𝕊

  -- a nest of identities, in the spirit of the category solver
  _ : ∀ {a b} {f : Hom[ a , b ]}
    → id ⋆ ((id ⋆ id ⋆ f) ⋆ id) ≡ (id ⋆ id) ⋆ (id ⋆ f)
  _ = solveCCC! 𝕊

  -- pairing commutes past the swap
  _ : ∀ {a b c} {f : Hom[ c , a ]} {g : Hom[ c , b ]}
    → (f ,p g) ⋆ (π₂ ,p π₁) ≡ (g ,p f)
  _ = solveCCC! 𝕊

  -- pair, swap twice, project: the swaps cancel
  _ : ∀ {a b} {h : Hom[ a , b ]}
    → (id ,p h) ⋆ ((π₂ ,p π₁) ⋆ ((π₂ ,p π₁) ⋆ π₁)) ≡ (id ,p h) ⋆ π₁
  _ = solveCCC! 𝕊

  -- BETA THROUGH AN EXPONENTIAL: abstract `f` over the terminal
  -- object, weaken it back along `!t`, and apply it to the argument
  _ : ∀ {a b} {f : Hom[ a , b ]}
    → ((!t ⋆ lda (π₂ ⋆ f)) ,p id) ⋆ app ≡ f
  _ = solveCCC! 𝕊

  -- UNDER A BINDER: the constant function `lda π₁`, applied to
  -- anything, is the identity
  _ : ∀ {a b} {g : Hom[ a , b ]} → (lda π₁ ,p g) ⋆ app ≡ id
  _ = solveCCC! 𝕊

  -- UNDER TWO BINDERS: `K = \x. \y. x`, applied twice, likewise
  _ : ∀ {a b} {g : Hom[ a , b ]}
    → (((lda (lda (π₁ ⋆ π₁)) ,p g) ⋆ app) ,p g) ⋆ app ≡ id
  _ = solveCCC! 𝕊

--------------------------------------------------------------------
-- Solved by calling the solver by hand.
--
-- CHURCH ARITHMETIC in any cartesian closed category: the numeral
-- two composed with itself is the numeral four.  Each side reduces
-- to `nfFour` in seconds, but comparing the two COMPUTATIONS to each
-- other -- which is what the macro's `refl` does -- does not
-- terminate, so this one is routed through the literal normal form.
--------------------------------------------------------------------

-- the walking arrow: one vertex, one endo-edge
Arrow : Quiver ℓ-zero ℓ-zero
Arrow = Unit , record { mor = Unit ; dom = λ _ → tt ; cod = λ _ → tt }

isSetArrowOb : isSet (Arrow .fst)
isSetArrowOb = isSetUnit

isSetArrowMor : isSet (QuiverOver.mor (Arrow .snd))
isSetArrowMor = isSetUnit

module _ (𝓓 : CartesianClosedCategory ℓD ℓD') where
  private
    module 𝓓 = CartesianClosedCategory 𝓓

  module _ (a : 𝓓.ob) (f : 𝓓.Hom[ a , a ]) where
    open Eval Arrow isSetArrowOb isSetArrowMor 𝓓
    open NF Arrow isSetArrowOb

    private
      module W = CartesianClosedCategory FREECCC

      ı : Interp
      ı = mkInterp (λ _ → a) (λ _ → f)

      X : Ty
      X = ↑ tt

      stepₑ : W.Hom[ (X ⇒ᵗ X) ×ᵗ X , X ] → W.Hom[ (X ⇒ᵗ X) ×ᵗ X , X ]
      stepₑ b = W._,p_ W.π₁ b W.⋆ W.app

      twiceₑ : W.Hom[ X ⇒ᵗ X , X ⇒ᵗ X ]
      twiceₑ = W.lda (stepₑ W.app)

      fourₑ : W.Hom[ X ⇒ᵗ X , X ⇒ᵗ X ]
      fourₑ = W.lda (stepₑ (stepₑ (stepₑ W.app)))

      nfFour : Nf (Tob (X ⇒ᵗ X) ∷ []) (Tob (X ⇒ᵗ X))
      nfFour =
        lamₙ (ne (appₙ (var (inr (inl refl)))
          (ne (appₙ (var (inr (inl refl)))
            (ne (appₙ (var (inr (inl refl)))
              (ne (appₙ (var (inr (inl refl)))
                (ne (var (inl refl)))))))))))

      twice⋆twice≡nfFour : eval (twiceₑ W.⋆ twiceₑ) ≡ nfFour
      twice⋆twice≡nfFour = refl

      four≡nfFour : eval fourₑ ≡ nfFour
      four≡nfFour = refl

    step𝓓 : 𝓓.Hom[ (a 𝓓.⇒ a) 𝓓.× a , a ] → 𝓓.Hom[ (a 𝓓.⇒ a) 𝓓.× a , a ]
    step𝓓 b = 𝓓._,p_ 𝓓.π₁ b 𝓓.⋆ 𝓓.app

    twice𝓓 : 𝓓.Hom[ a 𝓓.⇒ a , a 𝓓.⇒ a ]
    twice𝓓 = 𝓓.lda (step𝓓 𝓓.app)

    four𝓓 : 𝓓.Hom[ a 𝓓.⇒ a , a 𝓓.⇒ a ]
    four𝓓 = 𝓓.lda (step𝓓 (step𝓓 (step𝓓 𝓓.app)))

    church : twice𝓓 𝓓.⋆ twice𝓓 ≡ four𝓓
    church = solve ı (twiceₑ W.⋆ twiceₑ) fourₑ
      (twice⋆twice≡nfFour ∙ sym four≡nfFour)
