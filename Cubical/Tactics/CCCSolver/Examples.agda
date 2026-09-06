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

module _ (𝕊 : SolvableCCC ℓD ℓD') where
  private
    module 𝓓 = CartesianClosedCategory (SolvableCCC.ccc 𝕊)

  module _ (a : 𝓓.ob) (f : 𝓓.Hom[ a , a ]) where
    ⇒η : 𝓓.lda {c = a} {d = a} (𝓓.app {c = a} {d = a}) ≡ 𝓓.id
    ⇒η = solveCCC! 𝕊

    ×η : 𝓓._,p_ {a = a} {b = a} 𝓓.π₁ 𝓓.π₂ ≡ 𝓓.id
    ×η = solveCCC! 𝕊

    ×β : 𝓓._,p_ {a = a} {b = a} f 𝓓.id 𝓓.⋆ 𝓓.π₁ ≡ f
    ×β = solveCCC! 𝕊

    swap𝓓 : 𝓓.Hom[ a 𝓓.× a , a 𝓓.× a ]
    swap𝓓 = 𝓓._,p_ {a = a} {b = a} 𝓓.π₂ 𝓓.π₁

    swap-invol : swap𝓓 𝓓.⋆ swap𝓓 ≡ 𝓓.id
    swap-invol = solveCCC! 𝕊

    -- used inside an `≡⟨ ⟩` chain, exactly as `solveCat!` is
    swap³ : (swap𝓓 𝓓.⋆ swap𝓓) 𝓓.⋆ swap𝓓 ≡ swap𝓓
    swap³ =
      (swap𝓓 𝓓.⋆ swap𝓓) 𝓓.⋆ swap𝓓
        ≡⟨ solveCCC! 𝕊 ⟩
      𝓓.id 𝓓.⋆ swap𝓓
        ≡⟨ 𝓓.⋆IdL swap𝓓 ⟩
      swap𝓓 ∎


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
