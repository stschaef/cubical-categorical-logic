{-# OPTIONS --lossy-unification #-}
{-
  Kleisli objects for a formal monad in a bicategory.

  `_^opᴮ` reverses 1-cells and fixes 2-cells, so a monad in `B ^opᴮ`
  is a monad in `B` with its two unit laws exchanged, and the algebra
  prestack of the dual monad sends a probe `b` to the category of
  pairs `(y : a → b , t ⋆₁ y ⇒ y)`: the lax cocones under the monad.
  So the Kleisli object IS the EM object of `B ^opᴮ`.

  (`_^coᴮ` is the wrong duality here: it reverses the 2-cells, so a
  monad in `B ^coᴮ` is a comonad in `B` and its EM object is the
  coalgebra object, not the Kleisli object.)
-}
module Cubical.Categories.Bicategory.Monad.KleisliObject where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Properties.Coherence
open import Cubical.Categories.Bicategory.Constructions.Op
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Universal.Base
open import Cubical.Categories.Bicategory.Monad.Base
open import Cubical.Categories.Bicategory.Monad.Morphism
open import Cubical.Categories.Bicategory.Monad.Algebra
open import Cubical.Categories.Bicategory.Monad.EMObject

private
  variable
    ℓ ℓ' ℓ'' : Level

open Functor
open isIso

-- The data is unchanged; only the two unit laws swap and the
-- associativity law is transported across the associator's inverse.
module _ {B : Bicategory ℓ ℓ' ℓ''} {a : Bicategory.0Cell B} where
  private
    module B = Bicategory B

  opMonadOn : MonadOn B a → MonadOn (B ^opᴮ) a
  opMonadOn M .MonadOn.t = MonadOn.t M
  opMonadOn M .MonadOn.η = MonadOn.η M
  opMonadOn M .MonadOn.μ = MonadOn.μ M
  opMonadOn M .MonadOn.idL = MonadOn.idR M
  opMonadOn M .MonadOn.idR = MonadOn.idL M
  opMonadOn M .MonadOn.μAssoc =
      B.⟨⟩⋆₂⟨ sym (MonadOn.μAssoc M) ⟩
    ∙ sym (B.⋆₂Assoc _ _ _)
    ∙ B.⟨ αI B (MonadOn.t M) (MonadOn.t M) (MonadOn.t M) .snd .sec ⟩⋆₂⟨⟩
    ∙ B.⋆₂IdL _

module _ (B : Bicategory ℓ ℓ' ℓ'') (a : Bicategory.0Cell B)
  (M : MonadOn B a) where

  KleisliPrestack : Prestack (B ^opᴮ) (ℓ-max ℓ' ℓ'') ℓ''
  KleisliPrestack = EMPrestack (B ^opᴮ) a (opMonadOn M)

  KleisliObjectᴮ : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  KleisliObjectᴮ = EMObjectᴮ (B ^opᴮ) a (opMonadOn M)

module _ (B : Bicategory ℓ ℓ' ℓ'') where
  hasKleisliObjectsᴮ : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  hasKleisliObjectsᴮ =
    {a : Bicategory.0Cell B} (M : MonadOn B a) → KleisliObjectᴮ B a M

  KleisliObjectOfMonadᴮ : Monad B → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  KleisliObjectOfMonadᴮ M = KleisliObjectᴮ B (Monad.a M) (fromMonad B M)

module KleisliObjectᴮNotation {B : Bicategory ℓ ℓ' ℓ''}
  {a : Bicategory.0Cell B} {M : MonadOn B a} (K : KleisliObjectᴮ B a M)
  where
  private
    module B = Bicategory B
    module M = MonadOn M
  open EMObjectᴮNotation K public renaming (uᴮ to fᴮ; ξᴮ to κᴮ)

  -- `fᴮ : a → vertex` is the free 1-cell and `κᴮ` its action; both
  -- are `EMObjectᴮNotation`'s at `B ^opᴮ`, read back in `B`.
  free : B.1Cell a vertex
  free = fᴮ

  freeAction : B.2Cell (M.t B.⋆₁ free) free
  freeAction = κᴮ

{- The comparison 1-cell.  It is `intro` for the Kleisli object at the
   lax cocone whose carrier classifies the FREE algebra `(t , μ)`; its
   action is forced by the EM object's full faithfulness. -}
module Comparison {B : Bicategory ℓ ℓ' ℓ''}
  {a : Bicategory.0Cell B} {M : MonadOn B a}
  (E : EMObjectᴮ B a M) (K : KleisliObjectᴮ B a M) where
  private
    module B = Bicategory B
    module M = MonadOn M
  module E = EMObjectᴮNotation E
  module K = KleisliObjectᴮNotation K
  module A = EMPre {B = B} {a = a} M

  open Algebra
  open AlgebraMor

  -- The free algebra on the carrier: the monad's own multiplication.
  Fᴬ : A.Alg a
  Fᴬ .x = M.t
  Fᴬ .ξ = M.μ
  Fᴬ .α-unit = M.idR
  Fᴬ .α-mult = M.μAssoc

  private
    u : B.1Cell E.vertex a
    u = E.uᴮ

    y : B.1Cell a E.vertex
    y = E.introᴱ Fᴬ

    bf : B.2Cell (y B.⋆₁ u) M.t
    bf = E.β Fᴬ .fst .f

    bi : B.2Cell M.t (y B.⋆₁ u)
    bi = E.β Fᴬ .snd .inv .f

    bfbi : (bf B.⋆₂ bi) ≡ B.id₂
    bfbi = cong (λ m → m .f) (E.β Fᴬ .snd .ret)

    bibf : (bi B.⋆₂ bf) ≡ B.id₂
    bibf = cong (λ m → m .f) (E.β Fᴬ .snd .sec)

    -- α⁺, the comparison, μ and β⁻¹, composed in the EM category.
    c₁ : AlgebraMor B a M a (A.reindAlg (M.t B.⋆₁ y) E.element)
                            (A.reindAlg M.t (A.reindAlg y E.element))
    c₁ .f = B.α⁺ M.t y u
    c₁ .f-comm = A.ν⁻Cond y M.t E.element

    c₃ : AlgebraMor B a M a (A.reindAlg M.t Fᴬ) Fᴬ
    c₃ .f = M.μ
    c₃ .f-comm = B.⋆₂Assoc _ _ _ ∙ M.μAssoc

    Φ : AlgebraMor B a M a (A.reindAlg (M.t B.⋆₁ y) E.element)
                           (A.reindAlg y E.element)
    Φ = c₁ ⋆⟨ A.EMCat a ⟩
          (A.emReind M.t .F-hom (E.β Fᴬ .fst) ⋆⟨ A.EMCat a ⟩
            (c₃ ⋆⟨ A.EMCat a ⟩ E.β Fᴬ .snd .inv))

    ζ : B.2Cell (M.t B.⋆₁ y) y
    ζ = E.intro₂ {x = a} {h = M.t B.⋆₁ y} {k = y} Φ

    ζ▷u : (ζ B.▷w u) ≡ Φ .f
    ζ▷u = cong (λ m → m .f)
      (E.intro₂-β {x = a} {h = M.t B.⋆₁ y} {k = y} Φ)

    opAssoc : (B.α⁻ M.t M.t M.t B.⋆₂ ((M.μ B.▷w M.t) B.⋆₂ M.μ))
            ≡ ((M.t B.◁w M.μ) B.⋆₂ M.μ)
    opAssoc = MonadOn.μAssoc (opMonadOn M)

    law1 : ((M.η B.▷w y) B.⋆₂ ζ) ≡ B.λ⁺ y
    law1 = E.uᴮ-ext _ _ eq
      where
      eq : (((M.η B.▷w y) B.⋆₂ ζ) B.▷w u) ≡ (B.λ⁺ y B.▷w u)
      eq =
          ▷wSeq B (M.η B.▷w y) ζ u
        ∙ B.⟨⟩⋆₂⟨ ζ▷u ⟩
        ∙ pushr B (α⁺natL B M.η y u) _
        ∙ B.⟨⟩⋆₂⟨ pushr B (▷◁exch B M.η bf) _ ⟩
        ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ pushn B M.idL bi ⟩ ⟩
        ∙ B.⟨⟩⋆₂⟨ pushr B (λ-nat B bf) bi ⟩
        ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ bfbi ⟩ ∙ B.⋆₂IdR _ ⟩
        ∙ αλ B y u

    law2 : (B.α⁻ M.t M.t y B.⋆₂ ((M.μ B.▷w y) B.⋆₂ ζ))
         ≡ ((M.t B.◁w ζ) B.⋆₂ ζ)
    law2 = E.uᴮ-ext _ _ (lhs ∙ sym rhs)
      where
      Aty = B.α⁺ M.t y u
      Kb  = M.t B.◁w bf
      tail = M.μ B.⋆₂ bi

      N : B.2Cell ((M.t B.⋆₁ (M.t B.⋆₁ y)) B.⋆₁ u) (y B.⋆₁ u)
      N = B.α⁺ M.t (M.t B.⋆₁ y) u
            B.⋆₂ ((M.t B.◁w Aty)
              B.⋆₂ ((M.t B.◁w Kb) B.⋆₂ ((M.t B.◁w M.μ) B.⋆₂ tail)))

      ζbf : ((ζ B.▷w u) B.⋆₂ bf) ≡ (Aty B.⋆₂ (Kb B.⋆₂ M.μ))
      ζbf =
          B.⟨ ζ▷u ⟩⋆₂⟨⟩
        ∙ aR2 B Aty (Kb B.⋆₂ tail) bf
        ∙ B.⟨⟩⋆₂⟨ aR2 B Kb tail bf ⟩
        ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ aR2 B M.μ bi bf ⟩ ⟩
        ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ bibf ⟩ ∙ B.⋆₂IdR _ ⟩ ⟩

      lhs : ((B.α⁻ M.t M.t y B.⋆₂ ((M.μ B.▷w y) B.⋆₂ ζ)) B.▷w u) ≡ N
      lhs =
          ▷3 B (B.α⁻ M.t M.t y) (M.μ B.▷w y) ζ u
        ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ ζ▷u ⟩ ⟩
        ∙ B.⟨⟩⋆₂⟨ pushr B (α⁺natL B M.μ y u) _ ⟩
        ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ pushr B (▷◁exch B M.μ bf) _ ⟩ ⟩
        ∙ pushr B (sym (pentP4 B M.t M.t y u)) _
        ∙ B.⟨⟩⋆₂⟨ aR2 B (M.t B.◁w Aty) (B.α⁻ M.t M.t (y B.⋆₁ u)) _ ⟩
        ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨
            pushr B (sym (α⁻natR B M.t M.t bf)) _ ⟩ ⟩
        ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ rep3 B opAssoc bi ⟩ ⟩ ⟩

      rhs : (((M.t B.◁w ζ) B.⋆₂ ζ) B.▷w u) ≡ N
      rhs =
          ▷wSeq B (M.t B.◁w ζ) ζ u
        ∙ B.⟨⟩⋆₂⟨ ζ▷u ⟩
        ∙ pushr B (α⁺natM B M.t ζ u) _
        ∙ B.⟨⟩⋆₂⟨ sym (aR2 B (M.t B.◁w (ζ B.▷w u)) Kb tail)
                ∙ B.⟨ sym (◁wSeq B M.t (ζ B.▷w u) bf) ⟩⋆₂⟨⟩
                ∙ B.⟨ M.t B.◁⟨ ζbf ⟩ ⟩⋆₂⟨⟩
                ∙ B.⟨ ◁3 B M.t Aty Kb M.μ ⟩⋆₂⟨⟩
                ∙ aR3 B (M.t B.◁w Aty) (M.t B.◁w Kb) (M.t B.◁w M.μ)
                       tail ⟩

  -- The lax cocone under the monad classifying the free algebra.
  freeCocone : Algebra (B ^opᴮ) a (opMonadOn M) E.vertex
  freeCocone .x = y
  freeCocone .ξ = ζ
  freeCocone .α-unit = law1
  freeCocone .α-mult = law2

  comparisonᴮ : B.1Cell K.vertex E.vertex
  comparisonᴮ = K.introᴱ freeCocone

  -- Canonicity: composing with the free 1-cell recovers the 1-cell
  -- that classifies the free algebra.
  comparisonᴮβ : (K.free B.⋆₁ comparisonᴮ) B.≅₂ y
  comparisonᴮβ = K.introᴱβ freeCocone
