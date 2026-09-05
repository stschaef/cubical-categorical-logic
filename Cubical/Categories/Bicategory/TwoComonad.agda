{-# OPTIONS --lossy-unification #-}
{-
  2-comonads on a bicategory: a pseudofunctor `T : K → K` with a
  counit `ε : T ⇒ Id` and a comultiplication `δ : T ⇒ T ∘ T`.

  A 2-monad is a monad in the 2-category of lax functors, lax natural
  transformations and modifications, so `η` and `μ` are *1-cells*
  there, not 2-cells.  Dualising them therefore needs the duality
  that reverses the 1-cells of `Lax(K,K)`, and that is `_^opᴮ`, not
  `_^coᴮ`: `Lax(K ^op, K ^op)` is `Lax(K,K) ^op`.

  `_^coᴮ` reverses only the modifications, so `TwoMonad (K ^coᴮ)` is
  still a 2-monad — with oplax naturality — see `coIsNotDual` below.
  `_^coᴮ` *is* the right duality for the *formal* monads of
  `Cubical.Categories.Bicategory.Monad`, whose unit and multiplication
  are 2-cells; `Comonad` there is `Monad (K ^coᴮ)`.
-}
module Cubical.Categories.Bicategory.TwoComonad where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.TwoMonad
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Constructions.Op
open import Cubical.Categories.Bicategory.Constructions.Co
open import Cubical.Categories.Bicategory.Transformation

private
  variable
    ℓ ℓ' ℓ'' : Level

open LaxFunctor
open LaxNatTrans

TwoComonad : Bicategory ℓ ℓ' ℓ'' → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
TwoComonad K = TwoMonad (K ^opᴮ)

{- The identity 2-comonad, free from the identity 2-monad on `K ^opᴮ`. -}
idTwoComonad : (K : Bicategory ℓ ℓ' ℓ'') → TwoComonad K
idTwoComonad K = idTwoMonad (K ^opᴮ)

module TwoComonadNotation {K : Bicategory ℓ ℓ' ℓ''} (D : TwoComonad K) where
  private
    module K = Bicategory K
  open TwoMonad D public using (T; Tl; unitL; unitR; assoc)

  T₀ : K.ob → K.ob
  T₀ = Tl .F-ob

  T₁ : {x y : K.ob} → K.1Cell x y → K.1Cell (T₀ x) (T₀ y)
  T₁ {x} {y} f = LaxFunctor.F-1cell Tl {y} {x} f

  ε : (x : K.ob) → K.1Cell (T₀ x) x
  ε = TwoMonad.η D .N-1cell

  δ : (x : K.ob) → K.1Cell (T₀ x) (T₀ (T₀ x))
  δ = TwoMonad.μ D .N-1cell

{- The counit and comultiplication point the right way, definitionally. -}
module _ {K : Bicategory ℓ ℓ' ℓ''} (D : TwoComonad K) where
  private
    module K = Bicategory K
  open TwoComonadNotation D

  εDir : (x : K.ob) → K.1Cell (T₀ x) x
  εDir x = ε x

  δDir : (x : K.ob) → K.1Cell (T₀ x) (T₀ (T₀ x))
  δDir x = δ x

  εIsUnit : (x : K.ob) → ε x ≡ TwoMonad.η D .N-1cell x
  εIsUnit _ = refl

  δIsMult : (x : K.ob) → δ x ≡ TwoMonad.μ D .N-1cell x
  δIsMult _ = refl

{-
  The `co` dual does *not* reverse the unit: in `TwoMonad (K ^coᴮ)`
  the components of `η` still run `x → T x`, so it is a 2-monad, not
  a 2-comonad.
-}
module coIsNotDual {K : Bicategory ℓ ℓ' ℓ''} (M : TwoMonad (K ^coᴮ)) where
  private
    module K = Bicategory K
    module M = TwoMonad M

  ηStillAUnit : (x : K.ob) → K.1Cell x (M.Tl .F-ob x)
  ηStillAUnit = M.η .N-1cell

  μStillAMult : (x : K.ob)
    → K.1Cell (M.Tl .F-ob (M.Tl .F-ob x)) (M.Tl .F-ob x)
  μStillAMult = M.μ .N-1cell
