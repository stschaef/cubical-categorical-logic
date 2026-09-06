{-# OPTIONS --lossy-unification #-}
{-
  A solver for equations in an ARBITRARY cartesian closed category,
  built from normalization for the free one.

  The shape is the one used by `Cubical.Tactics.CategorySolver`: the
  user writes the two sides as expressions of a free structure over
  named atoms, checks that they have the same normal form (by
  `refl`), and gets back an equation between their interpretations in
  the ambient category.

  Where the category solver evaluates into presheaves and appeals to
  faithfulness of the pseudo-Yoneda embedding, here the evaluation is
  the normalization-by-gluing of `Gluing.Bicategorical.RecNormalization`
  and the faithfulness is its `solve`: equal normal forms already give
  an equation in the free cartesian closed category, and the semantics
  functor `rec` carries it into the ambient one.
-}
module Cubical.Tactics.CCCSolver.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Quiver.Base
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.List hiding ([_])

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Displayed.Instances.Weaken.UncurriedProperties

import Cubical.Categories.Instances.Free.CartesianClosedCategory.Forded
  as FCCC
open import
  Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
  using (Quiver→×⇒Quiver ; CCCExpr)

open import Gluing.Bicategorical.NormalForms
import Gluing.Bicategorical.RecNormalization as RecNorm

private
  variable ℓQ ℓQ' ℓD ℓD' : Level

open Functor

module Eval (Q : Quiver ℓQ ℓQ')
  (isSetOb : isSet (Q .fst))
  (isSetMor : isSet (QuiverOver.mor (Q .snd)))
  (𝓓 : CartesianClosedCategory ℓD ℓD') where

  open NF Q isSetOb

  private
    ×⇒Q = Quiver→×⇒Quiver Q
    module 𝓓 = CartesianClosedCategory 𝓓
    module W = CartesianClosedCategory FREECCC

  -- the objects and morphisms of the free cartesian closed category
  -- on `Q`, re-exported so callers need not open `NF`
  Obj : Type ℓQ
  Obj = Ty

  Mor : Obj → Obj → Type (ℓ-max ℓQ ℓQ')
  Mor A B = W.Hom[ A , B ]

  -- An interpretation of the atoms: an object of `𝓓` for each vertex
  -- of the quiver and a morphism of `𝓓` for each edge.
  Interp : Type (ℓ-max (ℓ-max ℓQ ℓQ') (ℓ-max ℓD ℓD'))
  Interp = FCCC.ElimInterpᴰ ×⇒Q (weakenCCC FREECCC 𝓓)

  mkInterp : (i-ob : Q .fst → 𝓓.ob)
    → ((e : QuiverOver.mor (Q .snd))
       → 𝓓.Hom[ i-ob (QuiverOver.dom (Q .snd) e)
              , i-ob (QuiverOver.cod (Q .snd) e) ])
    → Interp
  mkInterp i-ob i-hom = FCCC.mkElimInterpᴰ i-ob i-hom

  -- Normal forms are the evaluator, exactly as `eval` is in the
  -- category solver.
  -- the type at which `eval` lands.  `T` is the comparison functor
  -- of the recursor; it is the identity up to `T-ob`, and on any
  -- concrete type expression `Tob A` reduces to `A`.
  Tob : Ty → Ty
  Tob = RecNorm.T Q isSetOb isSetMor .F-ob

  eval : {A B : Ty} → W.Hom[ A , B ] → Nf (Tob A ∷ []) (Tob B)
  eval = RecNorm.normalize Q isSetOb isSetMor

  module _ (ı : Interp) where
    private
      sem : Functor W.C 𝓓.C
      sem = FCCC.rec ×⇒Q 𝓓 ı

    ⟦_⟧ob : Ty → 𝓓.ob
    ⟦_⟧ob = sem .F-ob

    ⟦_⟧ : {A B : Ty} → W.Hom[ A , B ] → 𝓓.Hom[ ⟦ A ⟧ob , ⟦ B ⟧ob ]
    ⟦_⟧ = sem .F-hom

    -- THE SOLVER.  Two expressions with the same normal form have
    -- equal interpretations in `𝓓`.
    solve : {A B : Ty} (e₁ e₂ : W.Hom[ A , B ])
      → eval e₁ ≡ eval e₂ → ⟦ e₁ ⟧ ≡ ⟦ e₂ ⟧
    solve e₁ e₂ p = cong ⟦_⟧ (RecNorm.solve Q isSetOb isSetMor e₁ e₂ p)


--------------------------------------------------------------------
-- The TAUTOLOGICAL interpretation, for the solver macro: the atoms
-- are all the objects and all the morphisms of the ambient category,
-- exactly as `Cat→Quiver` does for the category solver.
--
-- Unlike the category solver this needs `isSet` on the objects:
-- normalization is by gluing along a category `Ren` of contexts and
-- renamings, whose hom-sets are functions on variables and so are
-- sets only when the type expressions are.  That is why the macro
-- takes a `SolvableCCC` rather than a bare `CartesianClosedCategory`.
--------------------------------------------------------------------

record SolvableCCC (ℓ ℓ' : Level) : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
  where
  field
    ccc : CartesianClosedCategory ℓ ℓ'
    isSetObj : isSet (CartesianClosedCategory.ob ccc)

module Tautological {ℓ ℓ' : Level} (𝕊 : SolvableCCC ℓ ℓ') where
  open SolvableCCC 𝕊
  private
    module 𝓓 = CartesianClosedCategory ccc

  CCC→Quiver : Quiver ℓ (ℓ-max ℓ ℓ')
  CCC→Quiver .fst = 𝓓.ob
  CCC→Quiver .snd .QuiverOver.mor =
    Σ[ a ∈ 𝓓.ob ] Σ[ b ∈ 𝓓.ob ] 𝓓.Hom[ a , b ]
  CCC→Quiver .snd .QuiverOver.dom e = e .fst
  CCC→Quiver .snd .QuiverOver.cod e = e .snd .fst

  isSetTautMor : isSet (QuiverOver.mor (CCC→Quiver .snd))
  isSetTautMor =
    isSetΣ isSetObj λ _ → isSetΣ isSetObj λ _ → 𝓓.isSetHom

  open Eval CCC→Quiver isSetObj isSetTautMor ccc public

  taut : Interp
  taut = mkInterp (λ o → o) (λ e → e .snd .snd)

  solveT : (A B : Obj) (e₁ e₂ : Mor A B)
    → eval e₁ ≡ eval e₂ → ⟦ taut ⟧ e₁ ≡ ⟦ taut ⟧ e₂
  solveT A B = solve taut
