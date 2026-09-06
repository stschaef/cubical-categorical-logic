{-# OPTIONS --lossy-unification #-}
{-
  `solveCCC!`: a macro that proves equations between morphisms of a
  cartesian closed category by normalization.

  Modelled on `Cubical.Tactics.CategorySolver.Reflection`.  The goal
  is reflected into the free cartesian closed category on the ambient
  one, both sides are normalized, and `Tautological.solveT` carries
  the resulting equation back.

  Two differences from the category solver, both forced by the free
  cartesian closed category having STRUCTURED objects:

  * the objects of the goal must be reflected as well, since the
    expressions are indexed by object expressions and those indices
    are not recoverable by unification from the interpretation;

  * a morphism that is not built from `id`, `_⋆_`, `π₁`, `π₂`,
    `_,p_`, `lda`, `app` or `!t` becomes a generator, and generators
    of the free cartesian closed category on a QUIVER have atomic
    source and target, so such a morphism must sit between objects
    that are themselves atoms.
-}
module Cubical.Tactics.CCCSolver.Reflection where

open import Cubical.Foundations.Prelude

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.Sigma

open import Cubical.Data.Bool
open import Cubical.Data.List
open import Cubical.Data.Maybe
open import Cubical.Data.Unit
open import Cubical.Reflection.Base

open import Cubical.Tactics.Reflection
open import Cubical.Tactics.CCCSolver.Solver

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Exponentials
open import Cubical.Categories.Presheaf.Representable

import Cubical.Categories.Instances.Free.CartesianClosedCategory.Forded
  as FCCC
open import
  Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
  using (CCCExpr)

import Cubical.Data.Equality as Eq

module ReflectionSolver where
  -- OBJECTS.  `_×_`, `_⇒_` and `𝟙` all reduce to `vertex` of the
  -- corresponding universal element, which is the form the goal's
  -- type arrives in.
  pattern “×ob” a b =
    def (quote UniversalElement.vertex)
      (_ h∷ _ h∷ _ h∷ _ h∷ _ h∷
       def (quote CartesianCategory.bp)
         (_ h∷ _ h∷ _ v∷
          con (quote _,_) (_ h∷ _ h∷ _ h∷ _ h∷ a v∷ b v∷ []) v∷ [])
       v∷ [])

  pattern “⇒ob” a b =
    def (quote UniversalElement.vertex)
      (_ h∷ _ h∷ _ h∷ _ h∷ _ h∷
       def (quote CartesianClosedCategory.exps)
         (_ h∷ _ h∷ _ v∷ a v∷ b v∷ [])
       v∷ [])

  pattern “⊤ob” =
    def (quote UniversalElement.vertex)
      (_ h∷ _ h∷ _ h∷ _ h∷ _ h∷
       def (quote CartesianCategory.term) (_ h∷ _ h∷ _ v∷ []) v∷ [])

  buildOb : Term → Term
  buildOb (“×ob” a b) =
    con (quote CCCExpr._×_) (buildOb a v∷ buildOb b v∷ [])
  buildOb (“⇒ob” a b) =
    con (quote CCCExpr._⇒_) (buildOb a v∷ buildOb b v∷ [])
  buildOb “⊤ob” = con (quote CCCExpr.⊤) []
  buildOb a = con (quote CCCExpr.↑_) (a v∷ [])

  -- MORPHISMS
  pattern “id” = def (quote Category.id) (_ h∷ _ h∷ _ v∷ _ h∷ [])

  pattern “⋆” f g =
    def (quote Category._⋆_)
      (_ h∷ _ h∷ _ v∷ _ h∷ _ h∷ _ h∷ f v∷ g v∷ [])

  pattern “π₁” =
    def (quote BinProductNotation.π₁)
      (_ h∷ _ h∷ _ h∷ _ h∷ _ h∷ _ v∷ [])

  pattern “π₂” =
    def (quote BinProductNotation.π₂)
      (_ h∷ _ h∷ _ h∷ _ h∷ _ h∷ _ v∷ [])

  pattern “,p” f g =
    def (quote BinProductNotation._,p_)
      (_ h∷ _ h∷ _ h∷ _ h∷ _ h∷ _ v∷ _ h∷ f v∷ g v∷ [])

  pattern “lda” t =
    def (quote ExponentialNotation.lda)
      (_ h∷ _ h∷ _ h∷ _ h∷ _ h∷ _ v∷ _ v∷ _ h∷ t v∷ [])

  pattern “app” =
    def (quote ExponentialNotation.app)
      (_ h∷ _ h∷ _ h∷ _ h∷ _ h∷ _ v∷ _ v∷ [])

  pattern “!t” =
    def (quote TerminalNotation.!t) (_ h∷ _ h∷ _ h∷ _ v∷ _ h∷ [])

  buildExpr : Term → Term
  buildExpr “id” = con (quote FCCC.idₑ) (con (quote Eq.refl) [] v∷ [])
  buildExpr (“⋆” f g) =
    con (quote FCCC._⋆ₑ_) (buildExpr f v∷ buildExpr g v∷ [])
  buildExpr “π₁” =
    con (quote FCCC.π₁)
      (con (quote Eq.refl) [] v∷ con (quote Eq.refl) [] v∷ [])
  buildExpr “π₂” =
    con (quote FCCC.π₂)
      (con (quote Eq.refl) [] v∷ con (quote Eq.refl) [] v∷ [])
  buildExpr (“,p” f g) =
    con (quote FCCC.⟨_,_⟩)
      (buildExpr f v∷ buildExpr g v∷ con (quote Eq.refl) [] v∷ [])
  buildExpr (“lda” t) =
    con (quote FCCC.lam) (buildExpr t v∷ con (quote Eq.refl) [] v∷ [])
  buildExpr “app” =
    con (quote FCCC.eval)
      (con (quote Eq.refl) [] v∷ con (quote Eq.refl) [] v∷ [])
  buildExpr “!t” = con (quote FCCC.!ₑ) (con (quote Eq.refl) [] v∷ [])
  buildExpr f =
    con (quote FCCC.genₑ)
      (con (quote _,_)
        (unknown v∷ con (quote _,_) (unknown v∷ f v∷ []) v∷ []) v∷
       con (quote Eq.refl) [] v∷ con (quote Eq.refl) [] v∷ [])

  protectedNames : List Name
  protectedNames =
    ( quote Category.id ∷ quote Category._⋆_
    ∷ quote BinProductNotation.π₁ ∷ quote BinProductNotation.π₂
    ∷ quote BinProductNotation._,p_
    ∷ quote ExponentialNotation.lda ∷ quote ExponentialNotation.app
    ∷ quote TerminalNotation.!t
    ∷ [])

  getObs : Term → TC (Σ Term λ _ → Term)
  getObs (def (quote Category.Hom[_,_]) (_ h∷ _ h∷ _ v∷ x v∷ y v∷ [])) =
    returnTC (x , y)
  getObs t = typeError
    (strErr "solveCCC!: not a morphism type: " ∷ termErr t ∷ [])

  solve-macro : Term → Term → TC Unit
  solve-macro 𝕊 hole =
    withNormalisation false (
    withReduceDefs (false , protectedNames) (do
      goal ← inferType hole >>= reduce
      just (lhs , rhs) ← get-boundary goal
        where nothing → typeError
                (strErr "solveCCC!: the goal is not an equation: "
                 ∷ termErr goal ∷ [])
      elhs ← normalise lhs
      erhs ← normalise rhs
      ty ← inferType elhs >>= normalise
      xy ← getObs ty
      let call = def (quote Tautological.solveT)
            ( 𝕊 v∷ buildOb (xy .fst) v∷ buildOb (xy .snd)
            v∷ buildExpr elhs v∷ buildExpr erhs
            v∷ def (quote refl) [] v∷ [])
      noConstraints (unify hole call <|> typeError
        ( strErr "solveCCC! could not equate\n  " ∷ termErr elhs
        ∷ strErr "\nand\n  " ∷ termErr erhs ∷ []))))

macro
  solveCCC! : Term → Term → TC _
  solveCCC! = ReflectionSolver.solve-macro
