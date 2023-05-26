{-# OPTIONS --safe #-}

module Cubical.Tactics.CategorySolver.Reflection where

open import Cubical.Foundations.Prelude

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String

open import Cubical.Data.Bool
open import Cubical.Data.List
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Reflection.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Free.General
open import Cubical.Tactics.CategorySolver.Solver
open import Cubical.Tactics.Reflection

private
  variable
    ℓ ℓ' : Level

module ReflectionSolver where
  module _ (category : Term) where
    pattern category-args xs =
      _ h∷ _ h∷ _ v∷ xs

    pattern “id” =
      def (quote Category.id) (category-args (_ h∷ []))

    pattern “⋆” f g =
      def (quote Category._⋆_) (category-args (_ h∷ _ h∷ _ h∷ f v∷ g v∷ []))

    -- This seems really hacky tbh
    pattern “comp” f g =
      def (quote comp') (category-args (_ h∷ _ h∷ _ h∷ g v∷ f v∷ []))

    -- Parse the input into an exp
    buildExpression : Term → Term
    buildExpression “id” = con (quote FreeCategory.idₑ) []
    buildExpression (“⋆” f g) = con (quote FreeCategory._⋆ₑ_) (buildExpression f v∷ buildExpression g v∷ [])
    buildExpression (“comp” f g) = con (quote FreeCategory._⋆ₑ_) (buildExpression f v∷ buildExpression g v∷ [])
    buildExpression f = con (quote FreeCategory.↑_) (f v∷ [])

  solve-macro : Bool
              → Term -- ^ The term denoting the category
              → Term -- ^ The hole whose goal should be an equality between morphisms in the category
              → TC Unit
  solve-macro b category =
    equation-solver (quote Category.id ∷ quote Category._⋆_ ∷ quote comp' ∷ []) mk-call b where
      mk-call : Term → Term → TC Term
      mk-call lhs rhs = returnTC (def (quote solve)
                             (category v∷
                              buildExpression category lhs v∷
                              buildExpression category rhs v∷
                              def (quote refl) [] v∷ []))
macro
  solveCat! : Term → Term → TC _
  solveCat! = ReflectionSolver.solve-macro false

  solveCatDebug! : Term → Term → TC _
  solveCatDebug! = ReflectionSolver.solve-macro true
