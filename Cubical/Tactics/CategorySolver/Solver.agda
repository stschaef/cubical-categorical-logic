{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Tactics.CategorySolver.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base

open import Cubical.Categories.Constructions.Free.General
open import Cubical.Categories.Constructions.Free.UnderlyingGraph
open import Cubical.Categories.Constructions.Power

private
  variable
    ℓ ℓ' : Level
open Category
open Functor

module Eval (𝓒 : Category ℓ ℓ') where
  -- Semantics in 𝓒 itself, tautologically
  sem𝓒 = ε {𝓒 = 𝓒}
  ⟦_⟧c = sem𝓒 .F-hom
  𝓟 = PowerCategoryS (𝓒 .ob) (ℓ-max ℓ ℓ')
  𝓘 : Functor (FreeCat (Ugr 𝓒)) 𝓟
  𝓘 = PseudoYonedaS {C = FreeCat (Ugr 𝓒)}

  -- Semantics in 𝓟o 𝓒, interpreting fun symbols using Yoneda
  module YoSem = Semantics (Ugr 𝓒) 𝓟 (𝓘 ∘Interp η (Ugr 𝓒))
  ⟦_⟧yo = YoSem.sem .F-hom
  
  -- | Evaluate by taking the semantics in 𝓟 𝓒 and
  -- | use the Yoneda lemma to extract a morphism in 𝓒.
  eval : ∀ {A B} → FreeCat (Ugr 𝓒) [ A , B ] → _
  eval {A}{B} e = ⟦ e ⟧yo

  Yo-YoSem-agree : 𝓘 ≡ YoSem.sem
  Yo-YoSem-agree = YoSem.sem-uniq refl

  -- | Eval agrees with the tautological semantics
  solve : ∀ {A B} → (e₁ e₂ : FreeCat (Ugr 𝓒) [ A , B ])
        → eval e₁ ≡ eval e₂
        → ⟦ e₁ ⟧c ≡ ⟦ e₂ ⟧c
  solve {A}{B} e₁ e₂ p = cong ⟦_⟧c (isFaithfulPseudoYonedaS _ _ _ _ lem) where
    lem : 𝓘 ⟪ e₁ ⟫ ≡ 𝓘 ⟪ e₂ ⟫
    lem = transport (λ i → Yo-YoSem-agree (~ i) ⟪ e₁ ⟫ ≡ Yo-YoSem-agree (~ i) ⟪ e₂ ⟫) p

solve : (𝓒 : Category ℓ ℓ')
      → {A B : 𝓒 .ob}
      → (e₁ e₂ : FreeCat (Ugr 𝓒) [ A , B ])
      → (p : Eval.eval 𝓒 e₁ ≡ Eval.eval 𝓒 e₂)
      → _
solve = Eval.solve
