{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Finite.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.FinSet
open import Cubical.Data.Fin
open import Cubical.Data.Quiver.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Morphism
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Constructions.Free.Category.Quiver as Free
  hiding (rec)
open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.Constructions.BinProduct

private
  variable
    ℓ ℓ' ℓ'' : Level

module _
  {ℓQ ℓQ' : Level}
  (C : Category ℓ ℓ')
  (JQuiv : Quiver ℓQ ℓQ' )
  -- (isFinJ : isFinSet (JQuiv .fst))
  where
  J-cat = FreeCat JQuiv
  Cᴶ = FUNCTOR J-cat C

  open Functor
  open Category

  Δᴶ : Functor C Cᴶ
  Δᴶ = curryF J-cat C {Γ = C} .F-ob (Fst C J-cat)

  -- open QuiverOver

  -- fixOb : (F G : Cᴶ .ob) (j : J-cat .ob) → Type _
  -- fixOb F G j = F .F-ob j ≡ G .F-ob j

  -- -- a nat trans that fixes
  -- subsetAction : (F G : Cᴶ .ob) → {u v : J-cat .ob} → (s : ℙ ( J-cat [ u , v ] )) → Type _
  -- subsetAction F G {u}{v} s =
  --   ∀ (ϕ : J-cat [ u , v ]) → s ϕ .fst →
  --     (p : fixOb F G u) → (q : fixOb F G v) →
  --     PathP
  --       (λ i → cong₂ (λ a b → C [ a , b ]) p q i)
  --       (F ⟪ ϕ ⟫) (G ⟪ ϕ ⟫)

  -- data RedundantAxiomGenerator : Type {!!} where
  --   homMulti :
  --     (F G : Cᴶ .ob) → {u v : J-cat .ob} →
  --     (s : ℙ (J-cat [ u , v ])) →
  --     -- subsetAction F G {!!} →
  --     RedundantAxiomGenerator

  -- data RedundantAx : Type {!!} where
  --    idMulti : (F : Cᴶ .ob) → RedundantAx
  --    compMulti : (s : ℙ (J-cat .ob)) →
  --     (F G H : Cᴶ .ob) →
  --     -- subsetAction F G s →
  --     -- subsetAction G H s →
  --     ((j : J-cat .ob) →
  --       C [ F .F-ob j , G .F-ob j ] →
  --       C [ G .F-ob j , H .F-ob j ]) →
  --     RedundantAx
  --    agreeMulti :
  --      (F G : Cᴶ .ob) →
  --      (s : ℙ (J-cat .ob)) →
  --      -- subsetAction F G (λ j → (s j .fst → ⊥) , isProp→ isProp⊥) →
  --      RedundantAx
