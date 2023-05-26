{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Categories.Limits.AsRepresentable.Cone where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.Limits

open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.Profunctor.General

open import Cubical.Tactics.CategorySolver.Reflection

module _ {ℓj}{ℓj'}{ℓc}{ℓc'}(J : Category ℓj ℓj')(C : Category ℓc ℓc') where
  -- In point-wise notation
  -- CONE c D = NatTrans (J -> Set) (Konst c) D
  CONE : (FUNCTOR J C) *-[ ℓ-max (ℓ-max ℓj ℓj') ℓc' ]-o C
  CONE = HomFunctor (FUNCTOR J C) ∘F ((_^opF {C = C}{D = FUNCTOR J C} (λFr J C (Fst C J))) ×F Id {C = FUNCTOR J C})

  open Category
  open Functor
  open Cone
  open NatTrans

  module _ (D : Functor J C) (c : ob C) where
    CONE→Cone : (CONE ⟅ c , D ⟆) .fst → Cone D c
    CONE→Cone η .coneOut v = η .N-ob v
    CONE→Cone η .coneOutCommutes {u}{v} e = 
      η .N-ob u ⋆⟨ C ⟩ D .F-hom e
       ≡⟨ sym (η .N-hom e) ⟩
      fst (((λFr J C (Fst C J) ^opF) ×F Id) ⟅ c , D ⟆) .F-hom e ⋆⟨ C ⟩ N-ob η v
       ≡⟨ solveCat! C ⟩
      η .N-ob v ∎

    Cone→CONE : Cone D c → (CONE ⟅ c , D ⟆) .fst
    Cone→CONE record-cone .N-ob x =  record-cone .coneOut x
    Cone→CONE record-cone .N-hom {x}{y} f = 
      (fst (((λFr J C (Fst C J) ^opF) ×F Id) ⟅ c , D ⟆) .F-hom f
        ⋆⟨ C ⟩
        record-cone .coneOut y)
        ≡⟨ refl ⟩
      Constant J C c .F-hom f ⋆⟨ C ⟩ record-cone .coneOut y
        ≡⟨ solveCat! C ⟩
          record-cone .coneOut y
        ≡⟨ sym (record-cone .coneOutCommutes f) ⟩
      (record-cone .coneOut x
        ⋆⟨ C ⟩
        snd (((λFr J C (Fst C J) ^opF) ×F Id) ⟅ c , D ⟆) .F-hom f) ∎
