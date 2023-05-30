{-# OPTIONS --safe #-}

module Cubical.Categories.Limits.AsRepresentable where

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

open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Limits.AsRepresentable.Cone
open import Cubical.Categories.Limits.Limits

open import Cubical.Tactics.CategorySolver.Reflection

module _ {ℓj}{ℓj'}{ℓc}{ℓc'}(J : Category ℓj ℓj')(C : Category ℓc ℓc') where
  Limit : (D : Functor J C) → Type (ℓ-max (ℓ-max (ℓ-max ℓj ℓj') ℓc) ℓc')
  Limit D = UnivElt C (CONE J C ∘F (Id {C = C ^op} ,F Constant (C ^op) (FUNCTOR J C) D))

  open Cone
  open LimCone
  open UnivElt
  open isUniversal
  open Functor
  open NatTrans

  Limit→LimCone : ∀ {D : Functor J C} → Limit D → LimCone D
  Limit→LimCone x .lim = x .vertex
  Limit→LimCone {D} x .limCone = CONE→Cone J C D (x .vertex) (x .element)
  Limit→LimCone {D} x .univProp c cc =
    (x .universal .coinduction ηc , {!!}) , {!!}
    where
    -- ηc an element of this hom set
    -- i.e. a natural transformation
    ηc : (funcComp (CONE J C) (Id ,F Constant (C ^op) (FUNCTOR J C) _) ⟅ c ⟆) .fst
    ηc .N-ob v = cc .coneOut v
    ηc .N-hom {u}{v} ϕ =
      fst
      (((λFr J C (Fst C J) ^opF) ×F Id) ⟅
       (Id ,F Constant (C ^op) (FUNCTOR J C) D) ⟅ c ⟆ ⟆)
      .F-hom ϕ
      ⋆⟨ C ⟩ N-ob ηc v
        ≡⟨ {!solveCat! C!} ⟩
      coneOut cc v
        ≡⟨ sym (cc .coneOutCommutes ϕ) ⟩
      N-ob ηc u ⋆⟨ C ⟩
      snd
      (((λFr J C (Fst C J) ^opF) ×F Id) ⟅
       (Id ,F Constant (C ^op) (FUNCTOR J C) D) ⟅ c ⟆ ⟆)
      .F-hom ϕ ∎


  LimCone→Limit : ∀ {D : Functor J C} → LimCone D → Limit D
  LimCone→Limit x .vertex = x .lim
  LimCone→Limit x .element .N-ob v = x .limCone .coneOut v
  LimCone→Limit x .element .N-hom {u}{v} ϕ = {!!}
  LimCone→Limit x .universal .coinduction {b} x₁ = x .univProp b {!x₁!} .fst .fst
  LimCone→Limit x .universal .commutes {b} ϕ = {!!}
  LimCone→Limit x .universal .is-uniq {b} ϕ f x₁ = {!!}
    where
    cone-over-b : {b : Category.ob C} → {D : Functor J C} → (x₁ : (funcComp (CONE J C) (Id ,F Constant (C ^op) (FUNCTOR J C) D) ⟅ b ⟆) .fst) → Cone D b
    coneOut (cone-over-b {b} {D} x₁) v = x₁ .N-ob v
    coneOutCommutes (cone-over-b {b} {D} x₁) {u}{v} ϕ =
      seq' C (coneOut (cone-over-b x₁) u) (D .F-hom ϕ)
        ≡⟨ sym (x₁ .N-hom ϕ) ⟩
      fst
        (((λFr J C (Fst C J) ^opF) ×F Id) ⟅
         (Id ,F Constant (C ^op) (FUNCTOR J C) D) ⟅ b ⟆ ⟆)
        .F-hom ϕ
        ⋆⟨ C ⟩ N-ob x₁ v
        ≡⟨ {!solveCat! C!} ⟩
      coneOut (cone-over-b x₁) v ∎
