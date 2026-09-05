{-# OPTIONS --lossy-unification #-}
{- Formal monads in `CAT`: monads on a small category, their
   morphisms, algebras and distributive laws. -}
module Cubical.Categories.Bicategory.Instances.CAT.Monad where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.WildCat.Base hiding (_[_,_])

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Monad.Base
open import Cubical.Categories.Bicategory.Monad.Morphism
open import Cubical.Categories.Bicategory.Monad.Algebra
open import Cubical.Categories.Bicategory.DistributiveLaw
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Instances.Terminal
open import Cubical.Categories.Bicategory.Instances.CAT

import Cubical.Categories.Monad.Base as Ord

private
  variable
    ℓ ℓ' : Level

open Bicategory
open Functor
open NatTrans
open Category

SmallMonad : (ℓ ℓ' : Level) → Type _
SmallMonad ℓ ℓ' = Monad (CAT {ℓ} {ℓ'})

-- The formal-monad data, read at `CAT`.
module Unfold {ℓ ℓ'} (M : SmallMonad ℓ ℓ') where
  private
    module M = Monad M
    module CATb = Bicategory (CAT {ℓ} {ℓ'})

  A : Category ℓ ℓ'
  A = M.a

  T : Functor A A
  T = M.t

  η : CATb.2Cell CATb.id₁ T
  η = M.η

  μ : CATb.2Cell (T CATb.⋆₁ T) T
  μ = M.μ

  idL : ((η CATb.▷w T) CATb.⋆₂ μ) ≡ CATb.λ⁺ T
  idL = M.idL

  idR : ((T CATb.◁w η) CATb.⋆₂ μ) ≡ CATb.ρ⁺ T
  idR = M.idR

  μAssoc :
    (CATb.α⁺ T T T CATb.⋆₂ ((T CATb.◁w μ) CATb.⋆₂ μ))
      ≡ ((μ CATb.▷w T) CATb.⋆₂ μ)
  μAssoc = M.μAssoc

-- A Street monad in `CAT` IS the repo's ordinary `Monad A`.  The data
-- transfers definitionally: `CAT`'s `id₁` is `𝟙⟨ A ⟩` and `t ⋆₁ t` is
-- `funcComp t t`.  The laws are bridged pointwise, since `F-rUnit`,
-- `F-lUnit`, `F-assoc` are `refl` on objects and `CAT`'s λ⁺/ρ⁺/α⁺
-- have identity components.
module ToOrdinary {ℓ ℓ'} (M : SmallMonad ℓ ℓ') where
  private
    module M = Monad M
    module U = Unfold M
    module A = Category U.A

  ordFunctor : Functor U.A U.A
  ordFunctor = M.t

  ordUnit : NatTrans (𝟙⟨ U.A ⟩) ordFunctor
  ordUnit = M.η

  ordMult : NatTrans (funcComp ordFunctor ordFunctor) ordFunctor
  ordMult = M.μ

  id₁≡𝟙 : Bicategory.id₁ (CAT {ℓ} {ℓ'}) {U.A} ≡ 𝟙⟨ U.A ⟩
  id₁≡𝟙 = refl

  ⋆₁≡funcComp :
    Bicategory._⋆₁_ (CAT {ℓ} {ℓ'}) U.T U.T ≡ funcComp U.T U.T
  ⋆₁≡funcComp = refl

  private
    η' : (x : A.ob) → U.A [ x , U.T ⟅ x ⟆ ]
    η' x = M.η .N-ob x

    μ' : (x : A.ob) → U.A [ U.T ⟅ U.T ⟅ x ⟆ ⟆ , U.T ⟅ x ⟆ ]
    μ' x = M.μ .N-ob x

    idrPt : (x : A.ob) → U.T ⟪ η' x ⟫ A.⋆ μ' x ≡ A.id
    idrPt x =
        cong (A._⋆ μ' x) (sym (A.⋆IdR _))
      ∙ (λ i → M.idL i .N-ob x)

    idlPt : (x : A.ob) → η' (U.T ⟅ x ⟆) A.⋆ μ' x ≡ A.id
    idlPt x =
        cong (A._⋆ μ' x) (sym (A.⋆IdL _))
      ∙ (λ i → M.idR i .N-ob x)

    TTid : {x : A.ob} → U.T ⟪ U.T ⟪ A.id {x} ⟫ ⟫ ≡ A.id
    TTid = cong (U.T ⟪_⟫) (U.T .F-id) ∙ U.T .F-id

    assocPt : (x : A.ob) → U.T ⟪ μ' x ⟫ A.⋆ μ' x ≡ μ' (U.T ⟅ x ⟆) A.⋆ μ' x
    assocPt x =
        cong (A._⋆ μ' x) (sym (A.⋆IdR _))
      ∙ (λ i → M.μAssoc (~ i) .N-ob x)
      ∙ A.⋆IdL _
      ∙ cong (λ m → (m A.⋆ μ' (U.T ⟅ x ⟆)) A.⋆ μ' x) TTid
      ∙ cong (A._⋆ μ' x) (A.⋆IdL _)

  ordIsMonad : Ord.IsMonad ordFunctor
  ordIsMonad .Ord.IsMonad.η = ordUnit
  ordIsMonad .Ord.IsMonad.μ = ordMult
  ordIsMonad .Ord.IsMonad.idl-μ =
    makeNatTransPathP F-rUnit refl (funExt idlPt)
  ordIsMonad .Ord.IsMonad.idr-μ =
    makeNatTransPathP F-lUnit refl (funExt idrPt)
  ordIsMonad .Ord.IsMonad.assoc-μ =
    makeNatTransPathP F-assoc refl (funExt assocPt)

  ordMonad : Ord.Monad U.A
  ordMonad = ordFunctor , ordIsMonad

formalMonad→Monad : (ℓ ℓ' : Level) (M : SmallMonad ℓ ℓ')
  → Ord.Monad (Monad.a M)
formalMonad→Monad ℓ ℓ' M = ToOrdinary.ordMonad M

private
  𝟚 : Bicategory ℓ-zero ℓ-zero ℓ-zero
  𝟚 = TerminalBicategory ℓ-zero ℓ-zero ℓ-zero

-- A monad on a small category is a lax functor out of the walking
-- monad, by the generic equivalence at `C = CAT`.
smallMonad≃laxFunctor :
  (ℓ ℓ' : Level) → Iso (LaxFunctor 𝟚 (CAT {ℓ} {ℓ'})) (SmallMonad ℓ ℓ')
smallMonad≃laxFunctor ℓ ℓ' = LaxFunctorIsoMonad (CAT {ℓ} {ℓ'})

-- The category of monads on a fixed small category `A`, and the
-- Eilenberg-Moore category of a monad on a small category.
SmallMonadCat : (A : Category ℓ ℓ') → WildCat _ _
SmallMonadCat {ℓ} {ℓ'} A = MndWild (CAT {ℓ} {ℓ'}) A

EMCategoryOfSmallMonad : (M : SmallMonad ℓ ℓ') → WildCat _ _
EMCategoryOfSmallMonad {ℓ} {ℓ'} M =
  EMWildOfMonad (CAT {ℓ} {ℓ'}) M (Monad.a M)

-- A Beck law `Λ : T ∘F S ⇒ S ∘F T` of two monads on `A`, and the
-- composite monad it induces.
BeckDistributiveLaw : (A : Category ℓ ℓ')
  (S T : MonadOn (CAT {ℓ} {ℓ'}) A) → Type _
BeckDistributiveLaw {ℓ} {ℓ'} = DistributiveLaw (CAT {ℓ} {ℓ'})

compositeMonadCAT : (A : Category ℓ ℓ')
  (S T : MonadOn (CAT {ℓ} {ℓ'}) A)
  (D : BeckDistributiveLaw A S T)
  → Composite.idL-ty    (CAT {ℓ} {ℓ'}) A S T D
  → Composite.idR-ty    (CAT {ℓ} {ℓ'}) A S T D
  → Composite.μAssoc-ty (CAT {ℓ} {ℓ'}) A S T D
  → MonadOn (CAT {ℓ} {ℓ'}) A
compositeMonadCAT {ℓ} {ℓ'} A =
  Composite.compositeMonadOn (CAT {ℓ} {ℓ'}) A
