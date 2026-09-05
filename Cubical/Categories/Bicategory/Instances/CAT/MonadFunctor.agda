{-# OPTIONS --lossy-unification #-}
{- Monad functors between monads on (possibly different) small
   categories. -}
module Cubical.Categories.Bicategory.Instances.CAT.MonadFunctor where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Monad.Morphism
open import Cubical.Categories.Bicategory.Monad.Functor
open import Cubical.Categories.Bicategory.Instances.CAT

private
  variable
    ℓ ℓ' : Level

open MonadFunctor
open MonadOn
open NatTrans
open Functor

-- At `CAT` the unitors and associator have identity components, so
-- `makeNatTransPath` reduces each coherence law to pointwise
-- identity-law bookkeeping.
module CATMonadFunctor {ℓ ℓ'} where
  private
    SC : Bicategory _ _ _
    SC = CAT {ℓ} {ℓ'}
    module SC = Bicategory SC

  underlyingFunctor : {A A' : Category ℓ ℓ'}
    {M : MonadOn SC A} {M' : MonadOn SC A'}
    → MonadFunctor SC M M' → Functor A A'
  underlyingFunctor F = F .P

  underlyingComparison : {A A' : Category ℓ ℓ'}
    {M : MonadOn SC A} {M' : MonadOn SC A'}
    (F : MonadFunctor SC M M')
    → NatTrans (funcComp (F .P) (M .t)) (funcComp (M' .t) (F .P))
  underlyingComparison F = F .φ

  idMF : {A : Category ℓ ℓ'} (M : MonadOn SC A) → MonadFunctor SC M M
  idMF {A} M .P = SC.id₁
  idMF {A} M .φ = SC.ρ⁺ (M .t) SC.⋆₂ SC.λ⁻ (M .t)
  idMF {A} M .φ-η = makeNatTransPath (funExt law)
    where
    module A = Category A
    law : (x : A.ob)
      →   (N-ob (M .η) x A.⋆ A.id) A.⋆ (A.id A.⋆ A.id)
        ≡ A.id A.⋆ (A.id A.⋆ (A.id A.⋆ N-ob (M .η) x))
    law x =
        cong₂ A._⋆_ (A.⋆IdR _) (A.⋆IdL _)
      ∙ A.⋆IdR _
      ∙ sym (A.⋆IdL _ ∙ A.⋆IdL _ ∙ A.⋆IdL _)
  -- Both sides collapse to `μ x`; every object is pinned so that no
  -- metavariable has to guess a functor index.
  idMF {A} M .φ-μ = makeNatTransPath (funExt lawμ)
    where
    module A = Category A
    T = M .t
    lawμ : (x : A.ob)
      →   N-ob ((M .μ SC.▷w idMF M .P) SC.⋆₂ idMF M .φ) x
        ≡ N-ob (SC.α⁺ (M .t) (M .t) (idMF M .P) SC.⋆₂
             (M .t SC.◁w idMF M .φ) SC.⋆₂
             SC.α⁻ (M .t) (idMF M .P) (M .t) SC.⋆₂
             (idMF M .φ SC.▷w M .t) SC.⋆₂
             SC.α⁺ (idMF M .P) (M .t) (M .t) SC.⋆₂
             (idMF M .P SC.◁w M .μ)) x
    lawμ x = lhs≡ ∙ sym rhs≡
      where
      μx = N-ob (M .μ) x
      Tid : {z : A.ob} → T ⟪ A.id {z} ⟫ ≡ A.id
      Tid = T .F-id
      Tid2 : {z : A.ob} → T ⟪ A.id {z} A.⋆ A.id ⟫ ≡ A.id
      Tid2 = cong (T ⟪_⟫) (A.⋆IdL A.id) ∙ T .F-id
      TTid : {z : A.ob} → T ⟪ T ⟪ A.id {z} ⟫ ⟫ ≡ A.id
      TTid = cong (T ⟪_⟫) (T .F-id) ∙ T .F-id

      B1 : A.Hom[ T ⟅ T ⟅ x ⟆ ⟆ , T ⟅ T ⟅ x ⟆ ⟆ ]
      B1 = T ⟪ A.id ⟫ A.⋆ (A.id A.⋆ A.id)
      B2 : A.Hom[ T ⟅ T ⟅ x ⟆ ⟆ , T ⟅ T ⟅ x ⟆ ⟆ ]
      B2 = T ⟪ A.id A.⋆ A.id ⟫ A.⋆ A.id
      B3 : A.Hom[ T ⟅ T ⟅ x ⟆ ⟆ , T ⟅ x ⟆ ]
      B3 = T ⟪ T ⟪ A.id ⟫ ⟫ A.⋆ μx

      B1≡ : B1 ≡ A.id
      B1≡ = cong₂ A._⋆_ Tid (A.⋆IdL A.id) ∙ A.⋆IdR A.id
      B2≡ : B2 ≡ A.id
      B2≡ = cong (A._⋆ A.id) Tid2 ∙ A.⋆IdR A.id
      B3≡ : B3 ≡ μx
      B3≡ = cong (A._⋆ μx) TTid ∙ A.⋆IdL μx

      lhs≡ : (μx A.⋆ A.id) A.⋆ (A.id A.⋆ A.id) ≡ μx
      lhs≡ = cong₂ A._⋆_ (A.⋆IdR μx) (A.⋆IdL A.id) ∙ A.⋆IdR μx

      rhs≡ : A.id A.⋆ (B1 A.⋆ (A.id A.⋆ (B2 A.⋆ (A.id A.⋆ B3)))) ≡ μx
      rhs≡ =
          A.⋆IdL _
        ∙ cong (λ m → B1 A.⋆ m) (A.⋆IdL _)
        ∙ cong (λ m → B1 A.⋆ (B2 A.⋆ m)) (A.⋆IdL _)
        ∙ cong (λ m → m A.⋆ (B2 A.⋆ B3)) B1≡
        ∙ A.⋆IdL _
        ∙ cong (λ m → m A.⋆ B3) B2≡
        ∙ A.⋆IdL _
        ∙ B3≡

  -- The composite's DATA.  Its coherence laws, and the category laws
  -- of a monads-and-monad-functors category, are not available on the
  -- nose at `CAT`: `⋆IdL` would need `P ∘F 𝟙⟨ A ⟩ ≡ P`, which is only
  -- the propositional `F-lUnit`.
  module _ {A A' A'' : Category ℓ ℓ'}
    {M : MonadOn SC A} {M' : MonadOn SC A'} {M'' : MonadOn SC A''}
    (G : MonadFunctor SC M' M'') (F : MonadFunctor SC M M') where
    compMF-P : Functor A A''
    compMF-P = funcComp (G .P) (F .P)

    compMF-φ : SC.2Cell (M .t SC.⋆₁ (F .P SC.⋆₁ G .P))
                        ((F .P SC.⋆₁ G .P) SC.⋆₁ M'' .t)
    compMF-φ =
        SC.α⁻ (M .t) (F .P) (G .P)
      SC.⋆₂ ((F .φ SC.▷w G .P)
      SC.⋆₂ (SC.α⁺ (F .P) (M' .t) (G .P)
      SC.⋆₂ ((F .P SC.◁w G .φ)
      SC.⋆₂ SC.α⁻ (F .P) (G .P) (M'' .t))))
