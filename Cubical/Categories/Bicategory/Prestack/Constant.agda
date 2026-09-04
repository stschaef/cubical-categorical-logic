{-# OPTIONS --lossy-unification #-}
{- The constant prestack at a category. -}
module Cubical.Categories.Bicategory.Prestack.Constant where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.BinProduct

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Constructions.Op
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Prestack.Base

private
  variable
    ℓ ℓ' ℓ'' ℓp ℓp' : Level

open Functor
open NatTrans
open isIso
open LaxFunctor
open Pseudofunctor

module _ (A : Bicategory ℓ ℓ' ℓ'') (C : Category ℓp ℓp') where
  private
    module C = Category C

    ν : NatTrans (Id ∘F Id) (Id {C = C})
    ν .N-ob _ = C.id
    ν .N-hom _ = C.⋆IdR _ ∙ sym (C.⋆IdL _)

    ν⁻ : NatTrans (Id {C = C}) (Id ∘F Id)
    ν⁻ .N-ob _ = C.id
    ν⁻ .N-hom _ = C.⋆IdR _ ∙ sym (C.⋆IdL _)

  ConstLax : LaxFunctor A (CAT {ℓp} {ℓp'})
  ConstLax .F-ob _ = C
  ConstLax .F-Hom {x} {y} = Constant _ _ Id
  ConstLax .F-id .N-ob _ = idTrans Id
  ConstLax .F-id .N-hom _ = makeNatTransPath (funExt λ _ → refl)
  ConstLax .F-seq .N-ob _ = ν
  ConstLax .F-seq .N-hom _ = makeNatTransPath (funExt λ _ →
    C.⋆IdR _ ∙ C.⋆IdL _ ∙ sym (C.⋆IdR _))
  ConstLax .lax-λ _ _ _ = makeNatTransPath (funExt λ _ →
    cong (C._⋆ (C.id C.⋆ C.id)) (C.⋆IdL _) ∙ C.⋆IdL _ ∙ C.⋆IdL _)
  ConstLax .lax-ρ _ _ _ = makeNatTransPath (funExt λ _ →
    cong (C._⋆ (C.id C.⋆ C.id)) (C.⋆IdL _) ∙ C.⋆IdL _ ∙ C.⋆IdL _)
  ConstLax .lax-α _ _ _ _ _ _ _ = makeNatTransPath (funExt λ _ →
    cong (C._⋆ (C.id C.⋆ C.id)) (C.⋆IdL _) ∙ C.⋆IdL _ ∙ C.⋆IdL _
    ∙ sym (C.⋆IdL _ ∙ cong (C._⋆ C.id) (C.⋆IdL _) ∙ C.⋆IdL _))

  ConstPs : Pseudofunctor A (CAT {ℓp} {ℓp'})
  ConstPs .laxFunctor = ConstLax
  ConstPs .F-id-isIso _ .inv = idTrans Id
  ConstPs .F-id-isIso _ .sec = makeNatTransPath (funExt λ _ → C.⋆IdL _)
  ConstPs .F-id-isIso _ .ret = makeNatTransPath (funExt λ _ → C.⋆IdL _)
  ConstPs .F-seq-isIso _ .inv = ν⁻
  ConstPs .F-seq-isIso _ .sec = makeNatTransPath (funExt λ _ → C.⋆IdL _)
  ConstPs .F-seq-isIso _ .ret = makeNatTransPath (funExt λ _ → C.⋆IdL _)

module _ (B : Bicategory ℓ ℓ' ℓ'') (C : Category ℓp ℓp') where
  ConstPrestack : Prestack B ℓp ℓp'
  ConstPrestack = ConstPs (B ^opᴮ) C
