{-# OPTIONS --lossy-unification #-}
{- Fibrewise limits transfer from a prestack's fibres to `∫Pre`. -}
module Cubical.Categories.Bicategory.Prestack.Fiberwise where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism renaming (isIso to isIsoFun)
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties

open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Instances.LocallyDiscrete
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Grothendieck

private
  variable
    ℓ ℓ' ℓp ℓp' : Level

open Functor
open PshHom
open UniversalElement
open UniversalElementⱽ'

module _ {C : Category ℓ ℓ'} (P : Prestack (LocallyDiscrete C) ℓp ℓp') where
  private
    module C = Category C
    ∫P = ∫Pre P
    module ∫P = Categoryᴰ ∫P
    module F = Fibers ∫P
  open PrestackNotation {B = LocallyDiscrete C} P

  -- postcomposing with a fibrewise iso is a bijection on displayed homs
  private
    postIso : {Γ : C.ob} {Γᴰ a b : p[ Γ ]} (m : CatIso P⟨ Γ ⟩ a b)
      → Iso (P⟨ Γ ⟩ [ Γᴰ , a ]) (P⟨ Γ ⟩ [ Γᴰ , b ])
    postIso m .Iso.fun h = h Pᶜ.⋆ m .fst
    postIso m .Iso.inv h = h Pᶜ.⋆ m .snd .isIso.inv
    postIso m .Iso.sec h = Pᶜ.⋆Assoc _ _ _
      ∙ cong (h Pᶜ.⋆_) (m .snd .isIso.sec) ∙ Pᶜ.⋆IdR h
    postIso m .Iso.ret h = Pᶜ.⋆Assoc _ _ _
      ∙ cong (h Pᶜ.⋆_) (m .snd .isIso.ret) ∙ Pᶜ.⋆IdR h

  -- `∫Pre P` is always a fibration: the lift of `f` at `yᴰ` is `f ⋆ᴾ yᴰ`
  module _ {x y : C.ob} (f : C [ x , y ]) (yᴰ : p[ y ]) where
    private
      Q : Presheafⱽ y ∫P ℓp'
      Q = ∫P [-][-, yᴰ ]
      module Q = PresheafᴰNotation ∫P (C [-, y ]) Q

      Spec : Presheafⱽ x ∫P ℓp'
      Spec = CartesianLiftPshSpec (C [-, y ]) ∫P Q f
      module Spec = PresheafᴰNotation ∫P (C [-, x ]) Spec

      ε : ∫P.Hom[ f ][ f ⋆ᴾ yᴰ , yᴰ ]
      ε = Pᶜ.id

      elem : Spec.p[ C.id ][ f ⋆ᴾ yᴰ ]
      elem = F.reind (sym (C.⋆IdL f)) ε

      key : (Γ : C.ob) (Γᴰ : p[ Γ ]) (g : C [ Γ , x ])
        (gᴰ : ∫P.Hom[ g ][ Γᴰ , f ⋆ᴾ yᴰ ])
        → yoRecⱽ Spec elem .N-ob (Γ , Γᴰ , g) gᴰ
          ≡ postIso (⋆ᴾAssoc g f yᴰ) .Iso.fun gᴰ
      key Γ Γᴰ g gᴰ = F.rectify (F.≡out
          ( (F.≡in (cong (λ e → Q .F-hom (g , gᴰ , e) elem)
                     (C.isSetHom _ _ _ (cong (g C.⋆_) (C.⋆IdL f)))))
          ∙ Q.⋆ᴰ-reind gᴰ (cong (g C.⋆_) (C.⋆IdL f)) elem
          ∙ F.reind-filler⁻ refl
          ∙ F.⟨ refl ⟩⋆⟨ F.reind-filler⁻ (sym (C.⋆IdL f)) ⟩))
        ∙ cong (gᴰ Pᶜ.⋆_)
            (cong (Pᶜ._⋆ ⋆ᴾAssoc g f yᴰ .fst) (reind g .F-id)
             ∙ Pᶜ.⋆IdL _)

    ∫PreCartesianLift : CartesianLift ∫P f yᴰ
    ∫PreCartesianLift = REPRⱽ lift'
      where
      lift' : UniversalElementⱽ' ∫P x Spec
      lift' .vertexⱽ = f ⋆ᴾ yᴰ
      lift' .elementⱽ = elem
      lift' .universalⱽ (Γ , Γᴰ , g) =
        subst isIsoFun (sym (funExt (key Γ Γᴰ g)))
          (IsoToIsIso (postIso (⋆ᴾAssoc g f yᴰ)))

  ∫PreFibration : isFibration ∫P
  ∫PreFibration yᴰ _ f = ∫PreCartesianLift f yᴰ

  -- fibrewise terminal objects, preserved by reindexing
  module _ (term : (x : C.ob) → Terminal P⟨ x ⟩)
    (presTerm : {x y : C.ob} (f : C [ x , y ])
      → preservesTerminal P⟨ y ⟩ P⟨ x ⟩ (reind f))
    where
    ∫PreTerminalsⱽ : Terminalsⱽ ∫P
    ∫PreTerminalsⱽ x = REPRⱽ t
      where
      t : UniversalElementⱽ' ∫P x UnitPshᴰ
      t .vertexⱽ = term x .fst
      t .elementⱽ = tt
      t .universalⱽ (Γ , Γᴰ , g) .fst _ = presTerm g (term x) Γᴰ .fst
      t .universalⱽ (Γ , Γᴰ , g) .snd .fst _ = refl
      t .universalⱽ (Γ , Γᴰ , g) .snd .snd = presTerm g (term x) Γᴰ .snd

  -- a fibre morphism as a vertical displayed morphism
  private
    vertHom : {x : C.ob} {aᴰ bᴰ : p[ x ]} → P⟨ x ⟩ [ aᴰ , bᴰ ]
      → ∫P.Hom[ C.id ][ aᴰ , bᴰ ]
    vertHom m = m Pᶜ.⋆ ∫P.idᴰ

    vertComp : {Γ x : C.ob} {Γᴰ : p[ Γ ]} {aᴰ bᴰ : p[ x ]} (g : C [ Γ , x ])
      (gᴰ : ∫P.Hom[ g ][ Γᴰ , aᴰ ]) (m : P⟨ x ⟩ [ aᴰ , bᴰ ])
      → (gᴰ ∫P.⋆ᴰ vertHom m) F.∫≡ (gᴰ Pᶜ.⋆ reind g .F-hom m)
    vertComp {bᴰ = bᴰ} g gᴰ m =
        F.≡in (cong (gᴰ Pᶜ.⋆_)
                 (cong (Pᶜ._⋆ ⋆ᴾAssoc g C.id bᴰ .fst)
                       (reind g .F-seq m ∫P.idᴰ)
                  ∙ Pᶜ.⋆Assoc _ _ _)
               ∙ sym (Pᶜ.⋆Assoc gᴰ _ _))
      ∙ F.≡in (∫P.⋆IdRᴰ (gᴰ Pᶜ.⋆ reind g .F-hom m))

  -- fibrewise binary products, preserved by reindexing
  module _ (bp : {x : C.ob} (a b : p[ x ]) → BinProduct P⟨ x ⟩ (a , b))
    (presBP : {x y : C.ob} (f : C [ x , y ]) (a b : p[ y ])
      → preservesBinProduct (reind f) (bp a b))
    where
    ∫PreBinProductsⱽ : BinProductsⱽ ∫P
    ∫PreBinProductsⱽ {x} aᴰ bᴰ = REPRⱽ b
      where
      Spec : Presheafⱽ x ∫P ℓp'
      Spec = (∫P [-][-, aᴰ ]) ×ⱽPsh (∫P [-][-, bᴰ ])

      Q₁ = ∫P [-][-, aᴰ ]
      Q₂ = ∫P [-][-, bᴰ ]
      module Q₁ = PresheafᴰNotation ∫P (C [-, x ]) Q₁
      module Q₂ = PresheafᴰNotation ∫P (C [-, x ]) Q₂

      π₁ = bp aᴰ bᴰ .element .fst
      π₂ = bp aᴰ bᴰ .element .snd

      module Spec = PresheafᴰNotation ∫P (C [-, x ]) Spec

      elem : Spec.p[ C.id ][ bp aᴰ bᴰ .vertex ]
      elem = vertHom π₁ , vertHom π₂

      key : (Γ : C.ob) (Γᴰ : p[ Γ ]) (g : C [ Γ , x ])
        (gᴰ : ∫P.Hom[ g ][ Γᴰ , bp aᴰ bᴰ .vertex ])
        → yoRecⱽ Spec elem .N-ob (Γ , Γᴰ , g) gᴰ
          ≡ (gᴰ Pᶜ.⋆ reind g .F-hom π₁ , gᴰ Pᶜ.⋆ reind g .F-hom π₂)
      key Γ Γᴰ g gᴰ = ΣPathP
        ( F.rectify (F.≡out
            ( Q₁.⋆ᴰ-reind gᴰ (C.⋆IdR g) (vertHom π₁)
            ∙ F.reind-filler⁻ refl
            ∙ vertComp g gᴰ π₁))
        , F.rectify (F.≡out
            ( Q₂.⋆ᴰ-reind gᴰ (C.⋆IdR g) (vertHom π₂)
            ∙ F.reind-filler⁻ refl
            ∙ vertComp g gᴰ π₂)))

      b : UniversalElementⱽ' ∫P x Spec
      b .vertexⱽ = bp aᴰ bᴰ .vertex
      b .elementⱽ = elem
      b .universalⱽ (Γ , Γᴰ , g) =
        subst isIsoFun (sym (funExt (key Γ Γᴰ g)))
          (isEquivToIsIso _ (presBP g aᴰ bᴰ Γᴰ))

  -- the whole vertical cartesian structure at once
  ∫PreCartesianCategoryⱽ :
    (term : (x : C.ob) → Terminal P⟨ x ⟩)
    (presTerm : {x y : C.ob} (f : C [ x , y ])
      → preservesTerminal P⟨ y ⟩ P⟨ x ⟩ (reind f))
    (bp : {x : C.ob} (a b : p[ x ]) → BinProduct P⟨ x ⟩ (a , b))
    (presBP : {x y : C.ob} (f : C [ x , y ]) (a b : p[ y ])
      → preservesBinProduct (reind f) (bp a b))
    → CartesianCategoryⱽ C ℓp ℓp'
  ∫PreCartesianCategoryⱽ term presTerm bp presBP = cartesiancategoryⱽ
    ∫P (∫PreTerminalsⱽ term presTerm) (∫PreBinProductsⱽ bp presBP)
    ∫PreFibration
