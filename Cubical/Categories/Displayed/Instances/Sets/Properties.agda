{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Sets.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.More

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Exponentials

open import Cubical.Categories.Instances.Fiber hiding (fiber)

open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Sets.Base
  hiding (_[-][-,_])
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.UniversalQuantifier
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Exponential
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.CartesianClosedV

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓC ℓC' ℓD ℓD' : Level

open Categoryᴰ
open Category
open isIsoOver
open PshIso
open PshHom
open UniversalElementⱽ'

module _ {ℓ ℓ'} where
  private
    module SET = Category (SET ℓ)
    module SETᴰ = Fibers (SETᴰ ℓ ℓ')

  isFibrationSETᴰueⱽ :
    {X : hSet ℓ} →
    (Xᴰ : SETᴰ.ob[ X ]) →
    (Y : hSet ℓ) →
    (f : ⟨ Y ⟩ → ⟨ X ⟩) →
    UniversalElementⱽ' (SETᴰ ℓ ℓ') Y
      (reindPshᴰNatTrans (yoRec ((SET ℓ) [-, X ]) f)
      ((SETᴰ ℓ ℓ') [-][-, Xᴰ ]))
  isFibrationSETᴰueⱽ {X = X} Xᴰ Y f .vertexⱽ y = Xᴰ (f y)
  isFibrationSETᴰueⱽ {X = X} Xᴰ Y f .elementⱽ = λ _ z → z
  isFibrationSETᴰueⱽ {X = X} Xᴰ Y f .universalⱽ (Z , Zᴰ , g) .fst =
    λ z → z
  isFibrationSETᴰueⱽ {X = X} Xᴰ Y f .universalⱽ (Z , Zᴰ , g) .snd .fst γᴰ =
    -- I think these should have better inference for implicits if hSet were either
    -- 1. opaque, or
    -- 2. a no-eta-equality record
    --
    -- TODO make a local wrapper around hSet to test that
    SETᴰ.rectifyOut {a = Z}{b = X} {aᴰ = Zᴰ}{bᴰ = Xᴰ} $
      SETᴰ.reind-filler⁻ {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Xᴰ} _
  isFibrationSETᴰueⱽ {X = X} Xᴰ Y f .universalⱽ (Z , Zᴰ , g) .snd .snd γᴰ =
    SETᴰ.rectifyOut {a = Z}{b = X} {aᴰ = Zᴰ}{bᴰ = Xᴰ} $
      SETᴰ.reind-filler⁻ {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Xᴰ} _

  isFibrationSETᴰ : isFibration (SETᴰ ℓ ℓ')
  isFibrationSETᴰ Xᴰ Y f = REPRⱽ (isFibrationSETᴰueⱽ Xᴰ Y f)

  private
    module isFibrationSETᴰ = FibrationNotation (SETᴰ ℓ ℓ') isFibrationSETᴰ

  TerminalsⱽSETᴰueⱽ :
    (X : hSet ℓ) →
    UniversalElementⱽ' (SETᴰ ℓ ℓ') X UnitPshᴰ
  TerminalsⱽSETᴰueⱽ X .vertexⱽ _ = Unit* , isSetUnit*
  TerminalsⱽSETᴰueⱽ X .elementⱽ = tt
  TerminalsⱽSETᴰueⱽ X .universalⱽ (A , Aᴰ , f) .fst _ _ _ = tt*
  TerminalsⱽSETᴰueⱽ X .universalⱽ (A , Aᴰ , f) .snd .fst = λ _ → refl
  TerminalsⱽSETᴰueⱽ X .universalⱽ (A , Aᴰ , f) .snd .snd = λ _ → refl

  TerminalsⱽSETᴰ : Terminalsⱽ (SETᴰ ℓ ℓ')
  TerminalsⱽSETᴰ X = REPRⱽ (TerminalsⱽSETᴰueⱽ X)

  BinProductsⱽSETᴰueⱽ :
    {X : hSet ℓ} →
    (Xᴰ Yᴰ : SETᴰ.ob[ X ]) →
    UniversalElementⱽ' (SETᴰ ℓ ℓ') X
      ((SETᴰ ℓ ℓ' [-][-, Xᴰ ]) ×Psh (SETᴰ ℓ ℓ' [-][-, Yᴰ ]))
  BinProductsⱽSETᴰueⱽ Xᴰ Yᴰ .vertexⱽ x = _ , isSet× (Xᴰ x .snd) (Yᴰ x .snd)
  BinProductsⱽSETᴰueⱽ Xᴰ Yᴰ .elementⱽ = (λ x z → z .fst) , (λ x z → z .snd)
  BinProductsⱽSETᴰueⱽ Xᴰ Yᴰ .universalⱽ x .fst = λ z x₁ z₁ → z .fst x₁ z₁ , z .snd x₁ z₁
  BinProductsⱽSETᴰueⱽ {X = X} Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , _) .snd .fst (xᴰ , yᴰ) =
    ΣPathP ((SETᴰ.rectifyOut {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Xᴰ} $
               SETᴰ.reind-filler⁻ {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Xᴰ} _) ,
            (SETᴰ.rectifyOut {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Yᴰ} $
               SETᴰ.reind-filler⁻ {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Yᴰ} _))
  BinProductsⱽSETᴰueⱽ {X = X} Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , _) .snd .snd Zᴰ→XᴰYᴰ =
    funExt₂ λ z zᴰ →
      ΣPathP (
        funExt₂⁻ (SETᴰ.rectifyOut {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Xᴰ}{e' = refl} $
                    SETᴰ.reind-filler⁻ {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Xᴰ} _) z zᴰ ,
        funExt₂⁻ (SETᴰ.rectifyOut {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Yᴰ}{e' = refl} $
                    SETᴰ.reind-filler⁻ {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Yᴰ} _) z zᴰ)

  BinProductsⱽSETᴰ : BinProductsⱽ (SETᴰ ℓ ℓ')
  BinProductsⱽSETᴰ Xᴰ Yᴰ = REPRⱽ (BinProductsⱽSETᴰueⱽ Xᴰ Yᴰ)

  open CartesianCategoryⱽ
  SETᴰCCⱽ : CartesianCategoryⱽ (SET ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  SETᴰCCⱽ .Cᴰ = SETᴰ ℓ ℓ'
  SETᴰCCⱽ .termⱽ = TerminalsⱽSETᴰ
  SETᴰCCⱽ .bpⱽ = BinProductsⱽSETᴰ
  SETᴰCCⱽ .cartesianLifts = isFibrationSETᴰ

  AllLRⱽSETᴰ : AllLRⱽ (SETᴰ ℓ ℓ')
  AllLRⱽSETᴰ =
    BinProductsⱽ+Fibration→AllLRⱽ (SETᴰ ℓ ℓ') BinProductsⱽSETᴰ isFibrationSETᴰ

  -- As in isFibrationSETᴰueⱽ, the implicits below are supplied by hand: eta
  -- for hSet splits the implicit displayed object into _bᴰ.fst/_bᴰ.snd, which
  -- then occur applied to non-variables, so what Agda is left to solve is
  -- non-pattern.
  ExponentialsⱽSETᴰueⱽ :
    {X : hSet ℓ} →
    (Xᴰ Yᴰ : SETᴰ.ob[ X ]) →
    UniversalElementⱽ' (SETᴰ ℓ ℓ') X
      (LRⱽObᴰ→LRⱽ (SETᴰ ℓ ℓ')
        (Xᴰ , AllLRⱽSETᴰ Xᴰ) ⇒ⱽPshSmall (SETᴰ ℓ ℓ' ⟨ X ⟩[-][-, Yᴰ ]))
  ExponentialsⱽSETᴰueⱽ Xᴰ Yᴰ .vertexⱽ x =
    (⟨ Xᴰ x ⟩ → ⟨ Yᴰ x ⟩) , isSet→ (Yᴰ x .snd)
  ExponentialsⱽSETᴰueⱽ Xᴰ Yᴰ .elementⱽ = λ x z → z .fst (z .snd)
  ExponentialsⱽSETᴰueⱽ Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , _) .fst =
    λ z x z₁ z₂ → z x (z₁ , z₂)
  ExponentialsⱽSETᴰueⱽ {X = X} Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , g) .snd .fst f =
    SETᴰ.rectifyOut {a = Z}{b = X}{bᴰ = Yᴰ}{e' = refl} $
    SETᴰ.reind-filler⁻ {a = Z}{b = X}{bᴰ = Yᴰ} _
    ∙ SETᴰ.congᴰ {a = Z}{b = X}{bᴰ = Yᴰ} {f = λ _ → g}
        (λ (u : uTy) z zᴰ → f z (u z zᴰ))
        (funExt₂ λ z zᴰ → ΣPathP
          ( funExt₂⁻
              (SETᴰ.rectifyOut {a = Z}{b = Z}{bᴰ = Zᴰ}{e' = refl} $
               SETᴰ.reind-filler⁻ {a = Z}{b = Z}{bᴰ = Zᴰ} _)
              z zᴰ
          -- The three reinds at Xᴰ are indexed over Z → X and the last one at
          -- g*Xᴰ over Z → Z, so they live in different ∫-Σ-types and cannot be
          -- chained with a single ∙.
          , funExt₂⁻
              (SETᴰ.rectifyOut {a = Z}{b = X}{bᴰ = Xᴰ}{e' = refl} $
               SETᴰ.reind-filler⁻ {a = Z}{b = X}{bᴰ = Xᴰ} _
               ∙ SETᴰ.reind-filler⁻ {a = Z}{b = X}{bᴰ = Xᴰ} _
               ∙ SETᴰ.reind-filler⁻ {a = Z}{b = X}{bᴰ = Xᴰ} _)
              z zᴰ
            ∙ funExt₂⁻
                (SETᴰ.rectifyOut {a = Z}{b = Z}{bᴰ = g*Xᴰ}{e' = refl} $
                 SETᴰ.reind-filler⁻ {a = Z}{b = Z}{bᴰ = g*Xᴰ} _)
                z zᴰ))
    where
    g*Xᴰ = isFibrationSETᴰ._*_ {x = Z} g Xᴰ
    uTy = (z : ⟨ Z ⟩) → (⟨ Zᴰ z ⟩ × ⟨ Xᴰ (g z) ⟩) → ⟨ Zᴰ z ⟩ × ⟨ g*Xᴰ z ⟩
  ExponentialsⱽSETᴰueⱽ {X = X} Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , g) .snd .snd a =
    funExt λ z → funExt λ z₁ → funExt λ z₂ → funExt₂⁻
      (SETᴰ.rectifyOut {a = Z}{b = X}{bᴰ = Yᴰ}{e' = refl} $
       SETᴰ.reind-filler⁻ {a = Z}{b = X}{bᴰ = Yᴰ} _
       ∙ SETᴰ.congᴰ {a = Z}{b = X}{bᴰ = Yᴰ} {f = λ _ → g}
           (λ (u : uTy) z' zᴰ → a z' (u z' zᴰ .fst) (u z' zᴰ .snd))
           (funExt₂ λ z' zᴰ → ΣPathP
             ( funExt₂⁻
                 (SETᴰ.rectifyOut {a = Z}{b = Z}{bᴰ = Zᴰ}{e' = refl} $
                  SETᴰ.reind-filler⁻ {a = Z}{b = Z}{bᴰ = Zᴰ} _)
                 z' zᴰ
             , funExt₂⁻
                 (SETᴰ.rectifyOut {a = Z}{b = X}{bᴰ = Xᴰ}{e' = refl} $
                  SETᴰ.reind-filler⁻ {a = Z}{b = X}{bᴰ = Xᴰ} _
                  ∙ SETᴰ.reind-filler⁻ {a = Z}{b = X}{bᴰ = Xᴰ} _
                  ∙ SETᴰ.reind-filler⁻ {a = Z}{b = X}{bᴰ = Xᴰ} _)
                 z' zᴰ
               ∙ funExt₂⁻
                   (SETᴰ.rectifyOut {a = Z}{b = Z}{bᴰ = g*Xᴰ}{e' = refl} $
                    SETᴰ.reind-filler⁻ {a = Z}{b = Z}{bᴰ = g*Xᴰ} _)
                   z' zᴰ)))
      z (z₁ , z₂)
    where
    g*Xᴰ = isFibrationSETᴰ._*_ {x = Z} g Xᴰ
    uTy = (z : ⟨ Z ⟩) → (⟨ Zᴰ z ⟩ × ⟨ Xᴰ (g z) ⟩) → ⟨ Zᴰ z ⟩ × ⟨ g*Xᴰ z ⟩

  ExponentialsⱽSETᴰ : Exponentialsⱽ (SETᴰ ℓ ℓ') AllLRⱽSETᴰ
  ExponentialsⱽSETᴰ Xᴰ Yᴰ = REPRⱽ (ExponentialsⱽSETᴰueⱽ Xᴰ Yᴰ)

-- ∀ over ⟨ A ⟩ : Type ℓ lands the fibre in ℓ-max ℓ ℓ', so the quantifier and
-- the CCCⱽ it feeds are over SETᴰ ℓ (ℓ-max ℓ ℓ') rather than SETᴰ ℓ ℓ'.
module _ {ℓ ℓ'} where
  private
    module SETᴰ = Fibers (SETᴰ ℓ (ℓ-max ℓ ℓ'))
    module bpS = BinProductsNotation (BinProductsSET {ℓ})

  open UniversalQuantifiers

  UniversalQuantifiersSETᴰ :
    UniversalQuantifiers (SETᴰ ℓ (ℓ-max ℓ ℓ')) (BinProductsSET {ℓ})
      isFibrationSETᴰ
  UniversalQuantifiersSETᴰ .∀Ob {Γ} {A} Aᴰ = REPRⱽ ue where
    ue : UniversalElementⱽ' (SETᴰ ℓ (ℓ-max ℓ ℓ')) Γ
           (∀Pshⱽ (SETᴰ ℓ (ℓ-max ℓ ℓ')) A (λ c → BinProductsSET (c , A))
             (λ Δ yᴰ →
               isFibrationSETᴰ yᴰ (Δ bpS.× A) (bpS.π₁ {a = Δ}{b = A}))
             Aᴰ)
    ue .vertexⱽ γ =
      (∀ (a : ⟨ A ⟩) → ⟨ Aᴰ (γ , a) ⟩) , isSetΠ (λ a → Aᴰ (γ , a) .snd)
    ue .elementⱽ x h = h (x .snd)
    ue .universalⱽ (Δ , Δᴰ , f) .fst k d dd a = k (d , a) dd
    ue .universalⱽ (Δ , Δᴰ , f) .snd .fst b =
      SETᴰ.rectifyOut {a = Δ bpS.× A}{b = Γ bpS.× A}{bᴰ = Aᴰ}{e' = refl} $
      SETᴰ.reind-filler⁻ {a = Δ bpS.× A}{b = Γ bpS.× A}{bᴰ = Aᴰ} _
      ∙ SETᴰ.congᴰ {a = Δ bpS.× A}{b = Γ bpS.× A}{bᴰ = Aᴰ}
          {f = λ _ x → f (x .fst) , x .snd}
          (λ (u : uTy) x p → u x p (x .snd))
          ( SETᴰ.rectifyOut
              {a = Δ bpS.× A}{b = Γ}{bᴰ = ue .vertexⱽ}{e' = refl}
              (SETᴰ.reind-filler⁻
                {a = Δ bpS.× A}{b = Γ}{bᴰ = ue .vertexⱽ} _)
          ∙ cong (λ (q : qTy) x p a' → b (x .fst , a') (q x p))
              (SETᴰ.rectifyOut {a = Δ bpS.× A}{b = Δ}{bᴰ = Δᴰ}{e' = refl}
                (SETᴰ.reind-filler⁻ {a = Δ bpS.× A}{b = Δ}{bᴰ = Δᴰ} _)))
      where
      uTy = (x : ⟨ Δ bpS.× A ⟩) → ⟨ Δᴰ (x .fst) ⟩ →
            (a' : ⟨ A ⟩) → ⟨ Aᴰ (f (x .fst) , a') ⟩
      qTy = (x : ⟨ Δ bpS.× A ⟩) → ⟨ Δᴰ (x .fst) ⟩ → ⟨ Δᴰ (x .fst) ⟩
    ue .universalⱽ (Δ , Δᴰ , f) .snd .snd a =
      funExt λ d → funExt λ dd → funExt λ a₁ → funExt₂⁻
        (SETᴰ.rectifyOut {a = Δ bpS.× A}{b = Γ bpS.× A}{bᴰ = Aᴰ}{e' = refl} $
         SETᴰ.reind-filler⁻ {a = Δ bpS.× A}{b = Γ bpS.× A}{bᴰ = Aᴰ} _
         ∙ SETᴰ.congᴰ {a = Δ bpS.× A}{b = Γ bpS.× A}{bᴰ = Aᴰ}
             {f = λ _ x → f (x .fst) , x .snd}
             (λ (u : uTy) x p → u x p (x .snd))
             ( SETᴰ.rectifyOut
                 {a = Δ bpS.× A}{b = Γ}{bᴰ = ue .vertexⱽ}{e' = refl}
                 (SETᴰ.reind-filler⁻
                   {a = Δ bpS.× A}{b = Γ}{bᴰ = ue .vertexⱽ} _)
             ∙ cong (λ (q : qTy) x p a' → a (x .fst) (q x p) a')
                 (SETᴰ.rectifyOut
                   {a = Δ bpS.× A}{b = Δ}{bᴰ = Δᴰ}{e' = refl}
                   (SETᴰ.reind-filler⁻
                     {a = Δ bpS.× A}{b = Δ}{bᴰ = Δᴰ} _))))
        (d , a₁) dd
      where
      uTy = (x : ⟨ Δ bpS.× A ⟩) → ⟨ Δᴰ (x .fst) ⟩ →
            (a' : ⟨ A ⟩) → ⟨ Aᴰ (f (x .fst) , a') ⟩
      qTy = (x : ⟨ Δ bpS.× A ⟩) → ⟨ Δᴰ (x .fst) ⟩ → ⟨ Δᴰ (x .fst) ⟩

  open CartesianClosedCategoryⱽ

  SETᴰCCCⱽ : CartesianClosedCategoryⱽ (SETCC {ℓ})
    (ℓ-max ℓ (ℓ-suc (ℓ-max ℓ ℓ'))) (ℓ-max ℓ ℓ')
  SETᴰCCCⱽ .CCⱽ = SETᴰCCⱽ
  SETᴰCCCⱽ .lrⱽ = AllLRⱽSETᴰ
  SETᴰCCCⱽ .expⱽ = ExponentialsⱽSETᴰ
  SETᴰCCCⱽ .forallⱽ = UniversalQuantifiersSETᴰ

import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Sets as EqSets
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianClosedV
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.BiCartesianClosedV
open import Cubical.Categories.Displayed.Limits.BiCartesianClosedV

EqSETᴰCCⱽ : CartesianCategoryⱽ (SET ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
EqSETᴰCCⱽ = EqCCⱽ→CCⱽ EqSets.SetAssoc (SETᴰ _ _) EqSets.isCartesianⱽSETᴰ

EqSETᴰCCⱽ^op : CartesianCategoryⱽ (SET ℓ ^op) (ℓ-suc ℓ) ℓ
EqSETᴰCCⱽ^op {ℓ = ℓ} = EqCCⱽ→CCⱽ EqSets.SetAssoc^op ((SETᴰ _ _) ^opᴰ)
  EqSets.isCartesianⱽSETᴰ^op

EqSETᴰCCCⱽ : CartesianClosedCategoryⱽ SETCC (ℓ-suc ℓ) ℓ
EqSETᴰCCCⱽ  =
  EqCCCⱽ→CCCⱽ SETCC EqSets.SetAssoc EqSets.SetIdL EqSets.Setπ₁NatEq
    EqSets.Set×aF-seq (SETᴰ _ _) EqSets.isCCCⱽSETᴰ

EqSETᴰBCCCⱽ : BiCartesianClosedCategoryⱽ SETCC (ℓ-suc ℓ) ℓ
EqSETᴰBCCCⱽ =
  EqBCCCⱽ→BCCCⱽ SETCC EqSets.SetAssoc EqSets.SetIdL EqSets.Setπ₁NatEq
    EqSets.Set×aF-seq (SETᴰ _ _) EqSets.SetAssoc^op
    EqSets.isCCCⱽSETᴰ EqSets.isCartesianⱽSETᴰ^op
