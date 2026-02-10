{-
  The IsoComma category of two cartesian functors,
  viewed as a displayed cartesian category.

  Given a CartesianCategory CC, a Category D, and
  CartesianFunctors (F,F-bp) (G,G-bp) : CC → D that
  preserve terminal objects, the IsoComma displayed
  category reindexed along the diagonal Δ forms a
  displayed cartesian category over CC.
-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Constructions.IsoComma.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.Dependent

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Terminal as Term
open import Cubical.Categories.Limits.Terminal.More as Term
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Constructions.Reindex

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Constructions.Comma
open import Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Section.Base

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor
open Section
open CartesianCategory using (C; term; bp)
open CartesianCategoryᴰ
open isIsoOver

module _
  (CC : CartesianCategory ℓC ℓC')
  {D : Category ℓD ℓD'}
  ((F , F-bp) (G , G-bp) : CartesianFunctor CC D)
  (F-1 : Term.preservesTerminal (CC .C) D F)
  (G-1 : Term.preservesTerminal (CC .C) D G)
  where
  private
    module CC = CartesianCategory CC
    module D = Category D

    F,G-IsoC : Categoryᴰ CC.C _ _
    F,G-IsoC = Reindex.reindex (IsoCommaᴰ F G) (Δ CC.C)

  -- The IsoComma of two cartesian functors forms
  -- a displayed cartesian category
  IsoCommaCartesianᴰ : CartesianCategoryᴰ CC _ _
  IsoCommaCartesianᴰ .Cᴰ = F,G-IsoC
  IsoCommaCartesianᴰ .termᴰ =
    F⊤≅G⊤ , _ , isUniv
    where
    F⊤ : Terminal D
    F⊤ = _ , F-1 (Terminal'ToTerminal $ CC .term)

    G⊤ : Terminal D
    G⊤ = _ , G-1 (Terminal'ToTerminal $ CC .term)

    module G⊤ = TerminalNotation (terminalToUniversalElement G⊤)

    F⊤≅G⊤ : CatIso D (F ⟅ CC.𝟙 ⟆) (G ⟅ CC.𝟙 ⟆)
    F⊤≅G⊤ = terminalToIso D F⊤ G⊤

    isUniv : isUniversalᴰ F,G-IsoC _ _
      (CC .term) tt
    isUniv Γ Γᴰ .inv _ _ .fst = G⊤.𝟙extensionality
    isUniv Γ Γᴰ .inv _ _ .snd = _
    isUniv Γ Γᴰ .rightInv = λ _ _ → refl
    isUniv Γ Γᴰ .leftInv u v =
      isProp→PathP (λ _ → isPropΣ (D.isSetHom _ _) λ _ → isPropUnit) _ _
  IsoCommaCartesianᴰ .bpᴰ {A = A}{B = B} f g =
    F×≅G× , ((sym G×.×β₁ , tt) , (sym G×.×β₂ , tt)) , isUniv
    where
    module CC× = BinProductNotation (CC .bp (A , B))
    F× = preservesUniversalElement→UniversalElement
          (preservesBinProdCones F A B)
          (CC .bp (A , B)) (F-bp A B)
    G× = preservesUniversalElement→UniversalElement
          (preservesBinProdCones G A B)
          (CC .bp (A , B)) (G-bp A B)
    module F× = BinProductNotation F×
    module G× = BinProductNotation G×

    forward = (F×.π₁ D.⋆ f .fst) G×.,p (F×.π₂ D.⋆ g .fst)
    backward = (G×.π₁ D.⋆ f .snd .isIso.inv) F×.,p (G×.π₂ D.⋆ g .snd .isIso.inv)

    F×≅G× : CatIso D _ _
    F×≅G× .fst = forward
    F×≅G× .snd .isIso.inv = backward
    F×≅G× .snd .isIso.sec = G×.,p-extensionality
      (D.⋆Assoc _ _ _
      ∙ D.⟨ refl ⟩⋆⟨ G×.×β₁ ⟩
      ∙ sym (D.⋆Assoc _ _ _)
      ∙ D.⟨ F×.×β₁ ⟩⋆⟨ refl ⟩
      ∙ D.⋆Assoc _ _ _
      ∙ D.⟨ refl ⟩⋆⟨ f .snd .isIso.sec ⟩
      ∙ D.⋆IdR _
      ∙ sym (D.⋆IdL _))
      (D.⋆Assoc _ _ _
      ∙ D.⟨ refl ⟩⋆⟨ G×.×β₂ ⟩
      ∙ sym (D.⋆Assoc _ _ _)
      ∙ D.⟨ F×.×β₂ ⟩⋆⟨ refl ⟩
      ∙ D.⋆Assoc _ _ _
      ∙ D.⟨ refl ⟩⋆⟨ g .snd .isIso.sec ⟩
      ∙ D.⋆IdR _
      ∙ sym (D.⋆IdL _))
    F×≅G× .snd .isIso.ret = F×.,p-extensionality
      (D.⋆Assoc _ _ _
      ∙ D.⟨ refl ⟩⋆⟨ F×.×β₁ ⟩
      ∙ sym (D.⋆Assoc _ _ _)
      ∙ D.⟨ G×.×β₁ ⟩⋆⟨ refl ⟩
      ∙ D.⋆Assoc _ _ _
      ∙ D.⟨ refl ⟩⋆⟨ f .snd .isIso.ret ⟩
      ∙ D.⋆IdR _
      ∙ sym (D.⋆IdL _))
      (D.⋆Assoc _ _ _
      ∙ D.⟨ refl ⟩⋆⟨ F×.×β₂ ⟩
      ∙ sym (D.⋆Assoc _ _ _)
      ∙ D.⟨ G×.×β₂ ⟩⋆⟨ refl ⟩
      ∙ D.⋆Assoc _ _ _
      ∙ D.⟨ refl ⟩⋆⟨ g .snd .isIso.ret ⟩
      ∙ D.⋆IdR _
      ∙ sym (D.⋆IdL _))

    isUniv : isUniversalᴰ F,G-IsoC _ _
      (CC .bp (A , B))
      ((sym G×.×β₁ , tt) , (sym G×.×β₂ , tt))
    isUniv Γ Γᴰ .inv (u₁ , u₂) ((sq₁ , _) , (sq₂ , _)) .fst =
      G×.,p-extensionality
        (D.⋆Assoc _ _ _
        ∙ D.⟨ refl ⟩⋆⟨ G×.×β₁ ⟩
        ∙ sym (D.⋆Assoc _ _ _)
        ∙ D.⟨ sym (F .F-seq _ _) ∙ cong (F .F-hom) CC×.×β₁ ⟩⋆⟨ refl ⟩
        ∙ sq₁
        ∙ D.⟨ refl ⟩⋆⟨ sym (cong (G .F-hom) CC×.×β₁) ∙ G .F-seq _ _ ⟩
        ∙ sym (D.⋆Assoc _ _ _))
        (D.⋆Assoc _ _ _
        ∙ D.⟨ refl ⟩⋆⟨ G×.×β₂ ⟩
        ∙ sym (D.⋆Assoc _ _ _)
        ∙ D.⟨ sym (F .F-seq _ _) ∙ cong (F .F-hom) CC×.×β₂ ⟩⋆⟨ refl ⟩
        ∙ sq₂
        ∙ D.⟨ refl ⟩⋆⟨ sym (cong (G .F-hom) CC×.×β₂) ∙ G .F-seq _ _ ⟩
        ∙ sym (D.⋆Assoc _ _ _))
    isUniv Γ Γᴰ .inv _ _ .snd = tt
    isUniv Γ Γᴰ .rightInv _ _ =
      isProp→PathP (λ _ → isProp×
        (isPropΣ (D.isSetHom _ _) λ _ → isPropUnit)
        (isPropΣ (D.isSetHom _ _) λ _ → isPropUnit)) _ _
    isUniv Γ Γᴰ .leftInv _ _ =
      isProp→PathP (λ _ → isPropΣ (D.isSetHom _ _) λ _ → isPropUnit) _ _

  -- A global section of the IsoComma gives a natural isomorphism
  sectionToNatIso : GlobalSection F,G-IsoC → NatIso F G
  sectionToNatIso S .NatIso.trans .NatTrans.N-ob x = S .F-obᴰ x .fst
  sectionToNatIso S .NatIso.trans .NatTrans.N-hom f = S .F-homᴰ f .fst
  sectionToNatIso S .NatIso.nIso x = S .F-obᴰ x .snd
