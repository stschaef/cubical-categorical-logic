{-
  The IsoComma category of two cartesian closed functors,
  viewed as a displayed cartesian closed category.

  Extends IsoComma.Cartesian with exponential structure.
-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Constructions.IsoComma.CartesianClosed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.Dependent

open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation hiding (_⇒_)
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Exponentials.Small
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.Terminal as Term
open import Cubical.Categories.Limits.Terminal.More as Term
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Constructions.Reindex

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Constructions.Comma
open import Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Constructions.IsoComma.Cartesian
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Section.Base

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category hiding (_∘_)
open Functor
open Section
open CartesianCategory using (C; term; bp)
open CartesianClosedCategory using (CC; exps)
open CartesianCategoryᴰ
open CartesianClosedCategoryᴰ
open isIsoOver

module _ (CCC : CartesianClosedCategory ℓC ℓC') where
  private module CCC' = CartesianClosedCategory CCC
  open CCC' using (_⇒_; _×_; lda; app)

  module _
    {D : Category ℓD ℓD'}
    ((F , F-bp) (G , G-bp) : CartesianFunctor (CCC .CC) D)
    (F-1 : Term.preservesTerminal (CCC .CC .C) D F)
    (G-1 : Term.preservesTerminal (CCC .CC .C) D G)
    (⇒-iso : ∀ {A B} → CatIso D (F ⟅ A ⟆) (G ⟅ A ⟆)
                       → CatIso D (F ⟅ B ⟆) (G ⟅ B ⟆)
                       → CatIso D (F ⟅ A ⇒ B ⟆) (G ⟅ A ⇒ B ⟆))
    (⇒-lam : ∀ {A B Γ} (f : CatIso D (F ⟅ A ⟆) (G ⟅ A ⟆))
                         (g : CatIso D (F ⟅ B ⟆) (G ⟅ B ⟆))
                         (γ : CatIso D (F ⟅ Γ ⟆) (G ⟅ Γ ⟆))
             → (h : (CCC .CC .C) [ Γ × A , B ])
             → (D ._⋆_ (F ⟪ lda h ⟫) (⇒-iso f g .fst))
               ≡ (D ._⋆_ (γ .fst) (G ⟪ lda h ⟫)))
    where
    private
      module D = Category D

      theCC : CartesianCategoryᴰ (CCC .CC) _ _
      theCC = IsoCommaCartesianᴰ (CCC .CC) (F , F-bp) (G , G-bp) F-1 G-1

      F,G-IsoC : Categoryᴰ CCC'.C _ _
      F,G-IsoC = theCC .Cᴰ

    module _
      (⇒-eval : ∀ {A B} (f : CatIso D (F ⟅ A ⟆) (G ⟅ A ⟆))
                         (g : CatIso D (F ⟅ B ⟆) (G ⟅ B ⟆))
               → F ⟪ app ⟫ D.⋆ g .fst
                 ≡ theCC .bpᴰ (⇒-iso f g) f .fst .fst
                   D.⋆ G ⟪ app ⟫)
      where

      -- The IsoComma of two CCC functors forms
      -- a displayed cartesian closed category
      IsoCommaCCCᴰ : CartesianClosedCategoryᴰ CCC _ _
      IsoCommaCCCᴰ .CartesianClosedCategoryᴰ.CCᴰ = theCC
      IsoCommaCCCᴰ .CartesianClosedCategoryᴰ.expᴰ {A = A} f {B = B} g =
        ⇒-iso f g , (⇒-eval f g , tt) , isUniv
        where
        isUniv : isUniversalᴰ F,G-IsoC _ _
          (CCC .exps A B) (⇒-eval f g , tt)
        isUniv Γ Γᴰ .inv u uᴰ .fst = ⇒-lam f g Γᴰ u
        isUniv Γ Γᴰ .inv _ _ .snd = tt
        isUniv Γ Γᴰ .rightInv _ _ =
          isProp→PathP (λ _ → isPropΣ (D.isSetHom _ _) λ _ → isPropUnit) _ _
        isUniv Γ Γᴰ .leftInv _ _ =
          isProp→PathP (λ _ → isPropΣ (D.isSetHom _ _) λ _ → isPropUnit) _ _
