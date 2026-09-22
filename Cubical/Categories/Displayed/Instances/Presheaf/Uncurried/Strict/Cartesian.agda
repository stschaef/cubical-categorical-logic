{-# OPTIONS --lossy-unification #-}
{-
  Path-based (Eq-free) vertical cartesian structure on PRESHEAFᴰ: vertical
  terminal objects, vertical binary products and cartesian lifts, packaged
  as a `CartesianCategoryⱽ` over the strict PRESHEAF.

  Each vertical universal property is stated against a spec presheaf whose
  `F-hom` inserts a `reind` along a base identity law, and none of those
  `reind`s is ever forced: a `reind` is a `subst` in the large `PshHom`
  family, so evaluating one costs more than the rest of the file.  The
  discipline, used in every clause below, is to state each β law as
  `reind e (γᴰ ⋆ᴰ π) ≡ <reind-free term>` and strip the `reind`
  symbolically with `reind-filler⁻`, leaving a residual obligation that is
  definitional on `N-ob`; the η law is then derived from the β laws by
  `cong`/`cong₂`, never by pairing the two `reind`ed terms under a single
  `makePshHomPath`.
-}
module Cubical.Categories.Displayed.Instances.Presheaf.Uncurried.Strict.Cartesian where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.BinProduct as BP
open import Cubical.Categories.Presheaf.StrictHom

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Instances.Presheaf.Uncurried.Strict.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓP ℓPᴰ : Level

open PshIso
open UniversalElementⱽ'

module _ {C : Category ℓC ℓC'} (ℓP ℓPᴰ : Level)
         (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    PSHᴰ = PRESHEAFᴰ C ℓP ℓPᴰ Cᴰ
    module PSH = Category (PRESHEAF C ℓP)
    module PSHᴰ = Fibers PSHᴰ

  PSHᴰTerminalsⱽ : Terminalsⱽ PSHᴰ
  PSHᴰTerminalsⱽ P = REPRⱽ termⱽ where
    termⱽ : UniversalElementⱽ' PSHᴰ P UnitPshᴰ
    termⱽ .vertexⱽ = Unit*Psh
    termⱽ .elementⱽ = tt
    termⱽ .universalⱽ (R , Rᴰ , α) .fst _ =
      Unit*Psh-intro ⋆PshHom invPshIso (reindPsh-Unit* _) .trans
    termⱽ .universalⱽ (R , Rᴰ , α) .snd .fst _ = refl
    termⱽ .universalⱽ (R , Rᴰ , α) .snd .snd αᴰ = makePshHomPath refl

  module _ {P : Presheaf C ℓP} (Pᴰ Qᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
    private
      module _ {R : Presheaf C ℓP} {Rᴰ : Presheafᴰ R Cᴰ ℓPᴰ}
               {α : PshHomStrict R P} where
        ×proj₁ : PSHᴰ.Hom[ α ][ Rᴰ , Pᴰ ×Psh Qᴰ ] → PSHᴰ.Hom[ α ][ Rᴰ , Pᴰ ]
        ×proj₁ γᴰ = γᴰ ⋆PshHom reindPsh× _ Pᴰ Qᴰ .trans ⋆PshHom BP.π₁ _ _

        ×proj₂ : PSHᴰ.Hom[ α ][ Rᴰ , Pᴰ ×Psh Qᴰ ] → PSHᴰ.Hom[ α ][ Rᴰ , Qᴰ ]
        ×proj₂ γᴰ = γᴰ ⋆PshHom reindPsh× _ Pᴰ Qᴰ .trans ⋆PshHom BP.π₂ _ _

        ×introⱽ : PSHᴰ.Hom[ α ][ Rᴰ , Pᴰ ] → PSHᴰ.Hom[ α ][ Rᴰ , Qᴰ ]
          → PSHᴰ.Hom[ α ][ Rᴰ , Pᴰ ×Psh Qᴰ ]
        ×introⱽ αᴰP αᴰQ =
          ×PshIntro αᴰP αᴰQ ⋆PshHom invPshIso (reindPsh× _ Pᴰ Qᴰ) .trans

      elt₁ : PSHᴰ.Hom[ PSH.id ][ Pᴰ ×Psh Qᴰ , Pᴰ ]
      elt₁ = BP.π₁ Pᴰ Qᴰ ⋆PshHom PSHᴰ.idᴰ
      elt₂ : PSHᴰ.Hom[ PSH.id ][ Pᴰ ×Psh Qᴰ , Qᴰ ]
      elt₂ = BP.π₂ Pᴰ Qᴰ ⋆PshHom PSHᴰ.idᴰ

      module _ {R : Presheaf C ℓP} {Rᴰ : Presheafᴰ R Cᴰ ℓPᴰ}
               {α : PshHomStrict R P} where
        ×βⱽ₁ : (γᴰ : PSHᴰ.Hom[ α ][ Rᴰ , Pᴰ ×Psh Qᴰ ])
          → PSHᴰ.reind (PSH.⋆IdR α) (γᴰ PSHᴰ.⋆ᴰ elt₁) ≡ ×proj₁ γᴰ
        ×βⱽ₁ γᴰ = PSHᴰ.rectifyOut
          (PSHᴰ.reind-filler⁻ _ ∙ PSHᴰ.≡in {pth = refl} (makePshHomPath refl))

        ×βⱽ₂ : (γᴰ : PSHᴰ.Hom[ α ][ Rᴰ , Pᴰ ×Psh Qᴰ ])
          → PSHᴰ.reind (PSH.⋆IdR α) (γᴰ PSHᴰ.⋆ᴰ elt₂) ≡ ×proj₂ γᴰ
        ×βⱽ₂ γᴰ = PSHᴰ.rectifyOut
          (PSHᴰ.reind-filler⁻ _ ∙ PSHᴰ.≡in {pth = refl} (makePshHomPath refl))

        ×ηⱽ : (γᴰ : PSHᴰ.Hom[ α ][ Rᴰ , Pᴰ ×Psh Qᴰ ])
          → γᴰ ≡ ×introⱽ (×proj₁ γᴰ) (×proj₂ γᴰ)
        ×ηⱽ γᴰ = makePshHomPath refl

      bpⱽ : UniversalElementⱽ' PSHᴰ P
        ((PSHᴰ [-][-, Pᴰ ]) ×ⱽPsh (PSHᴰ [-][-, Qᴰ ]))
      bpⱽ .vertexⱽ = Pᴰ ×Psh Qᴰ
      bpⱽ .elementⱽ = elt₁ , elt₂
      bpⱽ .universalⱽ (R , Rᴰ , α) .fst (αᴰP , αᴰQ) = ×introⱽ αᴰP αᴰQ
      bpⱽ .universalⱽ (R , Rᴰ , α) .snd .fst (αᴰP , αᴰQ) =
        ≡-× (×βⱽ₁ _ ∙ makePshHomPath refl) (×βⱽ₂ _ ∙ makePshHomPath refl)
      bpⱽ .universalⱽ (R , Rᴰ , α) .snd .snd γᴰ =
        cong₂ ×introⱽ (×βⱽ₁ γᴰ) (×βⱽ₂ γᴰ) ∙ sym (×ηⱽ γᴰ)

    PSHᴰBinProductⱽ : BinProductⱽ PSHᴰ Pᴰ Qᴰ
    PSHᴰBinProductⱽ = REPRⱽ bpⱽ

  PSHᴰBinProductsⱽ : BinProductsⱽ PSHᴰ
  PSHᴰBinProductsⱽ = PSHᴰBinProductⱽ

  module _ {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
           {R : Presheaf C ℓP} (α : PshHomStrict R P) where
    private
      module _ {S : Presheaf C ℓP} {Sᴰ : Presheafᴰ S Cᴰ ℓPᴰ}
               {β : PshHomStrict S R} where
        fib-intro : PSHᴰ.Hom[ β PSH.⋆ α ][ Sᴰ , Pᴰ ]
          → PSHᴰ.Hom[ β ][ Sᴰ , reindPshᴰNatTransStrict α Pᴰ ]
        fib-intro βᴰ = βᴰ ⋆PshHom reindPshᴰNatTransStrict-seq β α Pᴰ .trans

        fib-intro⁻ : PSHᴰ.Hom[ β ][ Sᴰ , reindPshᴰNatTransStrict α Pᴰ ]
          → PSHᴰ.Hom[ β PSH.⋆ α ][ Sᴰ , Pᴰ ]
        fib-intro⁻ γᴰ =
          γᴰ ⋆PshHom invPshIso (reindPshᴰNatTransStrict-seq β α Pᴰ) .trans

      fibⱽ : UniversalElementⱽ' PSHᴰ R
        (reindPshᴰNatTrans (yoRec ((PRESHEAF C ℓP) [-, P ]) α)
          (PSHᴰ [-][-, Pᴰ ]))
      fibⱽ .vertexⱽ = reindPshᴰNatTransStrict α Pᴰ
      fibⱽ .elementⱽ = idPshHom
      fibⱽ .universalⱽ (S , Sᴰ , β) .fst = fib-intro
      fibⱽ .universalⱽ (S , Sᴰ , β) .snd .fst βᴰ = PSHᴰ.rectifyOut
        (PSHᴰ.reind-filler⁻ _ ∙ PSHᴰ.≡in {pth = refl} (makePshHomPath refl))
      fibⱽ .universalⱽ (S , Sᴰ , β) .snd .snd γᴰ =
        cong fib-intro
          (PSHᴰ.rectifyOut (PSHᴰ.reind-filler⁻ _
            ∙ PSHᴰ.≡in {pth = refl} (makePshHomPath {β = fib-intro⁻ γᴰ} refl)))
        ∙ makePshHomPath refl

    PSHᴰCartesianLift : CartesianLiftPsh ((PRESHEAF C ℓP) [-, P ]) PSHᴰ
      (PSHᴰ [-][-, Pᴰ ]) α
    PSHᴰCartesianLift = REPRⱽ fibⱽ

  PSHᴰisFibration : isFibration PSHᴰ
  PSHᴰisFibration Pᴰ R α = PSHᴰCartesianLift Pᴰ α

  PSHᴰCCⱽ : CartesianCategoryⱽ (PRESHEAF C ℓP) _ _
  PSHᴰCCⱽ .CartesianCategoryⱽ.Cᴰ = PSHᴰ
  PSHᴰCCⱽ .CartesianCategoryⱽ.termⱽ = PSHᴰTerminalsⱽ
  PSHᴰCCⱽ .CartesianCategoryⱽ.bpⱽ = PSHᴰBinProductsⱽ
  PSHᴰCCⱽ .CartesianCategoryⱽ.cartesianLifts = PSHᴰisFibration
