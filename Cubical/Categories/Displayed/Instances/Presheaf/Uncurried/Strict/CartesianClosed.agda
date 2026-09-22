{-# OPTIONS --lossy-unification #-}
{-
  Path-based (Eq-free) vertical exponentials for displayed presheaves.

  What is established here is the pointwise universal property of the
  vertical exponential, `expIsoⱽ`.  What is not established is naturality of
  that family, which `Exponentialⱽ` additionally requires, so this module
  does not yet produce `Exponentialⱽ PSHᴰ (Pᴰ , PSHᴰAllLRⱽ Pᴰ) Qᴰ`.

  Over the Eq slice the naturality triangle is discharged by matching
  `Eq.refl`; over the path slice it is a genuine path, and the residual
  obligation is the Frobenius bookkeeping of `Δᴰ` against `Δᴰ ×Psh (δ *Pᴰ)`
  -- the same square as `×LRⱽ-Path/→Eq/-square` in
  Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianClosedV.
-}
module Cubical.Categories.Displayed.Instances.Presheaf.Uncurried.Strict.CartesianClosed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.BinProduct as BP
open import Cubical.Categories.Presheaf.Constructions.Exponential
open import Cubical.Categories.Presheaf.StrictHom

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Exponential
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Instances.Presheaf.Uncurried.Strict.Base
open import Cubical.Categories.Displayed.Instances.Presheaf.Uncurried.Strict.Cartesian

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  ℓPSHᴰ : Level
  ℓPSHᴰ = ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ')

  private
    PSHᴰ = PRESHEAFᴰ C ℓPSHᴰ ℓPSHᴰ Cᴰ
    module PSH = Category (PRESHEAF C ℓPSHᴰ)
    module PSHᴰ = Fibers PSHᴰ

  PSHᴰAllLRⱽ : AllLRⱽ PSHᴰ
  PSHᴰAllLRⱽ = BinProductsⱽ+Fibration→AllLRⱽ PSHᴰ
    (PSHᴰBinProductsⱽ ℓPSHᴰ ℓPSHᴰ Cᴰ) (PSHᴰisFibration ℓPSHᴰ ℓPSHᴰ Cᴰ)

  module _ {P : Presheaf C ℓPSHᴰ} (Pᴰ Qᴰ : Presheafᴰ P Cᴰ ℓPSHᴰ) where
    private
      E : Presheafᴰ P Cᴰ ℓPSHᴰ
      E = Pᴰ ⇒PshLarge Qᴰ

    -- The forded route's `PSHᴰExponentials` chain, transcribed with the
    -- Eq-based reindexings replaced by their path-based counterparts.  The
    -- coercions between the two spellings of reindexing are
    -- `reindPshᴰNatTrans≅StrictId` rather than the library's
    -- `reindPshᴰNatTrans≅Strict`, whose `N-ob` is a transport that survives
    -- into every downstream equation.
    expIsoⱽ : ∀ {R : Presheaf C ℓPSHᴰ} (Rᴰ : Presheafᴰ R Cᴰ ℓPSHᴰ)
      (α : PshHomStrict R P)
      → Iso (PSHᴰ.Hom[ α ][ Rᴰ , E ])
            (PshHom (Rᴰ ×Psh reindPshᴰNatTransStrict α Pᴰ)
                    (reindPshᴰNatTransStrict α Qᴰ))
    expIsoⱽ Rᴰ α =
      compIso (postcomp⋆PshHom-Iso
                (invPshIso (reindPshᴰNatTrans≅StrictId E)))
      (compIso (invIso (push-UMP α' Rᴰ))
      (compIso (⇒PshLarge-UMP Pᴰ Qᴰ)
      (compIso (precomp⋆PshHom-Iso (FrobeniusReciprocity α' Rᴰ Pᴰ))
      (compIso (push-UMP α' (Rᴰ ×Psh reindPshᴰNatTrans α' Pᴰ))
      (compIso (precomp⋆PshHom-Iso
                 (×PshIso idPshIso
                   (invPshIso (reindPshᴰNatTrans≅StrictId Pᴰ))))
               (postcomp⋆PshHom-Iso
                 (reindPshᴰNatTrans≅StrictId Qᴰ)))))))
      where α' = PshHomStrict→PshHom α

    expSpec : Presheafⱽ P PSHᴰ ℓPSHᴰ
    expSpec =
      LRⱽObᴰ→LRⱽ PSHᴰ (Pᴰ , PSHᴰAllLRⱽ Pᴰ) ⇒ⱽPshSmall (PSHᴰ [-][-, Qᴰ ])

    -- `expIsoⱽ .fun` as a family over the slice: the `N-ob` of the
    -- `PshHomⱽ (PSHᴰ [-][-, E ]) expSpec` that `Exponentialⱽ` asks for.  It
    -- is naturality of this family that is still missing.
    expFun : ∀ (R3 : Category.ob (PSHᴰ / ((PRESHEAF C ℓPSHᴰ) [-, P ])))
      → PresheafNotation.p[ (PSHᴰ [-][-, E ]) ] R3
      → PresheafNotation.p[ expSpec ] R3
    expFun (R , Rᴰ , α) = expIsoⱽ Rᴰ α .Iso.fun
