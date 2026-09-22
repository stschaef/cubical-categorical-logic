{-# OPTIONS --lossy-unification #-}
{-
  The displayed category of uncurried, path-based displayed presheaves,
  displayed over the category PRESHEAF of presheaves and *strict* presheaf
  morphisms (Cubical.Categories.Presheaf.StrictHom.Base).

  This is the Eq-free counterpart of
  Cubical.Categories.Displayed.Instances.Presheaf.Eq.Base.PRESHEAFᴰ.  The
  fibre over P is `Presheafᴰ P Cᴰ ℓPᴰ = Presheaf (Cᴰ / P)` for the PATH
  slice `Cᴰ / P`, not the Eq slice `∫C (Cᴰ ×ᴰ EqElement P)` of the forded
  development, and reindexing is `reindPshᴰNatTransStrict`, a plain
  `reindPsh` along a functor built from a `PshHomStrict`.

  Taking PRESHEAF, rather than the PshHom-based category of presheaves, as
  the base is load-bearing.  A `PshHomStrict` takes its naturality equation
  `f ⋆ p' ≡ p` as an argument rather than producing one, so PRESHEAF's unit
  and associativity laws are `refl`, and every `reind` in a vertical
  universal property downstream is a `reind` along `refl`.  Over the
  PshHom-based base -- the variant in
  Cubical.Categories.Displayed.Instances.Presheaf.Uncurried.Base -- those
  laws are instead `makePshHomPath refl`, which does not reduce on `.N-ob`
  since PshHom is no-eta-equality, so each downstream β law needs a
  transport of a path in a large function space.
-}
module Cubical.Categories.Displayed.Instances.Presheaf.Uncurried.Strict.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.StrictHom

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base

open Categoryᴰ
open Functor
open PshHom
open PshIso

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓP ℓPᴰ : Level

module _ (C : Category ℓC ℓC') (ℓP ℓPᴰ : Level)
         (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  PshHomᴰStrict : {P Q : Presheaf C ℓP} (α : PshHomStrict P Q)
    (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (Qᴰ : Presheafᴰ Q Cᴰ ℓPᴰ) → Type _
  PshHomᴰStrict α Pᴰ Qᴰ = PshHom Pᴰ (reindPshᴰNatTransStrict α Qᴰ)

  PRESHEAFᴰ : Categoryᴰ (PRESHEAF C ℓP) _ _
  PRESHEAFᴰ .ob[_] P = Presheafᴰ P Cᴰ ℓPᴰ
  PRESHEAFᴰ .Hom[_][_,_] = PshHomᴰStrict
  PRESHEAFᴰ .idᴰ = invPshIso (reindPshᴰNatTransStrict-id _) .trans
  PRESHEAFᴰ ._⋆ᴰ_ {f = α} {g = β} {zᴰ = Rᴰ} αᴰ βᴰ =
    αᴰ ⋆PshHom reindPshHom (Idᴰ /FⱽStrict α) βᴰ
       ⋆PshHom invPshIso (reindPshᴰNatTransStrict-seq α β Rᴰ) .trans
  PRESHEAFᴰ .⋆IdLᴰ αᴰ = makePshHomPath refl
  PRESHEAFᴰ .⋆IdRᴰ αᴰ = makePshHomPath refl
  PRESHEAFᴰ .⋆Assocᴰ αᴰ βᴰ γᴰ = makePshHomPath refl
  PRESHEAFᴰ .isSetHomᴰ = isSetPshHom _ _

-- The library's `reindPshᴰNatTrans≅Strict` re-proved with identity
-- components.  The Strict-indexed and the PshHom-indexed reindexing of a
-- displayed presheaf have definitionally equal `F-ob`, since
-- `PshHomStrict→PshHom` does not touch `N-ob`; only the (propositional)
-- triangle of a slice hom differs, so the identity on elements is already an
-- iso between them.  The library proof goes through
-- `pathToNatIso (Functor≡ …)`, whose `N-ob` is a transport, and that
-- transport leaves an
-- `Xᴰ .F-hom (symNatIso (pathToNatIso …) .trans .N-ob c)` wrapper on one side
-- of every equation it appears in.
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {P R : Presheaf C ℓP} {α : PshHomStrict R P} where
  reindPshᴰNatTrans≅StrictId : (Xᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
    → PshIso (reindPshᴰNatTrans (PshHomStrict→PshHom α) Xᴰ)
             (reindPshᴰNatTransStrict α Xᴰ)
  reindPshᴰNatTrans≅StrictId Xᴰ .trans .N-ob c z = z
  reindPshᴰNatTrans≅StrictId Xᴰ .trans .N-hom c c' f z =
    cong (λ h → Xᴰ .F-hom h z) (Hom/≡ refl)
  reindPshᴰNatTrans≅StrictId Xᴰ .nIso c .fst z = z
  reindPshᴰNatTrans≅StrictId Xᴰ .nIso c .snd .fst _ = refl
  reindPshᴰNatTrans≅StrictId Xᴰ .nIso c .snd .snd _ = refl
