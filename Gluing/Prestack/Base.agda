{-# OPTIONS --lossy-unification #-}
{- The `SETᴰ`-glue of a set-valued interpretation, as the Grothendieck
   construction of a reindexed prestack. -}
module Gluing.Prestack.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Reindex.Base
open import Cubical.Categories.Displayed.Isomorphism
open import Cubical.Categories.Displayed.Instances.Sets.Base

open import Cubical.Categories.Bicategory.Instances.LocallyDiscrete
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Reindex
open import Cubical.Categories.Bicategory.Prestack.Strict
open import Cubical.Categories.Bicategory.Prestack.Grothendieck
open import Cubical.Categories.Bicategory.Prestack.Examples.Sets

private
  variable
    ℓ ℓ' ℓs ℓs' : Level

open Category
open Functorᴰ
open Isoᴰ

homGpdOf : {ℓc ℓc' : Level} (C : Category ℓc ℓc') → C .ob → C .ob
  → hGroupoid ℓc'
homGpdOf C x y = (C [ x , y ]) , isSet→isGroupoid (C .isSetHom {x} {y})

-- reindexing a *locally discrete* bicategory is always strict: a
-- 2-cell there is a path, and co-singletons of paths are contractible
module _ {C : Category ℓ ℓ'} {D : Category ℓs ℓs'} (F : Functor C D) where
  isStrictLocallyDiscreteF : isStrictPs (LocallyDiscreteF F)
  isStrictLocallyDiscreteF =
      (λ {x} → idHomDisc (homGpdOf D _ _) _)
    , (λ f g → idHomDisc (homGpdOf D _ _) _)

module _ {ℓs ℓs' : Level} {C : Category ℓ ℓ'} (F : Functor C (SET ℓs)) where
  private
    module C = Category C
    P = SETPre ℓs ℓs'

  -- the glue used by `Gluing/`: a `reindex` of the semantic `SETᴰ`
  GLᴰ : Categoryᴰ C (ℓ-max ℓs (ℓ-suc ℓs')) (ℓ-max ℓs ℓs')
  GLᴰ = reindex (SETᴰ ℓs ℓs') F

  -- the same glue as a Grothendieck construction of a prestack
  GLᴾ : Categoryᴰ C (ℓ-max ℓs (ℓ-suc ℓs')) (ℓ-max ℓs ℓs')
  GLᴾ = ∫Pre (reindexPrestack (LocallyDiscreteF F) P)

  isStrictGLᴾ : isStrictPrestack (reindexPrestack (LocallyDiscreteF F) P)
  isStrictGLᴾ = isStrictReindex (LocallyDiscreteF F) P
    (isStrictLocallyDiscreteF F) (isStrictSETPre ℓs ℓs')

  private
    module GLᴰ = Categoryᴰ GLᴰ
    module GLᴾ = Categoryᴰ GLᴾ

  glueOb : (c : C.ob) → GLᴰ.ob[ c ] ≡ GLᴾ.ob[ c ]
  glueOb _ = refl

  glueHom : {c c' : C.ob} (f : C [ c , c' ])
    (P : GLᴰ.ob[ c ]) (Q : GLᴰ.ob[ c' ])
    → GLᴰ.Hom[ f ][ P , Q ] ≡ GLᴾ.Hom[ f ][ P , Q ]
  glueHom _ _ _ = refl

  -- identity on all displayed data, both ways
  glueIsoᴰ : Isoᴰ GLᴰ GLᴾ
  glueIsoᴰ .funⱽ .F-obᴰ Pᴰ = Pᴰ
  glueIsoᴰ .funⱽ .F-homᴰ fᴰ = fᴰ
  glueIsoᴰ .funⱽ .F-idᴰ = reindexId F P
  glueIsoᴰ .funⱽ .F-seqᴰ = reindexSeq F P
  glueIsoᴰ .invⱽ .F-obᴰ Pᴰ = Pᴰ
  glueIsoᴰ .invⱽ .F-homᴰ fᴰ = fᴰ
  glueIsoᴰ .invⱽ .F-idᴰ = sym (reindexId F P)
  glueIsoᴰ .invⱽ .F-seqᴰ fᴰ gᴰ = sym (reindexSeq F P fᴰ gᴰ)
  glueIsoᴰ .obSec _ = refl
  glueIsoᴰ .obRet _ = refl
  glueIsoᴰ .homSec _ = refl
  glueIsoᴰ .homRet _ = refl

  glue≡ : GLᴰ ≡ GLᴾ
  glue≡ = sameDataᴰ≡ {Cᴰ = GLᴰ} {Dᴰ = GLᴾ}
    (λ _ → GLᴰ.ob[_]) (λ _ → GLᴰ.Hom[_][_,_])
    (λ i → reindexId F P i)
    (λ i {_} {_} {_} {f} {g} {xᴰ} {yᴰ} {zᴰ} fᴰ gᴰ →
      reindexSeq F P {f = f} {g} {xᴰ} {yᴰ} {zᴰ} fᴰ gᴰ i)

  -- so a `Section F SETᴰ` -- what `Gluing/` produces -- is a global
  -- section of the prestack glue
  toGLᴾ : Section F (SETᴰ ℓs ℓs') → GlobalSection GLᴾ
  toGLᴾ s = compFunctorᴰGlobalSection (glueIsoᴰ .funⱽ)
    (introS (Id {C = C}) (reindS' (Eq.refl , Eq.refl) s))

  -- and a section built *in* the prestack semantics lands there too
  toGLᴾ∫ : Section F (∫Pre (SETPre ℓs ℓs')) → GlobalSection GLᴾ
  toGLᴾ∫ s = compFunctorᴰGlobalSection (reindex∫Isoᴰ F (SETPre ℓs ℓs') .funⱽ)
    (introS (Id {C = C}) (reindS' (Eq.refl , Eq.refl) s))

  -- ... and can be read back as an ordinary `SETᴰ` section
  fromPrestackSection : Section F (∫Pre (SETPre ℓs ℓs'))
    → Section F (SETᴰ ℓs ℓs')
  fromPrestackSection s =
    reindS' (Eq.refl , Eq.refl)
      (compFunctorᴰSection (∫SETPreIsoᴰ ℓs ℓs' .funⱽ) s)
