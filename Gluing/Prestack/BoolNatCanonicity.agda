{-# OPTIONS --lossy-unification #-}
{- The Bool/Nat canonicity glue of
   `Gluing.CartesianCategory.BoolNatCanonicity.Forded`, presented as
   `∫Pre` of a reindexed prestack. -}
module Gluing.Prestack.BoolNatCanonicity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sum

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Reindex.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Sets.Properties

open import Cubical.Categories.Instances.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Instances.Free.CartesianCategory.Forded
  as FreeCC

open import Cubical.Categories.Bicategory.Instances.LocallyDiscrete.Base
open import Cubical.Categories.Bicategory.Prestack.Reindex
open import Cubical.Categories.Bicategory.Prestack.Strict
open import Cubical.Categories.Bicategory.Prestack.Grothendieck
open import Cubical.Categories.Bicategory.Prestack.Instances.Sets

open import Gluing.Canonicity
open import Gluing.Prestack.Base
open import Gluing.CartesianCategory.BoolNatCanonicity.Forded
  using (OB; bool; nat; MOR; tr; fl; ze; su; ×QUIVER;
         CanonicalFormBool; CanonicalFormNat; [bool]; [t]; [f]; [nat];
         ＂_＂; evalBool; evalNat; evalNat-＂_＂)

open Category
open Section

private
  FREECC = FreeCartesianCategory ×QUIVER
  module FREECC = CartesianCategory FREECC

Pts : Functor FREECC.C (SET ℓ-zero)
Pts = FREECC.C [ ⊤ ,-]

-- the glue of `Forded.agda`: a `Section Pts (SETᴰ 0 0)` is a global
-- section of this
GlueReindex : Categoryᴰ FREECC.C _ _
GlueReindex = reindex (SETᴰ ℓ-zero ℓ-zero) Pts

GlueReindex≡GLᴰ : GlueReindex ≡ GLᴰ {ℓs' = ℓ-zero} Pts
GlueReindex≡GLᴰ = refl

-- the same glue as a Grothendieck construction
GluePrestack : Categoryᴰ FREECC.C _ _
GluePrestack = GLᴾ {ℓs' = ℓ-zero} Pts

-- and the prestack it comes from is strict
strictGluePrestack : isStrictPrestack
  (reindexPrestack (LocallyDiscreteF Pts) (SETPre ℓ-zero ℓ-zero))
strictGluePrestack = isStrictGLᴾ {ℓs' = ℓ-zero} Pts

-- the canonicity section, built directly against the prestack
-- semantics (the interpretation data is the one from `Forded.agda`,
-- which is `private` there)
canonicityᴾ : Section Pts (∫Pre (SETPre ℓ-zero ℓ-zero))
canonicityᴾ = FreeCC.elimLocal ×QUIVER Pts (∫SETPreCCⱽ ℓ-zero ℓ-zero)
  (mkElimInterpᴰ
  (λ { bool e → CanonicalFormBool e ; nat e → CanonicalFormNat e })
  λ { tr e _ → inl (cong₂ _⋆ₑ_ (⊤→⊤IsId FREECC.term e) refl
                    ∙ FREECC.⋆IdL _)
    ; fl e _ → inr (cong₂ _⋆ₑ_ (⊤→⊤IsId FREECC.term e) refl
                    ∙ FREECC.⋆IdL _)
    ; ze e _ → 0 , (sym (cong₂ _⋆ₑ_ (⊤→⊤IsId FREECC.term e) refl
                         ∙ FREECC.⋆IdL _))
    ; su e (n , fib) → (suc n) , cong₂ _⋆ₑ_ fib refl
    })

-- it is a global section of the prestack glue
canonicityGLᴾ : GlobalSection GluePrestack
canonicityGLᴾ = toGLᴾ∫ {ℓs' = ℓ-zero} Pts canonicityᴾ

-- and it proves canonicity
canonicitySETᴰ : Section Pts (SETᴰ ℓ-zero ℓ-zero)
canonicitySETᴰ = fromPrestackSection {ℓs' = ℓ-zero} Pts canonicityᴾ

canonicity-bool : Iso [bool] Bool
canonicity-bool = BoolIso.canonicity-bool [t] [f] evalBool refl refl
  (λ e → canonicalize ⊤ canonicitySETᴰ _ e)

canonicity-nat : Iso [nat] ℕ
canonicity-nat = NatIso.canonicity-nat ＂_＂ evalNat evalNat-＂_＂
  (λ e → canonicalize ⊤ canonicitySETᴰ _ e)
