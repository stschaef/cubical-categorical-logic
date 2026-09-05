{- A right adjoint to `F : C → D` at `d` is a universal element of
   `c ↦ Hom(F c , d)`, i.e. a representation of that presheaf. -}
module Cubical.Categories.Adjoint.RightAdjoint where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Category.Base renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More

private
  variable
    ℓ ℓ' ℓD ℓD' : Level

open Category
open Functor

module _ {C : Category ℓ ℓ'} {D : Category ℓD ℓD'} (F : Functor C D) where
  RPsh : D .ob → Presheaf C ℓD'
  RPsh B = reindPsh F (D [-, B ])

  HasRightAdjointAt : D .ob → Type (ℓ-max (ℓ-max ℓ ℓ') ℓD')
  HasRightAdjointAt B = UniversalElement C (RPsh B)

  HasRightAdjoint : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓD) ℓD')
  HasRightAdjoint = ∀ B → HasRightAdjointAt B

{- The universal property, spelled out: `compare` is the presheaf
   action of the counit, `ff` is `universal` under that name. -}
module RightAdjointNotation {C : Category ℓ ℓ'} {D : Category ℓD ℓD'}
  {F : Functor C D} {d : D .ob} (U : HasRightAdjointAt F d) where
  private
    module D = Category D
  open UniversalElementNotation U public

  compare : {c : C .ob} → C [ c , vertex ] → D [ F ⟅ c ⟆ , d ]
  compare α = F ⟪ α ⟫ D.⋆ element

  ff : (c : C .ob) → isEquiv (compare {c})
  ff c = universal c

  compareIso : (c : C .ob) → Iso (C [ c , vertex ]) (D [ F ⟅ c ⟆ , d ])
  compareIso c = universalIso c

{- Universal elements of `RPsh F` move along isomorphisms, in either
   variable.  These are what make "absolute" statements portable
   across the unitors of a bicategory. -}
module _ {C : Category ℓ ℓ'} {D : Category ℓD ℓD'} {F : Functor C D} where
  private
    module C = Category C
    module D = Category D

    ⋆Equiv : {c : C .ob} {d d' : D .ob} (i : CatIso D d d')
      → (D [ F ⟅ c ⟆ , d ]) ≃ (D [ F ⟅ c ⟆ , d' ])
    ⋆Equiv i = isoToEquiv theIso where
      theIso : Iso _ _
      theIso .Iso.fun g = g D.⋆ i .fst
      theIso .Iso.inv g = g D.⋆ i .snd .isIsoC.inv
      theIso .Iso.sec g =
        D.⋆Assoc _ _ _ ∙ cong (g D.⋆_) (i .snd .isIsoC.sec) ∙ D.⋆IdR g
      theIso .Iso.ret g =
        D.⋆Assoc _ _ _ ∙ cong (g D.⋆_) (i .snd .isIsoC.ret) ∙ D.⋆IdR g

    -- precomposition with the inverse of an iso
    ∘Equiv : {c : C .ob} {v v' : C .ob} (i : CatIso C v v')
      → (C [ c , v' ]) ≃ (C [ c , v ])
    ∘Equiv i = isoToEquiv theIso where
      theIso : Iso _ _
      theIso .Iso.fun g = g C.⋆ i .snd .isIsoC.inv
      theIso .Iso.inv g = g C.⋆ i .fst
      theIso .Iso.sec g =
        C.⋆Assoc _ _ _ ∙ cong (g C.⋆_) (i .snd .isIsoC.ret) ∙ C.⋆IdR g
      theIso .Iso.ret g =
        C.⋆Assoc _ _ _ ∙ cong (g C.⋆_) (i .snd .isIsoC.sec) ∙ C.⋆IdR g

  -- the target moves: `e` is composed with the iso
  isUniversalRPsh⋆ : {d d' : D .ob} (i : CatIso D d d')
    {v : C .ob} {e : D [ F ⟅ v ⟆ , d ]}
    → isUniversal C (RPsh F d) v e
    → isUniversal C (RPsh F d') v (e D.⋆ i .fst)
  isUniversalRPsh⋆ i {v} {e} U c =
    subst isEquiv (funExt (λ φ → D.⋆Assoc _ _ _))
      (compEquiv (_ , U c) (⋆Equiv i) .snd)

  -- the vertex moves: `e` is reindexed along the inverse iso
  isUniversalRPsh∘ : {v v' : C .ob} (i : CatIso C v v')
    {d : D .ob} {e : D [ F ⟅ v ⟆ , d ]}
    → isUniversal C (RPsh F d) v e
    → isUniversal C (RPsh F d) v' (F ⟪ i .snd .isIsoC.inv ⟫ D.⋆ e)
  isUniversalRPsh∘ i {d} {e} U c =
    subst isEquiv (funExt (λ φ → cong (D._⋆ e) (F .F-seq _ _) ∙ D.⋆Assoc _ _ _))
      (compEquiv (∘Equiv i) (_ , U c) .snd)
