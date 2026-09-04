{- Pseudofunctors between bicategories -}
module Cubical.Categories.Bicategory.Functor.Pseudo where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Terminal

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Functor.Lax

private
  variable
    ℓb ℓb' ℓb'' ℓc ℓc' ℓc'' : Level

open Category

record Pseudofunctor (B : Bicategory ℓb ℓb' ℓb'')
                     (C : Bicategory ℓc ℓc' ℓc'') :
                     Type (ℓ-max (ℓ-max ℓb (ℓ-max ℓb' ℓb''))
                                 (ℓ-max ℓc (ℓ-max ℓc' ℓc''))) where
  no-eta-equality

  private
    module B = Bicategory B
    module C = Bicategory C

  field
    laxFunctor : LaxFunctor B C

  open LaxFunctor laxFunctor public

  field
    F-id-isIso : ∀ {x : B.ob} (p : 𝟙C .ob)
      → isIso (C.Hom[ F-ob x , F-ob x ])
              (NatTrans.N-ob (F-id {x}) p)

    F-seq-isIso : ∀ {x y z : B.ob}
      (p : (B.Hom[ x , y ] ×C B.Hom[ y , z ]) .ob)
      → isIso (C.Hom[ F-ob x , F-ob z ])
              (NatTrans.N-ob (F-seq {x} {y} {z}) p)

  F-id-NatIso : ∀ {x : B.ob}
    → NatIso (C.id {F-ob x})
             (F-Hom {x} {x} ∘F B.id {x})
  NatIso.trans F-id-NatIso = F-id
  NatIso.nIso F-id-NatIso = F-id-isIso

  F-seq-NatIso : ∀ {x y z : B.ob}
    → NatIso
        (C.seq (F-ob x) (F-ob y) (F-ob z)
          ∘F (F-Hom {x} {y} ×F F-Hom {y} {z}))
        (F-Hom {x} {z} ∘F B.seq x y z)
  NatIso.trans F-seq-NatIso = F-seq
  NatIso.nIso F-seq-NatIso = F-seq-isIso
