{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.Hyperdoctrine.Unary where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base

open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More

private
  variable
    ℓ ℓ' : Level

open Category

record Hyperdoctrine ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    cc : Category ℓ ℓ'
    bp : BinProducts cc
    func : Functor (cc  ^op) (POSETADJ ℓ ℓ')

  open Notation cc bp
  field
    {-
    Beck-Chevalley condition
    Expresses the naturality of the left/right adjoints of the a × _ projection:
    For f ∈ cc [b , c], we have the following commuting square:

                              func(π₂)
                 func(a × c) ⟵--------- func(c)
                   |         ---------→   |
      func(1 × f)  |         left-adj     | func(f)
                   |                      |
                   ↓          func(π₂)    ↓
                 func(a × b) ←--------- func(b)
                             ---------→
                             left-adj

    TODO: Can probably be more cleanly expressed as a bifunctor
    -}
    nat-left : ∀ {b c : cc .ob}
      (a : cc .ob) (f : cc [ b , c ]) →
      (π₂ab-left-adj : Σ[ L ∈ (POSETADJ ℓ ℓ') [ func ⟅ a × b ⟆ , func ⟅ b ⟆ ] ]
        (L .fst ⊣ (func ⟪ π₂ {a} {b} ⟫) .fst) ) →
      (π₂ac-left-adj : Σ[ L ∈ (POSETADJ ℓ ℓ') [ func ⟅ a × c ⟆ , func ⟅ c ⟆ ] ]
        (L .fst ⊣ (func ⟪ π₂ {a} {c} ⟫) .fst) ) →
      ((MonComp
        ((func ⟪ (cc .id) ×p f ⟫) .fst)
        (π₂ab-left-adj .fst .fst))
      ≡
      (MonComp
        (π₂ac-left-adj .fst .fst)
        ((func ⟪ f ⟫) .fst))
      )
    nat-right : ∀ {b c : cc .ob}
      (a : cc .ob) (f : cc [ b , c ]) →
      (π₂ab-right-adj : Σ[ R ∈ (POSETADJ ℓ ℓ') [ func ⟅ a × b ⟆ , func ⟅ b ⟆ ] ]
        ((func ⟪ π₂ {a} {b} ⟫) .fst ⊣ R .fst) ) →
      (π₂ac-right-adj : Σ[ R ∈ (POSETADJ ℓ ℓ') [ func ⟅ a × c ⟆ , func ⟅ c ⟆ ] ]
        ((func ⟪ π₂ {a} {c} ⟫) .fst ⊣ R .fst) ) →
      ((MonComp
        ((func ⟪ (cc .id) ×p f ⟫) .fst)
        (π₂ab-right-adj .fst .fst))
      ≡
      (MonComp
        (π₂ac-right-adj .fst .fst)
        ((func ⟪ f ⟫) .fst))
      )
