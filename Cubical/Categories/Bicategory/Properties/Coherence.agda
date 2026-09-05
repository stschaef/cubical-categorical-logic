{-# OPTIONS --lossy-unification #-}
{- Associator/pentagon calculus in a single bicategory: naturality of
   α, reassociation of long 2-cell composites, whiskering over them,
   the pentagon rearrangements and interchange. -}
module Cubical.Categories.Bicategory.Properties.Coherence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More hiding (α)
open import Cubical.Categories.Instances.BinProduct

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Constructions.Op
open import Cubical.Categories.Bicategory.Properties

private
  variable
    ℓ ℓ' ℓ'' : Level

open Functor
open isIso

module _ (C : Bicategory ℓ ℓ' ℓ'') where
  private
    module C = Bicategory C

  αI : {x y z w : C.0Cell}
    (p : C.1Cell x y) (q : C.1Cell y z) (r : C.1Cell z w)
    → CatIso C.Hom[ x , w ] ((p C.⋆₁ q) C.⋆₁ r) (p C.⋆₁ (q C.⋆₁ r))
  αI {x} {y} {z} {w} p q r = NatIsoAt (C.α x y z w) (p , q , r)

  ρI : {x y : C.0Cell} (p : C.1Cell x y)
    → CatIso C.Hom[ x , y ] (p C.⋆₁ C.id₁) p
  ρI {x} {y} p = NatIsoAt (C.ρU x y) (p , tt*)

  -- Naturality of the associator and of its inverse.
  α⁺nat : {x y z w : C.0Cell}
    {p p' : C.1Cell x y} {q q' : C.1Cell y z} {r r' : C.1Cell z w}
    (u : C.2Cell p p') (v : C.2Cell q q') (t : C.2Cell r r')
    →   ((u C.⋆ₕ v) C.⋆ₕ t) C.⋆₂ C.α⁺ p' q' r'
      ≡ C.α⁺ p q r C.⋆₂ (u C.⋆ₕ (v C.⋆ₕ t))
  α⁺nat {x} {y} {z} {w} u v t =
    NatTrans.N-hom (NatIso.trans (C.α x y z w)) (u , v , t)

  α⁻nat : {x y z w : C.0Cell}
    {p p' : C.1Cell x y} {q q' : C.1Cell y z} {r r' : C.1Cell z w}
    (u : C.2Cell p p') (v : C.2Cell q q') (t : C.2Cell r r')
    →   (u C.⋆ₕ (v C.⋆ₕ t)) C.⋆₂ C.α⁻ p' q' r'
      ≡ C.α⁻ p q r C.⋆₂ ((u C.⋆ₕ v) C.⋆ₕ t)
  α⁻nat {x} {y} {z} {w} u v t =
    NatTrans.N-hom (NatIso.trans (symNatIso (C.α x y z w))) (u , v , t)

  α⁺natL : {x y z w : C.0Cell} {p p' : C.1Cell x y}
    (u : C.2Cell p p') (r : C.1Cell y z) (s : C.1Cell z w)
    →   ((u C.▷w r) C.▷w s) C.⋆₂ C.α⁺ p' r s
      ≡ C.α⁺ p r s C.⋆₂ (u C.▷w (r C.⋆₁ s))
  α⁺natL u r s = α⁺nat u C.id₂ C.id₂ ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆ₕ⟨ C.⋆ₕId ⟩ ⟩

  α⁺natM : {x y z w : C.0Cell} (p : C.1Cell x y) {q q' : C.1Cell y z}
    (v : C.2Cell q q') (s : C.1Cell z w)
    →   ((p C.◁w v) C.▷w s) C.⋆₂ C.α⁺ p q' s
      ≡ C.α⁺ p q s C.⋆₂ (p C.◁w (v C.▷w s))
  α⁺natM p v s = α⁺nat C.id₂ v C.id₂

  α⁺natR : {x y z w : C.0Cell}
    (p : C.1Cell x y) (q : C.1Cell y z) {r r' : C.1Cell z w}
    (t : C.2Cell r r')
    →   ((p C.⋆₁ q) C.◁w t) C.⋆₂ C.α⁺ p q r'
      ≡ C.α⁺ p q r C.⋆₂ (p C.◁w (q C.◁w t))
  α⁺natR p q t = C.⟨ C.⟨ sym C.⋆ₕId ⟩⋆ₕ⟨⟩ ⟩⋆₂⟨⟩ ∙ α⁺nat C.id₂ C.id₂ t

  α⁻natL : {x y z w : C.0Cell} {p p' : C.1Cell x y}
    (u : C.2Cell p p') (r : C.1Cell y z) (s : C.1Cell z w)
    →   (u C.▷w (r C.⋆₁ s)) C.⋆₂ C.α⁻ p' r s
      ≡ C.α⁻ p r s C.⋆₂ ((u C.▷w r) C.▷w s)
  α⁻natL u r s = C.⟨ C.⟨⟩⋆ₕ⟨ sym C.⋆ₕId ⟩ ⟩⋆₂⟨⟩ ∙ α⁻nat u C.id₂ C.id₂

  α⁻natM : {x y z w : C.0Cell} (p : C.1Cell x y) {q q' : C.1Cell y z}
    (v : C.2Cell q q') (s : C.1Cell z w)
    →   (p C.◁w (v C.▷w s)) C.⋆₂ C.α⁻ p q' s
      ≡ C.α⁻ p q s C.⋆₂ ((p C.◁w v) C.▷w s)
  α⁻natM p v s = α⁻nat C.id₂ v C.id₂

  α⁻natR : {x y z w : C.0Cell}
    (p : C.1Cell x y) (q : C.1Cell y z) {r r' : C.1Cell z w}
    (t : C.2Cell r r')
    →   (p C.◁w (q C.◁w t)) C.⋆₂ C.α⁻ p q r'
      ≡ C.α⁻ p q r C.⋆₂ ((p C.⋆₁ q) C.◁w t)
  α⁻natR p q t = α⁻nat C.id₂ C.id₂ t ∙ C.⟨⟩⋆₂⟨ C.⟨ C.⋆ₕId ⟩⋆ₕ⟨⟩ ⟩

  -- Reassociating a left-nested prefix into right-nested form.
  aR2 : {x y : C.0Cell} {f₀ f₁ f₂ f₃ : C.1Cell x y}
    (p : C.2Cell f₀ f₁) (q : C.2Cell f₁ f₂) (t : C.2Cell f₂ f₃)
    → (p C.⋆₂ q) C.⋆₂ t ≡ p C.⋆₂ q C.⋆₂ t
  aR2 = C.⋆₂Assoc

  aR3 : {x y : C.0Cell} {f₀ f₁ f₂ f₃ f₄ : C.1Cell x y}
    (p : C.2Cell f₀ f₁) (q : C.2Cell f₁ f₂) (r : C.2Cell f₂ f₃)
    (t : C.2Cell f₃ f₄)
    → (p C.⋆₂ q C.⋆₂ r) C.⋆₂ t ≡ p C.⋆₂ q C.⋆₂ r C.⋆₂ t
  aR3 p q r t = C.⋆₂Assoc _ _ _ ∙ C.⟨⟩⋆₂⟨ aR2 q r t ⟩

  aR4 : {x y : C.0Cell} {f₀ f₁ f₂ f₃ f₄ f₅ : C.1Cell x y}
    (p : C.2Cell f₀ f₁) (q : C.2Cell f₁ f₂) (r : C.2Cell f₂ f₃)
    (s : C.2Cell f₃ f₄) (t : C.2Cell f₄ f₅)
    → (p C.⋆₂ q C.⋆₂ r C.⋆₂ s) C.⋆₂ t ≡ p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ t
  aR4 p q r s t = C.⋆₂Assoc _ _ _ ∙ C.⟨⟩⋆₂⟨ aR3 q r s t ⟩

  aR5 : {x y : C.0Cell} {f₀ f₁ f₂ f₃ f₄ f₅ f₆ : C.1Cell x y}
    (p : C.2Cell f₀ f₁) (q : C.2Cell f₁ f₂) (r : C.2Cell f₂ f₃)
    (s : C.2Cell f₃ f₄) (u : C.2Cell f₄ f₅) (t : C.2Cell f₅ f₆)
    →   (p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ u) C.⋆₂ t
      ≡ p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ u C.⋆₂ t
  aR5 p q r s u t = C.⋆₂Assoc _ _ _ ∙ C.⟨⟩⋆₂⟨ aR4 q r s u t ⟩

  aR6 : {x y : C.0Cell} {f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ : C.1Cell x y}
    (p : C.2Cell f₀ f₁) (q : C.2Cell f₁ f₂) (r : C.2Cell f₂ f₃)
    (s : C.2Cell f₃ f₄) (u : C.2Cell f₄ f₅) (v : C.2Cell f₅ f₆)
    (t : C.2Cell f₆ f₇)
    →   (p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ u C.⋆₂ v) C.⋆₂ t
      ≡ p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ u C.⋆₂ v C.⋆₂ t
  aR6 p q r s u v t = C.⋆₂Assoc _ _ _ ∙ C.⟨⟩⋆₂⟨ aR5 q r s u v t ⟩

  aR7 : {x y : C.0Cell} {f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : C.1Cell x y}
    (p : C.2Cell f₀ f₁) (q : C.2Cell f₁ f₂) (r : C.2Cell f₂ f₃)
    (s : C.2Cell f₃ f₄) (u : C.2Cell f₄ f₅) (v : C.2Cell f₅ f₆)
    (w : C.2Cell f₆ f₇) (t : C.2Cell f₇ f₈)
    →   (p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ u C.⋆₂ v C.⋆₂ w) C.⋆₂ t
      ≡ p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ u C.⋆₂ v C.⋆₂ w C.⋆₂ t
  aR7 p q r s u v w t = C.⋆₂Assoc _ _ _ ∙ C.⟨⟩⋆₂⟨ aR6 q r s u v w t ⟩

  aR8 : {x y : C.0Cell}
    {f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : C.1Cell x y}
    (p : C.2Cell f₀ f₁) (q : C.2Cell f₁ f₂) (r : C.2Cell f₂ f₃)
    (s : C.2Cell f₃ f₄) (u : C.2Cell f₄ f₅) (v : C.2Cell f₅ f₆)
    (w : C.2Cell f₆ f₇) (z : C.2Cell f₇ f₈) (t : C.2Cell f₈ f₉)
    →   (p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ u C.⋆₂ v C.⋆₂ w C.⋆₂ z) C.⋆₂ t
      ≡ p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ u C.⋆₂ v C.⋆₂ w C.⋆₂ z C.⋆₂ t
  aR8 p q r s u v w z t =
    C.⋆₂Assoc _ _ _ ∙ C.⟨⟩⋆₂⟨ aR7 q r s u v w z t ⟩

  aR9 : {x y : C.0Cell}
    {f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ g₀ : C.1Cell x y}
    (p : C.2Cell f₀ f₁) (q : C.2Cell f₁ f₂) (r : C.2Cell f₂ f₃)
    (s : C.2Cell f₃ f₄) (u : C.2Cell f₄ f₅) (v : C.2Cell f₅ f₆)
    (w : C.2Cell f₆ f₇) (z : C.2Cell f₇ f₈) (e : C.2Cell f₈ f₉)
    (t : C.2Cell f₉ g₀)
    →   (p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ u C.⋆₂ v C.⋆₂ w C.⋆₂ z C.⋆₂ e)
          C.⋆₂ t
      ≡ p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ u C.⋆₂ v C.⋆₂ w C.⋆₂ z C.⋆₂ e
          C.⋆₂ t
  aR9 p q r s u v w z e t =
    C.⋆₂Assoc _ _ _ ∙ C.⟨⟩⋆₂⟨ aR8 q r s u v w z e t ⟩

  aR10 : {x y : C.0Cell}
    {f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ g₀ g₁ : C.1Cell x y}
    (o : C.2Cell f₀ f₁) (p : C.2Cell f₁ f₂) (q : C.2Cell f₂ f₃)
    (r : C.2Cell f₃ f₄) (s : C.2Cell f₄ f₅) (u : C.2Cell f₅ f₆)
    (v : C.2Cell f₆ f₇) (w : C.2Cell f₇ f₈) (z : C.2Cell f₈ f₉)
    (e : C.2Cell f₉ g₀) (t : C.2Cell g₀ g₁)
    →   (o C.⋆₂ p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ u C.⋆₂ v C.⋆₂ w C.⋆₂ z
          C.⋆₂ e) C.⋆₂ t
      ≡ o C.⋆₂ p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ u C.⋆₂ v C.⋆₂ w C.⋆₂ z
          C.⋆₂ e C.⋆₂ t
  aR10 o p q r s u v w z e t =
    C.⋆₂Assoc _ _ _ ∙ C.⟨⟩⋆₂⟨ aR9 p q r s u v w z e t ⟩

  -- Rewriting the first two factors of a right-nested composite.
  pushn : {x y : C.0Cell} {f g h k : C.1Cell x y}
    {u : C.2Cell f g} {v : C.2Cell g h} {w : C.2Cell f h}
    → u C.⋆₂ v ≡ w → (t : C.2Cell h k)
    → u C.⋆₂ v C.⋆₂ t ≡ w C.⋆₂ t
  pushn e t = sym (C.⋆₂Assoc _ _ _) ∙ C.⟨ e ⟩⋆₂⟨⟩

  pushr : {x y : C.0Cell} {f g h m k : C.1Cell x y}
    {u : C.2Cell f g} {v : C.2Cell g h}
    {w₁ : C.2Cell f m} {w₂ : C.2Cell m h}
    → u C.⋆₂ v ≡ w₁ C.⋆₂ w₂ → (t : C.2Cell h k)
    → u C.⋆₂ v C.⋆₂ t ≡ w₁ C.⋆₂ w₂ C.⋆₂ t
  pushr e t = pushn e t ∙ C.⋆₂Assoc _ _ _

  -- Rewriting the first three factors of a right-nested composite.
  rep3 : {x y : C.0Cell} {f g h m n k : C.1Cell x y}
    {u : C.2Cell f g} {v : C.2Cell g h} {r : C.2Cell h m}
    {w₁ : C.2Cell f n} {w₂ : C.2Cell n m}
    → u C.⋆₂ v C.⋆₂ r ≡ w₁ C.⋆₂ w₂ → (t : C.2Cell m k)
    → u C.⋆₂ v C.⋆₂ r C.⋆₂ t ≡ w₁ C.⋆₂ w₂ C.⋆₂ t
  rep3 e t = sym (aR3 _ _ _ t) ∙ C.⟨ e ⟩⋆₂⟨⟩ ∙ aR2 _ _ t

  -- As `rep3`/`pushr`, but collapsing an n-factor right-nested prefix
  -- to a single 2-cell, and the 2 → 3 direction.
  rw3 : {x y : C.0Cell} {f g h m k : C.1Cell x y}
    {p : C.2Cell f g} {q : C.2Cell g h} {r : C.2Cell h m}
    {w : C.2Cell f m}
    → p C.⋆₂ q C.⋆₂ r ≡ w → (t : C.2Cell m k)
    → p C.⋆₂ q C.⋆₂ r C.⋆₂ t ≡ w C.⋆₂ t
  rw3 e t = sym (aR3 _ _ _ t) ∙ C.⟨ e ⟩⋆₂⟨⟩

  rw4 : {x y : C.0Cell} {f g h m n k : C.1Cell x y}
    {p : C.2Cell f g} {q : C.2Cell g h} {r : C.2Cell h m}
    {s : C.2Cell m n} {w : C.2Cell f n}
    → p C.⋆₂ q C.⋆₂ r C.⋆₂ s ≡ w → (t : C.2Cell n k)
    → p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ t ≡ w C.⋆₂ t
  rw4 e t = sym (aR4 _ _ _ _ t) ∙ C.⟨ e ⟩⋆₂⟨⟩

  rw5 : {x y : C.0Cell} {f₀ f₁ f₂ f₃ f₄ f₅ k : C.1Cell x y}
    {p : C.2Cell f₀ f₁} {q : C.2Cell f₁ f₂} {r : C.2Cell f₂ f₃}
    {s : C.2Cell f₃ f₄} {v : C.2Cell f₄ f₅} {w : C.2Cell f₀ f₅}
    → p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ v ≡ w → (t : C.2Cell f₅ k)
    → p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ v C.⋆₂ t ≡ w C.⋆₂ t
  rw5 e t = sym (aR5 _ _ _ _ _ t) ∙ C.⟨ e ⟩⋆₂⟨⟩

  rw6 : {x y : C.0Cell} {f₀ f₁ f₂ f₃ f₄ f₅ f₆ k : C.1Cell x y}
    {p : C.2Cell f₀ f₁} {q : C.2Cell f₁ f₂} {r : C.2Cell f₂ f₃}
    {s : C.2Cell f₃ f₄} {v : C.2Cell f₄ f₅} {u : C.2Cell f₅ f₆}
    {w : C.2Cell f₀ f₆}
    → p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ v C.⋆₂ u ≡ w → (t : C.2Cell f₆ k)
    → p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ v C.⋆₂ u C.⋆₂ t ≡ w C.⋆₂ t
  rw6 e t = sym (aR6 _ _ _ _ _ _ t) ∙ C.⟨ e ⟩⋆₂⟨⟩

  rw7 : {x y : C.0Cell} {f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ k : C.1Cell x y}
    {o : C.2Cell f₀ f₁} {p : C.2Cell f₁ f₂} {q : C.2Cell f₂ f₃}
    {r : C.2Cell f₃ f₄} {s : C.2Cell f₄ f₅} {v : C.2Cell f₅ f₆}
    {u : C.2Cell f₆ f₇} {w : C.2Cell f₀ f₇}
    → o C.⋆₂ p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ v C.⋆₂ u ≡ w
    → (t : C.2Cell f₇ k)
    →   o C.⋆₂ p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ v C.⋆₂ u C.⋆₂ t
      ≡ w C.⋆₂ t
  rw7 e t = sym (aR7 _ _ _ _ _ _ _ t) ∙ C.⟨ e ⟩⋆₂⟨⟩

  pushr3 : {x y : C.0Cell} {f g h n₁ n₂ k : C.1Cell x y}
    {u : C.2Cell f g} {v : C.2Cell g h}
    {w₁ : C.2Cell f n₁} {w₂ : C.2Cell n₁ n₂} {w₃ : C.2Cell n₂ h}
    → u C.⋆₂ v ≡ w₁ C.⋆₂ w₂ C.⋆₂ w₃ → (t : C.2Cell h k)
    → u C.⋆₂ v C.⋆₂ t ≡ w₁ C.⋆₂ w₂ C.⋆₂ w₃ C.⋆₂ t
  pushr3 e t = pushn e t ∙ aR3 _ _ _ t

  pushr4 : {x y : C.0Cell} {f g h n₁ n₂ n₃ k : C.1Cell x y}
    {u : C.2Cell f g} {v : C.2Cell g h}
    {w₁ : C.2Cell f n₁} {w₂ : C.2Cell n₁ n₂} {w₃ : C.2Cell n₂ n₃}
    {w₄ : C.2Cell n₃ h}
    → u C.⋆₂ v ≡ w₁ C.⋆₂ w₂ C.⋆₂ w₃ C.⋆₂ w₄ → (t : C.2Cell h k)
    → u C.⋆₂ v C.⋆₂ t ≡ w₁ C.⋆₂ w₂ C.⋆₂ w₃ C.⋆₂ w₄ C.⋆₂ t
  pushr4 e t = pushn e t ∙ aR4 _ _ _ _ t

  pushr5 : {x y : C.0Cell} {f g h n₁ n₂ n₃ n₄ k : C.1Cell x y}
    {u : C.2Cell f g} {v : C.2Cell g h}
    {w₁ : C.2Cell f n₁} {w₂ : C.2Cell n₁ n₂} {w₃ : C.2Cell n₂ n₃}
    {w₄ : C.2Cell n₃ n₄} {w₅ : C.2Cell n₄ h}
    → u C.⋆₂ v ≡ w₁ C.⋆₂ w₂ C.⋆₂ w₃ C.⋆₂ w₄ C.⋆₂ w₅
    → (t : C.2Cell h k)
    → u C.⋆₂ v C.⋆₂ t ≡ w₁ C.⋆₂ w₂ C.⋆₂ w₃ C.⋆₂ w₄ C.⋆₂ w₅ C.⋆₂ t
  pushr5 e t = pushn e t ∙ aR5 _ _ _ _ _ t

  pushr6 : {x y : C.0Cell} {f g h n₁ n₂ n₃ n₄ n₅ k : C.1Cell x y}
    {u : C.2Cell f g} {v : C.2Cell g h}
    {w₁ : C.2Cell f n₁} {w₂ : C.2Cell n₁ n₂} {w₃ : C.2Cell n₂ n₃}
    {w₄ : C.2Cell n₃ n₄} {w₅ : C.2Cell n₄ n₅} {w₆ : C.2Cell n₅ h}
    → u C.⋆₂ v ≡ w₁ C.⋆₂ w₂ C.⋆₂ w₃ C.⋆₂ w₄ C.⋆₂ w₅ C.⋆₂ w₆
    → (t : C.2Cell h k)
    →   u C.⋆₂ v C.⋆₂ t
      ≡ w₁ C.⋆₂ w₂ C.⋆₂ w₃ C.⋆₂ w₄ C.⋆₂ w₅ C.⋆₂ w₆ C.⋆₂ t
  pushr6 e t = pushn e t ∙ aR6 _ _ _ _ _ _ t

  pushr7 : {x y : C.0Cell} {f g h n₁ n₂ n₃ n₄ n₅ n₆ k : C.1Cell x y}
    {u : C.2Cell f g} {v : C.2Cell g h}
    {w₁ : C.2Cell f n₁} {w₂ : C.2Cell n₁ n₂} {w₃ : C.2Cell n₂ n₃}
    {w₄ : C.2Cell n₃ n₄} {w₅ : C.2Cell n₄ n₅} {w₆ : C.2Cell n₅ n₆}
    {w₇ : C.2Cell n₆ h}
    → u C.⋆₂ v ≡ w₁ C.⋆₂ w₂ C.⋆₂ w₃ C.⋆₂ w₄ C.⋆₂ w₅ C.⋆₂ w₆ C.⋆₂ w₇
    → (t : C.2Cell h k)
    →   u C.⋆₂ v C.⋆₂ t
      ≡ w₁ C.⋆₂ w₂ C.⋆₂ w₃ C.⋆₂ w₄ C.⋆₂ w₅ C.⋆₂ w₆ C.⋆₂ w₇ C.⋆₂ t
  pushr7 e t = pushn e t ∙ aR7 _ _ _ _ _ _ _ t

  -- Whiskering distributes over longer composites.
  ▷3 : {x y z : C.0Cell} {f₀ f₁ f₂ f₃ : C.1Cell x y}
    (p : C.2Cell f₀ f₁) (q : C.2Cell f₁ f₂) (r : C.2Cell f₂ f₃)
    (h : C.1Cell y z)
    →   ((p C.⋆₂ q C.⋆₂ r) C.▷w h)
      ≡ (p C.▷w h) C.⋆₂ (q C.▷w h) C.⋆₂ (r C.▷w h)
  ▷3 p q r h = ▷wSeq C p _ h ∙ C.⟨⟩⋆₂⟨ ▷wSeq C q r h ⟩

  ◁3 : {x y z : C.0Cell} (e : C.1Cell x y) {f₀ f₁ f₂ f₃ : C.1Cell y z}
    (p : C.2Cell f₀ f₁) (q : C.2Cell f₁ f₂) (r : C.2Cell f₂ f₃)
    →   (e C.◁w (p C.⋆₂ q C.⋆₂ r))
      ≡ (e C.◁w p) C.⋆₂ (e C.◁w q) C.⋆₂ (e C.◁w r)
  ◁3 e p q r = ◁wSeq C e p _ ∙ C.⟨⟩⋆₂⟨ ◁wSeq C e q r ⟩

  ▷5 : {x y z : C.0Cell} {f₀ f₁ f₂ f₃ f₄ f₅ : C.1Cell x y}
    (p : C.2Cell f₀ f₁) (q : C.2Cell f₁ f₂) (r : C.2Cell f₂ f₃)
    (s : C.2Cell f₃ f₄) (u : C.2Cell f₄ f₅) (h : C.1Cell y z)
    →   ((p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ u) C.▷w h)
      ≡ (p C.▷w h) C.⋆₂ (q C.▷w h) C.⋆₂ (r C.▷w h)
          C.⋆₂ (s C.▷w h) C.⋆₂ (u C.▷w h)
  ▷5 p q r s u h =
      ▷wSeq C p _ h
    ∙ C.⟨⟩⋆₂⟨ ▷wSeq C q _ h ∙ C.⟨⟩⋆₂⟨ ▷3 r s u h ⟩ ⟩

  ◁5 : {x y z : C.0Cell} (e : C.1Cell x y)
    {f₀ f₁ f₂ f₃ f₄ f₅ : C.1Cell y z}
    (p : C.2Cell f₀ f₁) (q : C.2Cell f₁ f₂) (r : C.2Cell f₂ f₃)
    (s : C.2Cell f₃ f₄) (u : C.2Cell f₄ f₅)
    →   (e C.◁w (p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ u))
      ≡ (e C.◁w p) C.⋆₂ (e C.◁w q) C.⋆₂ (e C.◁w r)
          C.⋆₂ (e C.◁w s) C.⋆₂ (e C.◁w u)
  ◁5 e p q r s u =
      ◁wSeq C e p _
    ∙ C.⟨⟩⋆₂⟨ ◁wSeq C e q _ ∙ C.⟨⟩⋆₂⟨ ◁3 e r s u ⟩ ⟩

  ▷6 : {x y z : C.0Cell} {f₀ f₁ f₂ f₃ f₄ f₅ f₆ : C.1Cell x y}
    (p : C.2Cell f₀ f₁) (q : C.2Cell f₁ f₂) (r : C.2Cell f₂ f₃)
    (s : C.2Cell f₃ f₄) (v : C.2Cell f₄ f₅) (w : C.2Cell f₅ f₆)
    (h : C.1Cell y z)
    →   ((p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ v C.⋆₂ w) C.▷w h)
      ≡ (p C.▷w h) C.⋆₂ (q C.▷w h) C.⋆₂ (r C.▷w h)
          C.⋆₂ (s C.▷w h) C.⋆₂ (v C.▷w h) C.⋆₂ (w C.▷w h)
  ▷6 p q r s v w h = ▷wSeq C p _ h ∙ C.⟨⟩⋆₂⟨ ▷5 q r s v w h ⟩

  ▷4 : {x y z : C.0Cell} {f₀ f₁ f₂ f₃ f₄ : C.1Cell x y}
    (p : C.2Cell f₀ f₁) (q : C.2Cell f₁ f₂) (r : C.2Cell f₂ f₃)
    (s : C.2Cell f₃ f₄) (h : C.1Cell y z)
    →   ((p C.⋆₂ q C.⋆₂ r C.⋆₂ s) C.▷w h)
      ≡ (p C.▷w h) C.⋆₂ (q C.▷w h) C.⋆₂ (r C.▷w h) C.⋆₂ (s C.▷w h)
  ▷4 p q r s h = ▷wSeq C p _ h ∙ C.⟨⟩⋆₂⟨ ▷3 q r s h ⟩

  ◁4 : {x y z : C.0Cell} (e : C.1Cell x y)
    {f₀ f₁ f₂ f₃ f₄ : C.1Cell y z}
    (p : C.2Cell f₀ f₁) (q : C.2Cell f₁ f₂) (r : C.2Cell f₂ f₃)
    (s : C.2Cell f₃ f₄)
    →   (e C.◁w (p C.⋆₂ q C.⋆₂ r C.⋆₂ s))
      ≡ (e C.◁w p) C.⋆₂ (e C.◁w q) C.⋆₂ (e C.◁w r) C.⋆₂ (e C.◁w s)
  ◁4 e p q r s = ◁wSeq C e p _ ∙ C.⟨⟩⋆₂⟨ ◁3 e q r s ⟩

  ◁6 : {x y z : C.0Cell} (e : C.1Cell x y)
    {f₀ f₁ f₂ f₃ f₄ f₅ f₆ : C.1Cell y z}
    (p : C.2Cell f₀ f₁) (q : C.2Cell f₁ f₂) (r : C.2Cell f₂ f₃)
    (s : C.2Cell f₃ f₄) (v : C.2Cell f₄ f₅) (w : C.2Cell f₅ f₆)
    →   (e C.◁w (p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ v C.⋆₂ w))
      ≡ (e C.◁w p) C.⋆₂ (e C.◁w q) C.⋆₂ (e C.◁w r)
          C.⋆₂ (e C.◁w s) C.⋆₂ (e C.◁w v) C.⋆₂ (e C.◁w w)
  ◁6 e p q r s v w = ◁wSeq C e p _ ∙ C.⟨⟩⋆₂⟨ ◁5 e q r s v w ⟩

  ▷7 : {x y z : C.0Cell} {f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ : C.1Cell x y}
    (o : C.2Cell f₀ f₁) (p : C.2Cell f₁ f₂) (q : C.2Cell f₂ f₃)
    (r : C.2Cell f₃ f₄) (s : C.2Cell f₄ f₅) (v : C.2Cell f₅ f₆)
    (w : C.2Cell f₆ f₇) (h : C.1Cell y z)
    →   ((o C.⋆₂ p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ v C.⋆₂ w) C.▷w h)
      ≡ (o C.▷w h) C.⋆₂ (p C.▷w h) C.⋆₂ (q C.▷w h) C.⋆₂ (r C.▷w h)
          C.⋆₂ (s C.▷w h) C.⋆₂ (v C.▷w h) C.⋆₂ (w C.▷w h)
  ▷7 o p q r s v w h = ▷wSeq C o _ h ∙ C.⟨⟩⋆₂⟨ ▷6 p q r s v w h ⟩

  ◁7 : {x y z : C.0Cell} (e : C.1Cell x y)
    {f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ : C.1Cell y z}
    (o : C.2Cell f₀ f₁) (p : C.2Cell f₁ f₂) (q : C.2Cell f₂ f₃)
    (r : C.2Cell f₃ f₄) (s : C.2Cell f₄ f₅) (v : C.2Cell f₅ f₆)
    (w : C.2Cell f₆ f₇)
    →   (e C.◁w (o C.⋆₂ p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ v C.⋆₂ w))
      ≡ (e C.◁w o) C.⋆₂ (e C.◁w p) C.⋆₂ (e C.◁w q) C.⋆₂ (e C.◁w r)
          C.⋆₂ (e C.◁w s) C.⋆₂ (e C.◁w v) C.⋆₂ (e C.◁w w)
  ◁7 e o p q r s v w = ◁wSeq C e o _ ∙ C.⟨⟩⋆₂⟨ ◁6 e p q r s v w ⟩

  ▷8 : {x y z : C.0Cell} {f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : C.1Cell x y}
    (n : C.2Cell f₀ f₁) (o : C.2Cell f₁ f₂) (p : C.2Cell f₂ f₃)
    (q : C.2Cell f₃ f₄) (r : C.2Cell f₄ f₅) (s : C.2Cell f₅ f₆)
    (v : C.2Cell f₆ f₇) (w : C.2Cell f₇ f₈) (h : C.1Cell y z)
    →   ((n C.⋆₂ o C.⋆₂ p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ v C.⋆₂ w) C.▷w h)
      ≡ (n C.▷w h) C.⋆₂ (o C.▷w h) C.⋆₂ (p C.▷w h) C.⋆₂ (q C.▷w h)
          C.⋆₂ (r C.▷w h) C.⋆₂ (s C.▷w h) C.⋆₂ (v C.▷w h)
          C.⋆₂ (w C.▷w h)
  ▷8 n o p q r s v w h = ▷wSeq C n _ h ∙ C.⟨⟩⋆₂⟨ ▷7 o p q r s v w h ⟩

  ◁8 : {x y z : C.0Cell} (e : C.1Cell x y)
    {f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : C.1Cell y z}
    (n : C.2Cell f₀ f₁) (o : C.2Cell f₁ f₂) (p : C.2Cell f₂ f₃)
    (q : C.2Cell f₃ f₄) (r : C.2Cell f₄ f₅) (s : C.2Cell f₅ f₆)
    (v : C.2Cell f₆ f₇) (w : C.2Cell f₇ f₈)
    →   (e C.◁w (n C.⋆₂ o C.⋆₂ p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ v C.⋆₂ w))
      ≡ (e C.◁w n) C.⋆₂ (e C.◁w o) C.⋆₂ (e C.◁w p) C.⋆₂ (e C.◁w q)
          C.⋆₂ (e C.◁w r) C.⋆₂ (e C.◁w s) C.⋆₂ (e C.◁w v)
          C.⋆₂ (e C.◁w w)
  ◁8 e n o p q r s v w = ◁wSeq C e n _ ∙ C.⟨⟩⋆₂⟨ ◁7 e o p q r s v w ⟩

  ▷9 : {x y z : C.0Cell}
    {f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : C.1Cell x y}
    (m : C.2Cell f₀ f₁) (n : C.2Cell f₁ f₂) (o : C.2Cell f₂ f₃)
    (p : C.2Cell f₃ f₄) (q : C.2Cell f₄ f₅) (r : C.2Cell f₅ f₆)
    (s : C.2Cell f₆ f₇) (v : C.2Cell f₇ f₈) (w : C.2Cell f₈ f₉)
    (h : C.1Cell y z)
    →   ((m C.⋆₂ n C.⋆₂ o C.⋆₂ p C.⋆₂ q C.⋆₂ r C.⋆₂ s C.⋆₂ v C.⋆₂ w)
          C.▷w h)
      ≡ (m C.▷w h) C.⋆₂ (n C.▷w h) C.⋆₂ (o C.▷w h) C.⋆₂ (p C.▷w h)
          C.⋆₂ (q C.▷w h) C.⋆₂ (r C.▷w h) C.⋆₂ (s C.▷w h)
          C.⋆₂ (v C.▷w h) C.⋆₂ (w C.▷w h)
  ▷9 m n o p q r s v w h =
    ▷wSeq C m _ h ∙ C.⟨⟩⋆₂⟨ ▷8 n o p q r s v w h ⟩

  ▷10 : {x y z : C.0Cell}
    {f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ g₀ : C.1Cell x y}
    (l : C.2Cell f₀ f₁) (m : C.2Cell f₁ f₂) (n : C.2Cell f₂ f₃)
    (o : C.2Cell f₃ f₄) (p : C.2Cell f₄ f₅) (q : C.2Cell f₅ f₆)
    (r : C.2Cell f₆ f₇) (s : C.2Cell f₇ f₈) (v : C.2Cell f₈ f₉)
    (w : C.2Cell f₉ g₀) (h : C.1Cell y z)
    →   ((l C.⋆₂ m C.⋆₂ n C.⋆₂ o C.⋆₂ p C.⋆₂ q C.⋆₂ r C.⋆₂ s
            C.⋆₂ v C.⋆₂ w) C.▷w h)
      ≡ (l C.▷w h) C.⋆₂ (m C.▷w h) C.⋆₂ (n C.▷w h) C.⋆₂ (o C.▷w h)
          C.⋆₂ (p C.▷w h) C.⋆₂ (q C.▷w h) C.⋆₂ (r C.▷w h)
          C.⋆₂ (s C.▷w h) C.⋆₂ (v C.▷w h) C.⋆₂ (w C.▷w h)
  ▷10 l m n o p q r s v w h =
    ▷wSeq C l _ h ∙ C.⟨⟩⋆₂⟨ ▷9 m n o p q r s v w h ⟩

  ◁9 : {x y z : C.0Cell} (e : C.1Cell x y)
    {f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : C.1Cell y z}
    (m : C.2Cell f₀ f₁) (n : C.2Cell f₁ f₂) (o : C.2Cell f₂ f₃)
    (p : C.2Cell f₃ f₄) (q : C.2Cell f₄ f₅) (r : C.2Cell f₅ f₆)
    (s : C.2Cell f₆ f₇) (v : C.2Cell f₇ f₈) (w : C.2Cell f₈ f₉)
    →   (e C.◁w (m C.⋆₂ n C.⋆₂ o C.⋆₂ p C.⋆₂ q C.⋆₂ r C.⋆₂ s
          C.⋆₂ v C.⋆₂ w))
      ≡ (e C.◁w m) C.⋆₂ (e C.◁w n) C.⋆₂ (e C.◁w o) C.⋆₂ (e C.◁w p)
          C.⋆₂ (e C.◁w q) C.⋆₂ (e C.◁w r) C.⋆₂ (e C.◁w s)
          C.⋆₂ (e C.◁w v) C.⋆₂ (e C.◁w w)
  ◁9 e m n o p q r s v w =
    ◁wSeq C e m _ ∙ C.⟨⟩⋆₂⟨ ◁8 e n o p q r s v w ⟩

  -- `⋆CancelL` along a whiskered iso.
  ▷wCancelL : {x y z : C.0Cell} {m m' : C.1Cell x y}
    {u : C.2Cell m m'} (iso : isIso C.Hom[ x , y ] u)
    (h : C.1Cell y z) {k : C.1Cell x z}
    {p q : C.2Cell (m' C.⋆₁ h) k}
    → (u C.▷w h) C.⋆₂ p ≡ (u C.▷w h) C.⋆₂ q → p ≡ q
  ▷wCancelL iso h e = ⋆CancelL (_ , ▷wIsIso C h iso) e

  ◁wCancelL : {x y z : C.0Cell} (e : C.1Cell x y)
    {m m' : C.1Cell y z} {u : C.2Cell m m'}
    (iso : isIso C.Hom[ y , z ] u) {k : C.1Cell x z}
    {p q : C.2Cell (e C.⋆₁ m') k}
    → (e C.◁w u) C.⋆₂ p ≡ (e C.◁w u) C.⋆₂ q → p ≡ q
  ◁wCancelL e iso q = ⋆CancelL (_ , ◁wIsIso C e iso) q

  -- Rearrangements of the pentagon axiom.
  module _ {x y z w v : C.0Cell}
    (p : C.1Cell x y) (q : C.1Cell y z)
    (r : C.1Cell z w) (s : C.1Cell w v) where
    private
      Ai : CatIso C.Hom[ x , v ]
        (((p C.⋆₁ q) C.⋆₁ r) C.⋆₁ s) ((p C.⋆₁ (q C.⋆₁ r)) C.⋆₁ s)
      Ai = C.α⁺ p q r C.▷w s , ▷wIsIso C s (αI p q r .snd)

      Bi : CatIso C.Hom[ x , v ]
        ((p C.⋆₁ (q C.⋆₁ r)) C.⋆₁ s) (p C.⋆₁ ((q C.⋆₁ r) C.⋆₁ s))
      Bi = αI p (q C.⋆₁ r) s

      Ci : CatIso C.Hom[ x , v ]
        (p C.⋆₁ ((q C.⋆₁ r) C.⋆₁ s)) (p C.⋆₁ (q C.⋆₁ (r C.⋆₁ s)))
      Ci = p C.◁w C.α⁺ q r s , ◁wIsIso C p (αI q r s .snd)

      Di : CatIso C.Hom[ x , v ]
        (((p C.⋆₁ q) C.⋆₁ r) C.⋆₁ s) ((p C.⋆₁ q) C.⋆₁ (r C.⋆₁ s))
      Di = αI (p C.⋆₁ q) r s

      Ei : CatIso C.Hom[ x , v ]
        ((p C.⋆₁ q) C.⋆₁ (r C.⋆₁ s)) (p C.⋆₁ (q C.⋆₁ (r C.⋆₁ s)))
      Ei = αI p q (r C.⋆₁ s)

      pent :   (C.α⁺ p q r C.▷w s) C.⋆₂ C.α⁺ p (q C.⋆₁ r) s
                 C.⋆₂ (p C.◁w C.α⁺ q r s)
             ≡ C.α⁺ (p C.⋆₁ q) r s C.⋆₂ C.α⁺ p q (r C.⋆₁ s)
      pent = C.pentagon x y z w v p q r s

    pentP1 :   C.α⁻ p (q C.⋆₁ r) s C.⋆₂ (C.α⁻ p q r C.▷w s)
                 C.⋆₂ C.α⁺ (p C.⋆₁ q) r s
             ≡ (p C.◁w C.α⁺ q r s) C.⋆₂ C.α⁻ p q (r C.⋆₁ s)
    pentP1 =
        sym (C.⋆₂Assoc _ _ _)
      ∙ sym (⋆InvLMove (⋆Iso Ai Bi)
          ( sym (C.⋆₂Assoc _ _ _)
          ∙ C.⟨ C.⋆₂Assoc _ _ _ ⟩⋆₂⟨⟩
          ∙ C.⟨ pent ⟩⋆₂⟨⟩
          ∙ C.⋆₂Assoc _ _ _
          ∙ C.⟨⟩⋆₂⟨ Ei .snd .ret ⟩
          ∙ C.⋆₂IdR _))

    pentP2 :   (p C.◁w C.α⁻ q r s) C.⋆₂ C.α⁻ p (q C.⋆₁ r) s
                 C.⋆₂ (C.α⁻ p q r C.▷w s)
             ≡ C.α⁻ p q (r C.⋆₁ s) C.⋆₂ C.α⁻ (p C.⋆₁ q) r s
    pentP2 =
        C.⟨⟩⋆₂⟨ ⋆InvRMove Di
          ( C.⋆₂Assoc (C.α⁻ p (q C.⋆₁ r) s) (C.α⁻ p q r C.▷w s)
                      (C.α⁺ (p C.⋆₁ q) r s)
          ∙ pentP1) ⟩
      ∙ sym (C.⋆₂Assoc _ _ _)
      ∙ C.⟨ sym (C.⋆₂Assoc _ _ _) ⟩⋆₂⟨⟩
      ∙ C.⟨ C.⟨ Ci .snd .sec ⟩⋆₂⟨⟩ ⟩⋆₂⟨⟩
      ∙ C.⟨ C.⋆₂IdL _ ⟩⋆₂⟨⟩

    pentP3 :   C.α⁻ (p C.⋆₁ q) r s C.⋆₂ (C.α⁺ p q r C.▷w s)
             ≡ C.α⁺ p q (r C.⋆₁ s) C.⋆₂ (p C.◁w C.α⁻ q r s)
                 C.⋆₂ C.α⁻ p (q C.⋆₁ r) s
    pentP3 = sym (⋆InvLMove Di
      ( sym (C.⋆₂Assoc _ _ _)
      ∙ C.⟨ sym pent ⟩⋆₂⟨⟩
      ∙ C.⋆₂Assoc _ _ _
      ∙ C.⟨⟩⋆₂⟨ ⋆Iso Bi Ci .snd .ret ⟩
      ∙ C.⋆₂IdR _))

    pentP4 :   C.α⁺ p (q C.⋆₁ r) s C.⋆₂ (p C.◁w C.α⁺ q r s)
                 C.⋆₂ C.α⁻ p q (r C.⋆₁ s)
             ≡ (C.α⁻ p q r C.▷w s) C.⋆₂ C.α⁺ (p C.⋆₁ q) r s
    pentP4 =
        C.⟨⟩⋆₂⟨ sym pentP1 ⟩
      ∙ sym (C.⋆₂Assoc _ _ _)
      ∙ C.⟨ Bi .snd .ret ⟩⋆₂⟨⟩
      ∙ C.⋆₂IdL _

  -- The associator against the unitors.
  αλ : {x y z : C.0Cell} (p : C.1Cell x y) (q : C.1Cell y z)
    → C.α⁺ C.id₁ p q C.⋆₂ C.λ⁺ (p C.⋆₁ q) ≡ (C.λ⁺ p C.▷w q)
  αλ p q =
      C.⟨⟩⋆₂⟨ sym (λ⋆₁ C p q) ⟩
    ∙ pushn (αI C.id₁ p q .snd .ret) _
    ∙ C.⋆₂IdL _

  ρα : {x y z : C.0Cell} (p : C.1Cell x y) (q : C.1Cell y z)
    → C.ρ⁻ (p C.⋆₁ q) C.⋆₂ C.α⁺ p q C.id₁ ≡ (p C.◁w C.ρ⁻ q)
  ρα p q =
      C.⟨ ρ⁻⋆₁ C p q ⟩⋆₂⟨⟩
    ∙ C.⋆₂Assoc _ _ _
    ∙ C.⟨⟩⋆₂⟨ αI p q C.id₁ .snd .sec ⟩
    ∙ C.⋆₂IdR _

  -- Interchange, in the form used to move a whiskered 2-cell past
  -- another.
  ▷◁exch : {x y z : C.0Cell} {k k' : C.1Cell x y} (σ : C.2Cell k k')
    {m n : C.1Cell y z} (θ : C.2Cell m n)
    → (σ C.▷w m) C.⋆₂ (k' C.◁w θ) ≡ (k C.◁w θ) C.⋆₂ (σ C.▷w n)
  ▷◁exch σ θ =
      sym (C.⋆ₕSeq σ C.id₂ C.id₂ θ)
    ∙ C.⟨ C.⋆₂IdR σ ⟩⋆ₕ⟨ C.⋆₂IdL θ ⟩
    ∙ C.⟨ sym (C.⋆₂IdL σ) ⟩⋆ₕ⟨ sym (C.⋆₂IdR θ) ⟩
    ∙ C.⋆ₕSeq C.id₂ σ θ C.id₂

  -- Right-whiskering twice, in terms of whiskering by the composite.
  ▷⋆₁ : {x y z w : C.0Cell} {m m' : C.1Cell x y} (α : C.2Cell m m')
    (s : C.1Cell y z) (t : C.1Cell z w)
    → (α C.▷w s) C.▷w t
      ≡ C.α⁺ m s t C.⋆₂ (α C.▷w (s C.⋆₁ t)) C.⋆₂ C.α⁻ m' s t
  ▷⋆₁ {m' = m'} α s t =
      ⋆InvRMove (αI m' s t) (α⁺natL α s t)
    ∙ C.⋆₂Assoc _ _ _


-- Second block, so `▷⋆₁` above can be instantiated at `C ^opᴮ`.
module _ (C : Bicategory ℓ ℓ' ℓ'') where
  private
    module C = Bicategory C

  ◁⋆₁ : {x y z w : C.0Cell} {m m' : C.1Cell z w} (α : C.2Cell m m')
    (s : C.1Cell y z) (t : C.1Cell x y)
    → t C.◁w (s C.◁w α)
      ≡ C.α⁻ t s m C.⋆₂ ((t C.⋆₁ s) C.◁w α) C.⋆₂ C.α⁺ t s m'
  ◁⋆₁ α s t = ▷⋆₁ (C ^opᴮ) α s t
