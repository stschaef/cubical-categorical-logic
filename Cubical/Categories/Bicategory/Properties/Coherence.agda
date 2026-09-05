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
