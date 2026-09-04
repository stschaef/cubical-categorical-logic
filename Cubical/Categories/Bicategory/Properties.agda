{-# OPTIONS --lossy-unification #-}
{- Kelly's unit coherence lemmas: the unitors interact with the
   associator exactly as the triangle axiom demands, even in the
   degenerate cases that are *not* axioms. -}
module Cubical.Categories.Bicategory.Properties where

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

private
  variable
    ℓ ℓ' ℓ'' : Level

open Functor
open NatTrans
open NatIso
open isIso

module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  -- Whiskering by id₁ turns vertical composites into composites.
  ◁wSeq : {x y z : B.0Cell} (f : B.1Cell x y) {m n p : B.1Cell y z}
    (a : B.2Cell m n) (b : B.2Cell n p)
    → f B.◁w (a B.⋆₂ b) ≡ (f B.◁w a) B.⋆₂ (f B.◁w b)
  ◁wSeq f a b =
    B.⟨ sym (B.⋆₂IdL B.id₂) ⟩⋆ₕ⟨⟩ ∙ B.⋆ₕSeq B.id₂ B.id₂ a b

  ▷wSeq : {x y z : B.0Cell} {m n p : B.1Cell x y}
    (a : B.2Cell m n) (b : B.2Cell n p) (h : B.1Cell y z)
    → (a B.⋆₂ b) B.▷w h ≡ (a B.▷w h) B.⋆₂ (b B.▷w h)
  ▷wSeq {x} {y} {z} a b h =
      B.⟨⟩⋆ₕ⟨_⟩ {α = a B.⋆₂ b}
           (sym (B.⋆₂IdL B.id₂))
    ∙ B.⋆ₕSeq a b B.id₂ B.id₂

  -- Naturality of the left unitor, phrased with whiskering.
  λ-nat : {x z : B.0Cell} {m n : B.1Cell x z} (u : B.2Cell m n)
    → (B.id₁ B.◁w u) B.⋆₂ B.λ⁺ n ≡ B.λ⁺ m B.⋆₂ u
  λ-nat {x} {z} {m} {n} u =
      B.⟨ B.⟨ sym (B.id {x} .F-id) ⟩⋆ₕ⟨⟩ ⟩⋆₂⟨⟩
    ∙ B.λU x z .trans .N-hom (refl , u)

  -- Naturality of the left unitor's inverse.
  λ⁻-nat : {x z : B.0Cell} {m n : B.1Cell x z} (u : B.2Cell m n)
    → u B.⋆₂ B.λ⁻ n ≡ B.λ⁻ m B.⋆₂ (B.id₁ B.◁w u)
  λ⁻-nat {x} {z} {m} {n} u =
    ⋆InvsFlipSq (NatIsoAt (B.λU x z) (tt* , m))
                (NatIsoAt (B.λU x z) (tt* , n))
                (sym (λ-nat u))

  -- Left-whiskering λ⁺ by id₁ is λ⁺ at the composite with id₁.
  ◁λ⁺ : {x z : B.0Cell} (f : B.1Cell x z)
    → B.id₁ B.◁w B.λ⁺ f ≡ B.λ⁺ (B.id₁ B.⋆₁ f)
  ◁λ⁺ {x} {z} f = ⋆CancelR (NatIsoAt (B.λU x z) (tt* , f)) (λ-nat (B.λ⁺ f))

  -- A 2-cell is recoverable from its left-whiskering by id₁ …
  ◁id₁-reduce : {x z : B.0Cell} {m n : B.1Cell x z} (u : B.2Cell m n)
    → u ≡ B.λ⁻ m B.⋆₂ ((B.id₁ B.◁w u) B.⋆₂ B.λ⁺ n)
  ◁id₁-reduce {x} {z} {m} {n} u =
      sym (B.⋆₂IdL u)
    ∙ cong (B._⋆₂ u) (sym (B.λU x z .nIso (tt* , m) .sec))
    ∙ B.⋆₂Assoc _ _ _
    ∙ cong (B.λ⁻ m B.⋆₂_) (sym (λ-nat u))

  -- … so left-whiskering by id₁ is faithful.
  ◁id₁-faithful : {x z : B.0Cell} {m n : B.1Cell x z} (u v : B.2Cell m n)
    → (B.id₁ B.◁w u) ≡ (B.id₁ B.◁w v) → u ≡ v
  ◁id₁-faithful {m = m} {n = n} u v p =
      ◁id₁-reduce u
    ∙ cong (λ w → B.λ⁻ m B.⋆₂ (w B.⋆₂ B.λ⁺ n)) p
    ∙ sym (◁id₁-reduce v)

  module _ {x y z : B.0Cell} (f : B.1Cell x y) (g : B.1Cell y z) where
    private
      A1 = B.α⁺ (B.id₁ {x}) (B.id₁ {x}) f
      A2 = B.α⁺ (B.id₁ {x}) (B.id₁ B.⋆₁ f) g
      A3 = B.α⁺ (B.id₁ {x}) f g
      A4 = B.α⁺ (B.id₁ {x} B.⋆₁ B.id₁) f g
      A5 = B.α⁺ (B.id₁ {x}) (B.id₁ {x}) (f B.⋆₁ g)
      W  = B.id₁ B.◁w B.λ⁺ (f B.⋆₁ g)

      LIso : CatIso B.Hom[ x , z ]
        (((B.id₁ B.⋆₁ B.id₁) B.⋆₁ f) B.⋆₁ g)
        ((B.id₁ B.⋆₁ (B.id₁ B.⋆₁ f)) B.⋆₁ g)
      LIso = F-Iso {F = B.seq x y z}
        (CatIso× B.Hom[ x , y ] B.Hom[ y , z ]
          (NatIsoAt (B.α x x x y) (B.id₁ , B.id₁ , f)) idCatIso)

      MIso : CatIso B.Hom[ x , z ]
        ((B.id₁ B.⋆₁ (B.id₁ B.⋆₁ f)) B.⋆₁ g)
        (B.id₁ B.⋆₁ ((B.id₁ B.⋆₁ f) B.⋆₁ g))
      MIso = NatIsoAt (B.α x x y z) (B.id₁ , B.id₁ B.⋆₁ f , g)

      -- naturality of α at (ρ⁺ id₁ , id₂ , id₂)
      natα1 : A4 B.⋆₂ (B.ρ⁺ B.id₁ B.▷w (f B.⋆₁ g))
            ≡ ((B.ρ⁺ B.id₁ B.▷w f) B.▷w g) B.⋆₂ A3
      natα1 =
          B.⟨⟩⋆₂⟨ B.⟨⟩⋆ₕ⟨ sym B.⋆ₕId ⟩ ⟩
        ∙ sym (B.α x x y z .trans .N-hom (B.ρ⁺ B.id₁ , B.id₂ , B.id₂))

      -- naturality of α at (id₂ , λ⁺ f , id₂)
      natα2 : ((B.id₁ B.◁w B.λ⁺ f) B.▷w g) B.⋆₂ A3
            ≡ A2 B.⋆₂ (B.id₁ B.◁w (B.λ⁺ f B.▷w g))
      natα2 = B.α x x y z .trans .N-hom (B.id₂ , B.λ⁺ f , B.id₂)

      big : (A1 B.▷w g) B.⋆₂ (A2 B.⋆₂ ((B.id₁ B.◁w A3) B.⋆₂ W))
          ≡ (A1 B.▷w g) B.⋆₂ (A2 B.⋆₂ (B.id₁ B.◁w (B.λ⁺ f B.▷w g)))
      big =
          cong ((A1 B.▷w g) B.⋆₂_) (sym (B.⋆₂Assoc A2 (B.id₁ B.◁w A3) W))
        ∙ sym (B.⋆₂Assoc (A1 B.▷w g) (A2 B.⋆₂ (B.id₁ B.◁w A3)) W)
        ∙ cong (B._⋆₂ W) (B.pentagon x x x y z B.id₁ B.id₁ f g)
        ∙ B.⋆₂Assoc A4 A5 W
        ∙ cong (A4 B.⋆₂_) (B.triangle x x z B.id₁ (f B.⋆₁ g))
        ∙ natα1
        ∙ cong (B._⋆₂ A3)
               ( cong (B._▷w g) (sym (B.triangle x x y B.id₁ f))
               ∙ ▷wSeq A1 (B.id₁ B.◁w B.λ⁺ f) g)
        ∙ B.⋆₂Assoc (A1 B.▷w g) ((B.id₁ B.◁w B.λ⁺ f) B.▷w g) A3
        ∙ cong ((A1 B.▷w g) B.⋆₂_) natα2

      step2 : (B.id₁ B.◁w A3) B.⋆₂ W ≡ B.id₁ B.◁w (B.λ⁺ f B.▷w g)
      step2 = ⋆CancelL MIso (⋆CancelL LIso big)

      aux : A3 B.⋆₂ B.λ⁺ (f B.⋆₁ g) ≡ B.λ⁺ f B.▷w g
      aux = ◁id₁-faithful _ _
        (◁wSeq B.id₁ A3 (B.λ⁺ (f B.⋆₁ g)) ∙ step2)

    λ⋆₁ : B.α⁻ B.id₁ f g B.⋆₂ (B.λ⁺ f B.▷w g) ≡ B.λ⁺ (f B.⋆₁ g)
    λ⋆₁ = sym (⋆InvLMove (NatIsoAt (B.α x x y z) (B.id₁ , f , g)) aux)

-- The dual, by instantiating λ⋆₁ at the opposite bicategory.
module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  ρ⋆₁ : {x y z : B.0Cell} (g : B.1Cell y z) (f : B.1Cell x y)
    → B.α⁺ f g B.id₁ B.⋆₂ (f B.◁w B.ρ⁺ g) ≡ B.ρ⁺ (f B.⋆₁ g)
  ρ⋆₁ g f = λ⋆₁ (B ^opᴮ) g f

  ▷wIsIso : {x y z : B.0Cell} {f g : B.1Cell x y} {u : B.2Cell f g}
    (h : B.1Cell y z)
    → isIso B.Hom[ x , y ] u → isIso B.Hom[ x , z ] (u B.▷w h)
  ▷wIsIso h isI .inv = isI .inv B.▷w h
  ▷wIsIso h isI .sec = sym (▷wSeq B _ _ h) ∙ B.⟨ isI .sec ⟩▷ h ∙ B.▷wId h
  ▷wIsIso h isI .ret = sym (▷wSeq B _ _ h) ∙ B.⟨ isI .ret ⟩▷ h ∙ B.▷wId h

  ◁wIsIso : {x y z : B.0Cell} (f : B.1Cell x y) {g h : B.1Cell y z}
    {u : B.2Cell g h}
    → isIso B.Hom[ y , z ] u → isIso B.Hom[ x , z ] (f B.◁w u)
  ◁wIsIso f isI .inv = f B.◁w isI .inv
  ◁wIsIso f isI .sec = sym (◁wSeq B f _ _) ∙ f B.◁⟨ isI .sec ⟩ ∙ B.◁wId f
  ◁wIsIso f isI .ret = sym (◁wSeq B f _ _) ∙ f B.◁⟨ isI .ret ⟩ ∙ B.◁wId f

  -- Naturality of the right unitor, dual to λ-nat.
  ρ-nat : {x z : B.0Cell} {m n : B.1Cell x z} (u : B.2Cell m n)
    → (u B.▷w B.id₁) B.⋆₂ B.ρ⁺ n ≡ B.ρ⁺ m B.⋆₂ u
  ρ-nat {x} {z} u = λ-nat (B ^opᴮ) {z} {x} u

  -- Right-whiskering by id₁ is faithful, dual to ◁id₁-faithful.
  ▷id₁-faithful : {x z : B.0Cell} {m n : B.1Cell x z} (u v : B.2Cell m n)
    → (u B.▷w B.id₁) ≡ (v B.▷w B.id₁) → u ≡ v
  ▷id₁-faithful {x} {z} = ◁id₁-faithful (B ^opᴮ) {z} {x}

  -- λ⋆₁ read on inverses.
  λ⁻⋆₁ : {x y z : B.0Cell} (f : B.1Cell x y) (g : B.1Cell y z)
    → (B.λ⁻ f B.▷w g) B.⋆₂ B.α⁺ B.id₁ f g ≡ B.λ⁻ (f B.⋆₁ g)
  λ⁻⋆₁ {x} {y} {z} f g =
    ⋆CancelL (NatIsoAt (B.λU x z) (tt* , f B.⋆₁ g))
      (  B.⟨ sym (λ⋆₁ B f g) ⟩⋆₂⟨⟩
       ∙ B.⋆₂Assoc _ _ _
       ∙ B.⟨⟩⋆₂⟨ sym (B.⋆₂Assoc _ _ _) ⟩
       ∙ B.⟨⟩⋆₂⟨ B.⟨ ▷wIsIso g (B.λU x y .nIso (tt* , f)) .ret ⟩⋆₂⟨⟩ ⟩
       ∙ B.⟨⟩⋆₂⟨ B.⋆₂IdL _ ⟩
       ∙ B.α x x y z .nIso (B.id₁ , f , g) .sec
       ∙ sym (B.λU x z .nIso (tt* , f B.⋆₁ g) .ret))

  -- Kelly: the two unitors agree at an identity 1-cell.
  λ⁺≡ρ⁺ : {x : B.0Cell} → B.λ⁺ (B.id₁ {x}) ≡ B.ρ⁺ (B.id₁ {x})
  λ⁺≡ρ⁺ {x} = ▷id₁-faithful _ _
    (  sym (B.⋆₂IdL _)
     ∙ B.⟨ sym (B.α x x x x .nIso (B.id₁ , B.id₁ , B.id₁) .ret) ⟩⋆₂⟨⟩
     ∙ B.⋆₂Assoc _ _ _
     ∙ B.⟨⟩⋆₂⟨ λ⋆₁ B B.id₁ B.id₁ ⟩
     ∙ B.⟨⟩⋆₂⟨ sym (◁λ⁺ B B.id₁) ⟩
     ∙ B.triangle x x x B.id₁ B.id₁)

  λ⁻≡ρ⁻ : {x : B.0Cell} → B.λ⁻ (B.id₁ {x}) ≡ B.ρ⁻ (B.id₁ {x})
  λ⁻≡ρ⁻ {x} = ⋆CancelL (NatIsoAt (B.λU x x) (tt* , B.id₁))
    (  B.λU x x .nIso (tt* , B.id₁) .ret
     ∙ sym (B.ρU x x .nIso (B.id₁ , tt*) .ret)
     ∙ B.⟨ sym λ⁺≡ρ⁺ ⟩⋆₂⟨⟩)

  -- Unitor/associator coherences.  Each of these had been reproved
  -- privately in two or more downstream files.
  α⁻ρ▷ : {x y z : B.0Cell} (a : B.1Cell x y) (b : B.1Cell y z)
    → B.α⁻ a B.id₁ b B.⋆₂ (B.ρ⁺ a B.▷w b) ≡ a B.◁w B.λ⁺ b
  α⁻ρ▷ {x} {y} {z} a b =
      B.⟨⟩⋆₂⟨ sym (B.triangle x y z a b) ⟩
    ∙ sym (B.⋆₂Assoc _ _ _)
    ∙ B.⟨ B.α x y y z .nIso (a , B.id₁ , b) .sec ⟩⋆₂⟨⟩
    ∙ B.⋆₂IdL _

  α⁻ρ◁ : {x y z : B.0Cell} (a : B.1Cell x y) (b : B.1Cell y z)
    → B.α⁻ a b B.id₁ B.⋆₂ B.ρ⁺ (a B.⋆₁ b) ≡ a B.◁w B.ρ⁺ b
  α⁻ρ◁ {x} {y} {z} a b =
      B.⟨⟩⋆₂⟨ sym (ρ⋆₁ b a) ⟩
    ∙ sym (B.⋆₂Assoc _ _ _)
    ∙ B.⟨ B.α x y z z .nIso (a , b , B.id₁) .sec ⟩⋆₂⟨⟩
    ∙ B.⋆₂IdL _

  ρ⁻◁ : {u v w : B.0Cell} (f : B.1Cell u v) (g : B.1Cell v w)
    → (f B.◁w B.ρ⁻ g) ≡ B.ρ⁻ (f B.⋆₁ g) B.⋆₂ B.α⁺ f g B.id₁
  ρ⁻◁ {u} {v} {w} f g =
    ⋆InvLMove (_ , B.ρU u w .nIso (f B.⋆₁ g , tt*))
      ( B.⟨ sym (ρ⋆₁ g f) ⟩⋆₂⟨⟩
      ∙ B.⋆₂Assoc _ _ _
      ∙ B.⟨⟩⋆₂⟨ sym (◁wSeq B f (B.ρ⁺ g) (B.ρ⁻ g))
              ∙ f B.◁⟨ B.ρU v w .nIso (g , tt*) .ret ⟩
              ∙ B.◁wId f ⟩
      ∙ B.⋆₂IdR _)

  ρ⁻⋆₁ : {u v w : B.0Cell} (f : B.1Cell u v) (g : B.1Cell v w)
    → B.ρ⁻ (f B.⋆₁ g) ≡ (f B.◁w B.ρ⁻ g) B.⋆₂ B.α⁻ f g B.id₁
  ρ⁻⋆₁ {u} {v} {w} f g =
    sym ( B.⟨ ρ⁻◁ f g ⟩⋆₂⟨⟩
        ∙ B.⋆₂Assoc _ _ _
        ∙ B.⟨⟩⋆₂⟨ B.α u v w w .nIso (f , g , B.id₁) .ret ⟩
        ∙ B.⋆₂IdR _)
