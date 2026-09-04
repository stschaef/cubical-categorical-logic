{-# OPTIONS --lossy-unification #-}
{- Composition of lax functors and of pseudofunctors. -}
module Cubical.Categories.Bicategory.Functor.Composition where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.Instances.BinProduct

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo

private
  variable
    ℓb ℓb' ℓb'' ℓc ℓc' ℓc'' ℓd ℓd' ℓd'' : Level

open Category
open Functor
open NatTrans
open LaxFunctor
open Pseudofunctor

module _ {B : Bicategory ℓb ℓb' ℓb''}
         {C : Bicategory ℓc ℓc' ℓc''}
         {D : Bicategory ℓd ℓd' ℓd''}
         (G : LaxFunctor C D) (F : LaxFunctor B C) where
  private
    module B = Bicategory B
    module C = Bicategory C
    module D = Bicategory D
    module F = LaxFunctor F
    module G = LaxFunctor G

    ob₀ : B.ob → D.ob
    ob₀ x = G.F-ob (F.F-ob x)

    Hom₀ : ∀ {x y} → Functor B.Hom[ x , y ] D.Hom[ ob₀ x , ob₀ y ]
    Hom₀ = G.F-Hom ∘F F.F-Hom

    1c : ∀ {x y} → B.1Cell x y → D.1Cell (ob₀ x) (ob₀ y)
    1c f = G.F-1cell (F.F-1cell f)

    2c : ∀ {x y}{f g : B.1Cell x y} → B.2Cell f g → D.2Cell (1c f) (1c g)
    2c α = G.F-2cell (F.F-2cell α)

    ε : ∀ {x} → D.2Cell D.id₁ (1c (B.id₁ {x}))
    ε = G.F⁰ D.⋆₂ G.F-2cell F.F⁰

    μ : ∀ {x y z} (f : B.1Cell x y) (g : B.1Cell y z)
      → D.2Cell (1c f D.⋆₁ 1c g) (1c (f B.⋆₁ g))
    μ f g = G.F² (F.F-1cell f) (F.F-1cell g) D.⋆₂ G.F-2cell (F.F² f g)

    G2id : ∀ {x y} (a : C.1Cell x y) → G.F-2cell (C.id₂ {f = a}) ≡ D.id₂
    G2id a = G.F-Hom .F-id

    -- G's F-seq naturality, in whiskered form.
    Gnat▷ : ∀ {x y z}{a a' : C.1Cell x y}
      (α : C.2Cell a a') (b : C.1Cell y z)
      → (G.F-2cell α D.▷w G.F-1cell b) D.⋆₂ G.F² a' b
        ≡ G.F² a b D.⋆₂ G.F-2cell (α C.▷w b)
    Gnat▷ {a = a}{a' = a'} α b =
      w ∙ G.F-seq .N-hom (α , C.id₂ {f = b})
      where
      w : (G.F-2cell α D.▷w G.F-1cell b) D.⋆₂ G.F² a' b
        ≡ (G.F-2cell α D.⋆ₕ G.F-2cell (C.id₂ {f = b})) D.⋆₂ G.F² a' b
      w = D.⟨ D.⟨⟩⋆ₕ⟨ sym (G2id b) ⟩ ⟩⋆₂⟨⟩

    Gnat◁ : ∀ {x y z} (a : C.1Cell x y){b b' : C.1Cell y z}
      (β : C.2Cell b b')
      → (G.F-1cell a D.◁w G.F-2cell β) D.⋆₂ G.F² a b'
        ≡ G.F² a b D.⋆₂ G.F-2cell (a C.◁w β)
    Gnat◁ a {b = b}{b' = b'} β =
      w ∙ G.F-seq .N-hom (C.id₂ {f = a} , β)
      where
      w : (G.F-1cell a D.◁w G.F-2cell β) D.⋆₂ G.F² a b'
        ≡ (G.F-2cell (C.id₂ {f = a}) D.⋆ₕ G.F-2cell β) D.⋆₂ G.F² a b'
      w = D.⟨ D.⟨ sym (G2id a) ⟩⋆ₕ⟨⟩ ⟩⋆₂⟨⟩

    idNat : ∀ {x} {p q : 𝟙C .ob} (u : 𝟙C [ p , q ])
      → D.id {ob₀ x} .F-hom u D.⋆₂ ε {x}
        ≡ ε {x} D.⋆₂ G.F-2cell (F.F-2cell (B.id {x} .F-hom u))
    idNat u =
        sym (D.⋆₂Assoc _ _ _)
      ∙ D.⟨ G.F-id .N-hom u ⟩⋆₂⟨⟩
      ∙ D.⋆₂Assoc _ _ _
      ∙ D.⟨⟩⋆₂⟨ sym (G.F-Hom .F-seq _ _) ⟩
      ∙ D.⟨⟩⋆₂⟨ cong G.F-2cell (F.F-id .N-hom u) ⟩
      ∙ D.⟨⟩⋆₂⟨ G.F-Hom .F-seq _ _ ⟩
      ∙ sym (D.⋆₂Assoc _ _ _)

    seqNat : ∀ {x y z}{p q : (B.Hom[ x , y ] ×C B.Hom[ y , z ]) .ob}
      (u : (B.Hom[ x , y ] ×C B.Hom[ y , z ]) [ p , q ])
      → (2c (u .fst) D.⋆ₕ 2c (u .snd)) D.⋆₂ μ (q .fst) (q .snd)
        ≡ μ (p .fst) (p .snd)
          D.⋆₂ G.F-2cell (F.F-2cell (u .fst B.⋆ₕ u .snd))
    seqNat u =
        sym (D.⋆₂Assoc _ _ _)
      ∙ D.⟨ G.F-seq .N-hom (F.F-2cell (u .fst) , F.F-2cell (u .snd)) ⟩⋆₂⟨⟩
      ∙ D.⋆₂Assoc _ _ _
      ∙ D.⟨⟩⋆₂⟨ sym (G.F-Hom .F-seq _ _) ⟩
      ∙ D.⟨⟩⋆₂⟨ cong G.F-2cell (F.F-seq .N-hom u) ⟩
      ∙ D.⟨⟩⋆₂⟨ G.F-Hom .F-seq _ _ ⟩
      ∙ sym (D.⋆₂Assoc _ _ _)

    ∘lax-λ : (x y : B.ob) (f : B.1Cell x y)
      → (ε {x} D.▷w 1c f) D.⋆₂ μ (B.id₁ {x}) f D.⋆₂ 2c (B.λ⁺ f)
        ≡ D.λ⁺ (1c f)
    ∘lax-λ x y f =
        D.⟨ ▷wSeq D G.F⁰ (G.F-2cell F.F⁰) (1c f) ⟩⋆₂⟨⟩
      ∙ D.⋆₂Assoc _ _ _
      ∙ D.⟨⟩⋆₂⟨ D.⟨⟩⋆₂⟨ D.⋆₂Assoc _ _ _ ⟩ ⟩
      ∙ D.⟨⟩⋆₂⟨ sym (D.⋆₂Assoc _ _ _) ⟩
      ∙ D.⟨⟩⋆₂⟨ D.⟨ Gnat▷ F.F⁰ (F.F-1cell f) ⟩⋆₂⟨⟩ ⟩
      ∙ D.⟨⟩⋆₂⟨ D.⋆₂Assoc _ _ _ ⟩
      ∙ D.⟨⟩⋆₂⟨ D.⟨⟩⋆₂⟨
            D.⟨⟩⋆₂⟨ sym (G.F-Hom .F-seq _ _) ⟩
          ∙ sym (G.F-Hom .F-seq _ _)
          ∙ cong G.F-2cell (F.lax-λ x y f) ⟩ ⟩
      ∙ G.lax-λ _ _ (F.F-1cell f)

    ∘lax-ρ : (x y : B.ob) (f : B.1Cell x y)
      → (1c f D.◁w ε {y}) D.⋆₂ μ f (B.id₁ {y}) D.⋆₂ 2c (B.ρ⁺ f)
        ≡ D.ρ⁺ (1c f)
    ∘lax-ρ x y f =
        D.⟨ ◁wSeq D (1c f) G.F⁰ (G.F-2cell F.F⁰) ⟩⋆₂⟨⟩
      ∙ D.⋆₂Assoc _ _ _
      ∙ D.⟨⟩⋆₂⟨ D.⟨⟩⋆₂⟨ D.⋆₂Assoc _ _ _ ⟩ ⟩
      ∙ D.⟨⟩⋆₂⟨ sym (D.⋆₂Assoc _ _ _) ⟩
      ∙ D.⟨⟩⋆₂⟨ D.⟨ Gnat◁ (F.F-1cell f) F.F⁰ ⟩⋆₂⟨⟩ ⟩
      ∙ D.⟨⟩⋆₂⟨ D.⋆₂Assoc _ _ _ ⟩
      ∙ D.⟨⟩⋆₂⟨ D.⟨⟩⋆₂⟨
            D.⟨⟩⋆₂⟨ sym (G.F-Hom .F-seq _ _) ⟩
          ∙ sym (G.F-Hom .F-seq _ _)
          ∙ cong G.F-2cell (F.lax-ρ x y f) ⟩ ⟩
      ∙ G.lax-ρ _ _ (F.F-1cell f)

    ∘lax-α : (x y z w : B.ob)
      (f : B.1Cell x y) (g : B.1Cell y z) (h : B.1Cell z w)
      →   (μ f g D.▷w 1c h) D.⋆₂ μ (f B.⋆₁ g) h D.⋆₂ 2c (B.α⁺ f g h)
        ≡ D.α⁺ (1c f) (1c g) (1c h)
          D.⋆₂ (1c f D.◁w μ g h) D.⋆₂ μ f (g B.⋆₁ h)
    ∘lax-α x y z w f g h =
        D.⟨ ▷wSeq D (G.F² (F.F-1cell f) (F.F-1cell g))
                    (G.F-2cell (F.F² f g)) (1c h) ⟩⋆₂⟨⟩
      ∙ D.⋆₂Assoc _ _ _
      ∙ D.⟨⟩⋆₂⟨ D.⟨⟩⋆₂⟨ D.⋆₂Assoc _ _ _ ⟩ ⟩
      ∙ D.⟨⟩⋆₂⟨ sym (D.⋆₂Assoc _ _ _) ⟩
      ∙ D.⟨⟩⋆₂⟨ D.⟨ Gnat▷ (F.F² f g) (F.F-1cell h) ⟩⋆₂⟨⟩ ⟩
      ∙ D.⟨⟩⋆₂⟨ D.⋆₂Assoc _ _ _ ⟩
      ∙ D.⟨⟩⋆₂⟨ D.⟨⟩⋆₂⟨
            D.⟨⟩⋆₂⟨ sym (G.F-Hom .F-seq _ _) ⟩
          ∙ sym (G.F-Hom .F-seq _ _)
          ∙ cong G.F-2cell (F.lax-α x y z w f g h)
          ∙ G.F-Hom .F-seq _ _
          ∙ D.⟨⟩⋆₂⟨ G.F-Hom .F-seq _ _ ⟩ ⟩ ⟩
      ∙ D.⟨⟩⋆₂⟨ sym (D.⋆₂Assoc _ _ _) ⟩
      ∙ sym (D.⋆₂Assoc _ _ _)
      ∙ D.⟨ G.lax-α _ _ _ _ (F.F-1cell f) (F.F-1cell g) (F.F-1cell h) ⟩⋆₂⟨⟩
      ∙ D.⋆₂Assoc _ _ _
      ∙ D.⟨⟩⋆₂⟨ D.⋆₂Assoc _ _ _ ⟩
      ∙ D.⟨⟩⋆₂⟨ D.⟨⟩⋆₂⟨ sym (D.⋆₂Assoc _ _ _) ⟩ ⟩
      ∙ D.⟨⟩⋆₂⟨ D.⟨⟩⋆₂⟨ D.⟨ sym (Gnat◁ (F.F-1cell f) (F.F² g h)) ⟩⋆₂⟨⟩ ⟩ ⟩
      ∙ D.⟨⟩⋆₂⟨ D.⟨⟩⋆₂⟨ D.⋆₂Assoc _ _ _ ⟩ ⟩
      ∙ D.⟨⟩⋆₂⟨ sym (D.⋆₂Assoc _ _ _) ⟩
      ∙ D.⟨⟩⋆₂⟨ D.⟨ sym (◁wSeq D (1c f) (G.F² (F.F-1cell g) (F.F-1cell h))
                                (G.F-2cell (F.F² g h))) ⟩⋆₂⟨⟩ ⟩

  compLax : LaxFunctor B D
  compLax .F-ob = ob₀
  compLax .F-Hom = Hom₀
  compLax .F-id .N-ob _ = ε
  compLax .F-id .N-hom = idNat
  compLax .F-seq .N-ob p = μ (p .fst) (p .snd)
  compLax .F-seq .N-hom = seqNat
  compLax .lax-λ = ∘lax-λ
  compLax .lax-ρ = ∘lax-ρ
  compLax .lax-α = ∘lax-α

infixr 30 _∘Lax_ _∘Ps_

_∘Lax_ : {B : Bicategory ℓb ℓb' ℓb''} {C : Bicategory ℓc ℓc' ℓc''}
         {D : Bicategory ℓd ℓd' ℓd''}
  → LaxFunctor C D → LaxFunctor B C → LaxFunctor B D
G ∘Lax F = compLax G F

_∘Ps_ : {B : Bicategory ℓb ℓb' ℓb''} {C : Bicategory ℓc ℓc' ℓc''}
        {D : Bicategory ℓd ℓd' ℓd''}
  → Pseudofunctor C D → Pseudofunctor B C → Pseudofunctor B D
(G ∘Ps F) .laxFunctor = G .laxFunctor ∘Lax F .laxFunctor
(G ∘Ps F) .F-id-isIso p =
  ⋆IsIso (G .F-id-isIso p)
         (F-PresIsIso {F = G .laxFunctor .F-Hom} (F .F-id-isIso p))
(G ∘Ps F) .F-seq-isIso p =
  ⋆IsIso (G .F-seq-isIso _)
         (F-PresIsIso {F = G .laxFunctor .F-Hom} (F .F-seq-isIso p))
