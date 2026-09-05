{-# OPTIONS --lossy-unification #-}
{-
  Inserters in a bicategory.

  An inserter of `f g : a → b` IS a biuniversal element of the
  inserter prestack: the vertex is the inserter 0-cell and the ELEMENT
  is the pair `(insᴮ , insθᴮ)` of the inserter projection and its
  2-cell, so `⟨ element ⟩ x` sends `h` to `h ⋆₁ insᴮ` carrying the
  reindexed `insθᴮ`.  Everything shape-independent is inherited from
  `Universal/Base.agda`.
-}
module Cubical.Categories.Bicategory.Limits.Inserter where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Inserter
open import Cubical.Categories.Bicategory.Universal.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

open Functor
open isIso

module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  Inserterᴮ : {a b : B.0Cell} (f g : B.1Cell a b)
    → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  Inserterᴮ {a} {b} f g = BiuniversalElement (InserterPrestack B {a} {b} f g)

  hasInsertersᴮ : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  hasInsertersᴮ = {a b : B.0Cell} (f g : B.1Cell a b) → Inserterᴮ f g

module InserterᴮNotation {B : Bicategory ℓ ℓ' ℓ''}
  {a b : Bicategory.0Cell B} {f g : Bicategory.1Cell B a b}
  (I : Inserterᴮ B f g) where
  private
    module B = Bicategory B
  module Ins = InserterPre {B = B} {a = a} {b = b} f g
  open BiuniversalElementNotation I public

  insᴮ : B.1Cell vertex a
  insᴮ = element .fst

  insθᴮ : B.2Cell (insᴮ B.⋆₁ f) (insᴮ B.⋆₁ g)
  insθᴮ = element .snd

  introᴵ : {x : B.0Cell} (h : B.1Cell x a) → Ins.Ins2 h → B.1Cell x vertex
  introᴵ h θ = intro (h , θ)

  introᴵβ : {x : B.0Cell} (h : B.1Cell x a) (θ : Ins.Ins2 h)
    → (introᴵ h θ B.⋆₁ insᴮ) B.≅₂ h
  introᴵβ {x} h θ = F-Iso {F = Ins.insForget x} (β (h , θ))

  -- `β` is a morphism of the inserter category: it carries the
  -- reindexed `insθᴮ` to `θ`.
  introᴵβ-cond : {x : B.0Cell} (h : B.1Cell x a) (θ : Ins.Ins2 h)
    → Ins.InsCond (Ins.reindθ (introᴵ h θ) insθᴮ) θ (introᴵβ h θ .fst)
  introᴵβ-cond h θ = β (h , θ) .fst .snd

  introᴵη : {x : B.0Cell} {h : B.1Cell x vertex} {k : B.1Cell x a}
    {θ : Ins.Ins2 k} (φ : (h B.⋆₁ insᴮ) B.≅₂ k)
    → Ins.InsCond (Ins.reindθ h insθᴮ) θ (φ .fst)
    → h B.≅₂ introᴵ k θ
  introᴵη φ c = intro≡ (Ins.insIso (φ .fst) (φ .snd) c)

  insᴮ-ext : {x : B.0Cell} {h k : B.1Cell x vertex} (α γ : B.2Cell h k)
    → (α B.▷w insᴮ) ≡ (γ B.▷w insᴮ) → α ≡ γ
  insᴮ-ext α γ p = extensionality α γ (Ins.InsHom≡ p)

  -- naturality in the probe, from the generic `intro-natural`
  introᴵ-nat : {x' x : B.0Cell} (k : B.1Cell x' x)
    (h : B.1Cell x a) (θ : Ins.Ins2 h)
    → (k B.⋆₁ introᴵ h θ) B.≅₂ introᴵ (k B.⋆₁ h) (Ins.reindθ k θ)
  introᴵ-nat k h θ = intro-natural k (h , θ)
