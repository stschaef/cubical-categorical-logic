{-# OPTIONS --lossy-unification #-}
{-
  The comma glue `SET ↓ F` presented as a category displayed over the
  syntax: an object over `X` is a set with a map into `F X`, which is
  the fibre of the comma category of `Gluing.Bicategorical.Artin`.
  This is the presentation the free CCC's eliminator would consume to
  produce a section strictly over the identity.  Only the terminal
  object is built here; the displayed products and exponentials are
  not (see the report).
-}
module Gluing.Bicategorical.Section where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties

open Category
open Categoryᴰ
open Functor
open isIsoOver

module _ {ℓs ℓC ℓC' : Level} {C : Category ℓC ℓC'}
  (F : Functor C (SET ℓs)) where

  -- a glue object over `X` is a set with a map into `F X`; a glue
  -- morphism over `f` is a function commuting with `F f`
  Glᴰ : Categoryᴰ C (ℓ-suc ℓs) ℓs
  Glᴰ .ob[_] X = Σ[ A ∈ hSet ℓs ] (⟨ A ⟩ → ⟨ F ⟅ X ⟆ ⟩)
  Glᴰ .Hom[_][_,_] f (A , α) (B , β) =
    Σ[ h ∈ (⟨ A ⟩ → ⟨ B ⟩) ] ((a : ⟨ A ⟩) → (F ⟪ f ⟫) (α a) ≡ β (h a))
  Glᴰ .idᴰ {p = A , α} = (λ a → a) , λ a → funExt⁻ (F .F-id) (α a)
  Glᴰ ._⋆ᴰ_ {f = f} {g} {xᴰ = A , α} (h , p) (k , q) =
    (λ a → k (h a))
    , λ a → funExt⁻ (F .F-seq f g) (α a)
          ∙ cong (F ⟪ g ⟫) (p a) ∙ q (h a)
  Glᴰ .⋆IdLᴰ fᴰ = ΣPathP (refl , isProp→PathP
    (λ _ → isPropΠ λ _ → (F ⟅ _ ⟆) .snd _ _) _ _)
  Glᴰ .⋆IdRᴰ fᴰ = ΣPathP (refl , isProp→PathP
    (λ _ → isPropΠ λ _ → (F ⟅ _ ⟆) .snd _ _) _ _)
  Glᴰ .⋆Assocᴰ fᴰ gᴰ hᴰ = ΣPathP (refl , isProp→PathP
    (λ _ → isPropΠ λ _ → (F ⟅ _ ⟆) .snd _ _) _ _)
  Glᴰ .isSetHomᴰ {yᴰ = B , β} = isSetΣ (isSetΠ λ _ → B .snd)
    λ _ → isProp→isSet (isPropΠ λ _ → (F ⟅ _ ⟆) .snd _ _)

  private
    module GlF = Fibers Glᴰ

  -- displayed homs are a function plus a proposition, so a path over
  -- any base path is determined by the function
  glPathP : {X Y : C .ob} {f g : C [ X , Y ]} {p : f ≡ g}
    {xᴰ : Glᴰ .Categoryᴰ.ob[_] X} {yᴰ : Glᴰ .Categoryᴰ.ob[_] Y}
    {mᴰ : Glᴰ [ f ][ xᴰ , yᴰ ]} {nᴰ : Glᴰ [ g ][ xᴰ , yᴰ ]}
    → mᴰ .fst ≡ nᴰ .fst
    → PathP (λ i → Glᴰ [ p i ][ xᴰ , yᴰ ]) mᴰ nᴰ
  glPathP q = ΣPathP
    (q , isProp→PathP (λ _ → isPropΠ λ _ → (F ⟅ _ ⟆) .snd _ _) _ _)

  -- the terminal glue object is `(F 1 , id)`
  module _ (term : Terminal' C) where
    private module 𝟙C = TerminalNotation term

    glTermᴰ : Terminalᴰ Glᴰ term
    glTermᴰ .fst = (F ⟅ 𝟙C.𝟙 ⟆) , (λ x → x)
    glTermᴰ .snd .fst = tt
    glTermᴰ .snd .snd Z (A , α) .inv _ _ =
      (λ a → (F ⟪ 𝟙C.!t ⟫) (α a)) , λ a → refl
    glTermᴰ .snd .snd Z (A , α) .rightInv _ _ = refl
    glTermᴰ .snd .snd Z (A , α) .leftInv f fᴰ = ΣPathP
      ( funExt (λ a → cong (λ z → (F ⟪ z ⟫) (α a)) 𝟙C.𝟙extensionality
                    ∙ fᴰ .snd a)
      , isProp→PathP (λ _ → isPropΠ λ _ → (F ⟅ _ ⟆) .snd _ _) _ _)

