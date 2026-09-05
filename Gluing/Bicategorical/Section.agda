{-# OPTIONS --lossy-unification #-}
{-
  The comma glue `SET ↓ F` presented as a category displayed over the
  syntax: an object over `X` is a set with a map into `F X`, which is
  the fibre of the comma category of `Gluing.Bicategorical.Artin`.
  This is the presentation the free cartesian category's eliminator
  consumes to produce a section strictly over the identity: the
  displayed terminal object and binary products here are exactly the
  classical Artin ones, with the base component forded away.
-}
module Gluing.Bicategorical.Section where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Equiv.Dependent.More
open import Cubical.Foundations.More
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties

open import Gluing.Bicategorical.Artin

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
    HomF : {X Y : C .ob} (xᴰ : Glᴰ .ob[_] X) (yᴰ : Glᴰ .ob[_] Y)
      → C [ X , Y ] → Type ℓs
    HomF xᴰ yᴰ h = Glᴰ [ h ][ xᴰ , yᴰ ]

  -- reindexing along a base path leaves the function component alone
  reindFst : {X Y : C .ob} {xᴰ : Glᴰ .ob[_] X} {yᴰ : Glᴰ .ob[_] Y}
    {f g : C [ X , Y ]} {e : f ≡ g} {mᴰ : Glᴰ [ f ][ xᴰ , yᴰ ]}
    → depReasoning.reind (HomF xᴰ yᴰ) e mᴰ .fst ≡ mᴰ .fst
  reindFst {xᴰ = xᴰ} {yᴰ} {e = e} {mᴰ} = sym (cong (λ z → z .snd .fst)
    (depReasoning.reind-filler (HomF xᴰ yᴰ) {p = mᴰ} e))

  -- a displayed hom over a fixed base morphism is determined by its
  -- function component
  -- a displayed hom over a fixed base morphism is determined by its
  -- function component
  glHom≡ : {X Y : C .ob} {f : C [ X , Y ]}
    {xᴰ : Glᴰ .ob[_] X} {yᴰ : Glᴰ .ob[_] Y}
    {mᴰ nᴰ : Glᴰ [ f ][ xᴰ , yᴰ ]} → mᴰ .fst ≡ nᴰ .fst → mᴰ ≡ nᴰ
  glHom≡ = Σ≡Prop (λ _ → isPropΠ λ _ → (F ⟅ _ ⟆) .snd _ _)

  -- the second component of a displayed hom is a proposition
  sqPathP : {X Y : C .ob} {A : hSet ℓs} {B : hSet ℓs}
    {f : I → C [ X , Y ]} {α : ⟨ A ⟩ → ⟨ F ⟅ X ⟆ ⟩}
    {β : ⟨ B ⟩ → ⟨ F ⟅ Y ⟆ ⟩} {h : I → ⟨ A ⟩ → ⟨ B ⟩}
    {c0 : (a : ⟨ A ⟩) → (F ⟪ f i0 ⟫) (α a) ≡ β (h i0 a)}
    {c1 : (a : ⟨ A ⟩) → (F ⟪ f i1 ⟫) (α a) ≡ β (h i1 a)}
    → PathP (λ i → (a : ⟨ A ⟩) → (F ⟪ f i ⟫) (α a) ≡ β (h i a)) c0 c1
  sqPathP = isProp→PathP (λ _ → isPropΠ λ _ → (F ⟅ _ ⟆) .snd _ _) _ _

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


  -- the classical Artin product, forded over the syntax; `Fp` is the
  -- product-preservation hypothesis
  module _ (bpC : BinProducts C)
    (Fp : preservesProvidedBinProducts F bpC) where
    private
      module ×S = BinProductsNotation bpC

      prD = pr F bpC Fp
      prβ₁D = prβ₁ F bpC Fp
      prβ₂D = prβ₂ F bpC Fp
      prExtD = prExt F bpC Fp

    glBpᴰ : BinProductsᴰ Glᴰ bpC
    glBpᴰ {X} {Y} (A , α) (B , β) .fst =
      ((⟨ A ⟩ × ⟨ B ⟩) , isSet× (A .snd) (B .snd))
      , λ p → prD X Y (α (p .fst)) (β (p .snd))
    glBpᴰ {X} {Y} (A , α) (B , β) .snd .fst =
      ((λ p → p .fst) , λ p → prβ₁D X Y (α (p .fst)) (β (p .snd)))
      , ((λ p → p .snd) , λ p → prβ₂D X Y (α (p .fst)) (β (p .snd)))
    glBpᴰ {X} {Y} (A , α) (B , β) .snd .snd Z (E , δ) =
      fiberwiseIsoOver→IsoOver _
        (λ a → (λ (fᴰ , gᴰ) →
                  (λ e → fᴰ .fst e , gᴰ .fst e)
                  , λ e → prExtD X Y
                      ( funExt⁻ (sym (F .F-seq a ×S.π₁)) (δ e)
                      ∙ fᴰ .snd e
                      ∙ sym (prβ₁D X Y _ _))
                      ( funExt⁻ (sym (F .F-seq a ×S.π₂)) (δ e)
                      ∙ gᴰ .snd e
                      ∙ sym (prβ₂D X Y _ _)))
              , (λ _ → ≡-×
                  (Σ≡Prop (λ _ → isPropΠ λ _ → (F ⟅ _ ⟆) .snd _ _)
                    (reindFst {xᴰ = E , δ} {yᴰ = A , α}))
                  (Σ≡Prop (λ _ → isPropΠ λ _ → (F ⟅ _ ⟆) .snd _ _)
                    (reindFst {xᴰ = E , δ} {yᴰ = B , β})))
              , (λ _ → Σ≡Prop (λ _ → isPropΠ λ _ → (F ⟅ _ ⟆) .snd _ _)
                  (funExt λ e → ΣPathP
                  ( funExt⁻ (reindFst {xᴰ = E , δ} {yᴰ = A , α}) e
                  , funExt⁻ (reindFst {xᴰ = E , δ} {yᴰ = B , β}) e))))
        (C .isSetHom) (isSet× (C .isSetHom) (C .isSetHom))

