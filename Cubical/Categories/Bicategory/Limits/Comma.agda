{-# OPTIONS --lossy-unification #-}
{-
  Comma objects in a bicategory, derived from products and inserters:
  the comma object of `f : a → c`, `g : b → c` IS the inserter of
  `π₁ ⋆₁ f` and `π₂ ⋆₁ g` on a product `a × b`.  Its projections are
  the inserter projection composed with the product's, and its 2-cell
  is the inserter's, reassociated.
-}
module Cubical.Categories.Bicategory.Limits.Comma where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Isomorphism.More

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Transformation.Composition
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Inserter
open import Cubical.Categories.Bicategory.Universal.Base
open import Cubical.Categories.Bicategory.Limits.Product
open import Cubical.Categories.Bicategory.Limits.Inserter

private
  variable
    ℓ ℓ' ℓ'' : Level

open Functor
open isIso

module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  CommaPrestack : {a b c : B.0Cell} (P : BinProductᴮ B a b)
    (f : B.1Cell a c) (g : B.1Cell b c)
    → Prestack B (ℓ-max ℓ' ℓ'') ℓ''
  CommaPrestack P f g =
    InserterPrestack B (BinProductᴮNotation.π₁ᴮ P B.⋆₁ f)
                       (BinProductᴮNotation.π₂ᴮ P B.⋆₁ g)

  Commaᴮ : {a b c : B.0Cell} (P : BinProductᴮ B a b)
    (f : B.1Cell a c) (g : B.1Cell b c) → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  Commaᴮ P f g = Inserterᴮ B (BinProductᴮNotation.π₁ᴮ P B.⋆₁ f)
                             (BinProductᴮNotation.π₂ᴮ P B.⋆₁ g)

  -- Comma objects come for free from products and inserters: the
  -- prestacks are literally the same.
  hasCommaObjectsᴮ : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  hasCommaObjectsᴮ = {a b c : B.0Cell} (P : BinProductᴮ B a b)
    (f : B.1Cell a c) (g : B.1Cell b c) → Commaᴮ P f g

  commaFromInsertersᴮ : hasInsertersᴮ B → hasCommaObjectsᴮ
  commaFromInsertersᴮ ins P f g = ins _ _

module CommaᴮNotation {B : Bicategory ℓ ℓ' ℓ''}
  {a b c : Bicategory.0Cell B} {P : BinProductᴮ B a b}
  {f : Bicategory.1Cell B a c} {g : Bicategory.1Cell B b c}
  (K : Commaᴮ B P f g) where
  private
    module B = Bicategory B
  module Pr = BinProductᴮNotation P
  open InserterᴮNotation K public

  commaπ₁ᴮ : B.1Cell vertex a
  commaπ₁ᴮ = insᴮ B.⋆₁ Pr.π₁ᴮ

  commaπ₂ᴮ : B.1Cell vertex b
  commaπ₂ᴮ = insᴮ B.⋆₁ Pr.π₂ᴮ

  commaθᴮ : B.2Cell (commaπ₁ᴮ B.⋆₁ f) (commaπ₂ᴮ B.⋆₁ g)
  commaθᴮ = B.α⁺ insᴮ Pr.π₁ᴮ f B.⋆₂ insθᴮ B.⋆₂ B.α⁻ insᴮ Pr.π₂ᴮ g

  -- the 2-cell a probe `m` sees
  pullθᴮ : {x : B.0Cell} (m : B.1Cell x vertex)
    → B.2Cell ((m B.⋆₁ commaπ₁ᴮ) B.⋆₁ f) ((m B.⋆₁ commaπ₂ᴮ) B.⋆₁ g)
  pullθᴮ m =
    B.α⁺ m commaπ₁ᴮ f B.⋆₂ (m B.◁w commaθᴮ) B.⋆₂ B.α⁻ m commaπ₂ᴮ g

  private
    F = Pr.π₁ᴮ B.⋆₁ f
    G = Pr.π₂ᴮ B.⋆₁ g

    ▷⋆₁ : {x y z w : B.0Cell} {m m' : B.1Cell x y} (α : B.2Cell m m')
      (s : B.1Cell y z) (t : B.1Cell z w)
      → (α B.▷w s) B.▷w t
        ≡ B.α⁺ m s t B.⋆₂ (α B.▷w (s B.⋆₁ t)) B.⋆₂ B.α⁻ m' s t
    ▷⋆₁ {m' = m'} α s t =
        ⋆InvRMove (αI B m' s t) (α⁺natL B α s t)
      ∙ B.⋆₂Assoc _ _ _

  -- Reassociation isomorphisms at a probe 1-cell `m`, and the
  -- comparison of `pullθᴮ m` with the inserter 2-cell pulled back
  -- along `m`.  This is where the pentagon is used.
  private
    module _ {x : B.0Cell} (m : B.1Cell x vertex) where
      Ω₁iso : CatIso B.Hom[ x , c ]
        ((m B.⋆₁ commaπ₁ᴮ) B.⋆₁ f) ((m B.⋆₁ insᴮ) B.⋆₁ F)
      Ω₁iso = ⋆Iso (F-Iso {F = B.postcomp f} (invIso (αI B m insᴮ Pr.π₁ᴮ)))
                   (αI B (m B.⋆₁ insᴮ) Pr.π₁ᴮ f)

      Ω₁ : B.2Cell ((m B.⋆₁ commaπ₁ᴮ) B.⋆₁ f) ((m B.⋆₁ insᴮ) B.⋆₁ F)
      Ω₁ = Ω₁iso .fst

      Ω₂ : B.2Cell ((m B.⋆₁ commaπ₂ᴮ) B.⋆₁ g) ((m B.⋆₁ insᴮ) B.⋆₁ G)
      Ω₂ = (B.α⁻ m insᴮ Pr.π₂ᴮ B.▷w g) B.⋆₂ B.α⁺ (m B.⋆₁ insᴮ) Pr.π₂ᴮ g

      Zof₁ : {h : B.1Cell x Pr.vertex} {u : B.1Cell x a}
        (n : B.2Cell (m B.⋆₁ insᴮ) h) (w : B.2Cell (h B.⋆₁ Pr.π₁ᴮ) u)
        → B.2Cell ((m B.⋆₁ insᴮ) B.⋆₁ F) (u B.⋆₁ f)
      Zof₁ {h} n w = (n B.▷w F) B.⋆₂ B.α⁻ h Pr.π₁ᴮ f B.⋆₂ (w B.▷w f)

      Zof₂ : {h : B.1Cell x Pr.vertex} {v : B.1Cell x b}
        (n : B.2Cell (m B.⋆₁ insᴮ) h) (w : B.2Cell (h B.⋆₁ Pr.π₂ᴮ) v)
        → B.2Cell ((m B.⋆₁ insᴮ) B.⋆₁ G) (v B.⋆₁ g)
      Zof₂ {h} n w = (n B.▷w G) B.⋆₂ B.α⁻ h Pr.π₂ᴮ g B.⋆₂ (w B.▷w g)

      ψexp₁ : {h : B.1Cell x Pr.vertex} {u : B.1Cell x a}
        (n : B.2Cell (m B.⋆₁ insᴮ) h) (w : B.2Cell (h B.⋆₁ Pr.π₁ᴮ) u)
        → ((B.α⁻ m insᴮ Pr.π₁ᴮ B.⋆₂ (n B.▷w Pr.π₁ᴮ) B.⋆₂ w) B.▷w f)
          ≡ Ω₁ B.⋆₂ Zof₁ n w
      ψexp₁ n w =
          ▷3 B _ _ _ f
        ∙ B.⟨⟩⋆₂⟨ B.⟨ ▷⋆₁ n Pr.π₁ᴮ f ⟩⋆₂⟨⟩ ∙ aR3 B _ _ _ _ ⟩
        ∙ sym (B.⋆₂Assoc _ _ _)

      ψexp₂ : {h : B.1Cell x Pr.vertex} {v : B.1Cell x b}
        (n : B.2Cell (m B.⋆₁ insᴮ) h) (w : B.2Cell (h B.⋆₁ Pr.π₂ᴮ) v)
        → ((B.α⁻ m insᴮ Pr.π₂ᴮ B.⋆₂ (n B.▷w Pr.π₂ᴮ) B.⋆₂ w) B.▷w g)
          ≡ Ω₂ B.⋆₂ Zof₂ n w
      ψexp₂ n w =
          ▷3 B _ _ _ g
        ∙ B.⟨⟩⋆₂⟨ B.⟨ ▷⋆₁ n Pr.π₂ᴮ g ⟩⋆₂⟨⟩ ∙ aR3 B _ _ _ _ ⟩
        ∙ sym (B.⋆₂Assoc _ _ _)

      private
        A₁ = B.α⁺ m commaπ₁ᴮ f
        B₁ = m B.◁w B.α⁺ insᴮ Pr.π₁ᴮ f
        X  = m B.◁w insθᴮ
        Y  = B.α⁻ m insᴮ G
        E₂ = m B.◁w B.α⁻ insᴮ Pr.π₂ᴮ g
        D₂ = B.α⁻ m commaπ₂ᴮ g

        tail₂ : E₂ B.⋆₂ D₂ B.⋆₂ Ω₂ ≡ Y
        tail₂ =
            B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ sym (pentP4 B m insᴮ Pr.π₂ᴮ g) ⟩ ⟩
          ∙ B.⟨⟩⋆₂⟨ pushn B (αI B m commaπ₂ᴮ g .snd .sec) _ ∙ B.⋆₂IdL _ ⟩
          ∙ pushn B ( sym (◁wSeq B m _ _)
                    ∙ m B.◁⟨ αI B insᴮ Pr.π₂ᴮ g .snd .sec ⟩
                    ∙ B.◁wId m) Y
          ∙ B.⋆₂IdL _

      claimA : pullθᴮ m B.⋆₂ Ω₂ ≡ Ω₁ B.⋆₂ Ins.reindθ m insθᴮ
      claimA = lhsA ∙ sym rhsA
        where
        pull5 : pullθᴮ m ≡ A₁ B.⋆₂ B₁ B.⋆₂ X B.⋆₂ E₂ B.⋆₂ D₂
        pull5 = B.⟨⟩⋆₂⟨ B.⟨ ◁3 B m _ _ _ ⟩⋆₂⟨⟩ ∙ aR3 B B₁ X E₂ D₂ ⟩

        lhsA : pullθᴮ m B.⋆₂ Ω₂ ≡ A₁ B.⋆₂ B₁ B.⋆₂ X B.⋆₂ Y
        lhsA =
            B.⟨ pull5 ⟩⋆₂⟨⟩
          ∙ aR5 B A₁ B₁ X E₂ D₂ Ω₂
          ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ tail₂ ⟩ ⟩ ⟩

        rhsA : Ω₁ B.⋆₂ Ins.reindθ m insθᴮ ≡ A₁ B.⋆₂ B₁ B.⋆₂ X B.⋆₂ Y
        rhsA =
            B.⟨ sym (pentP4 B m insᴮ Pr.π₁ᴮ f) ⟩⋆₂⟨⟩
          ∙ aR3 B A₁ B₁ _ _
          ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨
              pushn B (αI B m insᴮ F .snd .sec) _ ∙ B.⋆₂IdL _ ⟩ ⟩

  module _ {x : B.0Cell} (u : B.1Cell x a) (v : B.1Cell x b)
    (φ : B.2Cell (u B.⋆₁ f) (v B.⋆₁ g)) where
    private
      h = Pr.pairᴮ u v
      b₁ = Pr.pairᴮβ₁ u v .fst
      b₂ = Pr.pairᴮβ₂ u v .fst

    commaθof : Ins.Ins2 h
    commaθof =
        B.α⁻ h Pr.π₁ᴮ f
      B.⋆₂ (b₁ B.▷w f)
      B.⋆₂ φ
      B.⋆₂ (Pr.pairᴮβ₂ u v .snd .inv B.▷w g)
      B.⋆₂ B.α⁺ h Pr.π₂ᴮ g

    commaIntroᴮ : B.1Cell x vertex
    commaIntroᴮ = introᴵ h commaθof

    commaIntroβ₁ : (commaIntroᴮ B.⋆₁ commaπ₁ᴮ) B.≅₂ u
    commaIntroβ₁ =
      ⋆Iso (invIso (αI B commaIntroᴮ insᴮ Pr.π₁ᴮ))
        (⋆Iso (F-Iso {F = B.postcomp Pr.π₁ᴮ} (introᴵβ h commaθof))
              (Pr.pairᴮβ₁ u v))

    commaIntroβ₂ : (commaIntroᴮ B.⋆₁ commaπ₂ᴮ) B.≅₂ v
    commaIntroβ₂ =
      ⋆Iso (invIso (αI B commaIntroᴮ insᴮ Pr.π₂ᴮ))
        (⋆Iso (F-Iso {F = B.postcomp Pr.π₂ᴮ} (introᴵβ h commaθof))
              (Pr.pairᴮβ₂ u v))

    private
      W₂iso : CatIso B.Hom[ x , c ] (h B.⋆₁ G) (v B.⋆₁ g)
      W₂iso = ⋆Iso (invIso (αI B h Pr.π₂ᴮ g))
                   (F-Iso {F = B.postcomp g} (Pr.pairᴮβ₂ u v))

      V₁ : B.2Cell (h B.⋆₁ F) (u B.⋆₁ f)
      V₁ = B.α⁻ h Pr.π₁ᴮ f B.⋆₂ (b₁ B.▷w f)

      -- `commaθof`, conjugated by the product's β-isos, is `φ`
      claimθ : commaθof B.⋆₂ W₂iso .fst ≡ V₁ B.⋆₂ φ
      claimθ =
          aR5 B _ _ _ _ _ _
        ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨
            pushn B (αI B h Pr.π₂ᴮ g .snd .ret) _ ∙ B.⋆₂IdL _ ⟩ ⟩ ⟩ ⟩
        ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨
              sym (▷wSeq B _ _ g)
            ∙ B.⟨ Pr.pairᴮβ₂ u v .snd .sec ⟩▷ g
            ∙ B.▷wId g ⟩ ⟩ ⟩
        ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ B.⋆₂IdR _ ⟩ ⟩
        ∙ sym (B.⋆₂Assoc _ _ _)

      toZ : {m : B.1Cell x vertex} (n : B.2Cell (m B.⋆₁ insᴮ) h)
        → Ins.InsCond (Ins.reindθ m insθᴮ) commaθof n
        → Ins.reindθ m insθᴮ B.⋆₂ Zof₂ m n b₂ ≡ Zof₁ m n b₁ B.⋆₂ φ
      toZ n cnd =
          sym (B.⋆₂Assoc _ _ _)
        ∙ B.⟨ sym cnd ⟩⋆₂⟨⟩
        ∙ B.⋆₂Assoc _ _ _
        ∙ B.⟨⟩⋆₂⟨ claimθ ⟩
        ∙ sym (B.⋆₂Assoc _ _ _)

      fromZ : {m : B.1Cell x vertex} (n : B.2Cell (m B.⋆₁ insᴮ) h)
        → Ins.reindθ m insθᴮ B.⋆₂ Zof₂ m n b₂ ≡ Zof₁ m n b₁ B.⋆₂ φ
        → Ins.InsCond (Ins.reindθ m insθᴮ) commaθof n
      fromZ n e = ⋆CancelR W₂iso
        (  B.⋆₂Assoc _ _ _
         ∙ B.⟨⟩⋆₂⟨ claimθ ⟩
         ∙ sym (B.⋆₂Assoc _ _ _)
         ∙ sym e
         ∙ sym (B.⋆₂Assoc _ _ _))

    -- the comma β-law for the 2-cell: the projections' β-isos carry
    -- `commaθᴮ` to `φ`
    commaIntroβθ :
        pullθᴮ commaIntroᴮ B.⋆₂ (commaIntroβ₂ .fst B.▷w g)
      ≡ (commaIntroβ₁ .fst B.▷w f) B.⋆₂ φ
    commaIntroβθ =
        B.⟨⟩⋆₂⟨ ψexp₂ commaIntroᴮ n b₂ ⟩
      ∙ sym (B.⋆₂Assoc _ _ _)
      ∙ B.⟨ claimA commaIntroᴮ ⟩⋆₂⟨⟩
      ∙ B.⋆₂Assoc _ _ _
      ∙ B.⟨⟩⋆₂⟨ toZ n (introᴵβ-cond h commaθof) ⟩
      ∙ sym (B.⋆₂Assoc _ _ _)
      ∙ B.⟨ sym (ψexp₁ commaIntroᴮ n b₁) ⟩⋆₂⟨⟩
      where n = introᴵβ h commaθof .fst

    -- uniqueness: a probe with compatible β-isos factors through
    -- `commaIntroᴮ`
    module _ {m : B.1Cell x vertex}
      (ψ₁ : (m B.⋆₁ commaπ₁ᴮ) B.≅₂ u) (ψ₂ : (m B.⋆₁ commaπ₂ᴮ) B.≅₂ v)
      (compat : pullθᴮ m B.⋆₂ (ψ₂ .fst B.▷w g)
              ≡ (ψ₁ .fst B.▷w f) B.⋆₂ φ) where
      private
        ψ₁' : ((m B.⋆₁ insᴮ) B.⋆₁ Pr.π₁ᴮ) B.≅₂ u
        ψ₁' = ⋆Iso (αI B m insᴮ Pr.π₁ᴮ) ψ₁

        ψ₂' : ((m B.⋆₁ insᴮ) B.⋆₁ Pr.π₂ᴮ) B.≅₂ v
        ψ₂' = ⋆Iso (αI B m insᴮ Pr.π₂ᴮ) ψ₂

        nI : (m B.⋆₁ insᴮ) B.≅₂ h
        nI = Pr.pairᴮη ψ₁' ψ₂'

        n = nI .fst

        ψ₁≡ : B.α⁻ m insᴮ Pr.π₁ᴮ B.⋆₂ (n B.▷w Pr.π₁ᴮ) B.⋆₂ b₁ ≡ ψ₁ .fst
        ψ₁≡ =
            B.⟨⟩⋆₂⟨ cong fst (Pr.pairᴮη-β₁ ψ₁' ψ₂') ⟩
          ∙ pushn B (αI B m insᴮ Pr.π₁ᴮ .snd .sec) _
          ∙ B.⋆₂IdL _

        ψ₂≡ : B.α⁻ m insᴮ Pr.π₂ᴮ B.⋆₂ (n B.▷w Pr.π₂ᴮ) B.⋆₂ b₂ ≡ ψ₂ .fst
        ψ₂≡ =
            B.⟨⟩⋆₂⟨ cong fst (Pr.pairᴮη-β₂ ψ₁' ψ₂') ⟩
          ∙ pushn B (αI B m insᴮ Pr.π₂ᴮ .snd .sec) _
          ∙ B.⋆₂IdL _

        zEq : Ins.reindθ m insθᴮ B.⋆₂ Zof₂ m n b₂ ≡ Zof₁ m n b₁ B.⋆₂ φ
        zEq = ⋆CancelL (Ω₁iso m)
          (  sym (B.⋆₂Assoc _ _ _)
           ∙ B.⟨ sym (claimA m) ⟩⋆₂⟨⟩
           ∙ B.⋆₂Assoc _ _ _
           ∙ B.⟨⟩⋆₂⟨ sym (ψexp₂ m n b₂) ∙ B.⟨ ψ₂≡ ⟩▷ g ⟩
           ∙ compat
           ∙ B.⟨ B.⟨ sym ψ₁≡ ⟩▷ f ∙ ψexp₁ m n b₁ ⟩⋆₂⟨⟩
           ∙ B.⋆₂Assoc _ _ _)

      commaᴮη : m B.≅₂ commaIntroᴮ
      commaᴮη = introᴵη nI (fromZ n zEq)

  commaᴮ-ext : {x : B.0Cell} {m m' : B.1Cell x vertex}
    (α γ : B.2Cell m m')
    → (α B.▷w commaπ₁ᴮ) ≡ (γ B.▷w commaπ₁ᴮ)
    → (α B.▷w commaπ₂ᴮ) ≡ (γ B.▷w commaπ₂ᴮ)
    → α ≡ γ
  commaᴮ-ext α γ p q =
    insᴮ-ext α γ
      (Pr.pairᴮ-ext (α B.▷w insᴮ) (γ B.▷w insᴮ) (whisk p) (whisk q))
    where
    whisk : {d : B.0Cell} {s : B.1Cell Pr.vertex d}
      → (α B.▷w (insᴮ B.⋆₁ s)) ≡ (γ B.▷w (insᴮ B.⋆₁ s))
      → ((α B.▷w insᴮ) B.▷w s) ≡ ((γ B.▷w insᴮ) B.▷w s)
    whisk {s = s} r =
        ▷⋆₁ α insᴮ s
      ∙ B.⟨⟩⋆₂⟨ B.⟨ r ⟩⋆₂⟨⟩ ⟩
      ∙ sym (▷⋆₁ γ insᴮ s)
