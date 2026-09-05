{-# OPTIONS --lossy-unification #-}
{- Horizontal composition of lax natural transformations and of
   modifications, assembled into the composition functor. -}
module Cubical.Categories.Bicategory.Transformation.Composition where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.Instances.BinProduct

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Properties.Coherence
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.Transformation.Properties

private
  variable
    ℓb ℓb' ℓb'' ℓc ℓc' ℓc'' : Level

open Functor
open LaxNatTrans
open Modification
open isIso

module _ {B : Bicategory ℓb ℓb' ℓb''} {C : Bicategory ℓc ℓc' ℓc''}
  {F G H : LaxFunctor B C} where
  private
    module B = Bicategory B
    module C = Bicategory C
    module F = LaxFunctor F
    module G = LaxFunctor G
    module H = LaxFunctor H

  module _ (σ : LaxNatTrans F G) (τ : LaxNatTrans G H) where
    private
      module σ = LaxNatTrans σ
      module τ = LaxNatTrans τ

      nh : {x y : B.0Cell} (f : B.1Cell x y)
        → C.2Cell (F.F-1cell f C.⋆₁ (σ.N-1cell y C.⋆₁ τ.N-1cell y))
                  ((σ.N-1cell x C.⋆₁ τ.N-1cell x) C.⋆₁ H.F-1cell f)
      nh {x} {y} f =
          C.α⁻ (F.F-1cell f) (σ.N-1cell y) (τ.N-1cell y)
        C.⋆₂ (σ.N-hom f C.▷w τ.N-1cell y)
        C.⋆₂ C.α⁺ (σ.N-1cell x) (G.F-1cell f) (τ.N-1cell y)
        C.⋆₂ (σ.N-1cell x C.◁w τ.N-hom f)
        C.⋆₂ C.α⁻ (σ.N-1cell x) (τ.N-1cell x) (H.F-1cell f)

      nnat : {x y : B.0Cell} {f g : B.1Cell x y} (θ : B.2Cell f g)
        →   (F.F-2cell θ C.▷w (σ.N-1cell y C.⋆₁ τ.N-1cell y)) C.⋆₂ nh g
          ≡ nh f C.⋆₂ ((σ.N-1cell x C.⋆₁ τ.N-1cell x) C.◁w H.F-2cell θ)
      nnat {x} {y} {f} {g} θ =
          pushr C (α⁻natL C (F.F-2cell θ) ay by) _
        ∙ C.⟨⟩⋆₂⟨ pushr C e2 _ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ pushr C e3 _ ⟩ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ pushr C e4 _ ⟩ ⟩ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ e5 ⟩ ⟩ ⟩ ⟩
        ∙ sym (aR5 C _ _ _ _ _ _)
        where
        ax = σ.N-1cell x
        ay = σ.N-1cell y
        bx = τ.N-1cell x
        by = τ.N-1cell y
        e2 = sym (▷wSeq C _ _ by)
           ∙ C.⟨ σ.N-natural θ ⟩▷ by
           ∙ ▷wSeq C _ _ by
        e3 = α⁺natM C ax (G.F-2cell θ) by
        e4 = sym (◁wSeq C ax _ _)
           ∙ ax C.◁⟨ τ.N-natural θ ⟩
           ∙ ◁wSeq C ax _ _
        e5 = α⁻natR C ax bx (H.F-2cell θ)

      nid : (x : B.0Cell)
        →   (F.F⁰ C.▷w (σ.N-1cell x C.⋆₁ τ.N-1cell x)) C.⋆₂ nh B.id₁
          ≡   C.λ⁺ (σ.N-1cell x C.⋆₁ τ.N-1cell x)
            C.⋆₂ C.ρ⁻ (σ.N-1cell x C.⋆₁ τ.N-1cell x)
            C.⋆₂ ((σ.N-1cell x C.⋆₁ τ.N-1cell x) C.◁w H.F⁰)
      nid x =
          pushr C (α⁻natL C F.F⁰ a b) _
        ∙ C.⟨⟩⋆₂⟨ pushn C e2 _ ∙ aR3 C _ _ _ _ ⟩
        ∙ pushn C (λ⋆₁ C a b) _
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ pushr C (α⁺natM C a G.F⁰ b) _ ⟩ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ pushn C e5 _ ∙ aR3 C _ _ _ _ ⟩ ⟩ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ pushn C (C.triangle _ _ _ a b) _ ⟩ ⟩
        ∙ C.⟨⟩⋆₂⟨ pushn C e7 _ ∙ C.⋆₂IdL _ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ α⁻natR C a b H.F⁰ ⟩ ⟩
        ∙ C.⟨⟩⋆₂⟨ pushn C (sym (ρ⁻⋆₁ C a b)) _ ⟩
        where
        a = σ.N-1cell x
        b = τ.N-1cell x
        e2 = sym (▷wSeq C _ _ b)
           ∙ C.⟨ σ.lax-id x ⟩▷ b
           ∙ ▷3 C _ _ _ b
        e5 = sym (◁wSeq C a _ _)
           ∙ a C.◁⟨ τ.lax-id x ⟩
           ∙ ◁3 C a _ _ _
        e7 = sym (▷wSeq C _ _ b)
           ∙ C.⟨ ρI C a .snd .sec ⟩▷ b
           ∙ C.▷wId b

      module _ {x y z : B.0Cell} (f : B.1Cell x y) (g : B.1Cell y z)
        where
        private
          Ff = F.F-1cell f
          Fg = F.F-1cell g
          Gf = G.F-1cell f
          Gg = G.F-1cell g
          Hf = H.F-1cell f
          Hg = H.F-1cell g
          ax = σ.N-1cell x
          ay = σ.N-1cell y
          az = σ.N-1cell z
          bx = τ.N-1cell x
          by = τ.N-1cell y
          bz = τ.N-1cell z
          Af = σ.N-hom f
          Ag = σ.N-hom g
          Bf = τ.N-hom f
          Bg = τ.N-hom g

          c0 = C.α⁻ Ff (ay C.⋆₁ Gg) bz
          c1 = C.α⁻ ax (Gf C.⋆₁ by) Hg

          Y12 = C.α⁺ Ff Fg az C.⋆₂ (Ff C.◁w Ag)
          Y   = C.α⁻ Ff ay Gg C.⋆₂ (Af C.▷w Gg) C.⋆₂ C.α⁺ ax Gf Gg
          Z   = C.α⁺ Gf Gg bz C.⋆₂ (Gf C.◁w Bg) C.⋆₂ C.α⁻ Gf by Hg
          Zm  = (Bf C.▷w Hg) C.⋆₂ C.α⁺ bx Hf Hg

          Ng12  = C.α⁻ Fg az bz C.⋆₂ (Ag C.▷w bz)
          Ng345 = C.α⁺ ay Gg bz C.⋆₂ (ay C.◁w Bg) C.⋆₂ C.α⁻ ay by Hg
          Nf123 = C.α⁻ Ff ay by C.⋆₂ (Af C.▷w by) C.⋆₂ C.α⁺ ax Gf by
          Nf45  = (ax C.◁w Bf) C.⋆₂ C.α⁻ ax bx Hf

          V1 = C.α⁻ (Ff C.⋆₁ Fg) az bz C.⋆₂ (Y12 C.▷w bz)
          V2 =   (Y C.▷w bz) C.⋆₂ C.α⁺ ax (Gf C.⋆₁ Gg) bz
               C.⋆₂ (ax C.◁w Z)
          V3 = (ax C.◁w Zm) C.⋆₂ C.α⁻ ax bx (Hf C.⋆₁ Hg)

          W1 = C.α⁺ Ff Fg (az C.⋆₁ bz) C.⋆₂ (Ff C.◁w Ng12)
          W2 =   (Ff C.◁w Ng345) C.⋆₂ C.α⁻ Ff (ay C.⋆₁ by) Hg
               C.⋆₂ (Nf123 C.▷w Hg)
          W3 = (Nf45 C.▷w Hg) C.⋆₂ C.α⁺ (ax C.⋆₁ bx) Hf Hg

          claimA : V1 ≡ W1 C.⋆₂ c0
          claimA =
              C.⟨⟩⋆₂⟨ ▷wSeq C _ _ bz ⟩
            ∙ pushn C (pentP3 C Ff Fg az bz) _
            ∙ aR3 C _ _ _ _
            ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ sym (α⁻natM C Ff Ag bz) ⟩ ⟩
            ∙ C.⟨⟩⋆₂⟨ sym (C.⋆₂Assoc _ _ _) ⟩
            ∙ C.⟨⟩⋆₂⟨ C.⟨ sym (◁wSeq C Ff _ _) ⟩⋆₂⟨⟩ ⟩
            ∙ sym (aR2 C _ _ _)

          claimB : V3 ≡ c1 C.⋆₂ W3
          claimB =
              C.⟨ ◁wSeq C ax _ _ ⟩⋆₂⟨⟩
            ∙ aR2 C _ _ _
            ∙ C.⟨⟩⋆₂⟨ ⋆InvLMove (αI C ax (bx C.⋆₁ Hf) Hg)
                        (pentP4 C ax bx Hf Hg) ⟩
            ∙ pushn C (α⁻natM C ax Bf Hg) _
            ∙ aR2 C _ _ _
            ∙ C.⟨⟩⋆₂⟨ sym (C.⋆₂Assoc _ _ _) ⟩
            ∙ C.⟨⟩⋆₂⟨ C.⟨ sym (▷wSeq C _ _ Hg) ⟩⋆₂⟨⟩ ⟩

          claimC : c0 C.⋆₂ V2 C.⋆₂ c1 ≡ W2
          claimC =
              C.⟨⟩⋆₂⟨ aR3 C _ _ _ _ ⟩
            ∙ C.⟨⟩⋆₂⟨ C.⟨ ▷3 C _ _ _ bz ⟩⋆₂⟨⟩ ∙ aR3 C _ _ _ _ ⟩
            ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
                C.⟨ ◁3 C ax _ _ _ ⟩⋆₂⟨⟩ ∙ aR3 C _ _ _ _ ⟩ ⟩ ⟩ ⟩ ⟩
            ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
                rep3 C (C.pentagon _ _ _ _ _ ax Gf Gg bz) _ ⟩ ⟩ ⟩
            ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ pushr C (α⁺natL C Af Gg bz) _ ⟩ ⟩
            ∙ rep3 C (pentP1 C Ff ay Gg bz) _
            ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
                pushr C (sym (α⁺natR C ax Gf Bg)) _ ⟩ ⟩ ⟩
            ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
                sym (pentP3 C ax Gf by Hg) ⟩ ⟩ ⟩ ⟩
            ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ pushr C (▷◁exch C Af Bg) _ ⟩ ⟩
            ∙ C.⟨⟩⋆₂⟨ pushr C (sym (α⁻natR C Ff ay Bg)) _ ⟩
            ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
                pushr C (α⁻natL C Af by Hg) _ ⟩ ⟩ ⟩
            ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
                pushn C (sym (pentP2 C Ff ay by Hg)) _
                ∙ aR3 C _ _ _ _ ⟩ ⟩
            ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
                sym (▷3 C _ _ _ Hg) ⟩ ⟩ ⟩ ⟩
            ∙ sym (aR3 C _ _ _ _)
            ∙ C.⟨ sym (◁3 C Ff _ _ _) ⟩⋆₂⟨⟩

          blkL :   (F.F² f g C.▷w (az C.⋆₁ bz)) C.⋆₂ nh (f B.⋆₁ g)
                 ≡ V1 C.⋆₂ V2 C.⋆₂ V3
                     C.⋆₂ ((ax C.⋆₁ bx) C.◁w H.F² f g)
          blkL =
              pushr C (α⁻natL C (F.F² f g) az bz) _
            ∙ C.⟨⟩⋆₂⟨ pushr C eU _ ⟩
            ∙ C.⟨⟩⋆₂⟨ C.⟨ splitU ⟩⋆₂⟨⟩ ∙ aR2 C _ _ _ ⟩
            ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
                pushr C (α⁺natM C ax (G.F² f g) bz) _ ⟩ ⟩ ⟩
            ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
                pushn C eV _ ∙ aR3 C _ _ _ _ ⟩ ⟩ ⟩ ⟩
            ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
                α⁻natR C ax bx (H.F² f g) ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
            ∙ sym ( aR2 C _ _ _
                  ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ aR3 C _ _ _ _ ⟩ ⟩
                  ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
                      aR2 C _ _ _ ⟩ ⟩ ⟩ ⟩ ⟩)
            where
            splitU = C.⟨ sym (aR2 C _ _ _) ⟩▷ bz ∙ ▷wSeq C Y12 Y bz
            eU = sym (▷wSeq C _ _ bz)
               ∙ C.⟨ σ.lax-seq f g ∙ sym (aR5 C _ _ _ _ _ _) ⟩▷ bz
               ∙ ▷wSeq C _ _ bz
            splitZ = sym (aR3 C _ _ _ _)
                   ∙ C.⟨⟩⋆₂⟨ sym (aR2 C _ _ _) ⟩
            eV = sym (◁wSeq C ax _ _)
               ∙ ax C.◁⟨ τ.lax-seq f g ∙ splitZ ⟩
               ∙ ◁3 C ax _ _ _

          blkR :   C.α⁺ Ff Fg (az C.⋆₁ bz)
                     C.⋆₂ (Ff C.◁w nh g)
                     C.⋆₂ C.α⁻ Ff (ay C.⋆₁ by) Hg
                     C.⋆₂ (nh f C.▷w Hg)
                     C.⋆₂ C.α⁺ (ax C.⋆₁ bx) Hf Hg
                     C.⋆₂ ((ax C.⋆₁ bx) C.◁w H.F² f g)
                 ≡ W1 C.⋆₂ W2 C.⋆₂ W3
                     C.⋆₂ ((ax C.⋆₁ bx) C.◁w H.F² f g)
          blkR =
              C.⟨⟩⋆₂⟨ C.⟨ ea ⟩⋆₂⟨⟩ ∙ aR2 C _ _ _ ⟩
            ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
                C.⟨ eb ⟩⋆₂⟨⟩ ∙ aR2 C _ _ _ ⟩ ⟩ ⟩ ⟩
            ∙ sym ( aR2 C _ _ _
                  ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ aR3 C _ _ _ _ ⟩ ⟩
                  ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
                      aR2 C _ _ _ ⟩ ⟩ ⟩ ⟩ ⟩)
            where
            ea = Ff C.◁⟨ sym (aR2 C _ _ _) ⟩ ∙ ◁wSeq C Ff Ng12 Ng345
            eb = C.⟨ sym (aR3 C _ _ _ _) ⟩▷ Hg ∙ ▷wSeq C Nf123 Nf45 Hg

          mid : V1 C.⋆₂ V2 C.⋆₂ V3
                  C.⋆₂ ((ax C.⋆₁ bx) C.◁w H.F² f g)
              ≡ W1 C.⋆₂ W2 C.⋆₂ W3
                  C.⋆₂ ((ax C.⋆₁ bx) C.◁w H.F² f g)
          mid =
              C.⟨ claimA ⟩⋆₂⟨⟩
            ∙ aR2 C _ _ _
            ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
                C.⟨ claimB ⟩⋆₂⟨⟩ ∙ aR2 C _ _ _ ⟩ ⟩ ⟩
            ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ sym (C.⋆₂Assoc _ _ _) ⟩
                    ∙ sym (C.⋆₂Assoc _ _ _)
                    ∙ C.⟨ claimC ⟩⋆₂⟨⟩ ⟩

        nseq :   (F.F² f g C.▷w (σ.N-1cell z C.⋆₁ τ.N-1cell z))
                   C.⋆₂ nh (f B.⋆₁ g)
               ≡   C.α⁺ (F.F-1cell f) (F.F-1cell g)
                     (σ.N-1cell z C.⋆₁ τ.N-1cell z)
                 C.⋆₂ (F.F-1cell f C.◁w nh g)
                 C.⋆₂ C.α⁻ (F.F-1cell f)
                       (σ.N-1cell y C.⋆₁ τ.N-1cell y) (H.F-1cell g)
                 C.⋆₂ (nh f C.▷w H.F-1cell g)
                 C.⋆₂ C.α⁺ (σ.N-1cell x C.⋆₁ τ.N-1cell x)
                       (H.F-1cell f) (H.F-1cell g)
                 C.⋆₂ ((σ.N-1cell x C.⋆₁ τ.N-1cell x) C.◁w H.F² f g)
        nseq = blkL ∙ mid ∙ sym blkR

    seqLaxNatTrans : LaxNatTrans F H
    seqLaxNatTrans .N-1cell x = σ.N-1cell x C.⋆₁ τ.N-1cell x
    seqLaxNatTrans .N-hom = nh
    seqLaxNatTrans .N-natural = nnat
    seqLaxNatTrans .lax-id = nid
    seqLaxNatTrans .lax-seq = nseq

  module _ {σ σ' : LaxNatTrans F G} {τ τ' : LaxNatTrans G H}
    (Γ : Modification σ σ') (Δ : Modification τ τ') where
    private
      module σ = LaxNatTrans σ
      module τ = LaxNatTrans τ
      module σ' = LaxNatTrans σ'
      module τ' = LaxNatTrans τ'

      mh : {x y : B.0Cell} (f : B.1Cell x y)
        →   (F.F-1cell f C.◁w (Γ .M-ob y C.⋆ₕ Δ .M-ob y))
              C.⋆₂ seqLaxNatTrans σ' τ' .N-hom f
          ≡   seqLaxNatTrans σ τ .N-hom f
              C.⋆₂ ((Γ .M-ob x C.⋆ₕ Δ .M-ob x) C.▷w H.F-1cell f)
      mh {x} {y} f =
          pushr C (α⁻nat C C.id₂ γ' δ') _
        ∙ C.⟨⟩⋆₂⟨ pushr C e2 _ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ pushr C (α⁺nat C γ C.id₂ δ') _ ⟩ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ pushr C e4 _ ⟩ ⟩ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
            α⁻nat C γ δ C.id₂ ⟩ ⟩ ⟩ ⟩
        ∙ sym (aR5 C _ _ _ _ _ _)
        where
        γ  = Γ .M-ob x
        δ  = Δ .M-ob x
        γ' = Γ .M-ob y
        δ' = Δ .M-ob y
        e2 = sym (C.⋆ₕSeq (F.F-1cell f C.◁w γ') (σ' .N-hom f) δ' C.id₂)
           ∙ C.⟨ sym (Γ .M-hom f) ⟩⋆ₕ⟨ C.⋆₂IdR δ' ⟩
           ∙ C.⟨⟩⋆ₕ⟨ sym (C.⋆₂IdL δ') ⟩
           ∙ C.⋆ₕSeq (σ .N-hom f) (γ C.▷w G.F-1cell f) C.id₂ δ'
        e4 = sym (C.⋆ₕSeq γ C.id₂
                    (G.F-1cell f C.◁w δ') (τ' .N-hom f))
           ∙ C.⟨ C.⋆₂IdR γ ⟩⋆ₕ⟨ sym (Δ .M-hom f) ⟩
           ∙ C.⟨ sym (C.⋆₂IdL γ) ⟩⋆ₕ⟨⟩
           ∙ C.⋆ₕSeq C.id₂ γ (τ .N-hom f) (δ C.▷w H.F-1cell f)

    seqMod⋆ : Modification (seqLaxNatTrans σ τ) (seqLaxNatTrans σ' τ')
    seqMod⋆ .M-ob x = Γ .M-ob x C.⋆ₕ Δ .M-ob x
    seqMod⋆ .M-hom f = sym (mh f)

  seqLaxNatTransF : Functor
    (LaxNatTransCat {F = F} {G = G} ×C LaxNatTransCat {F = G} {G = H})
    (LaxNatTransCat {F = F} {G = H})
  seqLaxNatTransF .F-ob (σ , τ) = seqLaxNatTrans σ τ
  seqLaxNatTransF .F-hom (Γ , Δ) = seqMod⋆ Γ Δ
  seqLaxNatTransF .F-id = makeModificationPath (λ x → C.⋆ₕId)
  seqLaxNatTransF .F-seq (Γ , Δ) (Γ' , Δ') =
    makeModificationPath (λ x → C.⋆ₕSeq _ _ _ _)
