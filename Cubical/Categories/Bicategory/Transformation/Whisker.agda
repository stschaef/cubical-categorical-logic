{-# OPTIONS --lossy-unification #-}
{-
  Whiskering of a lax natural transformation, and of a modification, by
  a functor.  Right whiskering works for a lax functor; left whiskering
  needs a pseudofunctor, since the component 2-cell must come back out
  along the inverse of the composition constraint.  Each gives a
  functor between hom-categories of lax functors.
-}
module Cubical.Categories.Bicategory.Transformation.Whisker where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Isomorphism.More

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Properties.Coherence
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Functor.Composition
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.Transformation.Properties

private
  variable
    ℓa ℓa' ℓa'' ℓb ℓb' ℓb'' ℓc ℓc' ℓc'' : Level

open Functor
open LaxFunctor
open LaxNatTrans
open Modification
open isIso

module _ {A : Bicategory ℓa ℓa' ℓa''}
         {B : Bicategory ℓb ℓb' ℓb''}
         {C : Bicategory ℓc ℓc' ℓc''}
         {F G : LaxFunctor B C}
         (K : LaxFunctor A B) where
  private
    module A = Bicategory A
    module B = Bicategory B
    module C = Bicategory C
    module F = LaxFunctor F
    module G = LaxFunctor G
    module K = LaxFunctor K

  module _ (σ : LaxNatTrans F G) where
    private
      module σ = LaxNatTrans σ

      n : (x : A.ob) → C.1Cell (F.F-ob (K.F-ob x)) (G.F-ob (K.F-ob x))
      n x = σ.N-1cell (K.F-ob x)

      nh : ∀ {x y} (f : A.1Cell x y)
        → C.2Cell (F.F-1cell (K.F-1cell f) C.⋆₁ n y)
                  (n x C.⋆₁ G.F-1cell (K.F-1cell f))
      nh f = σ.N-hom (K.F-1cell f)

      wnat : ∀ {x y}{f g : A.1Cell x y} (θ : A.2Cell f g)
        →   (F.F-2cell (K.F-2cell θ) C.▷w n y) C.⋆₂ nh g
          ≡ nh f C.⋆₂ (n x C.◁w G.F-2cell (K.F-2cell θ))
      wnat θ = σ.N-natural (K.F-2cell θ)

      wid : (x : A.ob)
        →   ((F.F⁰ C.⋆₂ F.F-2cell K.F⁰) C.▷w n x) C.⋆₂ nh A.id₁
          ≡   C.λ⁺ (n x) C.⋆₂ C.ρ⁻ (n x)
            C.⋆₂ (n x C.◁w (G.F⁰ C.⋆₂ G.F-2cell K.F⁰))
      wid x =
          C.⟨ ▷wSeq C F.F⁰ (F.F-2cell K.F⁰) (n x) ⟩⋆₂⟨⟩
        ∙ C.⋆₂Assoc _ _ _
        ∙ C.⟨⟩⋆₂⟨ σ.N-natural K.F⁰ ⟩
        ∙ sym (C.⋆₂Assoc _ _ _)
        ∙ C.⟨ σ.lax-id (K.F-ob x) ⟩⋆₂⟨⟩
        ∙ C.⋆₂Assoc _ _ _
        ∙ C.⟨⟩⋆₂⟨ C.⋆₂Assoc _ _ _ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ sym (◁wSeq C (n x) G.F⁰ (G.F-2cell K.F⁰)) ⟩ ⟩

      wseq : ∀ {x y z} (f : A.1Cell x y) (g : A.1Cell y z)
        →   ((F.F² (K.F-1cell f) (K.F-1cell g) C.⋆₂ F.F-2cell (K.F² f g))
               C.▷w n z)
            C.⋆₂ nh (f A.⋆₁ g)
          ≡   C.α⁺ (F.F-1cell (K.F-1cell f)) (F.F-1cell (K.F-1cell g)) (n z)
            C.⋆₂ (F.F-1cell (K.F-1cell f) C.◁w nh g)
            C.⋆₂ C.α⁻ (F.F-1cell (K.F-1cell f)) (n y)
                      (G.F-1cell (K.F-1cell g))
            C.⋆₂ (nh f C.▷w G.F-1cell (K.F-1cell g))
            C.⋆₂ C.α⁺ (n x) (G.F-1cell (K.F-1cell f))
                      (G.F-1cell (K.F-1cell g))
            C.⋆₂ (n x C.◁w (G.F² (K.F-1cell f) (K.F-1cell g)
                              C.⋆₂ G.F-2cell (K.F² f g)))
      wseq f g =
          C.⟨ ▷wSeq C (F.F² (K.F-1cell f) (K.F-1cell g))
                      (F.F-2cell (K.F² f g)) (n _) ⟩⋆₂⟨⟩
        ∙ C.⋆₂Assoc _ _ _
        ∙ C.⟨⟩⋆₂⟨ σ.N-natural (K.F² f g) ⟩
        ∙ sym (C.⋆₂Assoc _ _ _)
        ∙ C.⟨ σ.lax-seq (K.F-1cell f) (K.F-1cell g) ⟩⋆₂⟨⟩
        ∙ C.⋆₂Assoc _ _ _
        ∙ C.⟨⟩⋆₂⟨ C.⋆₂Assoc _ _ _ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⋆₂Assoc _ _ _ ⟩ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⋆₂Assoc _ _ _ ⟩ ⟩ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⋆₂Assoc _ _ _ ⟩ ⟩ ⟩ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨
            sym (◁wSeq C (n _) (G.F² (K.F-1cell f) (K.F-1cell g))
                              (G.F-2cell (K.F² f g))) ⟩ ⟩ ⟩ ⟩ ⟩

    whiskerR : LaxNatTrans (F ∘Lax K) (G ∘Lax K)
    whiskerR .N-1cell = n
    whiskerR .N-hom = nh
    whiskerR .N-natural = wnat
    whiskerR .lax-id = wid
    whiskerR .lax-seq = wseq

  whiskerRMod : {σ τ : LaxNatTrans F G}
    → Modification σ τ → Modification (whiskerR σ) (whiskerR τ)
  whiskerRMod Γ .M-ob x = Γ .M-ob (K.F-ob x)
  whiskerRMod Γ .M-hom f = Γ .M-hom (K.F-1cell f)

  whiskerRF : Functor (LaxNatTransCat {F = F} {G = G})
                      (LaxNatTransCat {F = F ∘Lax K} {G = G ∘Lax K})
  whiskerRF .F-ob = whiskerR
  whiskerRF .F-hom = whiskerRMod
  whiskerRF .F-id = makeModificationPath λ x → refl
  whiskerRF .F-seq Γ Δ = makeModificationPath λ x → refl

-- Naturality of a lax functor's composition constraint in each slot.
module _ {B : Bicategory ℓb ℓb' ℓb''} {C : Bicategory ℓc ℓc' ℓc''}
         (K : LaxFunctor B C) where
  private
    module B = Bicategory B
    module C = Bicategory C
    module K = LaxFunctor K

  F²nat▷ : ∀ {x y z}{a a' : B.1Cell x y} (α : B.2Cell a a')
    (b : B.1Cell y z)
    →   (K.F-2cell α C.▷w K.F-1cell b) C.⋆₂ K.F² a' b
      ≡ K.F² a b C.⋆₂ K.F-2cell (α B.▷w b)
  F²nat▷ α b =
      C.⟨ C.⟨⟩⋆ₕ⟨ sym (K.F-Hom .F-id) ⟩ ⟩⋆₂⟨⟩
    ∙ NatTrans.N-hom K.F-seq (α , B.id₂)

  F²nat◁ : ∀ {x y z} (a : B.1Cell x y){b b' : B.1Cell y z}
    (β : B.2Cell b b')
    →   (K.F-1cell a C.◁w K.F-2cell β) C.⋆₂ K.F² a b'
      ≡ K.F² a b C.⋆₂ K.F-2cell (a B.◁w β)
  F²nat◁ a β =
      C.⟨ C.⟨ sym (K.F-Hom .F-id) ⟩⋆ₕ⟨⟩ ⟩⋆₂⟨⟩
    ∙ NatTrans.N-hom K.F-seq (B.id₂ , β)

-- Left whiskering by a pseudofunctor.  A lax `K` will not do: the
-- component 2-cell must travel back out of `K` along `K.F²`.
module _ {A : Bicategory ℓa ℓa' ℓa''}
         {B : Bicategory ℓb ℓb' ℓb''}
         {C : Bicategory ℓc ℓc' ℓc''}
         {F G : LaxFunctor A B}
         (K : Pseudofunctor B C) where
  private
    module A = Bicategory A
    module B = Bicategory B
    module C = Bicategory C
    module F = LaxFunctor F
    module G = LaxFunctor G
    module K = Pseudofunctor K

    Kl : LaxFunctor B C
    Kl = K.laxFunctor

    κ²I : ∀ {x y z} (a : B.1Cell x y) (b : B.1Cell y z)
      → CatIso C.Hom[ K.F-ob x , K.F-ob z ]
               (K.F-1cell a C.⋆₁ K.F-1cell b) (K.F-1cell (a B.⋆₁ b))
    κ²I a b = K.F² a b , K.F-seq-isIso (a , b)

    κ²⁻ : ∀ {x y z} (a : B.1Cell x y) (b : B.1Cell y z)
      → C.2Cell (K.F-1cell (a B.⋆₁ b)) (K.F-1cell a C.⋆₁ K.F-1cell b)
    κ²⁻ a b = κ²I a b .snd .inv

    aR6 : {x y : C.0Cell}{f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ : C.1Cell x y}
      (c₀ : C.2Cell f₀ f₁) (c₁ : C.2Cell f₁ f₂) (c₂ : C.2Cell f₂ f₃)
      (c₃ : C.2Cell f₃ f₄) (c₄ : C.2Cell f₄ f₅) (c₅ : C.2Cell f₅ f₆)
      (t : C.2Cell f₆ f₇)
      →   (c₀ C.⋆₂ c₁ C.⋆₂ c₂ C.⋆₂ c₃ C.⋆₂ c₄ C.⋆₂ c₅) C.⋆₂ t
        ≡ c₀ C.⋆₂ c₁ C.⋆₂ c₂ C.⋆₂ c₃ C.⋆₂ c₄ C.⋆₂ c₅ C.⋆₂ t
    aR6 c₀ c₁ c₂ c₃ c₄ c₅ t =
      C.⋆₂Assoc _ _ _ ∙ C.⟨⟩⋆₂⟨ aR5 C c₁ c₂ c₃ c₄ c₅ t ⟩

  module _ (σ : LaxNatTrans F G) where
    private
      module σ = LaxNatTrans σ

      n : (x : A.ob) → C.1Cell (K.F-ob (F.F-ob x)) (K.F-ob (G.F-ob x))
      n x = K.F-1cell (σ.N-1cell x)

      nh : ∀ {x y} (f : A.1Cell x y)
        → C.2Cell (K.F-1cell (F.F-1cell f) C.⋆₁ n y)
                  (n x C.⋆₁ K.F-1cell (G.F-1cell f))
      nh {x} {y} f =
          K.F² (F.F-1cell f) (σ.N-1cell y)
        C.⋆₂ K.F-2cell (σ.N-hom f)
        C.⋆₂ κ²⁻ (σ.N-1cell x) (G.F-1cell f)

      wnat : ∀ {x y}{f g : A.1Cell x y} (θ : A.2Cell f g)
        →   (K.F-2cell (F.F-2cell θ) C.▷w n y) C.⋆₂ nh g
          ≡ nh f C.⋆₂ (n x C.◁w K.F-2cell (G.F-2cell θ))
      wnat {x} {y} {f} {g} θ =
          pushr C (F²nat▷ Kl (F.F-2cell θ) (σ.N-1cell y)) _
        ∙ C.⟨⟩⋆₂⟨ pushr C mergeK _ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ flipK ⟩ ⟩
        ∙ sym (aR3 C _ _ _ _)
        where
        mergeK :
            K.F-2cell (F.F-2cell θ B.▷w σ.N-1cell y)
              C.⋆₂ K.F-2cell (σ.N-hom g)
          ≡ K.F-2cell (σ.N-hom f)
              C.⋆₂ K.F-2cell (σ.N-1cell x B.◁w G.F-2cell θ)
        mergeK =
            sym (K.F-Hom .F-seq _ _)
          ∙ cong K.F-2cell (σ.N-natural θ)
          ∙ K.F-Hom .F-seq _ _

        flipK :
            K.F-2cell (σ.N-1cell x B.◁w G.F-2cell θ)
              C.⋆₂ κ²⁻ (σ.N-1cell x) (G.F-1cell g)
          ≡ κ²⁻ (σ.N-1cell x) (G.F-1cell f)
              C.⋆₂ (n x C.◁w K.F-2cell (G.F-2cell θ))
        flipK =
          ⋆InvsFlipSq (κ²I (σ.N-1cell x) (G.F-1cell f))
                      (κ²I (σ.N-1cell x) (G.F-1cell g))
                      (sym (F²nat◁ Kl (σ.N-1cell x) (G.F-2cell θ)))

      wid : (x : A.ob)
        →   ((K.F⁰ C.⋆₂ K.F-2cell F.F⁰) C.▷w n x) C.⋆₂ nh A.id₁
          ≡   C.λ⁺ (n x) C.⋆₂ C.ρ⁻ (n x)
            C.⋆₂ (n x C.◁w (K.F⁰ C.⋆₂ K.F-2cell G.F⁰))
      wid x =
          C.⟨ ▷wSeq C K.F⁰ (K.F-2cell F.F⁰) (n x) ⟩⋆₂⟨⟩
        ∙ C.⋆₂Assoc _ _ _
        ∙ C.⟨⟩⋆₂⟨ pushr C (F²nat▷ Kl F.F⁰ (σ.N-1cell x)) _ ⟩
        ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ pushn C mergeU _ ∙ aR3 C _ _ _ _ ⟩ ⟩
        ∙ sym (aR3 C _ _ _ _)
        ∙ C.⟨ K.lax-λ _ _ (σ.N-1cell x) ⟩⋆₂⟨⟩
        ∙ C.⟨⟩⋆₂⟨ tail ⟩
        where
        mergeU :
            K.F-2cell (F.F⁰ B.▷w σ.N-1cell x)
              C.⋆₂ K.F-2cell (σ.N-hom A.id₁)
          ≡   K.F-2cell (B.λ⁺ (σ.N-1cell x))
            C.⋆₂ K.F-2cell (B.ρ⁻ (σ.N-1cell x))
            C.⋆₂ K.F-2cell (σ.N-1cell x B.◁w G.F⁰)
        mergeU =
            sym (K.F-Hom .F-seq _ _)
          ∙ cong K.F-2cell (σ.lax-id x)
          ∙ K.F-Hom .F-seq _ _
          ∙ C.⟨⟩⋆₂⟨ K.F-Hom .F-seq _ _ ⟩

        KρI : CatIso C.Hom[ K.F-ob (F.F-ob x) , K.F-ob (G.F-ob x) ]
                (K.F-1cell (σ.N-1cell x B.⋆₁ B.id₁)) (n x)
        KρI = K.F-2cell (B.ρ⁺ (σ.N-1cell x))
            , F-PresIsIso {F = K.F-Hom} (ρI B (σ.N-1cell x) .snd)

        rhoU :
            K.F-2cell (B.ρ⁻ (σ.N-1cell x)) C.⋆₂ κ²⁻ (σ.N-1cell x) B.id₁
          ≡ C.ρ⁻ (n x) C.⋆₂ (n x C.◁w K.F⁰)
        rhoU =
          ⋆InvsFlipSq (ρI C (n x)) (κ²I (σ.N-1cell x) B.id₁)
            (sym (⋆InvRMove KρI
              (C.⋆₂Assoc _ _ _ ∙ K.lax-ρ _ _ (σ.N-1cell x))))

        flipU :
            K.F-2cell (σ.N-1cell x B.◁w G.F⁰)
              C.⋆₂ κ²⁻ (σ.N-1cell x) (G.F-1cell A.id₁)
          ≡ κ²⁻ (σ.N-1cell x) B.id₁ C.⋆₂ (n x C.◁w K.F-2cell G.F⁰)
        flipU =
          ⋆InvsFlipSq (κ²I (σ.N-1cell x) B.id₁)
                      (κ²I (σ.N-1cell x) (G.F-1cell A.id₁))
                      (sym (F²nat◁ Kl (σ.N-1cell x) G.F⁰))

        tail :
            K.F-2cell (B.ρ⁻ (σ.N-1cell x))
              C.⋆₂ K.F-2cell (σ.N-1cell x B.◁w G.F⁰)
              C.⋆₂ κ²⁻ (σ.N-1cell x) (G.F-1cell A.id₁)
          ≡ C.ρ⁻ (n x) C.⋆₂ (n x C.◁w (K.F⁰ C.⋆₂ K.F-2cell G.F⁰))
        tail =
            C.⟨⟩⋆₂⟨ flipU ⟩
          ∙ sym (C.⋆₂Assoc _ _ _)
          ∙ C.⟨ rhoU ⟩⋆₂⟨⟩
          ∙ C.⋆₂Assoc _ _ _
          ∙ C.⟨⟩⋆₂⟨ sym (◁wSeq C (n x) K.F⁰ (K.F-2cell G.F⁰)) ⟩

      module WS {x y z : A.ob} (f : A.1Cell x y) (g : A.1Cell y z) where
        private
          Ff = F.F-1cell f
          Fg = F.F-1cell g
          Gf = G.F-1cell f
          Gg = G.F-1cell g
          sx = σ.N-1cell x
          sy = σ.N-1cell y
          sz = σ.N-1cell z
          p  = K.F-1cell Gf
          q  = K.F-1cell Gg

        -- The three factors that reassemble `G`'s laxity cell.
        lemLast :
            K.F² sx (Gf B.⋆₁ Gg)
              C.⋆₂ K.F-2cell (sx B.◁w G.F² f g)
              C.⋆₂ κ²⁻ sx (G.F-1cell (f A.⋆₁ g))
          ≡ (n x C.◁w K.F-2cell (G.F² f g))
        lemLast =
            sym (C.⋆₂Assoc _ _ _)
          ∙ C.⟨ sym (F²nat◁ Kl sx (G.F² f g)) ⟩⋆₂⟨⟩
          ∙ C.⋆₂Assoc _ _ _
          ∙ C.⟨⟩⋆₂⟨ κ²I sx (G.F-1cell (f A.⋆₁ g)) .snd .ret ⟩
          ∙ C.⋆₂IdR _

        lemEnd :
            K.F² (sx B.⋆₁ Gf) Gg C.⋆₂ K.F-2cell (B.α⁺ sx Gf Gg)
          ≡   (κ²⁻ sx Gf C.▷w q) C.⋆₂ C.α⁺ (n x) p q
            C.⋆₂ (n x C.◁w K.F² Gf Gg) C.⋆₂ K.F² sx (Gf B.⋆₁ Gg)
        lemEnd =
          ⋆InvLMove (K.F² sx Gf C.▷w q , ▷wIsIso C q (K.F-seq-isIso (sx , Gf)))
            (K.lax-α _ _ _ _ sx Gf Gg)

        backLem :
            K.F² (Ff B.⋆₁ sy) Gg
              C.⋆₂ K.F-2cell (σ.N-hom f B.▷w Gg)
              C.⋆₂ K.F-2cell (B.α⁺ sx Gf Gg)
              C.⋆₂ K.F-2cell (sx B.◁w G.F² f g)
              C.⋆₂ κ²⁻ sx (G.F-1cell (f A.⋆₁ g))
          ≡   (K.F-2cell (σ.N-hom f) C.▷w q) C.⋆₂ (κ²⁻ sx Gf C.▷w q)
            C.⋆₂ C.α⁺ (n x) p q C.⋆₂ (n x C.◁w K.F² Gf Gg)
            C.⋆₂ (n x C.◁w K.F-2cell (G.F² f g))
        backLem =
            pushr C (sym (F²nat▷ Kl (σ.N-hom f) Gg)) _
          ∙ C.⟨⟩⋆₂⟨ pushn C lemEnd _ ∙ aR4 C _ _ _ _ _ ⟩
          ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ lemLast ⟩ ⟩ ⟩ ⟩

        lemMid :
            K.F² Ff (sy B.⋆₁ Gg) C.⋆₂ K.F-2cell (B.α⁻ Ff sy Gg)
          ≡   (K.F-1cell Ff C.◁w κ²⁻ sy Gg)
            C.⋆₂ C.α⁻ (K.F-1cell Ff) (n y) q
            C.⋆₂ (K.F² Ff sy C.▷w q)
            C.⋆₂ K.F² (Ff B.⋆₁ sy) Gg
        lemMid =
          ⋆InvLMove (K.F-1cell Ff C.◁w K.F² sy Gg ,
                     ◁wIsIso C (K.F-1cell Ff) (K.F-seq-isIso (sy , Gg)))
            prem
          where
          KαI : CatIso C.Hom[ K.F-ob (F.F-ob x) , K.F-ob (G.F-ob z) ]
                  (K.F-1cell ((Ff B.⋆₁ sy) B.⋆₁ Gg))
                  (K.F-1cell (Ff B.⋆₁ (sy B.⋆₁ Gg)))
          KαI = K.F-2cell (B.α⁺ Ff sy Gg)
              , F-PresIsIso {F = K.F-Hom} (αI B Ff sy Gg .snd)

          prem :
              (K.F-1cell Ff C.◁w K.F² sy Gg)
                C.⋆₂ K.F² Ff (sy B.⋆₁ Gg)
                C.⋆₂ K.F-2cell (B.α⁻ Ff sy Gg)
            ≡   C.α⁻ (K.F-1cell Ff) (n y) q
              C.⋆₂ (K.F² Ff sy C.▷w q) C.⋆₂ K.F² (Ff B.⋆₁ sy) Gg
          premα :
              C.α⁺ (K.F-1cell Ff) (n y) q
                C.⋆₂ ((K.F-1cell Ff C.◁w K.F² sy Gg)
                        C.⋆₂ K.F² Ff (sy B.⋆₁ Gg))
            ≡   ((K.F² Ff sy C.▷w q) C.⋆₂ K.F² (Ff B.⋆₁ sy) Gg)
                C.⋆₂ K.F-2cell (B.α⁺ Ff sy Gg)
          premα =
            sym (K.lax-α _ _ _ _ Ff sy Gg) ∙ sym (C.⋆₂Assoc _ _ _)

          prem =
              sym (C.⋆₂Assoc _ _ _)
            ∙ ⋆InvsFlipSq (αI C (K.F-1cell Ff) (n y) q) KαI premα

        midLem :
            K.F² Ff (sy B.⋆₁ Gg)
              C.⋆₂ K.F-2cell (B.α⁻ Ff sy Gg)
              C.⋆₂ K.F-2cell (σ.N-hom f B.▷w Gg)
              C.⋆₂ K.F-2cell (B.α⁺ sx Gf Gg)
              C.⋆₂ K.F-2cell (sx B.◁w G.F² f g)
              C.⋆₂ κ²⁻ sx (G.F-1cell (f A.⋆₁ g))
          ≡   (K.F-1cell Ff C.◁w κ²⁻ sy Gg)
            C.⋆₂ C.α⁻ (K.F-1cell Ff) (n y) q
            C.⋆₂ (K.F² Ff sy C.▷w q)
            C.⋆₂ (K.F-2cell (σ.N-hom f) C.▷w q)
            C.⋆₂ (κ²⁻ sx Gf C.▷w q)
            C.⋆₂ C.α⁺ (n x) p q
            C.⋆₂ (n x C.◁w K.F² Gf Gg)
            C.⋆₂ (n x C.◁w K.F-2cell (G.F² f g))
        midLem =
            pushn C lemMid _ ∙ aR4 C _ _ _ _ _
          ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ backLem ⟩ ⟩ ⟩

        mergeS :
            K.F-2cell (F.F² f g B.▷w sz)
              C.⋆₂ K.F-2cell (σ.N-hom (f A.⋆₁ g))
          ≡   K.F-2cell (B.α⁺ Ff Fg sz)
            C.⋆₂ K.F-2cell (Ff B.◁w σ.N-hom g)
            C.⋆₂ K.F-2cell (B.α⁻ Ff sy Gg)
            C.⋆₂ K.F-2cell (σ.N-hom f B.▷w Gg)
            C.⋆₂ K.F-2cell (B.α⁺ sx Gf Gg)
            C.⋆₂ K.F-2cell (sx B.◁w G.F² f g)
        mergeS =
            sym (K.F-Hom .F-seq _ _)
          ∙ cong K.F-2cell (σ.lax-seq f g)
          ∙ K.F-Hom .F-seq _ _
          ∙ C.⟨⟩⋆₂⟨ K.F-Hom .F-seq _ _
              ∙ C.⟨⟩⋆₂⟨ K.F-Hom .F-seq _ _
                  ∙ C.⟨⟩⋆₂⟨ K.F-Hom .F-seq _ _
                      ∙ C.⟨⟩⋆₂⟨ K.F-Hom .F-seq _ _ ⟩ ⟩ ⟩ ⟩

        expandRHS :
            C.α⁺ (K.F-1cell Ff) (K.F-1cell Fg) (n z)
              C.⋆₂ (K.F-1cell Ff C.◁w nh g)
              C.⋆₂ C.α⁻ (K.F-1cell Ff) (n y) q
              C.⋆₂ (nh f C.▷w q)
              C.⋆₂ C.α⁺ (n x) p q
              C.⋆₂ (n x C.◁w (K.F² Gf Gg C.⋆₂ K.F-2cell (G.F² f g)))
          ≡   C.α⁺ (K.F-1cell Ff) (K.F-1cell Fg) (n z)
            C.⋆₂ (K.F-1cell Ff C.◁w K.F² Fg sz)
            C.⋆₂ (K.F-1cell Ff C.◁w K.F-2cell (σ.N-hom g))
            C.⋆₂ (K.F-1cell Ff C.◁w κ²⁻ sy Gg)
            C.⋆₂ C.α⁻ (K.F-1cell Ff) (n y) q
            C.⋆₂ (K.F² Ff sy C.▷w q)
            C.⋆₂ (K.F-2cell (σ.N-hom f) C.▷w q)
            C.⋆₂ (κ²⁻ sx Gf C.▷w q)
            C.⋆₂ C.α⁺ (n x) p q
            C.⋆₂ (n x C.◁w K.F² Gf Gg)
            C.⋆₂ (n x C.◁w K.F-2cell (G.F² f g))
        expandRHS =
          C.⟨⟩⋆₂⟨
              C.⟨ ◁3 C (K.F-1cell Ff) (K.F² Fg sz)
                       (K.F-2cell (σ.N-hom g)) (κ²⁻ sy Gg) ⟩⋆₂⟨
                C.⟨⟩⋆₂⟨
                    C.⟨ ▷3 C (K.F² Ff sy) (K.F-2cell (σ.N-hom f))
                             (κ²⁻ sx Gf) q ⟩⋆₂⟨
                      C.⟨⟩⋆₂⟨ ◁wSeq C (n x) (K.F² Gf Gg)
                                      (K.F-2cell (G.F² f g)) ⟩ ⟩
                  ∙ aR3 C _ _ _ _ ⟩ ⟩
            ∙ aR3 C _ _ _ _ ⟩

        result :
            ((K.F² Ff Fg C.⋆₂ K.F-2cell (F.F² f g)) C.▷w n z)
              C.⋆₂ nh (f A.⋆₁ g)
          ≡   C.α⁺ (K.F-1cell Ff) (K.F-1cell Fg) (n z)
            C.⋆₂ (K.F-1cell Ff C.◁w nh g)
            C.⋆₂ C.α⁻ (K.F-1cell Ff) (n y) q
            C.⋆₂ (nh f C.▷w q)
            C.⋆₂ C.α⁺ (n x) p q
            C.⋆₂ (n x C.◁w (K.F² Gf Gg C.⋆₂ K.F-2cell (G.F² f g)))
        result =
            C.⟨ ▷wSeq C (K.F² Ff Fg) (K.F-2cell (F.F² f g)) (n z) ⟩⋆₂⟨⟩
          ∙ C.⋆₂Assoc _ _ _
          ∙ C.⟨⟩⋆₂⟨ pushr C (F²nat▷ Kl (F.F² f g) sz) _ ⟩
          ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ pushn C mergeS _ ∙ aR6 _ _ _ _ _ _ _ ⟩ ⟩
          ∙ sym (aR3 C _ _ _ _)
          ∙ C.⟨ K.lax-α _ _ _ _ Ff Fg sz ⟩⋆₂⟨⟩
          ∙ aR3 C _ _ _ _
          ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ pushr C (sym (F²nat◁ Kl Ff (σ.N-hom g))) _ ⟩ ⟩
          ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ midLem ⟩ ⟩ ⟩
          ∙ sym expandRHS

    whiskerL : LaxNatTrans (Kl ∘Lax F) (Kl ∘Lax G)
    whiskerL .N-1cell = n
    whiskerL .N-hom = nh
    whiskerL .N-natural = wnat
    whiskerL .lax-id = wid
    whiskerL .lax-seq = WS.result

  whiskerLMod : {σ τ : LaxNatTrans F G}
    → Modification σ τ → Modification (whiskerL σ) (whiskerL τ)
  whiskerLMod Γ .M-ob x = K.F-2cell (Γ .M-ob x)
  whiskerLMod {σ} {τ} Γ .M-hom {x} {y} f =
      aR3 C _ _ _ _
    ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ sym flip1 ⟩ ⟩
    ∙ C.⟨⟩⋆₂⟨ pushr C merge _ ⟩
    ∙ pushr C (sym (F²nat◁ Kl (F.F-1cell f) (Γ .M-ob y))) _
    where
    flip1 :
        K.F-2cell (Γ .M-ob x B.▷w G.F-1cell f)
          C.⋆₂ κ²⁻ (τ .N-1cell x) (G.F-1cell f)
      ≡   κ²⁻ (σ .N-1cell x) (G.F-1cell f)
        C.⋆₂ (K.F-2cell (Γ .M-ob x) C.▷w K.F-1cell (G.F-1cell f))
    flip1 =
      ⋆InvsFlipSq (κ²I (σ .N-1cell x) (G.F-1cell f))
                  (κ²I (τ .N-1cell x) (G.F-1cell f))
                  (sym (F²nat▷ Kl (Γ .M-ob x) (G.F-1cell f)))

    merge :
        K.F-2cell (σ .N-hom f) C.⋆₂ K.F-2cell (Γ .M-ob x B.▷w G.F-1cell f)
      ≡   K.F-2cell (F.F-1cell f B.◁w Γ .M-ob y)
        C.⋆₂ K.F-2cell (τ .N-hom f)
    merge =
        sym (K.F-Hom .F-seq _ _)
      ∙ cong K.F-2cell (Γ .M-hom f)
      ∙ K.F-Hom .F-seq _ _

  whiskerLF : Functor (LaxNatTransCat {F = F} {G = G})
                      (LaxNatTransCat {F = Kl ∘Lax F} {G = Kl ∘Lax G})
  whiskerLF .F-ob = whiskerL
  whiskerLF .F-hom = whiskerLMod
  whiskerLF .F-id = makeModificationPath λ x → K.F-Hom .F-id
  whiskerLF .F-seq Γ Δ = makeModificationPath λ x → K.F-Hom .F-seq _ _
