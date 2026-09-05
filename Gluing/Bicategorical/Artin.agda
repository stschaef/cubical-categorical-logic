{-# OPTIONS --lossy-unification #-}
{-
  Artin gluing, done classically on the comma object supplied by
  `CAT`'s PIE limits: for `F : C → D` the glue is `D ↓ F`, with
  objects `(A , X , α : A → F X)`.
-}
module Gluing.Bicategorical.Artin where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Foundations.Structure
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Displayed.Instances.Dialgebras
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Exponentials.Small
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.Reindex

open import Gluing.Bicategorical.Comma

private
  variable
    ℓ ℓ' : Level

open Category
open Functor
open UniversalElement

module _ {ℓC ℓC' ℓD ℓD' : Level}
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D) where
  private
    module C = Category C
    module D = Category D

  -- the comma category `D ↓ F`, at unconstrained levels
  ArtinGlue : Category (ℓ-max (ℓ-max ℓD ℓC) ℓD')
                       (ℓ-max (ℓ-max ℓD' ℓC') ℓD')
  ArtinGlue = DIALG (Id ∘F Fst D C) (F ∘F Snd D C)

  private
    Gl = ArtinGlue
    module Gl = Category Gl

  -- The terminal object needs nothing of `D`: it is `(F 1 , 1 , id)`.
  module _ (termC : Terminal' C) where
    private
      module 𝟙C = TerminalNotation termC

    glueTerminal : Terminal Gl
    glueTerminal .fst = (F ⟅ 𝟙C.𝟙 ⟆ , 𝟙C.𝟙) , D.id
    glueTerminal .snd ((A , X) , α) .fst =
      (α D.⋆ F ⟪ 𝟙C.!t ⟫ , 𝟙C.!t) , sym (D.⋆IdR _)
    glueTerminal .snd ((A , X) , α) .snd ((h , f) , sq) =
      Σ≡Prop (λ _ → D.isSetHom _ _)
        (ΣPathP
          ( cong (λ z → α D.⋆ F ⟪ z ⟫) 𝟙C.𝟙extensionality
            ∙ sq ∙ D.⋆IdR h
          , 𝟙C.𝟙extensionality))

    glueTerminal' : Terminal' Gl
    glueTerminal' = terminalToUniversalElement glueTerminal

  -- Binary products are pointwise, and this is exactly where `F`
  -- preserving binary products is used: without it the product would
  -- be a pullback in `D`.
  module _ (bpC : BinProducts C) (bpD : BinProducts D)
    (Fp : preservesProvidedBinProducts F bpC) where

    glueBinProducts : BinProducts Gl
    glueBinProducts (((A , X) , α) , ((B , Y) , β)) = ue
      where
      module A×B = BinProductNotation (bpD (A , B))
      module X×Y = BinProductNotation (bpC (X , Y))
      module img = BinProductNotation
        (becomesUniversal→UniversalElement
          (preservesBinProdCones F X Y) (Fp X Y))

      γ : D [ A×B.vert , F ⟅ X×Y.vert ⟆ ]
      γ = img._,p_ (A×B.π₁ D.⋆ α) (A×B.π₂ D.⋆ β)

      p₁ : Gl [ ((A×B.vert , X×Y.vert) , γ) , ((A , X) , α) ]
      p₁ = (A×B.π₁ , X×Y.π₁) , img.×β₁

      p₂ : Gl [ ((A×B.vert , X×Y.vert) , γ) , ((B , Y) , β) ]
      p₂ = (A×B.π₂ , X×Y.π₂) , img.×β₂

      module _ {E : D .ob} {Z : C .ob} {δ : D [ E , F ⟅ Z ⟆ ]}
        (g₁ : Gl [ ((E , Z) , δ) , ((A , X) , α) ])
        (g₂ : Gl [ ((E , Z) , δ) , ((B , Y) , β) ]) where
        private
          h₁ = g₁ .fst .fst
          f₁ = g₁ .fst .snd
          h₂ = g₂ .fst .fst
          f₂ = g₂ .fst .snd

        pairSq : δ D.⋆ F ⟪ X×Y._,p_ f₁ f₂ ⟫
               ≡ A×B._,p_ h₁ h₂ D.⋆ γ
        pairSq = img.,p-extensionality
          ( D.⋆Assoc _ _ _
            ∙ cong (δ D.⋆_) (sym (F .F-seq _ _) ∙ cong (F ⟪_⟫) X×Y.×β₁)
            ∙ g₁ .snd
            ∙ cong (D._⋆ α) (sym A×B.×β₁)
            ∙ D.⋆Assoc _ _ _
            ∙ cong (A×B._,p_ h₁ h₂ D.⋆_) (sym img.×β₁)
            ∙ sym (D.⋆Assoc _ _ _))
          ( D.⋆Assoc _ _ _
            ∙ cong (δ D.⋆_) (sym (F .F-seq _ _) ∙ cong (F ⟪_⟫) X×Y.×β₂)
            ∙ g₂ .snd
            ∙ cong (D._⋆ β) (sym A×B.×β₂)
            ∙ D.⋆Assoc _ _ _
            ∙ cong (A×B._,p_ h₁ h₂ D.⋆_) (sym img.×β₂)
            ∙ sym (D.⋆Assoc _ _ _))

        pair : Gl [ ((E , Z) , δ) , ((A×B.vert , X×Y.vert) , γ) ]
        pair = (A×B._,p_ h₁ h₂ , X×Y._,p_ f₁ f₂) , pairSq

      ue : BinProduct Gl (((A , X) , α) , ((B , Y) , β))
      ue .vertex = (A×B.vert , X×Y.vert) , γ
      ue .element = p₁ , p₂
      ue .universal w = isoToIsEquiv (iso _
        (λ (g₁ , g₂) → pair g₁ g₂)
        (λ (g₁ , g₂) → ΣPathP
          ( Σ≡Prop (λ _ → D.isSetHom _ _)
              (ΣPathP (A×B.×β₁ , X×Y.×β₁))
          , Σ≡Prop (λ _ → D.isSetHom _ _)
              (ΣPathP (A×B.×β₂ , X×Y.×β₂))))
        λ g → Σ≡Prop (λ _ → D.isSetHom _ _)
          (ΣPathP (A×B.,p≡ refl refl , X×Y.,p≡ refl refl)))

{-
  Exponentials.  Taken in `SET`, where the classical pullback is a
  subset: the carrier of `(A , X , α) ⇒ (B , Y , β)` is the set of
  pairs `(h , k)` of a function `h : A → B` and a point `k` of
  `F (X ⇒ Y)` that are related, `β (h a) ≡ tapp k (α a)`.  `tapp` is
  the transpose of `F app` along the comparison, and needs `F` to
  preserve binary products -- which is why that is an argument.
-}
module _ {ℓs ℓC ℓC' : Level} {C : Category ℓC ℓC'}
  (F : Functor C (SET ℓs)) (bpC : BinProducts C)
  (expC : AllExponentiable C bpC)
  (Fp : preservesProvidedBinProducts F bpC) where
  module C = Category C
  module ×C = BinProductsNotation bpC
  module ⇒C = ExponentialsNotation bpC expC
  module ⇒ue (c d : C .ob) =
    ExponentialNotation.⇒ue (λ d' → bpC (d' , c)) (expC c d)

  Gl = ArtinGlue F
  module Gl = Category Gl

  img : (X Y : C .ob) → BinProduct (SET ℓs) (F ⟅ X ⟆ , F ⟅ Y ⟆)
  img X Y = becomesUniversal→UniversalElement
    (preservesBinProdCones F X Y) (Fp X Y)
  module Img (X Y : C .ob) = BinProductNotation (img X Y)

  one : hSet ℓs
  one = Unit* , isSetUnit*

  pr : (X Y : C .ob) → ⟨ F ⟅ X ⟆ ⟩ → ⟨ F ⟅ Y ⟆ ⟩ → ⟨ Img.vert X Y ⟩
  pr X Y x y = Img._,p_ X Y {Γ = one} (λ _ → x) (λ _ → y) tt*

  prβ₁ : (X Y : C .ob) (x : ⟨ F ⟅ X ⟆ ⟩) (y : ⟨ F ⟅ Y ⟆ ⟩)
    → (F ⟪ ×C.π₁ ⟫) (pr X Y x y) ≡ x
  prβ₁ X Y x y = funExt⁻
    (Img.×β₁ X Y {Γ = one} {f = λ _ → x} {g = λ _ → y}) tt*

  prβ₂ : (X Y : C .ob) (x : ⟨ F ⟅ X ⟆ ⟩) (y : ⟨ F ⟅ Y ⟆ ⟩)
    → (F ⟪ ×C.π₂ ⟫) (pr X Y x y) ≡ y
  prβ₂ X Y x y = funExt⁻
    (Img.×β₂ X Y {Γ = one} {f = λ _ → x} {g = λ _ → y}) tt*

  prExt : (X Y : C .ob) {z w : ⟨ Img.vert X Y ⟩}
    → (F ⟪ ×C.π₁ ⟫) z ≡ (F ⟪ ×C.π₁ ⟫) w
    → (F ⟪ ×C.π₂ ⟫) z ≡ (F ⟪ ×C.π₂ ⟫) w
    → z ≡ w
  prExt X Y {z} {w} p q = funExt⁻
    (Img.,p-extensionality X Y {Γ = one} {f = λ _ → z} {g = λ _ → w}
      (funExt (λ _ → p)) (funExt (λ _ → q))) tt*

  prPoint : {S : hSet ℓs} (X Y : C .ob)
    (f : ⟨ S ⟩ → ⟨ F ⟅ X ⟆ ⟩) (g : ⟨ S ⟩ → ⟨ F ⟅ Y ⟆ ⟩) (s : ⟨ S ⟩)
    → Img._,p_ X Y f g s ≡ pr X Y (f s) (g s)
  prPoint {S} X Y f g s = prExt X Y
    ( funExt⁻ (Img.×β₁ X Y {Γ = S} {f = f} {g = g}) s
    ∙ sym (prβ₁ X Y (f s) (g s)))
    ( funExt⁻ (Img.×β₂ X Y {Γ = S} {f = f} {g = g}) s
    ∙ sym (prβ₂ X Y (f s) (g s)))

  tapp : {X Y : C .ob} → ⟨ F ⟅ ⇒C._⇒_ X Y ⟆ ⟩ → ⟨ F ⟅ X ⟆ ⟩
    → ⟨ F ⟅ Y ⟆ ⟩
  tapp {X} {Y} k x = (F ⟪ ⇒C.app ⟫) (pr (⇒C._⇒_ X Y) X k x)

  tappNat : {Z X Y : C .ob} (m : C [ ×C._×_ Z X , Y ])
    (z : ⟨ F ⟅ Z ⟆ ⟩) (x : ⟨ F ⟅ X ⟆ ⟩)
    → (F ⟪ m ⟫) (pr Z X z x) ≡ tapp ((F ⟪ ⇒C.lda m ⟫) z) x
  tappNat {Z} {X} {Y} m z x =
      cong (λ n → (F ⟪ n ⟫) (pr Z X z x)) (sym (⇒ue.β X Y {Z} {m}))
    ∙ funExt⁻ (F .F-seq _ _) (pr Z X z x)
    ∙ cong (F ⟪ ⇒C.app ⟫) step
    where
    step : (F ⟪ ×C._,p_ (×C.π₁ C.⋆ ⇒C.lda m) ×C.π₂ ⟫) (pr Z X z x)
         ≡ pr (⇒C._⇒_ X Y) X ((F ⟪ ⇒C.lda m ⟫) z) x
    step = prExt _ _
      ( funExt⁻ (sym (F .F-seq _ _)) _
      ∙ cong (λ n → (F ⟪ n ⟫) (pr Z X z x)) ×C.×β₁
      ∙ funExt⁻ (F .F-seq _ _) _
      ∙ cong (F ⟪ ⇒C.lda m ⟫) (prβ₁ Z X z x)
      ∙ sym (prβ₁ _ _ _ _))
      ( funExt⁻ (sym (F .F-seq _ _)) _
      ∙ cong (λ n → (F ⟪ n ⟫) (pr Z X z x)) ×C.×β₂
      ∙ prβ₂ Z X z x
      ∙ sym (prβ₂ _ _ _ _))

  module Ds = Category (SET ℓs)

  bpGl : BinProducts Gl
  bpGl = glueBinProducts F bpC BinProductsSET Fp

  private
    module ×Gl = BinProductsNotation bpGl

  glueExponentials : AllExponentiable Gl bpGl
  glueExponentials ((A , X) , α) ((B , Y) , β) = ue
    where
    u : Gl.ob
    u = (A , X) , α

    W : C .ob
    W = ⇒C._⇒_ X Y

    Rel : (⟨ A ⟩ → ⟨ B ⟩) → ⟨ F ⟅ W ⟆ ⟩ → Type ℓs
    Rel h k = (a : ⟨ A ⟩) → β (h a) ≡ tapp k (α a)

    Eset : hSet ℓs
    Eset =
      (Σ[ h ∈ (⟨ A ⟩ → ⟨ B ⟩) ] Σ[ k ∈ ⟨ F ⟅ W ⟆ ⟩ ] Rel h k)
      , isSetΣ (isSetΠ (λ _ → B .snd))
          (λ h → isSetΣ ((F ⟅ W ⟆) .snd)
            (λ k → isProp→isSet (isPropΠ (λ a → (F ⟅ Y ⟆) .snd _ _))))

    γE : ⟨ Eset ⟩ → ⟨ F ⟅ W ⟆ ⟩
    γE e = e .snd .fst

    expOb : Gl.ob
    expOb = (Eset , W) , γE

    appD : ⟨ Eset ⟩ × ⟨ A ⟩ → ⟨ B ⟩
    appD p = p .fst .fst (p .snd)

    appGl : Gl [ bpGl (expOb , u) .vertex , ((B , Y) , β) ]
    appGl = (appD , ⇒C.app) , funExt (λ p →
        cong (F ⟪ ⇒C.app ⟫) (prPoint W X _ _ p)
      ∙ sym (p .fst .snd .snd (p .snd)))

    module At (G : hSet ℓs) (Z : C .ob) (δ : ⟨ G ⟩ → ⟨ F ⟅ Z ⟆ ⟩) where
      w : Gl.ob
      w = (G , Z) , δ

      ldaGl : Gl [ bpGl (w , u) .vertex , ((B , Y) , β) ]
        → Gl [ w , expOb ]
      ldaGl ((mD , mC) , msq) =
        ( (λ e → (λ a → mD (e , a))
                , (F ⟪ ⇒C.lda mC ⟫) (δ e)
                , λ a → sym (funExt⁻ msq (e , a))
                      ∙ cong (F ⟪ mC ⟫) (prPoint Z X _ _ (e , a))
                      ∙ tappNat mC (δ e) (α a))
        , ⇒C.lda mC ) , refl

      πw : Gl [ bpGl (w , u) .vertex , w ]
      πw = ×Gl.π₁ {a = w} {b = u}

      πu : Gl [ bpGl (w , u) .vertex , u ]
      πu = ×Gl.π₂ {a = w} {b = u}

      pull : Gl [ w , expOb ]
        → Gl [ bpGl (w , u) .vertex , bpGl (expOb , u) .vertex ]
      pull l = ×Gl._,p_ {a = expOb} {b = u} (πw Gl.⋆ l) πu

      ⟪⟫D : (l : Gl [ w , expOb ]) (p : ⟨ G ⟩ × ⟨ A ⟩)
        → pull l .fst .fst p ≡ (l .fst .fst (p .fst) , p .snd)
      ⟪⟫D l p = ΣPathP
        ( funExt⁻ (cong (λ n → n .fst .fst) (×Gl.×β₁ {a = expOb} {b = u}
            {f = πw Gl.⋆ l} {g = πu})) p
        , funExt⁻ (cong (λ n → n .fst .fst) (×Gl.×β₂ {a = expOb} {b = u}
            {f = πw Gl.⋆ l} {g = πu})) p)

      ⟪⟫C : (l : Gl [ w , expOb ])
        → ×C._,p_ (×C.π₁ C.⋆ l .fst .snd) ×C.π₂ ≡ pull l .fst .snd
      ⟪⟫C l = ×C.,p≡
        (sym (cong (λ n → n .fst .snd) (×Gl.×β₁ {a = expOb} {b = u}
          {f = πw Gl.⋆ l} {g = πu})))
        (sym (cong (λ n → n .fst .snd) (×Gl.×β₂ {a = expOb} {b = u}
          {f = πw Gl.⋆ l} {g = πu})))

      secGl : (m : Gl [ bpGl (w , u) .vertex , ((B , Y) , β) ])
        → pull (ldaGl m) Gl.⋆ appGl ≡ m
      secGl m@((mD , mC) , msq) = Σ≡Prop (λ _ → Ds.isSetHom _ _)
        (ΣPathP
          ( funExt (λ p → cong appD (⟪⟫D (ldaGl m) p))
          , cong (C._⋆ ⇒C.app) (sym (⟪⟫C (ldaGl m)))
            ∙ ⇒ue.β X Y {Z} {mC}))

      retGl : (l : Gl [ w , expOb ]) → ldaGl (pull l Gl.⋆ appGl) ≡ l
      retGl l = Σ≡Prop (λ _ → Ds.isSetHom _ _) (ΣPathP (funExt eq , ldaC))
        where
        ldaC : ⇒C.lda ((pull l Gl.⋆ appGl) .fst .snd) ≡ l .fst .snd
        ldaC = cong ⇒C.lda (cong (C._⋆ ⇒C.app) (sym (⟪⟫C l)))
             ∙ sym (⇒ue.η X Y {Z} {l .fst .snd})

        eq : (e : ⟨ G ⟩)
          → ldaGl (pull l Gl.⋆ appGl) .fst .fst e ≡ l .fst .fst e
        eq e = ΣPathP
          ( funExt (λ a → cong appD (⟪⟫D l (e , a)))
          , ΣPathP
            ( cong (λ n → (F ⟪ n ⟫) (δ e)) ldaC ∙ funExt⁻ (l .snd) e
            , isProp→PathP (λ i → isPropΠ (λ a → (F ⟅ Y ⟆) .snd _ _)) _ _))

    ue : Exponential Gl u ((B , Y) , β) (λ d → bpGl (d , u))
    ue .vertex = expOb
    ue .element = appGl
    ue .universal ((G , Z) , δ) =
      isoToIsEquiv (iso _ (At.ldaGl G Z δ) (At.secGl G Z δ)
        (At.retGl G Z δ))

-- At `CAT`'s levels -- one and the same object level for the syntax
-- and for the semantics -- this glue IS the comma object supplied by
-- `pieLimitsCAT`, on the nose.
module _ {ℓ ℓ' : Level} {C D : Category (ℓ-max ℓ ℓ') ℓ'}
  (F : Functor C D) where
  ArtinGlue≡Commaᴮ : ArtinGlue F ≡ glueCat {ℓ = ℓ} {ℓ' = ℓ'} F
  ArtinGlue≡Commaᴮ = refl
