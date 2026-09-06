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
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.Pullback.Alt
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.Reindex

open import Gluing.Bicategorical.Comma
open import Gluing.Bicategorical.CanonicityCore using (module Exp)

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

  -- Coproducts and the initial object need NOTHING of `F`: their
  -- structure map is built by copairing out of the two components,
  -- not by a comparison map into a product.
  module _ (initC : Initial' C) (initD : Initial' D) where
    private
      module 𝟘C = InitialNotation initC
      module 𝟘D = InitialNotation initD

    glueInitial : Initial' Gl
    glueInitial = terminalToUniversalElement
      ( ((𝟘D.𝟘 , 𝟘C.𝟘) , 𝟘D.absurd)
      , λ ((A , X) , α) →
          ((𝟘D.absurd , 𝟘C.absurd) , 𝟘D.𝟘extensionality)
        , λ ((h , f) , sq) → Σ≡Prop (λ _ → D.isSetHom _ _)
            (ΣPathP (𝟘D.𝟘extensionality , 𝟘C.𝟘extensionality)))

  module _ (bcpC : BinCoProducts C) (bcpD : BinCoProducts D) where

    glueBinCoProducts : BinCoProducts Gl
    glueBinCoProducts (((A , X) , α) , ((B , Y) , β)) = ue
      where
      module A+B = BinCoProductNotation (bcpD (A , B))
      module X+Y = BinCoProductNotation (bcpC (X , Y))

      γ : D [ A+B.vert , F ⟅ X+Y.vert ⟆ ]
      γ = A+B.[ α D.⋆ F ⟪ X+Y.σ₁ ⟫ ,p β D.⋆ F ⟪ X+Y.σ₂ ⟫ ]

      i₁ : Gl [ ((A , X) , α) , ((A+B.vert , X+Y.vert) , γ) ]
      i₁ = (A+B.σ₁ , X+Y.σ₁) , sym A+B.+β₁

      i₂ : Gl [ ((B , Y) , β) , ((A+B.vert , X+Y.vert) , γ) ]
      i₂ = (A+B.σ₂ , X+Y.σ₂) , sym A+B.+β₂

      module _ {E : D .ob} {Z : C .ob} {δ : D [ E , F ⟅ Z ⟆ ]}
        (g₁ : Gl [ ((A , X) , α) , ((E , Z) , δ) ])
        (g₂ : Gl [ ((B , Y) , β) , ((E , Z) , δ) ]) where
        private
          h₁ = g₁ .fst .fst
          f₁ = g₁ .fst .snd
          h₂ = g₂ .fst .fst
          f₂ = g₂ .fst .snd

        copairSq : γ D.⋆ F ⟪ X+Y.[ f₁ ,p f₂ ] ⟫
                 ≡ A+B.[ h₁ ,p h₂ ] D.⋆ δ
        copairSq = A+B.[-,p-]-extensionality
          ( sym (D.⋆Assoc _ _ _)
          ∙ cong (D._⋆ F ⟪ X+Y.[ f₁ ,p f₂ ] ⟫) A+B.+β₁
          ∙ D.⋆Assoc _ _ _
          ∙ cong (α D.⋆_) (sym (F .F-seq _ _) ∙ cong (F ⟪_⟫) X+Y.+β₁)
          ∙ g₁ .snd
          ∙ cong (D._⋆ δ) (sym A+B.+β₁)
          ∙ D.⋆Assoc _ _ _)
          ( sym (D.⋆Assoc _ _ _)
          ∙ cong (D._⋆ F ⟪ X+Y.[ f₁ ,p f₂ ] ⟫) A+B.+β₂
          ∙ D.⋆Assoc _ _ _
          ∙ cong (β D.⋆_) (sym (F .F-seq _ _) ∙ cong (F ⟪_⟫) X+Y.+β₂)
          ∙ g₂ .snd
          ∙ cong (D._⋆ δ) (sym A+B.+β₂)
          ∙ D.⋆Assoc _ _ _)

        copair : Gl [ ((A+B.vert , X+Y.vert) , γ) , ((E , Z) , δ) ]
        copair = (A+B.[ h₁ ,p h₂ ] , X+Y.[ f₁ ,p f₂ ]) , copairSq

      ue : BinCoProduct Gl (((A , X) , α) , ((B , Y) , β))
      ue .vertex = (A+B.vert , X+Y.vert) , γ
      ue .element = i₁ , i₂
      ue .universal w = isoToIsEquiv (iso _
        (λ (g₁ , g₂) → copair g₁ g₂)
        (λ (g₁ , g₂) → ΣPathP
          ( Σ≡Prop (λ _ → D.isSetHom _ _)
              (ΣPathP (A+B.+β₁ , X+Y.+β₁))
          , Σ≡Prop (λ _ → D.isSetHom _ _)
              (ΣPathP (A+B.+β₂ , X+Y.+β₂))))
        λ g → Σ≡Prop (λ _ → D.isSetHom _ _)
          (ΣPathP (A+B.[-,p-]≡ refl refl , X+Y.[-,p-]≡ refl refl)))

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
  (Fp : preservesProvidedBinProducts F bpC) where
  module C = Category C
  module ×C = BinProductsNotation bpC

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


-- the exponential also needs `C` cartesian closed
module _ {ℓs ℓC ℓC' : Level} {C : Category ℓC ℓC'}
  (F : Functor C (SET ℓs)) (bpC : BinProducts C)
  (expC : AllExponentiable C bpC)
  (Fp : preservesProvidedBinProducts F bpC) where
  module CE = Category C
  module ×CE = BinProductsNotation bpC
  module ⇒C = ExponentialsNotation bpC expC
  module ⇒ue (c d : C .ob) =
    ExponentialNotation.⇒ue (λ d' → bpC (d' , c)) (expC c d)

  GlE = ArtinGlue F
  module GlE = Category GlE

  prF = pr F bpC Fp
  prβ₁F = prβ₁ F bpC Fp
  prβ₂F = prβ₂ F bpC Fp
  prExtF = prExt F bpC Fp
  prPointF = prPoint F bpC Fp

  tapp : {X Y : C .ob} → ⟨ F ⟅ ⇒C._⇒_ X Y ⟆ ⟩ → ⟨ F ⟅ X ⟆ ⟩
    → ⟨ F ⟅ Y ⟆ ⟩
  tapp {X} {Y} k x = (F ⟪ ⇒C.app ⟫) (prF (⇒C._⇒_ X Y) X k x)

  tappNat : {Z X Y : C .ob} (m : C [ ×CE._×_ Z X , Y ])
    (z : ⟨ F ⟅ Z ⟆ ⟩) (x : ⟨ F ⟅ X ⟆ ⟩)
    → (F ⟪ m ⟫) (prF Z X z x) ≡ tapp ((F ⟪ ⇒C.lda m ⟫) z) x
  tappNat {Z} {X} {Y} m z x =
      cong (λ n → (F ⟪ n ⟫) (prF Z X z x)) (sym (⇒ue.β X Y {Z} {m}))
    ∙ funExt⁻ (F .F-seq _ _) (prF Z X z x)
    ∙ cong (F ⟪ ⇒C.app ⟫) step
    where
    step : (F ⟪ ×CE._,p_ (×CE.π₁ CE.⋆ ⇒C.lda m) ×CE.π₂ ⟫) (prF Z X z x)
         ≡ prF (⇒C._⇒_ X Y) X ((F ⟪ ⇒C.lda m ⟫) z) x
    step = prExtF _ _
      ( funExt⁻ (sym (F .F-seq _ _)) _
      ∙ cong (λ n → (F ⟪ n ⟫) (prF Z X z x)) ×CE.×β₁
      ∙ funExt⁻ (F .F-seq _ _) _
      ∙ cong (F ⟪ ⇒C.lda m ⟫) (prβ₁F Z X z x)
      ∙ sym (prβ₁F _ _ _ _))
      ( funExt⁻ (sym (F .F-seq _ _)) _
      ∙ cong (λ n → (F ⟪ n ⟫) (prF Z X z x)) ×CE.×β₂
      ∙ prβ₂F Z X z x
      ∙ sym (prβ₂F _ _ _ _))

  module Ds = Category (SET ℓs)

  bpGl : BinProducts GlE
  bpGl = glueBinProducts F bpC BinProductsSET Fp

  private
    module ×Gl = BinProductsNotation bpGl

  glueExponentials : AllExponentiable GlE bpGl
  glueExponentials ((A , X) , α) ((B , Y) , β) = ue
    where
    u : GlE.ob
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

    expOb : GlE.ob
    expOb = (Eset , W) , γE

    appD : ⟨ Eset ⟩ × ⟨ A ⟩ → ⟨ B ⟩
    appD p = p .fst .fst (p .snd)

    appGl : GlE [ bpGl (expOb , u) .vertex , ((B , Y) , β) ]
    appGl = (appD , ⇒C.app) , funExt (λ p →
        cong (F ⟪ ⇒C.app ⟫) (prPointF W X _ _ p)
      ∙ sym (p .fst .snd .snd (p .snd)))

    module At (G : hSet ℓs) (Z : C .ob) (δ : ⟨ G ⟩ → ⟨ F ⟅ Z ⟆ ⟩) where
      w : GlE.ob
      w = (G , Z) , δ

      ldaGl : GlE [ bpGl (w , u) .vertex , ((B , Y) , β) ]
        → GlE [ w , expOb ]
      ldaGl ((mD , mC) , msq) =
        ( (λ e → (λ a → mD (e , a))
                , (F ⟪ ⇒C.lda mC ⟫) (δ e)
                , λ a → sym (funExt⁻ msq (e , a))
                      ∙ cong (F ⟪ mC ⟫) (prPointF Z X _ _ (e , a))
                      ∙ tappNat mC (δ e) (α a))
        , ⇒C.lda mC ) , refl

      πw : GlE [ bpGl (w , u) .vertex , w ]
      πw = ×Gl.π₁ {a = w} {b = u}

      πu : GlE [ bpGl (w , u) .vertex , u ]
      πu = ×Gl.π₂ {a = w} {b = u}

      pull : GlE [ w , expOb ]
        → GlE [ bpGl (w , u) .vertex , bpGl (expOb , u) .vertex ]
      pull l = ×Gl._,p_ {a = expOb} {b = u} (πw GlE.⋆ l) πu

      ⟪⟫D : (l : GlE [ w , expOb ]) (p : ⟨ G ⟩ × ⟨ A ⟩)
        → pull l .fst .fst p ≡ (l .fst .fst (p .fst) , p .snd)
      ⟪⟫D l p = ΣPathP
        ( funExt⁻ (cong (λ n → n .fst .fst) (×Gl.×β₁ {a = expOb} {b = u}
            {f = πw GlE.⋆ l} {g = πu})) p
        , funExt⁻ (cong (λ n → n .fst .fst) (×Gl.×β₂ {a = expOb} {b = u}
            {f = πw GlE.⋆ l} {g = πu})) p)

      ⟪⟫C : (l : GlE [ w , expOb ])
        → ×CE._,p_ (×CE.π₁ CE.⋆ l .fst .snd) ×CE.π₂ ≡ pull l .fst .snd
      ⟪⟫C l = ×CE.,p≡
        (sym (cong (λ n → n .fst .snd) (×Gl.×β₁ {a = expOb} {b = u}
          {f = πw GlE.⋆ l} {g = πu})))
        (sym (cong (λ n → n .fst .snd) (×Gl.×β₂ {a = expOb} {b = u}
          {f = πw GlE.⋆ l} {g = πu})))

      secGl : (m : GlE [ bpGl (w , u) .vertex , ((B , Y) , β) ])
        → pull (ldaGl m) GlE.⋆ appGl ≡ m
      secGl m@((mD , mC) , msq) = Σ≡Prop (λ _ → Ds.isSetHom _ _)
        (ΣPathP
          ( funExt (λ p → cong appD (⟪⟫D (ldaGl m) p))
          , cong (CE._⋆ ⇒C.app) (sym (⟪⟫C (ldaGl m)))
            ∙ ⇒ue.β X Y {Z} {mC}))

      retGl : (l : GlE [ w , expOb ]) → ldaGl (pull l GlE.⋆ appGl) ≡ l
      retGl l = Σ≡Prop (λ _ → Ds.isSetHom _ _) (ΣPathP (funExt eq , ldaC))
        where
        ldaC : ⇒C.lda ((pull l GlE.⋆ appGl) .fst .snd) ≡ l .fst .snd
        ldaC = cong ⇒C.lda (cong (CE._⋆ ⇒C.app) (sym (⟪⟫C l)))
             ∙ sym (⇒ue.η X Y {Z} {l .fst .snd})

        eq : (e : ⟨ G ⟩)
          → ldaGl (pull l GlE.⋆ appGl) .fst .fst e ≡ l .fst .fst e
        eq e = ΣPathP
          ( funExt (λ a → cong appD (⟪⟫D l (e , a)))
          , ΣPathP
            ( cong (λ n → (F ⟪ n ⟫) (δ e)) ldaC ∙ funExt⁻ (l .snd) e
            , isProp→PathP (λ i → isPropΠ (λ a → (F ⟅ Y ⟆) .snd _ _)) _ _))

    ue : Exponential GlE u ((B , Y) , β) (λ d → bpGl (d , u))
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

{-
  Exponentials, generically.  `SET`'s subset carrier above is the
  special case of the classical construction in which the pullback is
  a Σ-type: in general the carrier is the pullback in `D` of
      A ⇒ B --(A ⇒ β)--> A ⇒ F Y <--ψ-- F (X ⇒ Y),
  so `D` needs pullbacks on top of its cartesian closed structure and
  `F` still needs to preserve binary products.  The point-free
  λ-calculus this runs on is `CanonicityCore.Exp`, written for the
  canonicity comparison isomorphisms and reused here verbatim.
-}
module _ {ℓC ℓC' ℓD ℓD' : Level}
  (𝒞 : CartesianClosedCategory ℓC ℓC')
  (𝒟 : CartesianClosedCategory ℓD ℓD')
  (F : Functor (CartesianClosedCategory.C 𝒞)
               (CartesianClosedCategory.C 𝒟))
  (pbD : Pullbacks (CartesianClosedCategory.C 𝒟))
  (Fp : preservesProvidedBinProducts F (CartesianClosedCategory.bp 𝒞))
  where
  private
    module 𝒞 = CartesianClosedCategory 𝒞
    module 𝒟 = CartesianClosedCategory 𝒟
    module ExpC = Exp 𝒞
    module ExpD = Exp 𝒟

  GlCCC : Category _ _
  GlCCC = ArtinGlue F

  private module GlCCC = Category GlCCC

  bpGlCCC : BinProducts GlCCC
  bpGlCCC = glueBinProducts F 𝒞.bp 𝒟.bp Fp

  private
    module ×GlCCC = BinProductsNotation bpGlCCC

    imgOb : (X Y : 𝒞.ob) → BinProduct 𝒟.C (F ⟅ X ⟆ , F ⟅ Y ⟆)
    imgOb X Y = becomesUniversal→UniversalElement
      (preservesBinProdCones F X Y) (Fp X Y)

    module ImgOb (X Y : 𝒞.ob) = BinProductNotation (imgOb X Y)

    imgSeq : ∀ {X Y : 𝒞.ob} {Γ Δ : 𝒟.ob} (m : 𝒟.Hom[ Γ , Δ ])
      (a : 𝒟.Hom[ Δ , F ⟅ X ⟆ ]) (b : 𝒟.Hom[ Δ , F ⟅ Y ⟆ ])
      → m 𝒟.⋆ ImgOb._,p_ X Y a b
        ≡ ImgOb._,p_ X Y (m 𝒟.⋆ a) (m 𝒟.⋆ b)
    imgSeq {X = X} {Y = Y} m a b = sym (ImgOb.,p≡ X Y
      (sym (𝒟.⋆Assoc _ _ _ ∙ cong (m 𝒟.⋆_) (ImgOb.×β₁ X Y)))
      (sym (𝒟.⋆Assoc _ _ _ ∙ cong (m 𝒟.⋆_) (ImgOb.×β₂ X Y))))

  glueExponentials' : AllExponentiable GlCCC bpGlCCC
  glueExponentials' ((A , X) , α) ((B , Y) , β) = ue
    where
    u : GlCCC.ob
    u = (A , X) , α

    v : GlCCC.ob
    v = (B , Y) , β

    W : 𝒞.ob
    W = 𝒞._⇒_ X Y

    φ : 𝒟.Hom[ 𝒟._⇒_ A B , 𝒟._⇒_ A (F ⟅ Y ⟆) ]
    φ = 𝒟.lda {c = A} {d = F ⟅ Y ⟆} (𝒟.app {c = A} {d = B} 𝒟.⋆ β)

    ψ : 𝒟.Hom[ F ⟅ W ⟆ , 𝒟._⇒_ A (F ⟅ Y ⟆) ]
    ψ = 𝒟.lda {c = A} {d = F ⟅ Y ⟆}
      (ImgOb._,p_ W X (𝒟.π₁ {a = F ⟅ W ⟆} {b = A})
        (𝒟.π₂ {a = F ⟅ W ⟆} {b = A} 𝒟.⋆ α)
       𝒟.⋆ F ⟪ 𝒞.app {c = X} {d = Y} ⟫)

    module Ep = PullbackNotation (pbD φ ψ)

    expOb : GlCCC.ob
    expOb = (Ep.vert , W) , Ep.pbπ₂

    appφ : ExpD.appOf φ ≡ 𝒟.app {c = A} {d = B} 𝒟.⋆ β
    appφ = ExpD.ldaβ _

    appψ : ExpD.appOf ψ
      ≡ ImgOb._,p_ W X (𝒟.π₁ {a = F ⟅ W ⟆} {b = A})
          (𝒟.π₂ {a = F ⟅ W ⟆} {b = A} 𝒟.⋆ α)
        𝒟.⋆ F ⟪ 𝒞.app {c = X} {d = Y} ⟫
    appψ = ExpD.ldaβ _

    γE : 𝒟.Hom[ 𝒟._×_ Ep.vert A , F ⟅ 𝒞._×_ W X ⟆ ]
    γE = ImgOb._,p_ W X
      (𝒟.π₁ {a = Ep.vert} {b = A} 𝒟.⋆ Ep.pbπ₂)
      (𝒟.π₂ {a = Ep.vert} {b = A} 𝒟.⋆ α)

    appD : 𝒟.Hom[ 𝒟._×_ Ep.vert A , B ]
    appD = ExpD.appOf Ep.pbπ₁

    γE≡ : γE ≡ ExpD.pl Ep.pbπ₂
      𝒟.⋆ ImgOb._,p_ W X (𝒟.π₁ {a = F ⟅ W ⟆} {b = A})
            (𝒟.π₂ {a = F ⟅ W ⟆} {b = A} 𝒟.⋆ α)
    γE≡ = ImgOb.⟨_⟩,p⟨_⟩ W X (sym 𝒟.×β₁)
            (sym (sym (𝒟.⋆Assoc _ _ _) ∙ cong (𝒟._⋆ α) 𝒟.×β₂))
        ∙ sym (imgSeq (ExpD.pl Ep.pbπ₂) _ _)

    appSq : γE 𝒟.⋆ F ⟪ 𝒞.app {c = X} {d = Y} ⟫ ≡ appD 𝒟.⋆ β
    appSq =
        cong (𝒟._⋆ F ⟪ 𝒞.app {c = X} {d = Y} ⟫) γE≡
      ∙ 𝒟.⋆Assoc _ _ _
      ∙ cong (ExpD.pl Ep.pbπ₂ 𝒟.⋆_) (sym appψ)
      ∙ sym (ExpD.appOfSeq Ep.pbπ₂ ψ)
      ∙ cong ExpD.appOf (sym Ep.pbCommutes)
      ∙ ExpD.appOfSeq Ep.pbπ₁ φ
      ∙ cong (ExpD.pl Ep.pbπ₁ 𝒟.⋆_) appφ
      ∙ sym (𝒟.⋆Assoc _ _ _)

    appGl : GlCCC [ bpGlCCC (expOb , u) .vertex , v ]
    appGl = (appD , 𝒞.app {c = X} {d = Y}) , appSq

    module At (G : 𝒟.ob) (Z : 𝒞.ob) (δ : 𝒟.Hom[ G , F ⟅ Z ⟆ ]) where
      w : GlCCC.ob
      w = (G , Z) , δ

      γW : 𝒟.Hom[ 𝒟._×_ G A , F ⟅ 𝒞._×_ Z X ⟆ ]
      γW = ImgOb._,p_ Z X
        (𝒟.π₁ {a = G} {b = A} 𝒟.⋆ δ)
        (𝒟.π₂ {a = G} {b = A} 𝒟.⋆ α)

      module _ (m : GlCCC [ bpGlCCC (w , u) .vertex , v ]) where
        private
          mD = m .fst .fst
          mC = m .fst .snd

          nC : 𝒞.Hom[ Z , W ]
          nC = 𝒞.lda {c = X} {d = Y} mC

          key : γW 𝒟.⋆ F ⟪ ExpC.pl nC ⟫
            ≡ ImgOb._,p_ W X
                (𝒟.π₁ {a = G} {b = A} 𝒟.⋆ (δ 𝒟.⋆ F ⟪ nC ⟫))
                (𝒟.π₂ {a = G} {b = A} 𝒟.⋆ α)
          key = ImgOb.,p-extensionality W X
            ( 𝒟.⋆Assoc _ _ _
            ∙ cong (γW 𝒟.⋆_)
                (sym (F .F-seq _ _) ∙ cong (F .F-hom) 𝒞.×β₁
                 ∙ F .F-seq _ _)
            ∙ sym (𝒟.⋆Assoc _ _ _)
            ∙ cong (𝒟._⋆ F ⟪ nC ⟫) (ImgOb.×β₁ Z X)
            ∙ 𝒟.⋆Assoc _ _ _
            ∙ sym (ImgOb.×β₁ W X))
            ( 𝒟.⋆Assoc _ _ _
            ∙ cong (γW 𝒟.⋆_)
                (sym (F .F-seq _ _) ∙ cong (F .F-hom) 𝒞.×β₂)
            ∙ ImgOb.×β₂ Z X
            ∙ sym (ImgOb.×β₂ W X))

          lhsAt : ExpD.appOf (𝒟.lda {c = A} {d = B} mD 𝒟.⋆ φ) ≡ mD 𝒟.⋆ β
          lhsAt =
              ExpD.appOfSeq (𝒟.lda {c = A} {d = B} mD) φ
            ∙ cong (ExpD.pl (𝒟.lda {c = A} {d = B} mD) 𝒟.⋆_) appφ
            ∙ sym (𝒟.⋆Assoc _ _ _)
            ∙ cong (𝒟._⋆ β) (ExpD.ldaβ mD)

          rhsAt : ExpD.appOf ((δ 𝒟.⋆ F ⟪ nC ⟫) 𝒟.⋆ ψ) ≡ mD 𝒟.⋆ β
          rhsAt =
              ExpD.appOfSeq (δ 𝒟.⋆ F ⟪ nC ⟫) ψ
            ∙ cong (ExpD.pl (δ 𝒟.⋆ F ⟪ nC ⟫) 𝒟.⋆_) appψ
            ∙ sym (𝒟.⋆Assoc _ _ _)
            ∙ cong (𝒟._⋆ F ⟪ 𝒞.app {c = X} {d = Y} ⟫)
                ( imgSeq (ExpD.pl (δ 𝒟.⋆ F ⟪ nC ⟫)) _ _
                ∙ ImgOb.⟨_⟩,p⟨_⟩ W X 𝒟.×β₁
                    (sym (𝒟.⋆Assoc _ _ _) ∙ cong (𝒟._⋆ α) 𝒟.×β₂)
                ∙ sym key)
            ∙ 𝒟.⋆Assoc _ _ _
            ∙ cong (γW 𝒟.⋆_)
                (sym (F .F-seq _ _) ∙ cong (F .F-hom) (ExpC.ldaβ mC))
            ∙ m .snd

          agree : 𝒟.lda {c = A} {d = B} mD 𝒟.⋆ φ
            ≡ (δ 𝒟.⋆ F ⟪ nC ⟫) 𝒟.⋆ ψ
          agree = ExpD.ldaExt (lhsAt ∙ sym rhsAt)

        ldaGl : GlCCC [ w , expOb ]
        ldaGl =
          ( Ep.pbIntro (𝒟.lda {c = A} {d = B} mD) (δ 𝒟.⋆ F ⟪ nC ⟫) agree
          , nC )
          , sym Ep.pbβ₂

      πw : GlCCC [ bpGlCCC (w , u) .vertex , w ]
      πw = ×GlCCC.π₁ {a = w} {b = u}

      πu : GlCCC [ bpGlCCC (w , u) .vertex , u ]
      πu = ×GlCCC.π₂ {a = w} {b = u}

      pull : GlCCC [ w , expOb ]
        → GlCCC [ bpGlCCC (w , u) .vertex , bpGlCCC (expOb , u) .vertex ]
      pull l = ×GlCCC._,p_ {a = expOb} {b = u} (πw GlCCC.⋆ l) πu

      pullD : (l : GlCCC [ w , expOb ])
        → pull l .fst .fst ≡ ExpD.pl (l .fst .fst)
      pullD l = 𝒟.,p-extensionality
        ( cong (λ n → n .fst .fst) (×GlCCC.×β₁ {a = expOb} {b = u}
            {f = πw GlCCC.⋆ l} {g = πu})
        ∙ sym 𝒟.×β₁)
        ( cong (λ n → n .fst .fst) (×GlCCC.×β₂ {a = expOb} {b = u}
            {f = πw GlCCC.⋆ l} {g = πu})
        ∙ sym 𝒟.×β₂)

      pullC : (l : GlCCC [ w , expOb ])
        → pull l .fst .snd ≡ ExpC.pl (l .fst .snd)
      pullC l = 𝒞.,p-extensionality
        ( cong (λ n → n .fst .snd) (×GlCCC.×β₁ {a = expOb} {b = u}
            {f = πw GlCCC.⋆ l} {g = πu})
        ∙ sym 𝒞.×β₁)
        ( cong (λ n → n .fst .snd) (×GlCCC.×β₂ {a = expOb} {b = u}
            {f = πw GlCCC.⋆ l} {g = πu})
        ∙ sym 𝒞.×β₂)

      secGl : (m : GlCCC [ bpGlCCC (w , u) .vertex , v ])
        → pull (ldaGl m) GlCCC.⋆ appGl ≡ m
      secGl m = Σ≡Prop (λ _ → 𝒟.isSetHom _ _)
        (ΣPathP
          ( cong (𝒟._⋆ appD) (pullD (ldaGl m))
            ∙ sym (ExpD.appOfSeq _ Ep.pbπ₁)
            ∙ cong ExpD.appOf Ep.pbβ₁
            ∙ ExpD.ldaβ (m .fst .fst)
          , cong (𝒞._⋆ 𝒞.app {c = X} {d = Y}) (pullC (ldaGl m))
            ∙ ExpC.ldaβ (m .fst .snd)))

      retGl : (l : GlCCC [ w , expOb ]) → ldaGl (pull l GlCCC.⋆ appGl) ≡ l
      retGl l = Σ≡Prop (λ _ → 𝒟.isSetHom _ _) (ΣPathP (dPart , cPart))
        where
        cPart : ldaGl (pull l GlCCC.⋆ appGl) .fst .snd ≡ l .fst .snd
        cPart = cong (𝒞.lda {c = X} {d = Y})
                  ( cong (𝒞._⋆ 𝒞.app {c = X} {d = Y}) (pullC l))
              ∙ ExpC.ldaExt (ExpC.ldaβ (ExpC.appOf (l .fst .snd)))

        dPart : ldaGl (pull l GlCCC.⋆ appGl) .fst .fst ≡ l .fst .fst
        dPart = Ep.pbExtensionality
          ( Ep.pbβ₁
          ∙ cong (𝒟.lda {c = A} {d = B})
              ( cong (𝒟._⋆ appD) (pullD l)
              ∙ sym (ExpD.appOfSeq (l .fst .fst) Ep.pbπ₁))
          ∙ ExpD.ldaExt (ExpD.ldaβ _))
          ( Ep.pbβ₂
          ∙ cong (λ z → δ 𝒟.⋆ F ⟪ z ⟫) cPart
          ∙ l .snd)

    ue : Exponential GlCCC u v (λ d → bpGlCCC (d , u))
    ue .vertex = expOb
    ue .element = appGl
    ue .universal ((G , Z) , δ) =
      isoToIsEquiv (iso _ (At.ldaGl G Z δ) (At.secGl G Z δ)
        (At.retGl G Z δ))
