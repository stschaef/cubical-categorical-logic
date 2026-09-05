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
open import Cubical.Categories.Exponentials.Small
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import
  Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialD

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
      module CS = Category C
      module GlC = Categoryᴰ Glᴰ

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


    -- The displayed product's `introᴰ` computes: it is the pair of
    -- the two function components.  Proving this is what lets the
    -- exponential's round trips reduce.
    private
      ProdFam : {Z X Y : C .ob} (Γᴰ : Glᴰ .ob[_] Z)
        (Aᴰ : Glᴰ .ob[_] X) (Bᴰ : Glᴰ .ob[_] Y)
        → (C [ Z , X ] × C [ Z , Y ]) → Type ℓs
      ProdFam Γᴰ Aᴰ Bᴰ fg =
        Glᴰ [ fg .fst ][ Γᴰ , Aᴰ ] × Glᴰ [ fg .snd ][ Γᴰ , Bᴰ ]

      prodReind₁ : {Z X Y : C .ob} (Γᴰ : Glᴰ .ob[_] Z)
        (Aᴰ : Glᴰ .ob[_] X) (Bᴰ : Glᴰ .ob[_] Y)
        {fg fg' : C [ Z , X ] × C [ Z , Y ]} {e : fg ≡ fg'}
        (q : ProdFam Γᴰ Aᴰ Bᴰ fg)
        → depReasoning.reind (ProdFam Γᴰ Aᴰ Bᴰ) e q .fst .fst
        ≡ q .fst .fst
      prodReind₁ Γᴰ Aᴰ Bᴰ {e = e} q = sym (cong (λ z → z .snd .fst .fst)
        (depReasoning.reind-filler (ProdFam Γᴰ Aᴰ Bᴰ) {p = q} e))

      prodReind₂ : {Z X Y : C .ob} (Γᴰ : Glᴰ .ob[_] Z)
        (Aᴰ : Glᴰ .ob[_] X) (Bᴰ : Glᴰ .ob[_] Y)
        {fg fg' : C [ Z , X ] × C [ Z , Y ]} {e : fg ≡ fg'}
        (q : ProdFam Γᴰ Aᴰ Bᴰ fg)
        → depReasoning.reind (ProdFam Γᴰ Aᴰ Bᴰ) e q .snd .fst
        ≡ q .snd .fst
      prodReind₂ Γᴰ Aᴰ Bᴰ {e = e} q = sym (cong (λ z → z .snd .snd .fst)
        (depReasoning.reind-filler (ProdFam Γᴰ Aᴰ Bᴰ) {p = q} e))

    glBpIntroFst : {Z X Y : C .ob} (Γᴰ : Glᴰ .ob[_] Z)
      (Aᴰ : Glᴰ .ob[_] X) (Bᴰ : Glᴰ .ob[_] Y)
      {fg : C [ Z , X ] × C [ Z , Y ]} {q : ProdFam Γᴰ Aᴰ Bᴰ fg}
      → glBpᴰ Aᴰ Bᴰ .snd .snd Z Γᴰ .inv fg q .fst
      ≡ (λ e → q .fst .fst e , q .snd .fst e)
    glBpIntroFst Γᴰ Aᴰ Bᴰ {fg} {q} = funExt λ e → ΣPathP
      ( funExt⁻ (prodReind₁ Γᴰ Aᴰ Bᴰ q) e
      , funExt⁻ (prodReind₂ Γᴰ Aᴰ Bᴰ q) e)

    -- the Artin exponential, forded over the syntax: pairs `(h , k)`
    -- of a function and a point of `F (X ⇒ Y)` that are related
    module _ (expC : AllExponentiable C bpC) where
      private
        module ⇒S = ExponentialsNotation bpC expC
        module ⇒ueS (c d : C .ob) =
          ExponentialNotation.⇒ue (λ d' → bpC (d' , c)) (expC c d)
        tappD = tapp F bpC expC Fp
        tappNatD = tappNat F bpC expC Fp

      glExpᴰ : AllExponentiableᴰ Glᴰ bpC glBpᴰ expC
      glExpᴰ {X} (A , α) {Y} (B , β) = expVertex , appElt , univ
        where
        W : C .ob
        W = ⇒S._⇒_ X Y

        Rel : (⟨ A ⟩ → ⟨ B ⟩) → ⟨ F ⟅ W ⟆ ⟩ → Type ℓs
        Rel h k = (x : ⟨ A ⟩) → β (h x) ≡ tappD k (α x)

        Eset : hSet ℓs
        Eset =
          (Σ[ h ∈ (⟨ A ⟩ → ⟨ B ⟩) ] Σ[ k ∈ ⟨ F ⟅ W ⟆ ⟩ ] Rel h k)
          , isSetΣ (isSetΠ λ _ → B .snd)
              (λ h → isSetΣ ((F ⟅ W ⟆) .snd)
                (λ k → isProp→isSet (isPropΠ λ _ → (F ⟅ Y ⟆) .snd _ _)))

        γE : ⟨ Eset ⟩ → ⟨ F ⟅ W ⟆ ⟩
        γE e = e .snd .fst

        expVertex : Glᴰ .ob[_] W
        expVertex = Eset , γE

        appElt : Glᴰ [ ⇒S.app ][ glBpᴰ expVertex (A , α) .fst , (B , β) ]
        appElt = (λ p → p .fst .fst (p .snd))
               , λ p → sym (p .fst .snd .snd (p .snd))

        module _ (Z : C .ob) (E : hSet ℓs) (δ : ⟨ E ⟩ → ⟨ F ⟅ Z ⟆ ⟩)
          (a : C [ Z , W ]) where
          Γᴰ' : Glᴰ .ob[_] Z
          Γᴰ' = E , δ

          pi1 : C [ ×S._×_ Z X , Z ]
          pi1 = ×S.π₁ {a = Z} {b = X}

          pi2 : C [ ×S._×_ Z X , X ]
          pi2 = ×S.π₂ {a = Z} {b = X}

          bpZA = glBpᴰ {Z} {X} Γᴰ' (A , α)
          bpWA = glBpᴰ {W} {X} expVertex (A , α)

          prodᴰ : Glᴰ .ob[_] (×S._×_ Z X)
          prodᴰ = bpZA .fst

          invAt : {m : C [ ×S._×_ Z X , Y ]} → ⇒S.lda m ≡ a
            → Glᴰ [ m ][ prodᴰ , (B , β) ]
            → Glᴰ [ a ][ Γᴰ' , expVertex ]
          invAt {m} meq mᴰ =
            (λ e → (λ x → mᴰ .fst (e , x))
                  , (F ⟪ a ⟫) (δ e)
                  , λ x → sym (mᴰ .snd (e , x))
                        ∙ tappNatD m (δ e) (α x)
                        ∙ cong (λ n → tappD ((F ⟪ n ⟫) (δ e)) (α x)) meq)
            , λ e → refl

          pullq : Glᴰ [ a ][ Γᴰ' , expVertex ]
            → ProdFam prodᴰ expVertex (A , α) (pi1 CS.⋆ a , pi2)
          pullq hᴰ =
            GlC._⋆ᴰ_ {x = ×S._×_ Z X} {y = Z} {z = W} {f = pi1} {g = a}
              {xᴰ = prodᴰ} {yᴰ = Γᴰ'} {zᴰ = expVertex}
              (bpZA .snd .fst .fst) hᴰ
            , bpZA .snd .fst .snd

          -- the presheafᴰ action, once its `introᴰ` is computed
          actFst : (hᴰ : Glᴰ [ a ][ Γᴰ' , expVertex ])
            → GlC._⋆ᴰ_ {x = ×S._×_ Z X} {y = ×S._×_ W X} {z = Y}
                {f = ×S._,p_ (pi1 CS.⋆ a) pi2} {g = ⇒S.app}
                {xᴰ = prodᴰ} {yᴰ = bpWA .fst} {zᴰ = B , β}
                (bpWA .snd .snd (×S._×_ Z X) prodᴰ
                  .inv (pi1 CS.⋆ a , pi2) (pullq hᴰ))
                appElt .fst
            ≡ (λ p → (hᴰ .fst (p .fst)) .fst (p .snd))
          actFst hᴰ = cong postApp
            (glBpIntroFst prodᴰ expVertex (A , α)
              {fg = pi1 CS.⋆ a , pi2} {q = pullq hᴰ})
            where
            postApp : (⟨ prodᴰ .fst ⟩ → ⟨ bpWA .fst .fst ⟩)
              → ⟨ prodᴰ .fst ⟩ → ⟨ B ⟩
            postApp u p = appElt .fst (u p)

        univ = λ Z (E , δ) → fiberwiseIsoOver→IsoOver _
          (λ a → (λ mᴰ → invAt Z E δ a (sym (⇒ueS.η X Y {Z} {a})) mᴰ)
                , (λ mᴰ → Σ≡Prop
                    (λ _ → isPropΠ λ _ → (F ⟅ _ ⟆) .snd _ _)
                    ( reindFst {xᴰ = prodᴰ Z E δ a} {yᴰ = B , β}
                    ∙ actFst Z E δ a
                        (invAt Z E δ a (sym (⇒ueS.η X Y {Z} {a})) mᴰ)))
                , (λ hᴰ → Σ≡Prop
                    (λ _ → isPropΠ λ _ → (F ⟅ _ ⟆) .snd _ _)
                    (funExt λ e → ΣPathP
                      ( funExt (λ x → funExt⁻
                          ( reindFst {xᴰ = prodᴰ Z E δ a} {yᴰ = B , β}
                          ∙ actFst Z E δ a hᴰ) (e , x))
                      , ΣPathP (hᴰ .snd e , isProp→PathP
                          (λ _ → isPropΠ λ _ → (F ⟅ Y ⟆) .snd _ _)
                          _ _)))))
          (C .isSetHom) (C .isSetHom)
