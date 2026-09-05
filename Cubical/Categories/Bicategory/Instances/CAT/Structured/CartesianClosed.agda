{-# OPTIONS --lossy-unification #-}
{- The bicategory of cartesian closed categories -}
module
  Cubical.Categories.Bicategory.Instances.CAT.Structured.CartesianClosed
  where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation hiding (_⇒_)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Exponentials.Small
open import Cubical.Categories.Presheaf.Constructions hiding (π₁; π₂)
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Displayed
open import Cubical.Categories.Bicategory.Displayed.Constructions.StructureOver
open import Cubical.Categories.Bicategory.Displayed.Constructions.Total
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Instances.CAT.Structured.Terminal
open import Cubical.Categories.Bicategory.Instances.CAT.Structured.Cartesian

private
  variable
    ℓ ℓ' : Level

open UniversalElement
open PshHom

-- Cartesian closed structure on a category.
module _ (C : Category ℓ ℓ') where
  CartesianClosedStr : Type (ℓ-max ℓ ℓ')
  CartesianClosedStr =
    Σ[ cart ∈ CartesianStr C ] AllExponentiable C (cart .snd)

{-
  Comparison data for a functor preserving the chosen binary products
  with a fixed object c: the image universal elements, the inverse
  comparison maps `comp⁻¹`, their β laws, and the naturality square
  relating the functorial actions of `- × c` and `- × F c`.
-}
module ProdComparison {ℓ ℓ' : Level} {C D : Category ℓ ℓ'} (F : Functor C D)
  (bpC : BinProducts C) (bpD : BinProducts D)
  (Fp : preservesProvidedBinProducts F bpC)
  (c : Category.ob C)
  where
  private
    module C = Category C
    module D = Category D
    module F = Functor F

  -×c : LocallyRepresentable (C [-, c ])
  -×c Γ = bpC (Γ , c)

  -×Fc : LocallyRepresentable (D [-, F.F-ob c ])
  -×Fc Δ = bpD (Δ , F.F-ob c)

  ×cF : Functor C C
  ×cF = LRPsh→Functor ((C [-, c ]) , -×c)

  ×FcF : Functor D D
  ×FcF = LRPsh→Functor ((D [-, F.F-ob c ]) , -×Fc)

  module ×c Γ = UniversalElementNotation (-×c Γ)
  module ×Fc Δ = UniversalElementNotation (-×Fc Δ)

  -- the chosen projections
  π₁c : ∀ Γ → C [ ×c.vertex Γ , Γ ]
  π₁c Γ = -×c Γ .element .fst

  π₂c : ∀ Γ → C [ ×c.vertex Γ , c ]
  π₂c Γ = -×c Γ .element .snd

  π₁Fc : ∀ Δ → D [ ×Fc.vertex Δ , Δ ]
  π₁Fc Δ = -×Fc Δ .element .fst

  π₂Fc : ∀ Δ → D [ ×Fc.vertex Δ , F.F-ob c ]
  π₂Fc Δ = -×Fc Δ .element .snd

  -- β laws for the functorial actions
  ×cFβ₁ : ∀ {Δ Γ} (γ : C [ Δ , Γ ])
    → ×cF ⟪ γ ⟫ C.⋆ π₁c Γ ≡ π₁c Δ C.⋆ γ
  ×cFβ₁ = πLRF ((C [-, c ]) , -×c) .NatTrans.N-hom

  ×cFβ₂ : ∀ {Δ Γ} (γ : C [ Δ , Γ ])
    → ×cF ⟪ γ ⟫ C.⋆ π₂c Γ ≡ π₂c Δ
  ×cFβ₂ {Δ} {Γ} γ = cong snd (×c.β Γ)

  ×FcFβ₁ : ∀ {Δ Γ} (δ : D [ Δ , Γ ])
    → ×FcF ⟪ δ ⟫ D.⋆ π₁Fc Γ ≡ π₁Fc Δ D.⋆ δ
  ×FcFβ₁ = πLRF ((D [-, F.F-ob c ]) , -×Fc) .NatTrans.N-hom

  ×FcFβ₂ : ∀ {Δ Γ} (δ : D [ Δ , Γ ])
    → ×FcF ⟪ δ ⟫ D.⋆ π₂Fc Γ ≡ π₂Fc Δ
  ×FcFβ₂ {Δ} {Γ} δ = cong snd (×Fc.β Γ)

  -- the image of the chosen product, universal by assumption
  imgUE : ∀ Γ → BinProduct D (F.F-ob Γ , F.F-ob c)
  imgUE Γ = becomesUniversal→UniversalElement
    (preservesBinProdCones F Γ c) (Fp Γ c)

  module img Γ = UniversalElementNotation (imgUE Γ)

  -- the inverse comparison map F Γ ×Fc → F (Γ ×c)
  comp⁻¹ : ∀ Γ → D [ ×Fc.vertex (F.F-ob Γ) , F.F-ob (×c.vertex Γ) ]
  comp⁻¹ Γ = img.intro Γ (-×Fc (F.F-ob Γ) .element)

  comp⁻¹β₁ : ∀ Γ → comp⁻¹ Γ D.⋆ F.F-hom (π₁c Γ) ≡ π₁Fc (F.F-ob Γ)
  comp⁻¹β₁ Γ = cong fst (img.β Γ)

  comp⁻¹β₂ : ∀ Γ → comp⁻¹ Γ D.⋆ F.F-hom (π₂c Γ) ≡ π₂Fc (F.F-ob Γ)
  comp⁻¹β₂ Γ = cong snd (img.β Γ)

  -- naturality of the inverse comparison maps
  key-square : ∀ {Δ Γ} (γ : C [ Δ , Γ ])
    → comp⁻¹ Δ D.⋆ F.F-hom (×cF ⟪ γ ⟫) ≡ ×FcF ⟪ F.F-hom γ ⟫ D.⋆ comp⁻¹ Γ
  key-square {Δ} {Γ} γ = img.extensionality Γ (ΣPathP
    ( ( D.⋆Assoc _ _ _
      ∙ D.⟨ refl ⟩⋆⟨ sym (F.F-seq _ _)
                     ∙ cong F.F-hom (×cFβ₁ γ)
                     ∙ F.F-seq _ _ ⟩
      ∙ sym (D.⋆Assoc _ _ _)
      ∙ D.⟨ comp⁻¹β₁ Δ ⟩⋆⟨ refl ⟩ )
      ∙ sym
      ( D.⋆Assoc _ _ _
      ∙ D.⟨ refl ⟩⋆⟨ comp⁻¹β₁ Γ ⟩
      ∙ ×FcFβ₁ (F.F-hom γ) )
    , ( D.⋆Assoc _ _ _
      ∙ D.⟨ refl ⟩⋆⟨ sym (F.F-seq _ _)
                     ∙ cong F.F-hom (×cFβ₂ γ) ⟩
      ∙ comp⁻¹β₂ Δ )
      ∙ sym
      ( D.⋆Assoc _ _ _
      ∙ D.⟨ refl ⟩⋆⟨ comp⁻¹β₂ Γ ⟩
      ∙ ×FcFβ₂ (F.F-hom γ) )
    ))

-- The comparison heteromorphism between the chosen exponential
-- presheaves, for a functor preserving the chosen binary products.
module _ {ℓ ℓ' : Level} {C D : Category ℓ ℓ'} (F : Functor C D)
  (bpC : BinProducts C) (bpD : BinProducts D)
  (Fp : preservesProvidedBinProducts F bpC)
  (c d : Category.ob C)
  where
  private
    module D = Category D
    module F = Functor F
    open ProdComparison F bpC bpD Fp c

  ⇒PshSmallHet :
    PshHet F
      (((C [-, c ]) , (λ Γ → bpC (Γ , c))) ⇒PshSmall (C [-, d ]))
      (((D [-, F ⟅ c ⟆ ]) , (λ Δ → bpD (Δ , F ⟅ c ⟆))) ⇒PshSmall
        (D [-, F ⟅ d ⟆ ]))
  ⇒PshSmallHet .N-ob Γ e = comp⁻¹ Γ D.⋆ F.F-hom e
  ⇒PshSmallHet .N-hom Δ Γ γ e =
    D.⟨ refl ⟩⋆⟨ F.F-seq _ _ ⟩
    ∙ sym (D.⋆Assoc _ _ _)
    ∙ D.⟨ key-square γ ⟩⋆⟨ refl ⟩
    ∙ D.⋆Assoc _ _ _

-- Preservation of the chosen exponentials by a strict functor that
-- preserves the chosen binary products (a prop).
module _ {C D : Category ℓ ℓ'} (F : Functor C D)
  {bpC : BinProducts C} (bpD : BinProducts D)
  (expsC : AllExponentiable C bpC)
  (Fp : preservesProvidedBinProducts F bpC)
  where
  preservesExponentials : Type (ℓ-max ℓ ℓ')
  preservesExponentials = ∀ c d →
    preservesUniversalElement
      (⇒PshSmallHet F bpC bpD Fp c d)
      (expsC c d)

-- The 1-cell structure: preservation of all of the cartesian closed
-- structure.
module _ {C D : Category ℓ ℓ'} (F : Functor C D)
  (strC : CartesianClosedStr C) (strD : CartesianClosedStr D) where
  preservesCartesianClosedStr : Type (ℓ-max ℓ ℓ')
  preservesCartesianClosedStr =
    Σ[ pres-cart ∈ preservesCartesianStr F (strC .fst) (strD .fst) ]
      preservesExponentials F (strD .fst .snd) (strC .snd) (pres-cart .snd)

-- Closure under identity: the identity's image universal elements are
-- definitionally the chosen products themselves, so the comparison
-- map is the intro of the product's own element, i.e. the identity by
-- weak-η.
module _ {C : Category ℓ ℓ'} {bpC : BinProducts C}
  (expsC : AllExponentiable C bpC) where
  private
    module C = Category C

  idPreservesExponentials :
    preservesExponentials (Id {C = C}) bpC expsC
      (idPreservesBinProducts bpC)
  idPreservesExponentials c d =
    veryStrictlyPreservesUniversalElement
      (⇒PshSmallHet Id bpC bpC (idPreservesBinProducts bpC) c d)
      (expsC c d)
      (expsC c d .element)
      (expsC c d .universal)
      (sym (C.⋆IdL _) ∙ C.⟨ ue.weak-η ⟩⋆⟨ refl ⟩)
    where
    module ue = UniversalElementNotation (bpC (expsC c d .vertex , c))

-- Closure under composition: transfer the preservation of the image
-- exponential through the second functor's comparison, then identify
-- the composite comparison map with the composite's comparison map.
module _ {C D E : Category ℓ ℓ'} {F : Functor C D} {G : Functor D E}
  {bpC : BinProducts C} {bpD : BinProducts D} {bpE : BinProducts E}
  {expsC : AllExponentiable C bpC} {expsD : AllExponentiable D bpD}
  (Fp : preservesProvidedBinProducts F bpC)
  (Gp : preservesProvidedBinProducts G bpD)
  where
  private
    module E = Category E
    module F = Functor F
    module G = Functor G

  compPreservesExponentials :
    preservesExponentials F bpD expsC Fp
    → preservesExponentials G bpE expsD Gp
    → preservesExponentials (G ∘F F) bpE expsC
        (compPreservesBinProducts {F = F} {G = G} {bpC = bpC} {bpD = bpD}
          Fp Gp)
  compPreservesExponentials Fe Ge c d =
    substIsUniversal _
      (preservesUniversalElement→PreservesUniversalElements
        (⇒PshSmallHet G bpD bpE Gp (F.F-ob c) (F.F-ob d))
        (expsD (F.F-ob c) (F.F-ob d))
        (Ge (F.F-ob c) (F.F-ob d))
        (becomesUniversal→UniversalElement
          (⇒PshSmallHet F bpC bpD Fp c d)
          (Fe c d)))
      ( E.⟨ refl ⟩⋆⟨ G.F-seq _ _ ⟩
      ∙ sym (E.⋆Assoc _ _ _)
      ∙ E.⟨ sym (comp⁻¹-comp (expsC c d .vertex)) ⟩⋆⟨ refl ⟩ )
    where
    module PF = ProdComparison F bpC bpD Fp c
    module PG = ProdComparison G bpD bpE Gp (F.F-ob c)
    module PGF = ProdComparison (G ∘F F) bpC bpE
      (compPreservesBinProducts {F = F} {G = G} {bpC = bpC} {bpD = bpD}
        Fp Gp)
      c

    -- the inverse comparison maps compose
    comp⁻¹-comp : ∀ Γ
      → PGF.comp⁻¹ Γ ≡ PG.comp⁻¹ (F.F-ob Γ) E.⋆ G.F-hom (PF.comp⁻¹ Γ)
    comp⁻¹-comp Γ = PGF.img.extensionality Γ (ΣPathP
      ( PGF.comp⁻¹β₁ Γ
        ∙ sym
        ( E.⋆Assoc _ _ _
        ∙ E.⟨ refl ⟩⋆⟨ sym (G.F-seq _ _)
                       ∙ cong G.F-hom (PF.comp⁻¹β₁ Γ) ⟩
        ∙ PG.comp⁻¹β₁ (F.F-ob Γ) )
      , PGF.comp⁻¹β₂ Γ
        ∙ sym
        ( E.⋆Assoc _ _ _
        ∙ E.⟨ refl ⟩⋆⟨ sym (G.F-seq _ _)
                       ∙ cong G.F-hom (PF.comp⁻¹β₂ Γ) ⟩
        ∙ PG.comp⁻¹β₂ (F.F-ob Γ) )
      ))

module _ {ℓ ℓ' : Level} where
  open StructureOverᴮ

  private
    preservesCartesianClosedStr-cell : {C D : Category ℓ ℓ'}
      (F : Functor C D)
      → CartesianClosedStr C → CartesianClosedStr D
      → Type (ℓ-max ℓ ℓ')
    preservesCartesianClosedStr-cell = preservesCartesianClosedStr

  CartesianClosedStructure : StructureOverᴮ (CAT {ℓ} {ℓ'})
    (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  CartesianClosedStructure .ob[_] = CartesianClosedStr
  CartesianClosedStructure .1Cellᴰ[_][_,_] = preservesCartesianClosedStr-cell
  CartesianClosedStructure .id₁ᴰ {xᴰ = (term , bp) , exps} =
    (idPreservesTerminal' term , idPreservesBinProducts bp)
    , idPreservesExponentials exps
  CartesianClosedStructure ._⋆₁ᴰ_ {f = F} {g = G}
    {xᴰ = (termC , bpC) , expsC} {yᴰ = (termD , bpD) , expsD}
    {zᴰ = (termE , bpE) , expsE}
    ((Fpt , Fpb) , Fpe) ((Gpt , Gpb) , Gpe) =
    ( compPreservesTerminal' {F = F} {G = G} {termC = termC} {termD = termD}
        Fpt Gpt
    , compPreservesBinProducts {F = F} {G = G} {bpC = bpC} {bpD = bpD}
        Fpb Gpb )
    , compPreservesExponentials {F = F} {G = G} {bpC = bpC} {bpD = bpD}
        {bpE = bpE} {expsC = expsC} {expsD = expsD} Fpb Gpb Fpe Gpe

  -- The displayed bicategory of cartesian closed structure over
  -- CAT, and the bicategory of cartesian closed categories.
  CartesianClosedCATᴰ : Bicategoryᴰ (CAT {ℓ} {ℓ'}) _ _ _
  CartesianClosedCATᴰ = StructureOverᴮ→Bicategoryᴰ CartesianClosedStructure

  CartesianClosedCAT : Bicategory _ _ _
  CartesianClosedCAT = ∫ᴮ CartesianClosedCATᴰ
