{-
If a category C and D eacb have products/coproducts/exponentials, then the
product category C ×C D has products/coproducts/exponentials, respectively.

TODO This can likely be extended to any limit through a more general
argument, but it is unclear that this construction has nice
definitional properties.
-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Limits.ProductCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Constructions.BinProduct.Redundant.Base
  hiding (_×C_)
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinCoproduct
open import Cubical.Categories.Limits.Terminal hiding (hasTerminal)
open import Cubical.Categories.Limits.Initial hiding (hasInitial)
open import Cubical.Categories.Exponentials

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

-- TODO : Limits is a bad term here, as not each of these right
-- adjoints does come from a limit, but the naming is in line with
-- what Cubical upstream currently has
module productCategoryLimits
  (C : Category ℓC ℓC')
  (D : Category ℓD ℓD')
  where

  the-product : Category (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')
  the-product = C ×C D

  open BinProduct
  open Category
  open UniversalElement

  hasTerminal : Terminal C → Terminal D → Terminal the-product
  hasTerminal tC tD .fst = (tC .fst) , (tD .fst)
  hasTerminal tC tD .snd y .fst =
    (tC .snd (y .fst) .fst) , (tD .snd (y .snd) .fst)
  hasTerminal tC tD .snd y .snd y₁ =
    ΣPathP (
      (tC .snd (y .fst) .snd (y₁ .fst)) ,
      ((tD .snd (y .snd) .snd (y₁ .snd)))
    )

  hasInitial : Initial C → Initial D → Initial the-product
  hasInitial iC iD .fst = iC .fst , iD .fst
  hasInitial iC iD .snd y .fst = iC .snd (y .fst) .fst , iD .snd (y .snd) .fst
  hasInitial iC iD .snd y .snd y₁ =
    ΣPathP (
      (iC .snd (y .fst) .snd (y₁ .fst)) ,
      iD .snd (y .snd) .snd (y₁ .snd)
    )

  hasProducts : BinProducts C →
                       BinProducts D →
                       BinProducts the-product
  hasProducts bpC bpD (c , d) (c' , d') .binProdOb =
    bpC c c' .binProdOb , bpD d d' .binProdOb
  hasProducts bpC bpD (c , d) (c' , d') .binProdPr₁ =
    bpC c c' .binProdPr₁ , bpD d d' .binProdPr₁
  hasProducts bpC bpD (c , d) (c' , d') .binProdPr₂ =
    bpC c c' .binProdPr₂ , bpD d d' .binProdPr₂
  hasProducts bpC bpD (c , d) (c' , d')
    .univProp (f , g) (f' , g') =
    let cUniv = bpC c c' .univProp f f'
        dUniv = bpD d d' .univProp g g'
    in
    (((cUniv .fst .fst) ,
      (dUniv .fst .fst)) ,
      (ΣPathP (cUniv .fst .snd .fst ,
               dUniv .fst .snd .fst) ,
      ΣPathP (cUniv .fst .snd .snd ,
             dUniv .fst .snd .snd))) ,
      λ y → Σ≡Prop
        (λ _ → isProp× (the-product .isSetHom _ _)
                       (the-product .isSetHom _ _))
        (
          ΣPathP
            (cong fst (cUniv .snd (
              (y .fst .fst) ,
              cong fst (y .snd .fst) ,
              cong fst (y .snd .snd))
              ) ,
            cong fst (dUniv .snd (
              (y .fst .snd) ,
              (cong snd (y .snd .fst) ,
              cong snd (y .snd .snd)))))
        )

  hasExponentials :
    (bpC : BinProducts C) → (bpD : BinProducts D) →
    Exponentials C bpC → Exponentials D bpD →
    Exponentials the-product (hasProducts bpC bpD)
  hasExponentials bpC bpD expC expD x .vertex =
    expC (x .fst .fst , x .snd .fst) .vertex ,
    expD (x .fst .snd , x .snd .snd) .vertex
  hasExponentials bpC bpD expC expD x .element =
    (expC (x .fst .fst , (x .snd .fst)) .element) ,
    (expD (x .fst .snd , (x .snd .snd)) .element)
  hasExponentials bpC bpD expC expD x
    .universal A .equiv-proof y =
    let
    cEquivProof = expC ((x .fst .fst) , (x .snd .fst)) .universal
          (A .fst) .equiv-proof (y .fst)
    dEquivProof = expD (x .fst .snd , x .snd .snd) .universal
          (A .snd) .equiv-proof (y .snd)
    in
    (((cEquivProof .fst .fst) , (dEquivProof .fst .fst)) ,
    ΣPathP ((cEquivProof .fst .snd) , (dEquivProof .fst .snd))
    ),
    λ z →
      Σ≡Prop
        (λ _ → the-product .isSetHom _ _)
        (ΣPathP (
          (cong fst (cEquivProof .snd ((z .fst .fst) ,
            (cong fst (z .snd))))) ,
        cong fst (dEquivProof .snd ((z .fst .snd) ,
          (cong snd (z .snd))))))

  open BinCoproduct

  hasCoproducts :
    BinCoproducts C → BinCoproducts D → BinCoproducts the-product
  hasCoproducts cpC cpD x y .binCoprodOb .fst =
    cpC (x .fst) (y .fst) .binCoprodOb
  hasCoproducts cpC cpD x y .binCoprodOb .snd =
    cpD (x .snd) (y .snd) .binCoprodOb
  hasCoproducts cpC cpD x y .binCoprodInj₁ .fst =
    cpC (x .fst) (y .fst) .binCoprodInj₁
  hasCoproducts cpC cpD x y .binCoprodInj₁ .snd =
    cpD (x .snd) (y .snd) .binCoprodInj₁
  hasCoproducts cpC cpD x y .binCoprodInj₂ .fst =
    cpC (x .fst) (y .fst) .binCoprodInj₂
  hasCoproducts cpC cpD x y .binCoprodInj₂ .snd =
    cpD (x .snd) (y .snd) .binCoprodInj₂
  hasCoproducts cpC cpD x y .univProp f₁ f₂ .fst .fst .fst =
    cpC (x .fst) (y .fst) .univProp (f₁ .fst) (f₂ .fst) .fst .fst
  hasCoproducts cpC cpD x y .univProp f₁ f₂ .fst .fst .snd =
    cpD (x .snd) (y .snd) .univProp (f₁ .snd) (f₂ .snd) .fst .fst
  hasCoproducts cpC cpD x y .univProp f₁ f₂ .fst .snd .fst =
    ΣPathP (
      (cpC (x .fst) (y .fst) .univProp (f₁ .fst) (f₂ .fst) .fst .snd .fst) ,
      (cpD (x .snd) (y .snd) .univProp (f₁ .snd) (f₂ .snd) .fst .snd .fst)
    )
  hasCoproducts cpC cpD x y .univProp f₁ f₂ .fst .snd .snd =
    ΣPathP (
      (cpC (x .fst) (y .fst) .univProp (f₁ .fst) (f₂ .fst) .fst .snd .snd) ,
      (cpD (x .snd) (y .snd) .univProp (f₁ .snd) (f₂ .snd) .fst .snd .snd)
    )
  hasCoproducts cpC cpD x y .univProp f₁ f₂ .snd y₁ =
    Σ≡Prop
      (λ s a b → isProp× (the-product .isSetHom _ _)
                         (the-product .isSetHom _ _) a b)
    (ΣPathP (
    cong fst (cpC (x .fst) (y .fst) .univProp (f₁ .fst) (f₂ .fst) .snd
      (y₁ .fst .fst , (cong fst (y₁ .snd .fst)) , (cong fst (y₁ .snd .snd)))) ,
    cong fst (cpD (x .snd) (y .snd) .univProp (f₁ .snd) (f₂ .snd) .snd
      ((y₁ .fst .snd) , ((cong snd (y₁ .snd .fst)) ,
        (cong snd (y₁ .snd .snd)))))
      ))
