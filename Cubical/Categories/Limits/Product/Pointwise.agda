{-
If a category C and D eacb have products/exponentials, then the
product category C ×C D has products/exponentials, respectively.

TODO This can likely be extended to any limit through a more general
argument, but it is unclear that this construction has nice
definitional properties.
-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.Product.Pointwise where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Constructions.BinProduct.Redundant.Base hiding (_×C_)
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Exponentials

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _
  (C : Category ℓC ℓC')
  (D : Category ℓD ℓD')
  where

  the-product : Category (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')
  the-product = C ×C D

  open BinProduct
  open Category
  open UniversalElement

  productHasProducts : BinProducts C →
                       BinProducts D →
                       BinProducts the-product
  productHasProducts bpC bpD (c , d) (c' , d') .binProdOb =
    bpC c c' .binProdOb , bpD d d' .binProdOb
  productHasProducts bpC bpD (c , d) (c' , d') .binProdPr₁ =
    bpC c c' .binProdPr₁ , bpD d d' .binProdPr₁
  productHasProducts bpC bpD (c , d) (c' , d') .binProdPr₂ =
    bpC c c' .binProdPr₂ , bpD d d' .binProdPr₂
  productHasProducts bpC bpD (c , d) (c' , d')
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

  productHasExponentials :
    (bpC : BinProducts C) → (bpD : BinProducts D) →
    Exponentials C bpC → Exponentials D bpD →
    Exponentials the-product (productHasProducts bpC bpD)
  productHasExponentials bpC bpD expC expD x .vertex =
    expC (x .fst .fst , x .snd .fst) .vertex ,
    expD (x .fst .snd , x .snd .snd) .vertex
  productHasExponentials bpC bpD expC expD x .element =
    (expC (x .fst .fst , (x .snd .fst)) .element) ,
    (expD (x .fst .snd , (x .snd .snd)) .element)
  productHasExponentials bpC bpD expC expD x
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
