{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.BinProduct.ProductOfSets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
import Cubical.Categories.Constructions.BinProduct.Redundant.Base as R
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Bifunctor.Base
import Cubical.Categories.Bifunctor.Redundant as R

open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Instances.Sets
open import Cubical.Data.Unit

private
  variable
    ℓ ℓ' : Level

open Iso
open UnivElt
open isUniversal
open BinProduct
open Category
open Functor


module _ (ℓS : Level)
  where

  bp : BinProducts (SET ℓS)
  bp = λ x y →
    record {
    binProdOb = x .fst Cubical.Data.Sigma.× y .fst , λ p q e₁ e₂ i →
      ΣPathP
      (x .snd (p .fst) (q .fst) (cong fst e₁) (cong fst e₂) i ,
      y .snd (p .snd) (q .snd) (cong snd e₁) (cong snd e₂) i
      );
    binProdPr₁ = fst ;
    binProdPr₂ = snd ;
    univProp =
    λ {z} p₁ p₂ →
      ((λ a → p₁ a , p₂ a) , refl , refl) ,
      λ (mor , fstMor≡p₁ , sndMor≡p₂) →
        let q = (λ i z₀ → fstMor≡p₁ (~ i) z₀ , sndMor≡p₂ (~ i) z₀)
        in
        Σ≡Prop (λ f →
          isProp× (isSetHom (SET ℓS) {z}{x} (λ x → fst (f x)) p₁)
                  (isSetHom (SET ℓS) {z}{y} (λ x → snd (f x)) p₂))
          q

        -- Σ≡Prop {!isPropIsBinProduct!} {!!}
        -- {!!}
        -- ΣPathP (
            -- q ,
            -- {!!}
            -- ΣPathP ((λ i → SET ℓS .isSetHom (fstMor≡p₁ (~ i)) p₁ (λ j → {!fstMor≡p₁ (~ j)!}) {!refl!} i) , {!!})
        -- )
          -- (funExt
            -- (λ a i → fstMor≡p₁ (~ i) a ,
                     -- sndMor≡p₂ (~ i) a) ,
            -- λ i → (funExt (λ a → {!fstMor≡p₁!})) , {!!}
          -- )

    }



  open Notation (SET ℓS) bp

  -- Want that product in the category of sets coincides with
  -- the type theoretic product
  prodIsΣ : (A B : (SET ℓS) .ob) →
      (A × B) .fst ≡ (A × B) .fst
  prodIsΣ = λ A B → refl

  -- Assuming prodIsΣ, we would also want π₁ ≡ fst and π₂ ≡ snd
  -- _ : (A B : (SET ℓS) .ob) →
  --     π₁ {a = A}{b = B} ≡ π₁
  -- _ = λ A B → refl

  -- _ : (A B : (SET ℓS) .ob) →
  --     π₂ {a = A}{b = B} ≡ π₂
  -- _ = λ A B → refl


  -- Experimenting with introducing some
  -- product element ab : A × B from a : A and b : B

  1Set : SET ℓS .ob
  1Set = Unit* , isSetUnit*

  1SetIsTerminal : isTerminal (SET ℓS) 1Set
  1SetIsTerminal = λ y → (λ _ → tt*) , λ z → funExt (λ _ → refl)

  elt→morphism : (A : SET ℓS .ob) → (a : A .fst) → (SET ℓS) [ 1Set , A ]
  elt→morphism A a = λ _ → a

  morphism→elt : (A : SET ℓS .ob) → (f : (SET ℓS) [ 1Set , A ]) → A .fst
  morphism→elt A f = f tt*

  _ : (A B : SET ℓS .ob) (a : A .fst) (b : B .fst) → A .fst
  _ = λ A B a b → π₁ {A}{B} (morphism→elt (A × B) (elt→morphism A a ,p elt→morphism B b))
