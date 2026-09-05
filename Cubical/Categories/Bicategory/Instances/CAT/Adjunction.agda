{- Adjunctions in the bicategory `CAT`. -}
module Cubical.Categories.Bicategory.Instances.CAT.Adjunction where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Bicategory.Adjunction
open import Cubical.Categories.Bicategory.Instances.CAT

private
  variable
    ℓ ℓ' : Level

-- 0-cells are categories, 1-cells functors, 2-cells natural
-- transformations; the unitors and associator are not identity
-- 2-cells, but all of their components are identity morphisms, so the
-- zig-zags still reduce to the classical triangle identities.
AdjointFunctorᴮ : Type (ℓ-suc (ℓ-max ℓ ℓ'))
AdjointFunctorᴮ {ℓ} {ℓ'} = Adjunction (CAT {ℓ} {ℓ'})
