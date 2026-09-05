{- CAT's associators are componentwise identities, and whiskering
   preserves componentwise identities. -}
module Cubical.Categories.Bicategory.Instances.CAT.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Isomorphism.More

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Instances.CAT

private
  variable
    ℓp ℓp' : Level

open Functor
open NatTrans

module _ {X Y Z : Category ℓp ℓp'} where
  private
    module CATᴮ = Bicategory (CAT {ℓp} {ℓp'})

  ▷wIsIdHom : {F F' : Functor X Y} {θ : NatTrans F F'} (K : Functor Y Z)
    (e : X .Category.ob) → isIdHom {C = Y} (θ .N-ob e)
    → isIdHom {C = Z} ((θ CATᴮ.▷w K) .N-ob e)
  ▷wIsIdHom K e s = ⋆IsIdHom {C = Z} (F-isIdHom K s) (idIsIdHom {C = Z})

  ◁wIsIdHom : (K : Functor X Y) {G G' : Functor Y Z} {θ : NatTrans G G'}
    (e : X .Category.ob) → isIdHom {C = Z} (θ .N-ob (K .F-ob e))
    → isIdHom {C = Z} ((K CATᴮ.◁w θ) .N-ob e)
  ◁wIsIdHom K {G = G} e s =
    ⋆IsIdHom {C = Z} (F-isIdHom G (idIsIdHom {C = Y})) s

module _ {W X Y Z : Category ℓp ℓp'} where
  private
    module CATᴮ = Bicategory (CAT {ℓp} {ℓp'})

  α⁺IsIdHom : (F : Functor W X) (G : Functor X Y) (H : Functor Y Z)
    (e : W .Category.ob) → isIdHom {C = Z} (CATᴮ.α⁺ F G H .N-ob e)
  α⁺IsIdHom F G H e = refl

  α⁻IsIdHom : (F : Functor W X) (G : Functor X Y) (H : Functor Y Z)
    (e : W .Category.ob) → isIdHom {C = Z} (CATᴮ.α⁻ F G H .N-ob e)
  α⁻IsIdHom F G H e = refl
