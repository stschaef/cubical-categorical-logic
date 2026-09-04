{- The unit category with independently chosen object and hom levels. -}
module Cubical.Categories.Instances.Terminal.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit

open import Cubical.Categories.Category

private
  variable
    ℓa ℓb : Level

open Category

UnitCategory : (ℓa ℓb : Level) → Category ℓa ℓb
UnitCategory ℓa ℓb .ob = Unit* {ℓa}
UnitCategory ℓa ℓb .Hom[_,_] _ _ = Unit* {ℓb}
UnitCategory ℓa ℓb .id = tt*
UnitCategory ℓa ℓb ._⋆_ _ _ = tt*
UnitCategory ℓa ℓb .⋆IdL _ = refl
UnitCategory ℓa ℓb .⋆IdR _ = refl
UnitCategory ℓa ℓb .⋆Assoc _ _ _ = refl
UnitCategory ℓa ℓb .isSetHom = isSetUnit*
