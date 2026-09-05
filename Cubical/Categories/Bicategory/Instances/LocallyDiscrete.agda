-- A 1-category as a bicategory with only identity 2-cells.
module Cubical.Categories.Bicategory.Instances.LocallyDiscrete where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Discrete
open import Cubical.Categories.HLevels

-- re-exported because `hasPropHomsLD` is stated with it
open import Cubical.Categories.HLevels public using (hasPropHoms)

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo

open Category
open Functor
open NatTrans
open NatIso
open isIso
open Bicategory

private
  variable
    ℓ ℓ' ℓc ℓc' : Level


module _ (C : Category ℓ ℓ') where
  private
    module C = Category C

    homGpd : (x y : C.ob) → hGroupoid ℓ'
    homGpd x y = C.Hom[ x , y ] , isSet→isGroupoid C.isSetHom

    -- every 2-cell type is a proposition; this discharges every law
    isProp2 : {x y : C.ob} {f g : C.Hom[ x , y ]} → isProp (f ≡ g)
    isProp2 = C.isSetHom _ _

  LocallyDiscrete : Bicategory ℓ ℓ' ℓ'
  LocallyDiscrete .ob = C.ob
  LocallyDiscrete .Hom[_,_] x y = DiscreteCategory (homGpd x y)
  LocallyDiscrete .id .F-ob _ = C.id
  LocallyDiscrete .id .F-hom _ = refl
  LocallyDiscrete .id .F-id = refl
  LocallyDiscrete .id .F-seq _ _ = isProp2 _ _
  LocallyDiscrete .seq _ _ _ .F-ob (f , g) = f C.⋆ g
  LocallyDiscrete .seq _ _ _ .F-hom (p , q) = cong₂ C._⋆_ p q
  LocallyDiscrete .seq _ _ _ .F-id = isProp2 _ _
  LocallyDiscrete .seq _ _ _ .F-seq _ _ = isProp2 _ _
  LocallyDiscrete .λU _ _ .trans .N-ob (_ , f) = C.⋆IdL f
  LocallyDiscrete .λU _ _ .trans .N-hom _ = isProp2 _ _
  LocallyDiscrete .λU _ _ .nIso (_ , f) .inv = sym (C.⋆IdL f)
  LocallyDiscrete .λU _ _ .nIso _ .sec = isProp2 _ _
  LocallyDiscrete .λU _ _ .nIso _ .ret = isProp2 _ _
  LocallyDiscrete .ρU _ _ .trans .N-ob (f , _) = C.⋆IdR f
  LocallyDiscrete .ρU _ _ .trans .N-hom _ = isProp2 _ _
  LocallyDiscrete .ρU _ _ .nIso (f , _) .inv = sym (C.⋆IdR f)
  LocallyDiscrete .ρU _ _ .nIso _ .sec = isProp2 _ _
  LocallyDiscrete .ρU _ _ .nIso _ .ret = isProp2 _ _
  LocallyDiscrete .α _ _ _ _ .trans .N-ob (f , g , h) = C.⋆Assoc f g h
  LocallyDiscrete .α _ _ _ _ .trans .N-hom _ = isProp2 _ _
  LocallyDiscrete .α _ _ _ _ .nIso (f , g , h) .inv = sym (C.⋆Assoc f g h)
  LocallyDiscrete .α _ _ _ _ .nIso _ .sec = isProp2 _ _
  LocallyDiscrete .α _ _ _ _ .nIso _ .ret = isProp2 _ _
  LocallyDiscrete .triangle _ _ _ _ _ = isProp2 _ _
  LocallyDiscrete .pentagon _ _ _ _ _ _ _ _ _ = isProp2 _ _

  -- the hom-categories are discrete on sets, hence have prop homs
  hasPropHomsLD : (x y : C.ob)
    → hasPropHoms (Bicategory.Hom[_,_] LocallyDiscrete x y)
  hasPropHomsLD x y = isProp2

module _ {C : Category ℓc ℓc'} {D : Category ℓ ℓ'} (F : Functor C D) where
  private
    module F = Functor F
    -- every equation between 2-cells of `LocallyDiscrete D` is a prop
    isProp2 : {x y : Category.ob D} {f g : D [ x , y ]} → isProp (f ≡ g)
    isProp2 = D .Category.isSetHom _ _

  LocallyDiscreteLax : LaxFunctor (LocallyDiscrete C) (LocallyDiscrete D)
  LocallyDiscreteLax .LaxFunctor.F-ob = F.F-ob
  LocallyDiscreteLax .LaxFunctor.F-Hom .F-ob = F.F-hom
  LocallyDiscreteLax .LaxFunctor.F-Hom .F-hom = cong F.F-hom
  LocallyDiscreteLax .LaxFunctor.F-Hom .F-id = isProp2 _ _
  LocallyDiscreteLax .LaxFunctor.F-Hom .F-seq _ _ = isProp2 _ _
  LocallyDiscreteLax .LaxFunctor.F-id .N-ob _ = sym F.F-id
  LocallyDiscreteLax .LaxFunctor.F-id .N-hom _ = isProp2 _ _
  LocallyDiscreteLax .LaxFunctor.F-seq .N-ob (f , g) = sym (F.F-seq f g)
  LocallyDiscreteLax .LaxFunctor.F-seq .N-hom _ = isProp2 _ _
  LocallyDiscreteLax .LaxFunctor.lax-λ _ _ _ = isProp2 _ _
  LocallyDiscreteLax .LaxFunctor.lax-ρ _ _ _ = isProp2 _ _
  LocallyDiscreteLax .LaxFunctor.lax-α _ _ _ _ _ _ _ = isProp2 _ _

  LocallyDiscreteF : Pseudofunctor (LocallyDiscrete C) (LocallyDiscrete D)
  LocallyDiscreteF .Pseudofunctor.laxFunctor = LocallyDiscreteLax
  LocallyDiscreteF .Pseudofunctor.F-id-isIso _ .inv = F.F-id
  LocallyDiscreteF .Pseudofunctor.F-id-isIso _ .sec = isProp2 _ _
  LocallyDiscreteF .Pseudofunctor.F-id-isIso _ .ret = isProp2 _ _
  LocallyDiscreteF .Pseudofunctor.F-seq-isIso (f , g) .inv = F.F-seq f g
  LocallyDiscreteF .Pseudofunctor.F-seq-isIso _ .sec = isProp2 _ _
  LocallyDiscreteF .Pseudofunctor.F-seq-isIso _ .ret = isProp2 _ _
