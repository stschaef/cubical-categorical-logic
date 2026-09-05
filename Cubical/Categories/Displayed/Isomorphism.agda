{- Isomorphism of displayed categories over a fixed base: a pair of
   mutually inverse vertical functors.  `sameDataᴰ≡` below upgrades the
   identity-on-data case to a path of `Categoryᴰ`s. -}
module Cubical.Categories.Displayed.Isomorphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More

private
  variable
    ℓ ℓ' ℓc ℓc' ℓd ℓd' : Level

open Functorᴰ

module _ {C : Category ℓ ℓ'} where
  private module C = Category C

  record Isoᴰ (Cᴰ : Categoryᴰ C ℓc ℓc') (Dᴰ : Categoryᴰ C ℓd ℓd')
    : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓd ℓd')))
    where
    no-eta-equality
    private
      module Cᴰ = Categoryᴰ Cᴰ
      module Dᴰ = Categoryᴰ Dᴰ
    field
      funⱽ : Functorⱽ Cᴰ Dᴰ
      invⱽ : Functorⱽ Dᴰ Cᴰ
      obSec : {x : C.ob} (xᴰ : Dᴰ.ob[ x ])
        → funⱽ .F-obᴰ (invⱽ .F-obᴰ xᴰ) ≡ xᴰ
      obRet : {x : C.ob} (xᴰ : Cᴰ.ob[ x ])
        → invⱽ .F-obᴰ (funⱽ .F-obᴰ xᴰ) ≡ xᴰ
      homSec : {x y : C.ob} {f : C [ x , y ]}
        {xᴰ : Dᴰ.ob[ x ]} {yᴰ : Dᴰ.ob[ y ]} (fᴰ : Dᴰ.Hom[ f ][ xᴰ , yᴰ ])
        → PathP (λ i → Dᴰ.Hom[ f ][ obSec xᴰ i , obSec yᴰ i ])
            (funⱽ .F-homᴰ (invⱽ .F-homᴰ fᴰ)) fᴰ
      homRet : {x y : C.ob} {f : C [ x , y ]}
        {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
        → PathP (λ i → Cᴰ.Hom[ f ][ obRet xᴰ i , obRet yᴰ i ])
            (invⱽ .F-homᴰ (funⱽ .F-homᴰ fᴰ)) fᴰ

  open Isoᴰ

  idIsoᴰ : {Cᴰ : Categoryᴰ C ℓc ℓc'} → Isoᴰ Cᴰ Cᴰ
  idIsoᴰ .funⱽ = Idᴰ
  idIsoᴰ .invⱽ = Idᴰ
  idIsoᴰ .obSec _ = refl
  idIsoᴰ .obRet _ = refl
  idIsoᴰ .homSec _ = refl
  idIsoᴰ .homRet _ = refl

  invIsoᴰ : {Cᴰ : Categoryᴰ C ℓc ℓc'} {Dᴰ : Categoryᴰ C ℓd ℓd'}
    → Isoᴰ Cᴰ Dᴰ → Isoᴰ Dᴰ Cᴰ
  invIsoᴰ α .funⱽ = α .invⱽ
  invIsoᴰ α .invⱽ = α .funⱽ
  invIsoᴰ α .obSec = α .obRet
  invIsoᴰ α .obRet = α .obSec
  invIsoᴰ α .homSec = α .homRet
  invIsoᴰ α .homRet = α .homSec

  -- Two displayed categories with the same data are equal: given a
  -- path of objects and displayed homs (`refl` in practice) over which
  -- `idᴰ` and `⋆ᴰ` agree, the laws follow because displayed homs are
  -- sets, so every remaining field is a proposition.
  module _ {Cᴰ Dᴰ : Categoryᴰ C ℓc ℓc'}
    (ob≡ : Categoryᴰ.ob[_] Cᴰ ≡ Categoryᴰ.ob[_] Dᴰ)
    (hom≡ : PathP
      (λ i → {x y : C.ob} → C [ x , y ] → ob≡ i x → ob≡ i y → Type ℓc')
      (Categoryᴰ.Hom[_][_,_] Cᴰ) (Categoryᴰ.Hom[_][_,_] Dᴰ))
    (id≡ : PathP (λ i → {x : C.ob} {xᴰ : ob≡ i x} → hom≡ i C.id xᴰ xᴰ)
      (Categoryᴰ.idᴰ Cᴰ) (Categoryᴰ.idᴰ Dᴰ))
    (⋆≡ : PathP (λ i → {x y z : C.ob} {f : C [ x , y ]} {g : C [ y , z ]}
        {xᴰ : ob≡ i x} {yᴰ : ob≡ i y} {zᴰ : ob≡ i z}
        → hom≡ i f xᴰ yᴰ → hom≡ i g yᴰ zᴰ → hom≡ i (f C.⋆ g) xᴰ zᴰ)
      (Categoryᴰ._⋆ᴰ_ Cᴰ) (Categoryᴰ._⋆ᴰ_ Dᴰ))
    where
    private
      setLine : PathP (λ i → {x y : C.ob} {f : C [ x , y ]}
          {xᴰ : ob≡ i x} {yᴰ : ob≡ i y} → isSet (hom≡ i f xᴰ yᴰ))
        (Categoryᴰ.isSetHomᴰ Cᴰ) (Categoryᴰ.isSetHomᴰ Dᴰ)
      setLine = isProp→PathP
        (λ _ → isPropImplicitΠ λ _ → isPropImplicitΠ λ _ → isPropImplicitΠ
          λ _ → isPropImplicitΠ λ _ → isPropImplicitΠ λ _ → isPropIsSet)
        _ _

      ⋆IdLLine : I → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓc ℓc'))
      ⋆IdLLine i = {x y : C.ob} {f : C [ x , y ]}
        {xᴰ : ob≡ i x} {yᴰ : ob≡ i y} (fᴰ : hom≡ i f xᴰ yᴰ)
        → PathP (λ j → hom≡ i (C.⋆IdL f j) xᴰ yᴰ) (⋆≡ i (id≡ i) fᴰ) fᴰ

      ⋆IdRLine : I → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓc ℓc'))
      ⋆IdRLine i = {x y : C.ob} {f : C [ x , y ]}
        {xᴰ : ob≡ i x} {yᴰ : ob≡ i y} (fᴰ : hom≡ i f xᴰ yᴰ)
        → PathP (λ j → hom≡ i (C.⋆IdR f j) xᴰ yᴰ) (⋆≡ i fᴰ (id≡ i)) fᴰ

      ⋆AssocLine : I → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓc ℓc'))
      ⋆AssocLine i = {x y z w : C.ob} {f : C [ x , y ]} {g : C [ y , z ]}
        {h : C [ z , w ]} {xᴰ : ob≡ i x} {yᴰ : ob≡ i y} {zᴰ : ob≡ i z}
        {wᴰ : ob≡ i w}
        (fᴰ : hom≡ i f xᴰ yᴰ) (gᴰ : hom≡ i g yᴰ zᴰ) (hᴰ : hom≡ i h zᴰ wᴰ)
        → PathP (λ j → hom≡ i (C.⋆Assoc f g h j) xᴰ wᴰ)
            (⋆≡ i (⋆≡ i fᴰ gᴰ) hᴰ) (⋆≡ i fᴰ (⋆≡ i gᴰ hᴰ))

    sameDataᴰ≡ : Cᴰ ≡ Dᴰ
    sameDataᴰ≡ i .Categoryᴰ.ob[_] = ob≡ i
    sameDataᴰ≡ i .Categoryᴰ.Hom[_][_,_] = hom≡ i
    sameDataᴰ≡ i .Categoryᴰ.idᴰ = id≡ i
    sameDataᴰ≡ i .Categoryᴰ._⋆ᴰ_ = ⋆≡ i
    sameDataᴰ≡ i .Categoryᴰ.⋆IdLᴰ = isProp→PathP {B = ⋆IdLLine}
      (λ i → isPropImplicitΠ λ _ → isPropImplicitΠ λ _ → isPropImplicitΠ
        λ _ → isPropImplicitΠ λ _ → isPropImplicitΠ λ _ → isPropΠ
        λ _ → isOfHLevelPathP' 1 (setLine i) _ _)
      (Categoryᴰ.⋆IdLᴰ Cᴰ) (Categoryᴰ.⋆IdLᴰ Dᴰ) i
    sameDataᴰ≡ i .Categoryᴰ.⋆IdRᴰ = isProp→PathP {B = ⋆IdRLine}
      (λ i → isPropImplicitΠ λ _ → isPropImplicitΠ λ _ → isPropImplicitΠ
        λ _ → isPropImplicitΠ λ _ → isPropImplicitΠ λ _ → isPropΠ
        λ _ → isOfHLevelPathP' 1 (setLine i) _ _)
      (Categoryᴰ.⋆IdRᴰ Cᴰ) (Categoryᴰ.⋆IdRᴰ Dᴰ) i
    sameDataᴰ≡ i .Categoryᴰ.⋆Assocᴰ = isProp→PathP {B = ⋆AssocLine}
      (λ i → isPropImplicitΠ λ _ → isPropImplicitΠ λ _ → isPropImplicitΠ
        λ _ → isPropImplicitΠ λ _ → isPropImplicitΠ λ _ → isPropImplicitΠ
        λ _ → isPropImplicitΠ λ _ → isPropImplicitΠ λ _ → isPropImplicitΠ
        λ _ → isPropImplicitΠ λ _ → isPropImplicitΠ λ _ → isPropΠ3
        λ _ _ _ → isOfHLevelPathP' 1 (setLine i) _ _)
      (Categoryᴰ.⋆Assocᴰ Cᴰ) (Categoryᴰ.⋆Assocᴰ Dᴰ) i
    sameDataᴰ≡ i .Categoryᴰ.isSetHomᴰ = setLine i
