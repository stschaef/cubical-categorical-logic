{-# OPTIONS --lossy-unification #-}
{- A right adjoint to `f : c → d` as a universal element, one probe
   0-cell at a time: `y ⋆₁ u` is the right lifting of the probe `y`
   through `f`.  So this is `Limits/Extension.agda`'s `RightLiftingᴮ`
   -- `Adjoint.RightAdjoint` at `postcomp f` -- in every fibre, and
   the probe quantifier is absoluteness of the lifting of `id₁`, up
   to the right unitor. -}
module Cubical.Categories.Bicategory.Adjunction.Universal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Adjoint.RightAdjoint

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Limits.Extension
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Properties.Coherence
open import Cubical.Categories.Bicategory.Adjunction
open import Cubical.Categories.Bicategory.Adjunction.Transposition

private
  variable
    ℓ ℓ' ℓ'' : Level

open NatIso
open Cubical.Categories.Category.isIso

module _ {B : Bicategory ℓ ℓ' ℓ''} where
  private
    module B = Bicategory B
  module _ {c d : B.0Cell} (f : B.1Cell c d) where
    -- x ↦ 2Cell (x ⋆₁ f) y, a presheaf on the fibre Hom[ e , c ].
    RPre : (e : B.0Cell) (y : B.1Cell e d) → Presheaf B.Hom[ e , c ] ℓ''
    RPre e y = RiftPshᴮ B {x = e} f y

    -- `ε` whiskered by a probe `y`: the element of `RPre e y` at the
    -- candidate vertex `y ⋆₁ u`.
    module _ {u : B.1Cell d c} (ε : B.2Cell (u B.⋆₁ f) B.id₁) where
      εEl : {e : B.0Cell} (y : B.1Cell e d)
        → B.2Cell ((y B.⋆₁ u) B.⋆₁ f) y
      εEl y = B.α⁺ y u f B.⋆₂ (y B.◁w ε) B.⋆₂ B.ρ⁺ y

      -- `y ⋆₁ u` is the right lifting of `y` through `f`, at every
      -- probe 0-cell `e`: absoluteness of the lifting of `id₁`.
      isRightAdjointᴮ : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
      isRightAdjointᴮ = (e : B.0Cell) (y : B.1Cell e d)
        → isRightLiftingᴮ B {x = e} f (y B.⋆₁ u) (εEl y)

    RightAdjointᴮ : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
    RightAdjointᴮ =
      Σ[ u ∈ B.1Cell d c ] Σ[ ε ∈ B.2Cell (u B.⋆₁ f) B.id₁ ]
        isRightAdjointᴮ ε

{- A formal adjunction gives the universal property: transposition is
   the presheaf action of `εw`, so `transposeIso` *is* the equivalence
   `isUniversal` asks for. -}
module _ {B : Bicategory ℓ ℓ' ℓ''} (A : Adjunction B) where
  private
    module B = Bicategory B
  open AdjunctionNotation A

  adjunction→RightAdjointᴮ : RightAdjointᴮ {B = B} {c = c} {d = d} f
  adjunction→RightAdjointᴮ =
    u , ε , λ e y x → isoToIsEquiv (invIso (transposeIso A))

{- Conversely, the universal property produces the unit, and both
   zigzags are its β-rule. -}
module RightAdjointᴮNotation {B : Bicategory ℓ ℓ' ℓ''}
  {c d : Bicategory.0Cell B}
  {f : Bicategory.1Cell B c d} {u : Bicategory.1Cell B d c}
  {ε : Bicategory.2Cell B (Bicategory._⋆₁_ B u f) (Bicategory.id₁ B)}
  (U : isRightAdjointᴮ {B = B} {c = c} {d = d} f {u = u} ε) where
  private
    module B = Bicategory B

    -- `εEl`, spelled out: the implicits of a `Bicategory` are not
    -- inferable from a 1-cell, so types never mention `εEl` itself.
    εB : {e : B.0Cell} (y : B.1Cell e d) → B.2Cell ((y B.⋆₁ u) B.⋆₁ f) y
    εB y = B.α⁺ y u f B.⋆₂ (y B.◁w ε) B.⋆₂ B.ρ⁺ y

  -- the shared 1-cell-level notation, at the probe `(e , y)`
  module Rift {e : B.0Cell} (y : B.1Cell e d) =
    RightLiftingᴮNotation {B = B} {x = e} {g = f} {f = y}
      (isUniversal→UniversalElement _ (U e y))

  -- the transpose, as the inverse of the presheaf action of `εEl`
  Ψ : {e : B.0Cell} {y : B.1Cell e d} {x : B.1Cell e c}
    → B.2Cell (x B.⋆₁ f) y → B.2Cell x (y B.⋆₁ u)
  Ψ {e} {y} {x} = Rift.intro y

  ηU : B.2Cell B.id₁ (f B.⋆₁ u)
  ηU = Ψ {y = f} {x = B.id₁} (B.λ⁺ f)

  βU : (ηU B.▷w f) B.⋆₂ εB f ≡ B.λ⁺ f
  βU = Rift.β f

  zigzagLU : B.λ⁻ f B.⋆₂ ((ηU B.▷w f)
      B.⋆₂ (B.α⁺ f u f B.⋆₂ ((f B.◁w ε) B.⋆₂ B.ρ⁺ f)))
    ≡ B.id₂
  zigzagLU = B.⟨⟩⋆₂⟨ βU ⟩ ∙ B.λU c d .nIso (tt* , f) .sec

  -- `ε` is the transpose of the left unitor: coherence, no unit.
  lemΦλ : (B.λ⁻ u B.▷w f) B.⋆₂ εB B.id₁ ≡ ε
  lemΦλ =
      sym (B.⋆₂Assoc _ _ _)
    ∙ B.⟨ λ⁻⋆₁ B u f ⟩⋆₂⟨⟩
    ∙ sym (B.⋆₂Assoc _ _ _)
    ∙ B.⟨ sym (λ⁻-nat B ε) ⟩⋆₂⟨⟩
    ∙ B.⋆₂Assoc _ _ _
    ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ sym (λ⁺≡ρ⁺ B) ⟩
            ∙ B.λU d d .nIso (tt* , B.id₁) .sec ⟩
    ∙ B.⋆₂IdR _

  private
    -- the whiskered unit transposes back to the identity: this is
    -- `transposeIso`'s retraction, and needs only the left zigzag.
    Φfml : {e : B.0Cell} {y : B.1Cell e d} {x : B.1Cell e c}
      (θ : B.2Cell (x B.⋆₁ f) y)
      → ((ηw B ηU ε x B.⋆₂ (θ B.▷w u)) B.▷w f) B.⋆₂ εB y ≡ θ
    Φfml {e} {y} {x} θ =
        B.⟨ ▷wSeq B _ _ f ⟩⋆₂⟨⟩
      ∙ B.⋆₂Assoc _ _ _
      ∙ B.⟨⟩⋆₂⟨ εwNat B ηU ε θ ⟩
      ∙ sym (B.⋆₂Assoc _ _ _)
      ∙ B.⟨ whiskerZigzagL B ηU ε βU x ⟩⋆₂⟨⟩
      ∙ B.⋆₂IdL _

  ΨFormula : {e : B.0Cell} {y : B.1Cell e d} {x : B.1Cell e c}
    (θ : B.2Cell (x B.⋆₁ f) y)
    → Ψ θ ≡ ηw B ηU ε x B.⋆₂ (θ B.▷w u)
  ΨFormula {e} {y} {x} θ = Rift.intro≡ y (sym (Φfml θ))

  private
    eqnR : ηw B ηU ε u B.⋆₂ (ε B.▷w u) ≡ B.λ⁻ u
    eqnR = sym (ΨFormula {y = B.id₁} {x = u} ε)
         ∙ Rift.intro≡ B.id₁ (sym lemΦλ)

  zigzagRU : B.ρ⁻ u B.⋆₂ ((u B.◁w ηU)
      B.⋆₂ (B.α⁻ u f u B.⋆₂ ((ε B.▷w u) B.⋆₂ B.λ⁺ u)))
    ≡ B.id₂
  zigzagRU =
      B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ sym (B.⋆₂Assoc _ _ _) ⟩ ⟩
    ∙ B.⟨⟩⋆₂⟨ sym (B.⋆₂Assoc _ _ _) ⟩
    ∙ sym (B.⋆₂Assoc _ _ _)
    ∙ B.⟨ B.⟨⟩⋆₂⟨ sym (B.⋆₂Assoc _ _ _) ⟩ ∙ sym (B.⋆₂Assoc _ _ _) ⟩⋆₂⟨⟩
    ∙ B.⟨ eqnR ⟩⋆₂⟨⟩
    ∙ B.λU d c .nIso (tt* , u) .sec

  -- The `extensionality` of `BiuniversalElementNotation`, at a probe:
  -- a 2-cell into `y ⋆₁ u` is determined by its transpose.
  transposeFaithful : {e : B.0Cell} {x : B.1Cell e c} {y : B.1Cell e d}
    (φ φ' : B.2Cell x (y B.⋆₁ u))
    → (φ B.▷w f) B.⋆₂ εB y ≡ (φ' B.▷w f) B.⋆₂ εB y → φ ≡ φ'
  transposeFaithful {e} {x} {y} φ φ' p = Rift.extensionality y p

  -- Transposition is the universal property, nothing more.
  transposeIsoU : {e : B.0Cell} {x : B.1Cell e c} {y : B.1Cell e d}
    → Iso (B.2Cell (x B.⋆₁ f) y) (B.2Cell x (y B.⋆₁ u))
  transposeIsoU {e} {x} {y} = invIso (Rift.compareIso y x)

  -- The right whiskered zigzag is `Ψ` applied to `Φ id₂`.
  whiskerZigzagRU : {e : B.0Cell} (y : B.1Cell e d)
    → ηw B ηU ε (y B.⋆₁ u) B.⋆₂ (εB y B.▷w u) ≡ B.id₂
  whiskerZigzagRU {e} y =
      sym (ΨFormula (εB y))
    ∙ Rift.intro≡ y (sym (B.⟨ B.▷wId f ⟩⋆₂⟨⟩ ∙ B.⋆₂IdL _))

  {- `u` is the right lifting of `id₁` through `f`, and the probe
     quantifier says exactly that the lifting is absolute -- modulo
     the right unitor, which mediates between the probe `y` and the
     composite `y ⋆₁ id₁` that absoluteness lifts. -}
  riftU : RightLiftingᴮ B {x = d} f B.id₁
  riftU .UniversalElement.vertex = u
  riftU .UniversalElement.element = ε
  riftU .UniversalElement.universal =
    substIsUniversal _ (isUniversalRPsh∘ λu (U d B.id₁)) lemΦλ
    where
    λu : CatIso B.Hom[ d , c ] (B.id₁ B.⋆₁ u) u
    λu = B.λ⁺ u , B.λU d c .nIso (tt* , u)

  absoluteRiftU : isAbsoluteRiftᴮ B riftU
  absoluteRiftU {w} k =
    substIsUniversal _ (isUniversalRPsh⋆ ρk (U w k))
      (B.⋆₂Assoc _ _ _
      ∙ B.⟨⟩⋆₂⟨ B.⋆₂Assoc _ _ _
              ∙ B.⟨⟩⋆₂⟨ B.ρU w d .nIso (k , tt*) .ret ⟩
              ∙ B.⋆₂IdR _ ⟩)
    where
    ρk : CatIso B.Hom[ w , d ] k (k B.⋆₁ B.id₁)
    ρk .fst = B.ρ⁻ k
    ρk .snd .inv = B.ρ⁺ k
    ρk .snd .sec = B.ρU w d .nIso (k , tt*) .ret
    ρk .snd .ret = B.ρU w d .nIso (k , tt*) .sec

  RightAdjointᴮ→Adjunction : Adjunction B
  RightAdjointᴮ→Adjunction = A where
    A : Adjunction B
    A .Adjunction.c = c
    A .Adjunction.d = d
    A .Adjunction.f = f
    A .Adjunction.u = u
    A .Adjunction.η = ηU
    A .Adjunction.ε = ε
    A .Adjunction.zigzagL = zigzagLU
    A .Adjunction.zigzagR = zigzagRU

{- Conversely, an absolute right lifting of `id₁` through `f` is a
   right adjoint: reunitoring `k ⋆₁ id₁` to `k` turns absoluteness
   into the probe quantifier. -}
module _ {B : Bicategory ℓ ℓ' ℓ''} {c d : Bicategory.0Cell B}
  {f : Bicategory.1Cell B c d}
  (R : RightLiftingᴮ B {x = d} f (Bicategory.id₁ B))
  (A : isAbsoluteRiftᴮ B R) where
  private
    module B = Bicategory B
    module R = RightLiftingᴮNotation R

  absoluteRift→isRightAdjointᴮ :
    isRightAdjointᴮ {B = B} {c = c} {d = d} f {u = R.rift} R.riftε
  absoluteRift→isRightAdjointᴮ e y =
    substIsUniversal _ (isUniversalRPsh⋆ ρy (A y)) (B.⋆₂Assoc _ _ _)
    where
    ρy : CatIso B.Hom[ e , d ] (y B.⋆₁ B.id₁) y
    ρy = B.ρ⁺ y , B.ρU e d .nIso (y , tt*)

{- The two formulations agree, at a fixed left leg. -}
module _ {B : Bicategory ℓ ℓ' ℓ''} {c d : Bicategory.0Cell B}
  (f : Bicategory.1Cell B c d) where
  private
    module B = Bicategory B

    ZL : (u : B.1Cell d c) (η : B.2Cell B.id₁ (f B.⋆₁ u))
      (ε : B.2Cell (u B.⋆₁ f) B.id₁) → Type ℓ''
    ZL u η ε = B.λ⁻ f B.⋆₂ ((η B.▷w f)
        B.⋆₂ (B.α⁺ f u f B.⋆₂ ((f B.◁w ε) B.⋆₂ B.ρ⁺ f)))
      ≡ B.id₂

    ZR : (u : B.1Cell d c) (η : B.2Cell B.id₁ (f B.⋆₁ u))
      (ε : B.2Cell (u B.⋆₁ f) B.id₁) → Type ℓ''
    ZR u η ε = B.ρ⁻ u B.⋆₂ ((u B.◁w η)
        B.⋆₂ (B.α⁻ u f u B.⋆₂ ((ε B.▷w u) B.⋆₂ B.λ⁺ u)))
      ≡ B.id₂

  -- the adjunctions in `B` whose left leg is `f`
  AdjunctionAt : Type (ℓ-max ℓ' ℓ'')
  AdjunctionAt = Σ[ u ∈ B.1Cell d c ] Σ[ ε ∈ B.2Cell (u B.⋆₁ f) B.id₁ ]
    Σ[ η ∈ B.2Cell B.id₁ (f B.⋆₁ u) ] (ZL u η ε × ZR u η ε)

  private
    toAdj : AdjunctionAt → Adjunction B
    toAdj (u , ε , η , zl , zr) = A where
      A : Adjunction B
      A .Adjunction.c = c
      A .Adjunction.d = d
      A .Adjunction.f = f
      A .Adjunction.u = u
      A .Adjunction.η = η
      A .Adjunction.ε = ε
      A .Adjunction.zigzagL = zl
      A .Adjunction.zigzagR = zr

    isPropIsRA : (u : B.1Cell d c) (ε : B.2Cell (u B.⋆₁ f) B.id₁)
      → isProp (isRightAdjointᴮ {B = B} {c = c} {d = d} f {u = u} ε)
    isPropIsRA u ε = isPropΠ2 λ _ _ → isPropIsUniversal _ _ _ _

  AdjunctionAt≅RightAdjointᴮ :
    Iso AdjunctionAt (RightAdjointᴮ {B = B} {c = c} {d = d} f)
  AdjunctionAt≅RightAdjointᴮ .Iso.fun t =
    t .fst , t .snd .fst , adjunction→RightAdjointᴮ (toAdj t) .snd .snd
  AdjunctionAt≅RightAdjointᴮ .Iso.inv (u , ε , U) =
    u , ε , N.ηU , N.zigzagLU , N.zigzagRU
    where
    module N = RightAdjointᴮNotation {B = B} {c = c} {d = d}
                 {f = f} {u = u} {ε = ε} U
  AdjunctionAt≅RightAdjointᴮ .Iso.sec (u , ε , U) =
    ΣPathP (refl , ΣPathP (refl , isPropIsRA u ε _ _))
  AdjunctionAt≅RightAdjointᴮ .Iso.ret t@(u , ε , η , zl , zr) =
    ΣPathP (refl , ΣPathP (refl , ΣPathP (ηeq ,
      isProp→PathP (λ _ → isProp× (B.isSet2Cell _ _) (B.isSet2Cell _ _))
        _ _)))
    where
    Ut = adjunction→RightAdjointᴮ (toAdj t) .snd .snd
    module N = RightAdjointᴮNotation {B = B} {c = c} {d = d}
                 {f = f} {u = u} {ε = ε} Ut
    ηeq : N.ηU ≡ η
    ηeq = N.Rift.intro≡ f (sym (AdjunctionNotation.zigzagL⁺ (toAdj t)))

  -- absolute right liftings of `id₁` through `f`
  AbsoluteRiftᴮ : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  AbsoluteRiftᴮ =
    Σ[ R ∈ RightLiftingᴮ B {x = d} f B.id₁ ] isAbsoluteRiftᴮ B R

  private
    isPropIsAbs : (R : RightLiftingᴮ B {x = d} f B.id₁)
      → isProp (isAbsoluteRiftᴮ B R)
    isPropIsAbs R = isPropImplicitΠ λ _ → isPropΠ λ _ →
      isPropIsUniversal _ _ _ _

  -- `f ⊣ u` iff `u` is an absolute right lifting of `id₁` through `f`
  RightAdjointᴮ≅AbsoluteRiftᴮ :
    Iso (RightAdjointᴮ {B = B} {c = c} {d = d} f) AbsoluteRiftᴮ
  RightAdjointᴮ≅AbsoluteRiftᴮ .Iso.fun (u , ε , U) = N.riftU , N.absoluteRiftU
    where
    module N = RightAdjointᴮNotation {B = B} {c = c} {d = d}
                 {f = f} {u = u} {ε = ε} U
  RightAdjointᴮ≅AbsoluteRiftᴮ .Iso.inv (R , A) =
    RightLiftingᴮNotation.rift R , RightLiftingᴮNotation.riftε R ,
    absoluteRift→isRightAdjointᴮ R A
  RightAdjointᴮ≅AbsoluteRiftᴮ .Iso.sec (R , A) =
    ΣPathP (Rpath , isProp→PathP (λ i → isPropIsAbs (Rpath i)) _ _)
    where
    module N = RightAdjointᴮNotation (absoluteRift→isRightAdjointᴮ R A)
    Rpath : N.riftU ≡ R
    Rpath i .UniversalElement.vertex = R .UniversalElement.vertex
    Rpath i .UniversalElement.element = R .UniversalElement.element
    Rpath i .UniversalElement.universal =
      isPropIsUniversal _ _ _ _ (N.riftU .UniversalElement.universal)
        (R .UniversalElement.universal) i
  RightAdjointᴮ≅AbsoluteRiftᴮ .Iso.ret (u , ε , U) =
    ΣPathP (refl , ΣPathP (refl , isPropIsRA u ε _ _))

  AdjunctionAt≅AbsoluteRiftᴮ : Iso AdjunctionAt AbsoluteRiftᴮ
  AdjunctionAt≅AbsoluteRiftᴮ =
    Cubical.Foundations.Isomorphism.compIso
      AdjunctionAt≅RightAdjointᴮ RightAdjointᴮ≅AbsoluteRiftᴮ
