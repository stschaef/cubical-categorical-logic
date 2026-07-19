-- Direct categories.
module Cubical.Categories.Direct.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary
import Cubical.Data.Equality as Eq

open import Cubical.Induction.WellFounded

open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.StructureOver.Base
open import Cubical.Categories.Displayed.Section.Base

private
  variable
    ℓC ℓC' ℓD ℓ< : Level

-- Pull a well-founded relation back along a function.
-- TODO put this somewhere else
module _ {A : Type ℓC} {W : Type ℓD} (deg : A → W)
         (_<_ : W → W → Type ℓ<) where
  pullback< : A → A → Type ℓ<
  pullback< a a' = deg a < deg a'

  accPullback : ∀ a → Acc _<_ (deg a) → Acc pullback< a
  accPullback a (acc r) = acc (λ a' p → accPullback a' (r (deg a') p))

  wfPullback : WellFounded _<_ → WellFounded pullback<
  wfPullback wf a = accPullback a (wf (deg a))

record WFOrder (ℓD ℓ< : Level) : Type (ℓ-suc (ℓ-max ℓD ℓ<)) where
  field
    D       : Type ℓD
    isSetD  : isSet D
    _<_     : D → D → Type ℓ<
    isProp< : ∀ a b → isProp (a < b)
    trans<  : ∀ {a b c} → a < b → b < c → a < c
    wf<     : WellFounded _<_

  ¬<refl : ∀ {a} → ¬ (a < a)
  ¬<refl = wf→x≮x wf<

  -- less-than-or-equal-to is less-than or equal-to
  _≤_ : D → D → Type (ℓ-max ℓD ℓ<)
  a ≤ b = (a < b) ⊎ (a Eq.≡ b)

  isProp≤ : ∀ {a b} → isProp (a ≤ b)
  isProp≤ {a} {b} = isProp⊎ (isProp< a b) isPropEq
    (λ a<b a≡b → ¬<refl (Eq.transport (a <_) (Eq.sym a≡b) a<b))
    where
      isPropEq : isProp (a Eq.≡ b)
      isPropEq = isOfHLevelRetract 1
        Eq.eqToPath Eq.pathToEq Eq.pathToEq-eqToPath (isSetD a b)

  ≤-refl : ∀ {a} → a ≤ a
  ≤-refl = inr Eq.refl

  ≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
  ≤-trans         (inl a<b) (inl b<c) = inl (trans< a<b b<c)
  ≤-trans {a = a} (inl a<b) (inr b≡c) = inl (Eq.transport (a <_) b≡c a<b)
  ≤-trans {c = c} (inr a≡b) (inl b<c) = inl (Eq.transport (_< c) (Eq.sym a≡b) b<c)
  ≤-trans         (inr a≡b) (inr b≡c) = inr (a≡b Eq.∙ b≡c)

  ≤-<-trans : ∀ {a b c} → a ≤ b → b < c → a < c
  ≤-<-trans         (inl a<b) b<c = trans< a<b b<c
  ≤-<-trans {c = c} (inr a≡b) b<c = Eq.transport (λ z → z < c) (Eq.sym a≡b) b<c

  <-≤-trans : ∀ {a b c} → a < b → b ≤ c → a < c
  <-≤-trans         a<b (inl b<c) = trans< a<b b<c
  <-≤-trans {a = a} a<b (inr b≡c) = Eq.transport (λ z → a < z) b≡c a<b

-- Pull a whole well-founded order back along a measure `A → D`.
module _ {ℓA : Level} (Wo : WFOrder ℓD ℓ<)
         {A : Type ℓA} (isSetA : isSet A) (meas : A → WFOrder.D Wo) where
  private module Wo = WFOrder Wo
  pullbackWFOrder : WFOrder ℓA ℓ<
  pullbackWFOrder = record
    { D       = A
    ; isSetD  = isSetA
    ; _<_     = λ a b → meas a Wo.< meas b
    ; isProp< = λ a b → Wo.isProp< (meas a) (meas b)
    ; trans<  = λ {a} {b} {c} → Wo.trans< {meas a} {meas b} {meas c}
    ; wf<     = wfPullback meas Wo._<_ Wo.wf<
    }

module _ {C : Category ℓC ℓC'} (Wo : WFOrder ℓD ℓ<) where
  private
    module C  = Category C
    module Wo = WFOrder Wo

  -- Degree data living over a category
  Deg≤ : StructureOver C ℓD (ℓ-max ℓD ℓ<)
  Deg≤ .StructureOver.ob[_] _          = Wo.D
  Deg≤ .StructureOver.Hom[_][_,_] f a b = a Wo.≤ b
  Deg≤ .StructureOver.idᴰ              = Wo.≤-refl
  Deg≤ .StructureOver._⋆ᴰ_             = Wo.≤-trans
  Deg≤ .StructureOver.isPropHomᴰ       = Wo.isProp≤

  Deg≤ᴰ : Categoryᴰ C ℓD (ℓ-max ℓD ℓ<)
  Deg≤ᴰ = StructureOver→Catᴰ Deg≤

  -- A direct structure on a category demonstrates that
  -- morhpisms flow in the same order as the ordering on objects
  DirectStr : Type _
  DirectStr = GlobalSection Deg≤ᴰ

  mkDirectStr :
      (deg : C.ob → Wo.D)
    → (non-dec : ∀ {x y} → C [ x , y ] → deg x Wo.≤ deg y)
    → DirectStr
  mkDirectStr deg non-dec .Section.F-obᴰ        = deg
  mkDirectStr deg non-dec .Section.F-homᴰ       = non-dec
  mkDirectStr deg non-dec .Section.F-idᴰ        =
    isProp→PathP (λ _ → Wo.isProp≤) _ _
  mkDirectStr deg non-dec .Section.F-seqᴰ _ _   =
    isProp→PathP (λ _ → Wo.isProp≤) _ _

module DirectNotation
  {ℓC ℓC' ℓD ℓ< : Level} {C : Category ℓC ℓC'} {Wo : WFOrder ℓD ℓ<}
  (dir : DirectStr {C = C} Wo) where
  private
    module C  = Category C
    module Wo = WFOrder Wo
  open Section dir

  deg : C.ob → Wo.D
  deg = F-obᴰ

  non-dec : ∀ {x y} → C [ x , y ] → deg x Wo.≤ deg y
  non-dec = F-homᴰ

  _≺_ : C.ob → C.ob → Type ℓ<
  x ≺ y = deg x Wo.< deg y

  isProp≺ : ∀ x y → isProp (x ≺ y)
  isProp≺ x y = Wo.isProp< _ _

  wf≺ : WellFounded _≺_
  wf≺ = wfPullback deg Wo._<_ Wo.wf<

  ≺-precomp : ∀ {z y x} → C [ z , y ] → y ≺ x → z ≺ x
  ≺-precomp f y≺x = Wo.≤-<-trans (non-dec f) y≺x

  ≺-postcomp : ∀ {y x x'} → y ≺ x → C [ x , x' ] → y ≺ x'
  ≺-postcomp y≺x f = Wo.<-≤-trans y≺x (non-dec f)
