{-# OPTIONS --lossy-unification #-}
{- Pseudofunctors into a bicategory of structured categories.

   A pseudofunctor into the total bicategory of a `StructureOverᴮ` is
   exactly a pseudofunctor into the base together with fibrewise
   structure that the images of the 1-cells preserve.  No coherence is
   imposed, because a `StructureOverᴮ` has trivial displayed 2-cells.

   Instantiating at the prestack `Pseudofunctor (B ^opᴮ) CAT` and at
   the terminal/cartesian structures on `CAT` identifies prestacks
   valued in categories-with-terminal-objects, resp. cartesian
   categories, with the fibrewise input of
   `Prestack.Fiberwise.∫PreTerminalsⱽ`, resp.
   `Prestack.Fiberwise.∫PreCartesianCategoryⱽ`. -}
module Cubical.Categories.Bicategory.Prestack.Structured where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
  using (Terminalsⱽ)

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Displayed.Constructions.StructureOver
open import Cubical.Categories.Bicategory.Displayed.Constructions.Total
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Constructions.Op
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Instances.CAT.Structured.Terminal
open import Cubical.Categories.Bicategory.Instances.CAT.Structured.Cartesian
open import
  Cubical.Categories.Bicategory.Instances.CAT.Structured.CartesianClosed
open import Cubical.Categories.Bicategory.Instances.LocallyDiscrete.Base
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Fiberwise
open import Cubical.Categories.Bicategory.Prestack.Grothendieck

private
  variable
    ℓ ℓ' ℓ'' ℓb ℓb' ℓb'' ℓᴰ ℓᴰ' ℓp ℓp' : Level

open Functor
open NatTrans
open isIso
open LaxFunctor renaming
  ( F-ob to LF-ob ; F-Hom to LF-Hom ; F-id to LF-id ; F-seq to LF-seq )
open Pseudofunctor using (laxFunctor ; F-id-isIso ; F-seq-isIso)

module _ {B : Bicategory ℓ ℓ' ℓ''} {B' : Bicategory ℓb ℓb' ℓb''}
  (S : StructureOverᴮ B' ℓᴰ ℓᴰ') where
  private
    module B = Bicategory B
    module S = StructureOverᴮ S

  ∫ᴮStr : Bicategory (ℓ-max ℓb ℓᴰ) (ℓ-max ℓb' ℓᴰ') ℓb''
  ∫ᴮStr = ∫ᴮ (StructureOverᴮ→Bicategoryᴰ S)

  -- Fibrewise structure on a pseudofunctor: structure on each image
  -- 0-cell, preserved by each image 1-cell.
  module _ (F : Pseudofunctor B B') where
    private
      module F = Pseudofunctor F

    StructureOn : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓᴰ ℓᴰ'))
    StructureOn =
      Σ[ obs ∈ ((x : B.ob) → S.ob[ F.F-ob x ]) ]
        ({x y : B.ob} (f : B.1Cell x y)
          → S.1Cellᴰ[ F.F-1cell f ][ obs x , obs y ])

  -- fibrewise structure ⇒ pseudofunctor into the total bicategory
  module _ (F : Pseudofunctor B B') (str : StructureOn F) where
    private
      module F = Pseudofunctor F
      obs = str .fst
      pres = str .snd

    toStructured : Pseudofunctor B ∫ᴮStr
    toStructured .laxFunctor .LF-ob x = F.F-ob x , obs x
    toStructured .laxFunctor .LF-Hom .F-ob f = F.F-1cell f , pres f
    toStructured .laxFunctor .LF-Hom .F-hom β = F.F-Hom .F-hom β , tt
    toStructured .laxFunctor .LF-Hom .F-id = ΣPathP (F.F-Hom .F-id , refl)
    toStructured .laxFunctor .LF-Hom .F-seq β γ =
      ΣPathP (F.F-Hom .F-seq β γ , refl)
    toStructured .laxFunctor .LF-id .N-ob p = F.F-id .N-ob p , tt
    toStructured .laxFunctor .LF-id .N-hom β =
      ΣPathP (F.F-id .N-hom β , refl)
    toStructured .laxFunctor .LF-seq .N-ob p = F.F-seq .N-ob p , tt
    toStructured .laxFunctor .LF-seq .N-hom β =
      ΣPathP (F.F-seq .N-hom β , refl)
    toStructured .laxFunctor .lax-λ x y f = ΣPathP (F.lax-λ x y f , refl)
    toStructured .laxFunctor .lax-ρ x y f = ΣPathP (F.lax-ρ x y f , refl)
    toStructured .laxFunctor .lax-α x y z w f g h =
      ΣPathP (F.lax-α x y z w f g h , refl)
    toStructured .F-id-isIso p .inv = F.F-id-isIso p .inv , tt
    toStructured .F-id-isIso p .sec = ΣPathP (F.F-id-isIso p .sec , refl)
    toStructured .F-id-isIso p .ret = ΣPathP (F.F-id-isIso p .ret , refl)
    toStructured .F-seq-isIso p .inv = F.F-seq-isIso p .inv , tt
    toStructured .F-seq-isIso p .sec = ΣPathP (F.F-seq-isIso p .sec , refl)
    toStructured .F-seq-isIso p .ret = ΣPathP (F.F-seq-isIso p .ret , refl)

  -- pseudofunctor into the total bicategory ⇒ fibrewise structure
  module _ (Q : Pseudofunctor B ∫ᴮStr) where
    private
      module Q = Pseudofunctor Q

    fromStructuredBase : Pseudofunctor B B'
    fromStructuredBase .laxFunctor .LF-ob x = Q.F-ob x .fst
    fromStructuredBase .laxFunctor .LF-Hom .F-ob f = Q.F-Hom .F-ob f .fst
    fromStructuredBase .laxFunctor .LF-Hom .F-hom β = Q.F-Hom .F-hom β .fst
    fromStructuredBase .laxFunctor .LF-Hom .F-id = cong fst (Q.F-Hom .F-id)
    fromStructuredBase .laxFunctor .LF-Hom .F-seq β γ =
      cong fst (Q.F-Hom .F-seq β γ)
    fromStructuredBase .laxFunctor .LF-id .N-ob p = Q.F-id .N-ob p .fst
    fromStructuredBase .laxFunctor .LF-id .N-hom β =
      cong fst (Q.F-id .N-hom β)
    fromStructuredBase .laxFunctor .LF-seq .N-ob p = Q.F-seq .N-ob p .fst
    fromStructuredBase .laxFunctor .LF-seq .N-hom β =
      cong fst (Q.F-seq .N-hom β)
    fromStructuredBase .laxFunctor .lax-λ x y f = cong fst (Q.lax-λ x y f)
    fromStructuredBase .laxFunctor .lax-ρ x y f = cong fst (Q.lax-ρ x y f)
    fromStructuredBase .laxFunctor .lax-α x y z w f g h =
      cong fst (Q.lax-α x y z w f g h)
    fromStructuredBase .F-id-isIso p .inv = Q.F-id-isIso p .inv .fst
    fromStructuredBase .F-id-isIso p .sec = cong fst (Q.F-id-isIso p .sec)
    fromStructuredBase .F-id-isIso p .ret = cong fst (Q.F-id-isIso p .ret)
    fromStructuredBase .F-seq-isIso p .inv = Q.F-seq-isIso p .inv .fst
    fromStructuredBase .F-seq-isIso p .sec = cong fst (Q.F-seq-isIso p .sec)
    fromStructuredBase .F-seq-isIso p .ret = cong fst (Q.F-seq-isIso p .ret)

    fromStructuredStr : StructureOn fromStructuredBase
    fromStructuredStr .fst x = Q.F-ob x .snd
    fromStructuredStr .snd f = Q.F-Hom .F-ob f .snd

  fromStructured : Pseudofunctor B ∫ᴮStr
    → Σ[ F ∈ Pseudofunctor B B' ] StructureOn F
  fromStructured Q = fromStructuredBase Q , fromStructuredStr Q

  -- Both round trips.  Every component is definitional; the paths only
  -- reassemble the no-eta records `Functor`, `LaxFunctor` and
  -- `Pseudofunctor`.
  private
    module B'ᵇ = Bicategory B'
    module ∫ᵇ = Bicategory ∫ᴮStr

  module _ (F : Pseudofunctor B B') (str : StructureOn F) where
    private
      module F = Pseudofunctor F
      module R = Pseudofunctor (fromStructuredBase (toStructured F str))

      pHom : {x y : B.ob} → R.F-Hom {x} {y} ≡ F.F-Hom {x} {y}
      pHom = Functor≡ (λ _ → refl) (λ _ → refl)

    fromToBase : fromStructuredBase (toStructured F str) ≡ F
    fromToBase i .laxFunctor .LF-ob = F.F-ob
    fromToBase i .laxFunctor .LF-Hom {x} {y} = pHom {x} {y} i
    fromToBase i .laxFunctor .LF-id {x} =
      makeNatTransPathP {α = R.F-id} {β = F.F-id} refl
        (λ j → pHom {x} {x} j ∘F B.id) refl i
    fromToBase i .laxFunctor .LF-seq {x} {y} {z} =
      makeNatTransPathP {α = R.F-seq} {β = F.F-seq}
        (λ j → B'ᵇ.seq _ _ _ ∘F (pHom {x} {y} j ×F pHom {y} {z} j))
        (λ j → pHom {x} {z} j ∘F B.seq x y z)
        refl i
    fromToBase i .laxFunctor .lax-λ x y f =
      B'ᵇ.Hom[ F.F-ob x , F.F-ob y ] .Category.isSetHom _ _
        (R.lax-λ x y f) (F.lax-λ x y f) i
    fromToBase i .laxFunctor .lax-ρ x y f =
      B'ᵇ.Hom[ F.F-ob x , F.F-ob y ] .Category.isSetHom _ _
        (R.lax-ρ x y f) (F.lax-ρ x y f) i
    fromToBase i .laxFunctor .lax-α x y z w f g h =
      B'ᵇ.Hom[ F.F-ob x , F.F-ob w ] .Category.isSetHom _ _
        (R.lax-α x y z w f g h) (F.lax-α x y z w f g h) i
    fromToBase i .F-id-isIso {x} =
      isPropΠ (λ p → isPropIsIso _) (R.F-id-isIso {x}) (F.F-id-isIso {x}) i
    fromToBase i .F-seq-isIso {x} {y} {z} =
      isPropΠ (λ p → isPropIsIso _)
        (R.F-seq-isIso {x} {y} {z}) (F.F-seq-isIso {x} {y} {z}) i

    fromTo : fromStructured (toStructured F str) ≡ (F , str)
    fromTo = ΣPathP (fromToBase , refl)

  module _ (Q : Pseudofunctor B ∫ᴮStr) where
    private
      module Q = Pseudofunctor Q
      module T = Pseudofunctor
        (toStructured (fromStructuredBase Q) (fromStructuredStr Q))

      pHom : {x y : B.ob} → T.F-Hom {x} {y} ≡ Q.F-Hom {x} {y}
      pHom = Functor≡ (λ _ → refl) (λ _ → refl)

    toFrom : toStructured (fromStructuredBase Q) (fromStructuredStr Q) ≡ Q
    toFrom i .laxFunctor .LF-ob = Q.F-ob
    toFrom i .laxFunctor .LF-Hom {x} {y} = pHom {x} {y} i
    toFrom i .laxFunctor .LF-id {x} =
      makeNatTransPathP {α = T.F-id} {β = Q.F-id} refl
        (λ j → pHom {x} {x} j ∘F B.id) refl i
    toFrom i .laxFunctor .LF-seq {x} {y} {z} =
      makeNatTransPathP {α = T.F-seq} {β = Q.F-seq}
        (λ j → ∫ᵇ.seq _ _ _ ∘F (pHom {x} {y} j ×F pHom {y} {z} j))
        (λ j → pHom {x} {z} j ∘F B.seq x y z)
        refl i
    toFrom i .laxFunctor .lax-λ x y f =
      ∫ᵇ.Hom[ Q.F-ob x , Q.F-ob y ] .Category.isSetHom _ _
        (T.lax-λ x y f) (Q.lax-λ x y f) i
    toFrom i .laxFunctor .lax-ρ x y f =
      ∫ᵇ.Hom[ Q.F-ob x , Q.F-ob y ] .Category.isSetHom _ _
        (T.lax-ρ x y f) (Q.lax-ρ x y f) i
    toFrom i .laxFunctor .lax-α x y z w f g h =
      ∫ᵇ.Hom[ Q.F-ob x , Q.F-ob w ] .Category.isSetHom _ _
        (T.lax-α x y z w f g h) (Q.lax-α x y z w f g h) i
    toFrom i .F-id-isIso {x} =
      isPropΠ (λ p → isPropIsIso _) (T.F-id-isIso {x}) (Q.F-id-isIso {x}) i
    toFrom i .F-seq-isIso {x} {y} {z} =
      isPropΠ (λ p → isPropIsIso _)
        (T.F-seq-isIso {x} {y} {z}) (Q.F-seq-isIso {x} {y} {z}) i

  -- A pseudofunctor into the total bicategory of a `StructureOverᴮ` is
  -- the same thing as a pseudofunctor into the base with fibrewise
  -- structure preserved by the image 1-cells.
  StructuredPseudofunctorIso : Iso (Pseudofunctor B ∫ᴮStr)
    (Σ[ F ∈ Pseudofunctor B B' ] StructureOn F)
  StructuredPseudofunctorIso .Iso.fun = fromStructured
  StructuredPseudofunctorIso .Iso.inv (F , str) = toStructured F str
  StructuredPseudofunctorIso .Iso.sec (F , str) = fromTo F str
  StructuredPseudofunctorIso .Iso.ret = toFrom

  StructuredPseudofunctorEquiv : Pseudofunctor B ∫ᴮStr
    ≃ (Σ[ F ∈ Pseudofunctor B B' ] StructureOn F)
  StructuredPseudofunctorEquiv = isoToEquiv StructuredPseudofunctorIso

-- ------------------------------------------------------------------
-- Prestacks valued in categories with terminal objects, resp. in
-- cartesian categories.
-- ------------------------------------------------------------------

module _ {B : Bicategory ℓ ℓ' ℓ''} (P : Prestack B ℓp ℓp') where
  private
    module B = Bicategory B
  open PrestackNotation P

  -- a 1-cell `x → y` of `B ^opᴮ` is a 1-cell `f : B.1Cell y x`, and
  -- `reind f` goes from the fibre over `x` to the fibre over `y`
  FibrewiseTerminal : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓp ℓp'))
  FibrewiseTerminal =
    Σ[ term ∈ ((x : B.ob) → Terminal' P⟨ x ⟩) ]
      ({x y : B.ob} (f : B.1Cell y x)
        → preservesTerminal' (reind f) (term x))

  FibrewiseCartesian : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓp ℓp'))
  FibrewiseCartesian =
    Σ[ str ∈ ((x : B.ob) → CartesianStr P⟨ x ⟩) ]
      ({x y : B.ob} (f : B.1Cell y x)
        → preservesCartesianStr (reind f) (str x) (str y))

  FibrewiseCartesianClosed : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓp ℓp'))
  FibrewiseCartesianClosed =
    Σ[ str ∈ ((x : B.ob) → CartesianClosedStr P⟨ x ⟩) ]
      ({x y : B.ob} (f : B.1Cell y x)
        → preservesCartesianClosedStr (reind f) (str x) (str y))

module _ {B : Bicategory ℓ ℓ' ℓ''} where
  -- A prestack valued in categories-with-terminal-objects is a
  -- prestack whose fibres have terminal objects preserved by
  -- reindexing.
  TerminalPrestackIso : Iso (Pseudofunctor (B ^opᴮ) (TerminalCAT {ℓp} {ℓp'}))
    (Σ[ P ∈ Prestack B ℓp ℓp' ] FibrewiseTerminal P)
  TerminalPrestackIso = StructuredPseudofunctorIso TerminalStructure

  -- ... and likewise for cartesian structure.
  CartesianPrestackIso :
    Iso (Pseudofunctor (B ^opᴮ) (CartesianCAT {ℓp} {ℓp'}))
      (Σ[ P ∈ Prestack B ℓp ℓp' ] FibrewiseCartesian P)
  CartesianPrestackIso = StructuredPseudofunctorIso CartesianStructure

  CartesianClosedPrestackIso :
    Iso (Pseudofunctor (B ^opᴮ) (CartesianClosedCAT {ℓp} {ℓp'}))
      (Σ[ P ∈ Prestack B ℓp ℓp' ] FibrewiseCartesianClosed P)
  CartesianClosedPrestackIso =
    StructuredPseudofunctorIso CartesianClosedStructure

-- ------------------------------------------------------------------
-- Agreement with the fibrewise presentation of `Prestack.Fiberwise`.
-- ------------------------------------------------------------------

private
  preservesTerminal'→preservesTerminal :
    {C : Category ℓ ℓ'} {D : Category ℓb ℓb'}
    (F : Functor C D) (t : Terminal' C)
    → preservesTerminal' F t → preservesTerminal C D F
  preservesTerminal'→preservesTerminal {C = C} {D = D} F t p =
    preserveOnePreservesAll C D F (Terminal'ToTerminal t)
      (Terminal'ToTerminal
        (becomesUniversal→UniversalElement
          (invPshIso (reindPsh-Unit F) .PshIso.trans) p) .snd)

module _ {C : Category ℓ ℓ'} (P : Prestack (LocallyDiscrete C) ℓp ℓp') where
  open PrestackNotation P

  FibrewiseTerminal→Terminalsⱽ : FibrewiseTerminal P → Terminalsⱽ (∫Pre P)
  FibrewiseTerminal→Terminalsⱽ (term , pres) =
    ∫PreTerminalsⱽ P (λ x → Terminal'ToTerminal (term x))
      (λ {x} {y} f →
        preservesTerminal'→preservesTerminal (reind f) (term y) (pres f))

  FibrewiseCartesian→CartesianCategoryⱽ :
    FibrewiseCartesian P → CartesianCategoryⱽ C ℓp ℓp'
  FibrewiseCartesian→CartesianCategoryⱽ (str , pres) =
    ∫PreCartesianCategoryⱽ P
      (λ x → Terminal'ToTerminal (str x .fst))
      (λ {x} {y} f →
        preservesTerminal'→preservesTerminal (reind f) (str y .fst)
          (pres f .fst))
      (λ {x} a b → str x .snd (a , b))
      (λ f a b → pres f .snd a b)

-- The pseudofunctor presentation feeds `Fiberwise` directly: a
-- pseudofunctor into `CartesianCAT` makes its Grothendieck
-- construction a vertically cartesian fibration.
module _ {C : Category ℓ ℓ'} where
  CartesianPrestack→CartesianCategoryⱽ :
    (Q : Pseudofunctor (LocallyDiscrete C ^opᴮ) (CartesianCAT {ℓp} {ℓp'}))
    → CartesianCategoryⱽ C ℓp ℓp'
  CartesianPrestack→CartesianCategoryⱽ Q =
    FibrewiseCartesian→CartesianCategoryⱽ
      (CartesianPrestackIso .Iso.fun Q .fst)
      (CartesianPrestackIso .Iso.fun Q .snd)

  TerminalPrestack→Terminalsⱽ :
    (Q : Pseudofunctor (LocallyDiscrete C ^opᴮ) (TerminalCAT {ℓp} {ℓp'}))
    → Terminalsⱽ (∫Pre (TerminalPrestackIso .Iso.fun Q .fst))
  TerminalPrestack→Terminalsⱽ Q =
    FibrewiseTerminal→Terminalsⱽ (TerminalPrestackIso .Iso.fun Q .fst)
      (TerminalPrestackIso .Iso.fun Q .snd)
