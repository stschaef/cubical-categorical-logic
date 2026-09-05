{-# OPTIONS --lossy-unification #-}
{- The equifier prestack of `θ φ : B.2Cell f g`: a probe `x` is sent to
   the full subcategory of `B.Hom[ x , a ]` on the `h` with
   `h ◁w θ ≡ h ◁w φ`. -}
module Cubical.Categories.Bicategory.Prestack.Equifier where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More hiding (α)
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.FullSubcategory

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Properties.Coherence
open import Cubical.Categories.Bicategory.Constructions.Op
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Hom
open import Cubical.Categories.Bicategory.Transformation.Composition

private
  variable
    ℓ ℓ' ℓ'' : Level

open Category
open Functor
open NatTrans
open NatIso
open isIso
open LaxFunctor
open Pseudofunctor

-- Mirror of `▷⋆₁`, by instantiating it at the opposite bicategory.
module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B
module EquifierPre {B : Bicategory ℓ ℓ' ℓ''} {a b : Bicategory.0Cell B}
  {f g : Bicategory.1Cell B a b} (θ φ : Bicategory.2Cell B f g) where
  private
    module B = Bicategory B

  EqPred : {x : B.0Cell} → B.1Cell x a → Type ℓ''
  EqPred h = (h B.◁w θ) ≡ (h B.◁w φ)

  isPropEqPred : {x : B.0Cell} (h : B.1Cell x a) → isProp (EqPred h)
  isPropEqPred {x} h = B.Hom[ x , b ] .isSetHom _ _

  reindPred : {x y : B.0Cell} (k : B.1Cell y x) {h : B.1Cell x a}
    → EqPred h → EqPred (k B.⋆₁ h)
  reindPred k {h} p =
    ⋆CancelR (αI B k h g)
      (⋆CancelL (invIso (αI B k h f))
        (sym (◁⋆₁ B θ h k) ∙ (λ i → k B.◁w p i) ∙ ◁⋆₁ B φ h k))

  EqCat : B.0Cell → Category (ℓ-max ℓ' ℓ'') ℓ''
  EqCat x = FullSubcategory B.Hom[ x , a ] EqPred

  eqReind : {x y : B.0Cell} (k : B.1Cell y x)
    → Functor (EqCat x) (EqCat y)
  eqReind {x} {y} k = MapFullSubcategory B.Hom[ x , a ] EqPred
    B.Hom[ y , a ] EqPred (B.precomp k) (λ _ → reindPred k)

  eqReind₂ : {x y : B.0Cell} {k k' : B.1Cell y x} (σ : B.2Cell k k')
    → NatTrans (eqReind k) (eqReind k')
  eqReind₂ σ .N-ob e = σ B.▷w (e .fst)
  eqReind₂ σ .N-hom β = sym (▷◁exch B σ β)

  private
    module HA = Pseudofunctor (Hom B a)

    EqPrecomp : {x y : B.0Cell}
      → Functor B.Hom[ y , x ] (FUNCTOR (EqCat x) (EqCat y))
    EqPrecomp .F-ob k = eqReind k
    EqPrecomp .F-hom σ = eqReind₂ σ
    EqPrecomp .F-id = makeNatTransPath (funExt λ e → B.▷wId (e .fst))
    EqPrecomp .F-seq σ τ =
      makeNatTransPath (funExt λ e → ▷wSeq B σ τ (e .fst))

    ιNT : (x : B.0Cell) → NatTrans (Id {C = EqCat x}) (eqReind B.id₁)
    ιNT x .N-ob e = B.λ⁻ (e .fst)
    ιNT x .N-hom β = λ⁻-nat B β

    ι⁻NT : (x : B.0Cell) → NatTrans (eqReind B.id₁) (Id {C = EqCat x})
    ι⁻NT x .N-ob e = B.λ⁺ (e .fst)
    ι⁻NT x .N-hom β = λ-nat B β

    νNT : {x y z : B.0Cell} (k : B.1Cell y x) (l : B.1Cell z y)
      → NatTrans (seqCAT (EqCat x) (EqCat y) (EqCat z)
                    .F-ob (eqReind k , eqReind l))
                 (eqReind (l B.⋆₁ k))
    νNT k l .N-ob e = B.α⁻ l k (e .fst)
    νNT k l .N-hom β = α⁻natR B l k β

    ν⁻NT : {x y z : B.0Cell} (k : B.1Cell y x) (l : B.1Cell z y)
      → NatTrans (eqReind (l B.⋆₁ k))
                 (seqCAT (EqCat x) (EqCat y) (EqCat z)
                    .F-ob (eqReind k , eqReind l))
    ν⁻NT k l .N-ob e = B.α⁺ l k (e .fst)
    ν⁻NT k l .N-hom β = α⁺natR B l k β

  EquifierLax : LaxFunctor (B ^opᴮ) (CAT {ℓ-max ℓ' ℓ''} {ℓ''})
  EquifierLax .F-ob = EqCat
  EquifierLax .F-Hom {x} {y} = EqPrecomp {x} {y}
  EquifierLax .F-id {x} .N-ob _ = ιNT x
  EquifierLax .F-id {x} .N-hom σ = makeNatTransPath (funExt λ e →
    N-obPath (HA.F-id .N-hom σ) (e .fst))
  EquifierLax .F-seq .N-ob (k , l) = νNT k l
  EquifierLax .F-seq .N-hom στ = makeNatTransPath (funExt λ e →
    N-obPath (HA.F-seq .N-hom στ) (e .fst))
  EquifierLax .lax-λ x y k = makeNatTransPath (funExt λ e →
    N-obPath (HA.lax-λ x y k) (e .fst))
  EquifierLax .lax-ρ x y k = makeNatTransPath (funExt λ e →
    N-obPath (HA.lax-ρ x y k) (e .fst))
  EquifierLax .lax-α x y z w k l m = makeNatTransPath (funExt λ e →
    N-obPath (HA.lax-α x y z w k l m) (e .fst))

  Prestk : Prestack B (ℓ-max ℓ' ℓ'') ℓ''
  Prestk .laxFunctor = EquifierLax
  Prestk .F-id-isIso {x} _ .inv = ι⁻NT x
  Prestk .F-id-isIso {x} _ .sec = makeNatTransPath (funExt λ e →
    B.λU x a .nIso (tt* , e .fst) .ret)
  Prestk .F-id-isIso {x} _ .ret = makeNatTransPath (funExt λ e →
    B.λU x a .nIso (tt* , e .fst) .sec)
  Prestk .F-seq-isIso (k , l) .inv = ν⁻NT k l
  Prestk .F-seq-isIso {x} {y} {z} (k , l) .sec =
    makeNatTransPath (funExt λ e →
      B.α z y x a .nIso (l , k , e .fst) .ret)
  Prestk .F-seq-isIso {x} {y} {z} (k , l) .ret =
    makeNatTransPath (funExt λ e →
      B.α z y x a .nIso (l , k , e .fst) .sec)

  -- The forgetful functor to `Hom B a` is the full inclusion, so isos
  -- upstairs are just invertible 2-cells satisfying the predicate.
  eqForget : (x : B.0Cell) → Functor (EqCat x) B.Hom[ x , a ]
  eqForget x = FullInclusion B.Hom[ x , a ] EqPred

  eqIso : {x : B.0Cell} {h h' : B.1Cell x a} {p : EqPred h} {q : EqPred h'}
    → h B.≅₂ h' → CatIso (EqCat x) (h , p) (h' , q)
  eqIso {x} = Incl-Iso-inv B.Hom[ x , a ] EqPred _ _

module _ (B : Bicategory ℓ ℓ' ℓ'') {a b : Bicategory.0Cell B}
  {f g : Bicategory.1Cell B a b} where
  EquifierPrestack : (θ φ : Bicategory.2Cell B f g)
    → Prestack B (ℓ-max ℓ' ℓ'') ℓ''
  EquifierPrestack θ φ = EquifierPre.Prestk {B = B} {a = a} {b = b} θ φ
