{-# OPTIONS --lossy-unification #-}
{-
  2-monads on a bicategory: a pseudofunctor `T : K → K` with a lax
  natural unit and multiplication, whose unit and associativity laws
  hold up to invertible modification.

  This is *not* a formal monad in a bicategory (a 1-cell `t : a → a`
  with 2-cells `a ⇒ t` and `t ⋆ t ⇒ t`); that is
  `Cubical.Categories.Bicategory.Monad`.

  The laws are invertible modifications, not equalities: `∘Lax` is
  unital and associative only up to `ridLax`/`lidLax`/`assocLax`, and
  already for the identity 2-monad the two sides differ by a unitor.
  Only the three laws are asked for here; the two further coherence
  axioms that would make this a pseudomonad in the sense of Marmolejo
  are not part of the record.
-}
module Cubical.Categories.Bicategory.TwoMonad where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Functor.Identity
open import Cubical.Categories.Bicategory.Functor.Composition
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.Transformation.Properties
open import Cubical.Categories.Bicategory.Transformation.Identity
open import Cubical.Categories.Bicategory.Transformation.Composition
open import Cubical.Categories.Bicategory.Transformation.Coherence
open import Cubical.Categories.Bicategory.Transformation.Whisker

private
  variable
    ℓ ℓ' ℓ'' : Level

open NatIso
open isIso
open LaxNatTrans
open Modification

record TwoMonad (K : Bicategory ℓ ℓ' ℓ'') :
  Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
  no-eta-equality
  field
    T : Pseudofunctor K K

  Tl : LaxFunctor K K
  Tl = T .Pseudofunctor.laxFunctor

  field
    η : LaxNatTrans (LaxId K) Tl
    μ : LaxNatTrans (Tl ∘Lax Tl) Tl

  Tη : LaxNatTrans (Tl ∘Lax LaxId K) (Tl ∘Lax Tl)
  Tη = whiskerL T η

  ηT : LaxNatTrans (LaxId K ∘Lax Tl) (Tl ∘Lax Tl)
  ηT = whiskerR Tl η

  Tμ : LaxNatTrans (Tl ∘Lax (Tl ∘Lax Tl)) (Tl ∘Lax Tl)
  Tμ = whiskerL T μ

  μT : LaxNatTrans ((Tl ∘Lax Tl) ∘Lax Tl) (Tl ∘Lax Tl)
  μT = whiskerR Tl μ

  field
    unitL : CatIso LaxNatTransCat (seqLaxNatTrans Tη μ) (ridLax Tl)
    unitR : CatIso LaxNatTransCat (seqLaxNatTrans ηT μ) (lidLax Tl)
    assoc : CatIso LaxNatTransCat
              (seqLaxNatTrans μT μ)
              (seqLaxNatTrans (assocLax Tl Tl Tl) (seqLaxNatTrans Tμ μ))

{-
  The identity 2-monad.  Not free: `seqLaxNatTrans` is unital only up
  to `lamMod`, so each law is that unitor, transported across the
  `id₂`s that `whiskerL` inserts.
-}
module _ (K : Bicategory ℓ ℓ' ℓ'') where
  private
    module K = Bicategory K

    IK : LaxFunctor K K
    IK = LaxId K

    II : LaxFunctor K K
    II = IK ∘Lax IK

    ηI : LaxNatTrans IK IK
    ηI = idLaxNatTrans IK

    μI : LaxNatTrans II IK
    μI = ridLax IK

    TηI : LaxNatTrans II II
    TηI = whiskerL (Idᴮ K) ηI

    ηTI : LaxNatTrans II II
    ηTI = whiskerR IK ηI

    TμI : LaxNatTrans (IK ∘Lax II) II
    TμI = whiskerL (Idᴮ K) μI

    μTI : LaxNatTrans (II ∘Lax IK) II
    μTI = whiskerR IK μI

    AI : LaxNatTrans (II ∘Lax IK) (IK ∘Lax II)
    AI = assocLax IK IK IK

    λI : (x : K.ob) → isIso K.Hom[ x , x ] (K.λ⁺ K.id₁)
    λI x = K.λU x x .nIso (tt* , K.id₁)

    -- `whiskerL (Idᴮ K)` inserts the two identity laxity cells.
    dropId₂ : {x y : K.ob} {f g : K.1Cell x y} (u : K.2Cell f g)
      → K.id₂ K.⋆₂ (u K.⋆₂ K.id₂) ≡ u
    dropId₂ u = K.⋆₂IdL _ ∙ K.⋆₂IdR _

    unitLMod : Modification (seqLaxNatTrans TηI μI) μI
    unitLMod .M-ob x = K.λ⁺ K.id₁
    unitLMod .M-hom f =
        K.⟨ K.⟨⟩⋆₂⟨ K.⟨ K.⟨ dropId₂ _ ⟩▷ K.id₁ ⟩⋆₂⟨⟩ ⟩ ⟩⋆₂⟨⟩
      ∙ lamMod μI .M-hom f

    unitRMod : Modification (seqLaxNatTrans ηTI μI) (lidLax IK)
    unitRMod .M-ob x = K.λ⁺ K.id₁
    unitRMod .M-hom f = lamMod μI .M-hom f

    assocMod₁ : Modification (seqLaxNatTrans AI TμI) μTI
    assocMod₁ .M-ob x = K.λ⁺ K.id₁
    assocMod₁ .M-hom f =
        K.⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨ K.id₁ K.◁⟨ dropId₂ _ ⟩ ⟩⋆₂⟨⟩ ⟩ ⟩ ⟩ ⟩⋆₂⟨⟩
      ∙ lamMod μTI .M-hom f

    assocMod₁Inv : Modification μTI (seqLaxNatTrans AI TμI)
    assocMod₁Inv = invMod assocMod₁ λI

    assocStep : Modification (seqLaxNatTrans μTI μI)
                             (seqLaxNatTrans (seqLaxNatTrans AI TμI) μI)
    assocStep = seqMod⋆ assocMod₁Inv (idMod μI)

  idTwoMonad : TwoMonad K
  idTwoMonad .TwoMonad.T = Idᴮ K
  idTwoMonad .TwoMonad.η = ηI
  idTwoMonad .TwoMonad.μ = μI
  idTwoMonad .TwoMonad.unitL = unitLMod , modIsIso unitLMod λI
  idTwoMonad .TwoMonad.unitR = unitRMod , modIsIso unitRMod λI
  idTwoMonad .TwoMonad.assoc =
      seqMod assocStep (assocMod AI TμI μI)
    , ⋆IsIso (modIsIso assocStep
                (λ x → ▷wIsIso K K.id₁
                  (invIso (K.λ⁺ K.id₁ , λI x) .snd)))
             (modIsIso (assocMod AI TμI μI)
                (λ x → K.α x x x x .nIso (K.id₁ , K.id₁ , K.id₁)))
