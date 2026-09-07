{-# OPTIONS --lossy-unification #-}
{-
  Conservativity of the free cartesian CLOSED category over the free
  category, through the RECURSOR applied to the Artin comma category.

  The glue is `PSH ↓ nerve` for the nerve of `⊆ : FREE → FREECCC`, so
  `D` is a presheaf category and the glue's exponential is the generic
  one of `Gluing.Bicategorical.Artin`, whose carrier is a pullback.
  A single functor `S : FREECCC → GLUE` built by `rec` gives both
  halves: its presheaf projection extends Yoneda, which is
  faithfulness, and its syntactic projection is naturally isomorphic
  to the identity, which turns the glue's witnesses into preimages.

  Compare
  `Gluing.CartesianClosedCategory.Conservativity.OverCategories.Forded`,
  which proves the same two theorems through displayed presheaves and
  `elimLocal`.
-}
module Gluing.Bicategorical.RecConservativity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Quiver.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Cartesian.More
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.Pullback.Alt
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.StrictHom
open import Cubical.Categories.Presheaf.Nerve

import Cubical.Categories.Instances.Free.Category.Forded as FC
import Cubical.Categories.Instances.Free.CartesianClosedCategory.Forded
  as FCCC
open import
  Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
  using (Quiver→×⇒Quiver; ↑_; CCCExpr)

import Gluing.Bicategorical.Artin as Artin
open import Gluing.Bicategorical.CanonicityCore using (module Exp)

private
  variable ℓQ ℓQ' ℓC ℓC' ℓP : Level

open Category
open Functor
open PshHomStrict
open UniversalElement
open CartesianCategory using (C; term; bp)
open CartesianClosedCategory using (CC; exps)


module _ (Q : Quiver ℓQ ℓQ') where
  private
    module Q = QuiverOver (Q .snd)
    ×⇒Q = Quiver→×⇒Quiver Q
    ℓ = ℓ-max ℓQ ℓQ'

  FREE : Category ℓQ ℓ
  FREE = FC.FreeCat Q

  private module FREE = Category FREE

  FREECCC : CartesianClosedCategory ℓQ ℓ
  FREECCC = FCCC.FreeCartesianClosedCategory ×⇒Q

  private module FREECCC = CartesianClosedCategory FREECCC

  ı : FC.Interp Q FREECCC.C
  ı ._$g_ = ↑_
  ı ._<$g>_ = FCCC.↑ₑ ×⇒Q

  ⊆ : Functor FREE FREECCC.C
  ⊆ = FC.rec Q ı

  PSH : CartesianClosedCategory _ _
  PSH = CCC-PRESHEAF FREE ℓ

  private module PSH = CartesianClosedCategory PSH

  nerve : Functor FREECCC.C PSH.C
  nerve = Nerve ⊆

  nerve-bp : preservesProvidedBinProducts nerve FREECCC.bp
  nerve-bp = Nerve-pres-bp ⊆ FREECCC.bp

  -- the unit of the nerve, at a generating object
  unit : (o : Q .fst) → PshHomStrict (YOStrict ⟅ o ⟆) (nerve ⟅ ↑ o ⟆)
  unit o .N-ob c k = ⊆ ⟪ k ⟫
  unit o .N-hom c c' f k' k e =
    sym (⊆ .F-seq f k') ∙ cong (⊆ .F-hom) e

  -- the glue is the comma category `PSH ↓ nerve`, cartesian closed by
  -- the generic construction, whose carrier is a presheaf pullback
  GLUE : CartesianClosedCategory _ _
  GLUE .CC .C =
    Artin.GlCCC FREECCC PSH nerve (Artin.PSHPullbacks FREE ℓ) nerve-bp
  GLUE .CC .term = Artin.glueTerminal' nerve FREECCC.term
  GLUE .CC .bp =
    Artin.bpGlCCC FREECCC PSH nerve (Artin.PSHPullbacks FREE ℓ) nerve-bp
  GLUE .exps =
    Artin.glueExponentials' FREECCC PSH nerve (Artin.PSHPullbacks FREE ℓ)
      nerve-bp

  private module GLUE = CartesianClosedCategory GLUE

  glueOb : (o : Q .fst) → GLUE.C .ob
  glueOb o = (YOStrict ⟅ o ⟆ , ↑ o) , unit o

  glueHom : (e : Q.mor) → GLUE.C [ glueOb (Q.dom e) , glueOb (Q.cod e) ]
  glueHom e = (YOStrict ⟪ FC.⇑ Q e ⟫ , FCCC.↑ₑ ×⇒Q e)
    , makePshHomStrictPath
        (funExt₂ λ c k → sym (⊆ .F-seq k (FC.⇑ Q e)))

  S : Functor FREECCC.C GLUE.C
  S = FCCC.rec ×⇒Q GLUE (FCCC.mkElimInterpᴰ glueOb glueHom)

  projPsh : Functor GLUE.C PSH.C
  projPsh .F-ob g = g .fst .fst
  projPsh .F-hom m = m .fst .fst
  projPsh .F-id = refl
  projPsh .F-seq _ _ = refl

  projSyn : Functor GLUE.C FREECCC.C
  projSyn .F-ob g = g .fst .snd
  projSyn .F-hom m = m .fst .snd
  projSyn .F-id = refl
  projSyn .F-seq _ _ = refl

  extension : Functor FREECCC.C PSH.C
  extension = projPsh ∘F S

  T : Functor FREECCC.C FREECCC.C
  T = projSyn ∘F S

  -- FAITHFULNESS: the presheaf projection extends Yoneda
  commutes : YOStrict ≡ extension ∘F ⊆
  commutes = FC.FreeCatFunctor≡ Q _ _
    (record { _$gᴰ_ = λ _ → refl ; _<$g>ᴰ_ = λ _ → refl })

  ⊆-Faithful : isFaithful ⊆
  ⊆-Faithful = isFaithful-YOStrict-factor commutes

  private
    module CORE = Exp FREECCC
    open CORE using (module ⇒At)

    TCart : CartesianFunctor (FREECCC .CC) FREECCC.C
    TCart = T , λ c c' → FREECCC.bp (T ⟅ c ⟆ , T ⟅ c' ⟆) .universal

    IdCart : CartesianFunctor (FREECCC .CC) FREECCC.C
    IdCart = Id , λ c c' → FREECCC.bp (c , c') .universal

    FREECCC1 : Terminal FREECCC.C
    FREECCC1 = Terminal'ToTerminal FREECCC.term

    T-1 : preservesTerminal FREECCC.C FREECCC.C T
    T-1 = preserveOnePreservesAll FREECCC.C FREECCC.C T
      FREECCC1 (FREECCC1 .snd)

    Id-1 : preservesTerminal FREECCC.C FREECCC.C Id
    Id-1 = preserveOnePreservesAll FREECCC.C FREECCC.C Id
      FREECCC1 (FREECCC1 .snd)

    ⇒-isoT : ∀ {A B} → CatIso FREECCC.C (T ⟅ A ⟆) A
           → CatIso FREECCC.C (T ⟅ B ⟆) B
           → CatIso FREECCC.C (T ⟅ CCCExpr._⇒_ A B ⟆) (CCCExpr._⇒_ A B)
    ⇒-isoT f g = ⇒At.expIso f g

  -- The uniqueness principle, discharged for `T`.  Choosing
  -- `idCatIso` at the generators is what makes the components at
  -- generating objects the identity, which is what fullness needs.
  ηT : NatIso T (Id {C = FREECCC.C})
  ηT = FCCC.FreeCCCFunctor≅ ×⇒Q TCart IdCart T-1 Id-1 ⇒-isoT
    (λ f g → ⇒At.evalSq f g)
    (λ f g γ h sq → ⇒At.lamSq f g γ h (T ⟪ h ⟫) sq)
    (FCCC.mkElimInterpᴰ (λ _ → idCatIso)
      (λ _ → (FREECCC.⋆IdR _ ∙ sym (FREECCC.⋆IdL _)) , tt))

  -- FULLNESS
  module _ (o o' : Q .fst) (f : FREECCC.C [ ↑ o , ↑ o' ]) where
    private
      m : GLUE.C [ glueOb o , glueOb o' ]
      m = S ⟪ f ⟫

      preimage : FREE [ o , o' ]
      preimage = m .fst .fst .N-ob o FREE.id

      atId : ⊆ ⟪ FREE.id ⟫ ⋆⟨ FREECCC.C ⟩ T ⟪ f ⟫ ≡ ⊆ ⟪ preimage ⟫
      atId i = m .snd i .N-ob o FREE.id

      T≡ : T ⟪ f ⟫ ≡ ⊆ ⟪ preimage ⟫
      T≡ = sym (FREECCC.⋆IdL _)
         ∙ cong (FREECCC._⋆ T ⟪ f ⟫) (sym (⊆ .F-id))
         ∙ atId

      nat : T ⟪ f ⟫ ⋆⟨ FREECCC.C ⟩ FREECCC.id
          ≡ FREECCC.id ⋆⟨ FREECCC.C ⟩ f
      nat = ηT .NatIso.trans .NatTrans.N-hom f

    fullnessAt : Σ[ g ∈ FREE [ o , o' ] ] ⊆ ⟪ g ⟫ ≡ f
    fullnessAt = preimage
      , sym T≡ ∙ sym (FREECCC.⋆IdR _) ∙ nat ∙ FREECCC.⋆IdL f

  ⊆-Full : isFull ⊆
  ⊆-Full o o' f = ∣ fullnessAt o o' f ∣₁

  ⊆-FullyFaithful : isFullyFaithful ⊆
  ⊆-FullyFaithful =
    isFull+Faithful→isFullyFaithful {F = ⊆} ⊆-Full ⊆-Faithful
