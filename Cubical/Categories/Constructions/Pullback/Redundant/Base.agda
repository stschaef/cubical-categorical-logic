{-# OPTIONS --safe #-}

{- The universal category C ⊗ D with a redundant bifunctor C , D → C ⊗ D -}
{- Isomorphic (but not definitionally) to the cartesian product -}
{- Credit to Andreas Nuyts for suggesting this approach -}

module Cubical.Categories.Constructions.Pullback.Redundant.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base hiding (Id)
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Cospan
open import Cubical.Categories.Instances.Finite.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Data.Graph.Base
open import Cubical.Data.Sum as Sum hiding (rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Quiver.Base
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Constructions.Slice.Base

open import Cubical.Tactics.CategorySolver.Reflection

open import Cubical.Categories.Constructions.Free.Category.Quiver as Free
  hiding (rec)
open import Cubical.Categories.Constructions.Presented as Presented

private
  variable
    ℓb ℓb' ℓc ℓc' ℓd ℓd' ℓe ℓe' ℓ ℓ' : Level

open Category
open Functor
open QuiverOver
open Axioms

{--
-- The idea is to echo the reasoning from BinProduct.Redundant.Base except
-- in the shape of a pullback
--
--      s₁
-- l --------> m
--             ^
--             |
--             | s₂
--             |
--             r
----}
module RedundantPullback (C : Category ℓc ℓc') where
  private
    open Cospan
    data PBGenerator : Type ((ℓ-max ℓc ℓc')) where
      homl : ∀ (cspn : Cospan C) {l' : C .ob} →
        C [ l' , cspn .l ] → PBGenerator
      homr : ∀ (cspn : Cospan C){r' : C .ob} →
        C [ r' , cspn .r ] → PBGenerator
      homm : ∀ (cspn : Cospan C){m' : C .ob} →
        C [ cspn .m , m' ] → PBGenerator
      homlm : ∀ (cspn : Cospan C){l' m' : C .ob} →
        C [ l' , cspn .l ] → C [ cspn .m , m' ] → PBGenerator
      homrm : ∀ (cspn : Cospan C){r' m' : C .ob} →
        C [ r' , cspn .r ] → C [ cspn .m , m' ] → PBGenerator
      homlr : ∀ (cspn : Cospan C){l' r' : C .ob} →
        C [ l' , cspn .l ] → C [ r' , cspn .r ] → PBGenerator
      homlmr : ∀ (cspn : Cospan C){l' r' m' : C .ob} →
        C [ l' , cspn .l ] → C [ cspn .m , m' ] → C [ r' , cspn .r ] →
        PBGenerator

    data PBAx : Type (ℓ-max ℓc ℓc') where
      idPB : ∀ (cspn : Cospan C) → PBAx
      seqPB : ∀ (cspn : Cospan C) {l' m' r' l'' m'' r'' : C .ob} →
              C [ l' , cspn .l ] → C [ cspn .m , m' ] → C [ r' , cspn .r ] →
              C [ l'' , l' ] → C [ m' , m'' ] → C [ r'' , r' ] → PBAx
      lagree : ∀ (cspn : Cospan C) → {l' : C .ob} → C [ l' , cspn .l ] → PBAx
      ragree : ∀ (cspn : Cospan C) → {r' : C .ob} → C [ r' , cspn .r ] → PBAx
      magree : ∀ (cspn : Cospan C) → {m' : C .ob} → C [ cspn .m , m' ] → PBAx
      lmagree : ∀ (cspn : Cospan C) {l' m' : C .ob} → C [ l' , cspn .l ] →
                C [ cspn .m , m' ] → PBAx
      rmagree : ∀ (cspn : Cospan C) {r' m' : C .ob} → C [ r' , cspn .r ] →
                C [ cspn .m , m' ] → PBAx
      lragree : ∀ (cspn : Cospan C){l' r' : C .ob} → C [ l' , cspn .l ] →
                C [ r' , cspn .r ] → PBAx

    data cospanIdxObs : Type₀ where
      cspnl : cospanIdxObs
      cspnm : cospanIdxObs
      cspnr : cospanIdxObs

    data cospanIdxHoms : Type (ℓ-suc ℓ-zero) where
      cspns₁ : cospanIdxHoms
      cspns₂ : cospanIdxHoms

    cospanQuiv : Quiver ℓ-zero (ℓ-suc ℓ-zero)
    cospanQuiv .fst = cospanIdxObs
    cospanQuiv .snd .mor = cospanIdxHoms
    cospanQuiv .snd .dom cspns₁ = cspnl
    cospanQuiv .snd .cod cspns₁ = cspnm
    cospanQuiv .snd .dom cspns₂ = cspnr
    cospanQuiv .snd .cod cspns₂ = cspnm

    cospanFunCat : Category
      (ℓ-max (ℓ-max ℓ-zero (ℓ-suc ℓ-zero)) (ℓ-max ℓc ℓc'))
      (ℓ-max (ℓ-max ℓ-zero (ℓ-suc ℓ-zero)) ℓc')
    cospanFunCat = Cᴶ C cospanQuiv

    interp : (Cospan C) → Interp cospanQuiv C
    interp (cospan l m r s₁ s₂) $g cspnl = l
    interp (cospan l m r s₁ s₂) $g cspnm = m
    interp (cospan l m r s₁ s₂) $g cspnr = r
    interp (cospan l m r s₁ s₂) <$g> cspns₁ = s₁
    interp (cospan l m r s₁ s₂) <$g> cspns₂ = s₂

    mkCospanFun : (cspn : Cospan C) → (cospanFunCat .ob)
    mkCospanFun cspn = Free.rec cospanQuiv (interp cspn)

    Q : Quiver (ℓ-max ℓc ℓc') (ℓ-max ℓc ℓc')
    Q .fst = Cospan C
    Q .snd .mor = PBGenerator
    Q .snd .dom (homl (cospan l m r s s') {l'} f) =
      (cospan l m r s s')
    Q .snd .cod (homl (cospan l m r s s') {l'} f) =
      (cospan l' m r (f ⋆⟨ C ⟩ s) s')
    Q .snd .dom (homr (cospan l m r s s') {r'} f) =
      (cospan l m r s s')
    Q .snd .cod (homr (cospan l m r s s') {r'} f) =
      (cospan l m r' s (f ⋆⟨ C ⟩ s'))
    Q .snd .dom (homm (cospan l m r s s') {m'} f) =
      (cospan l m r s s')
    Q .snd .cod (homm (cospan l m r s s') {m'} f) =
      (cospan l m' r (s ⋆⟨ C ⟩ f) (s' ⋆⟨ C ⟩ f))
    Q .snd .dom (homlm (cospan l m r s s') {l'}{m'} f g) =
      (cospan l m r s s')
    Q .snd .cod (homlm (cospan l m r s s') {l'}{m'} f g) =
      (cospan l' m' r (f ⋆⟨ C ⟩ s ⋆⟨ C ⟩ g) (s' ⋆⟨ C ⟩ g))
    Q .snd .dom (homrm (cospan l m r s s') {r'}{m'} f g) =
      (cospan l m r s s')
    Q .snd .cod (homrm (cospan l m r s s') {r'}{m'} f g) =
      (cospan l m' r' (s ⋆⟨ C ⟩ g) (f ⋆⟨ C ⟩ s' ⋆⟨ C ⟩ g))
    Q .snd .dom (homlr (cospan l m r s s') {l'}{r'} f g) =
      (cospan l m r s s')
    Q .snd .cod (homlr (cospan l m r s s') {l'}{r'} f g) =
      (cospan l' m r' (f ⋆⟨ C ⟩ s) (g ⋆⟨ C ⟩ s'))
    Q .snd .dom (homlmr (cospan l m r s s') {l'}{r'}{m'} f g h) =
      (cospan l m r s s')
    Q .snd .cod (homlmr (cospan l m r s s') {l'}{r'}{m'} f g h) =
      (cospan l' m' r' (f ⋆⟨ C ⟩ s ⋆⟨ C ⟩ g) (h ⋆⟨ C ⟩ s' ⋆⟨ C ⟩ g))

    transport-cod-lmr : (cspn cspn' : Cospan C) →
      (ϕ : C [ cspn' .l , cspn' .m ])(ψ : C [ cspn' .r , cspn' .m ])
      (p : cspn' .s₁ ≡ ϕ) (q : cspn' .s₂ ≡ ψ) →
      (FreeCat Q [ cspn , cspn' ]) →
      (FreeCat Q [ cspn ,
                   (cospan (cspn' .l) (cspn' .m) (cspn' .r) ϕ ψ) ])
    transport-cod-lmr cspn cspn' ϕ ψ p q f =
      transport
        (cong₂ (λ a b →
          (FreeCat Q) [
            cspn ,
            (cospan (cspn' .l) (cspn' .m) (cspn' .r) a b) ])
           p
           q
        )
        f

    mkAxHelper :
      PBAx →
        Σ-syntax (FreeCat Q .ob)
        (λ A →
           Σ-syntax (FreeCat Q .ob)
           (λ B → (FreeCat Q [ A , B ]) × (FreeCat Q [ A , B ])))
    mkAxHelper (idPB (cospan l m r s s')) =
      _ , _ ,
      η Q <$g> homlmr (cospan l m r s s') (C .id) (C .id) (C .id) ,
      transport-cod-lmr _ _ _ _
        (sym (C .⋆IdR _ ∙ C .⋆IdL _))
        (sym (C .⋆IdR _ ∙ C .⋆IdL _))
        (FreeCat Q .id)
    mkAxHelper (seqPB cspn {l'}{m'}{r'}{l''}{m''}{r''} f g h f' g' h') =
      _ , _ ,
      (η Q <$g> homlmr cspn (f' ⋆⟨ C ⟩ f) (g ⋆⟨ C ⟩ g') (h' ⋆⟨ C ⟩ h)) ,
      η Q <$g> homlmr cspn f g h
        ⋆⟨ FreeCat Q ⟩ (
      transport-cod-lmr
        _ _ _ _
        -- TODO : category solver busted?
        (C .⋆Assoc _ _ _ ∙
        cong (λ a → f' ⋆⟨ C ⟩ a) (C .⋆Assoc _ _ _) ∙
        sym (C .⋆Assoc _ _ _) ∙
        cong (λ a → a ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ g')) (sym (C .⋆Assoc _ _ _)))
        (C .⋆Assoc _ _ _ ∙
        cong (λ a → h' ⋆⟨ C ⟩ a) (C .⋆Assoc _ _ _) ∙
        sym (C .⋆Assoc _ _ _) ∙
        cong (λ a → a ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ g')) (sym (C .⋆Assoc _ _ _)))
        (η Q <$g> homlmr (cospan l' m' r' _ _) f' g' h'))
    mkAxHelper (lagree cspn f) =
      _ , _ ,
      (η Q <$g> homl cspn f) ,
      transport-cod-lmr
      _ _ _ _
      (C .⋆IdR _)
      (C .⋆IdR _ ∙ C .⋆IdL _)
      (η Q <$g> homlmr cspn f (C .id) (C .id))
    mkAxHelper (ragree cspn f) =
      _ , _ ,
      (η Q <$g> homr cspn f) ,
      transport-cod-lmr _ _ _ _
      (C .⋆IdR _ ∙ C .⋆IdL _)
      (C .⋆IdR _)
      (η Q <$g> homlmr cspn (C .id) (C .id) f)
    mkAxHelper (magree cspn f) =
      _ , _ ,
      (η Q <$g> homm cspn f) ,
      transport-cod-lmr _ _ _ _
      (C .⋆Assoc _ _ _ ∙ C .⋆IdL _)
      (C .⋆Assoc _ _ _ ∙ C .⋆IdL _)
      (η Q <$g> homlmr cspn (C .id) f (C .id))
    mkAxHelper (lmagree cspn f g) =
      _ , _ ,
      (η Q <$g> homlm cspn f g),
      transport-cod-lmr _ _ _ _
      refl
      (C .⋆Assoc _ _ _ ∙ C .⋆IdL _)
      (η Q <$g> homlmr cspn f g (C .id))
    mkAxHelper (rmagree cspn f g) =
      _ , _ ,
      (η Q <$g> homrm cspn f g),
      transport-cod-lmr _ _ _ _
      (C .⋆Assoc _ _ _ ∙ C .⋆IdL _)
      refl
      (η Q <$g> homlmr cspn (C .id) g f)
    mkAxHelper (lragree cspn f g) =
      _ , _ ,
      (η Q <$g> homlr cspn f g),
      transport-cod-lmr _ _ _ _
      (C .⋆IdR _)
      (C .⋆IdR _)
      (η Q <$g> homlmr cspn f (C .id) g)

    Ax : Axioms (FreeCat Q) (ℓ-max ℓc ℓc')
    Ax = mkAx (FreeCat Q) PBAx mkAxHelper

  module PbCat = QuoByAx (FreeCat Q) Ax
  PresCat = PbCat.PresentedCat

  rec : {E : Category ℓ ℓ'} → (Interp Q E) → Functor PresCat E
  rec {E = E} int = PbCat.rec E (Free.rec Q int) ax-to-path where

    ax-to-path : (eq : Ax .equation) →
                   Free.rec Q int ⟪ Ax .lhs eq ⟫ ≡ Free.rec Q int ⟪ Ax .rhs eq ⟫
    ax-to-path (idPB cspn) = ?
    ax-to-path (seqPB cspn f g h f' g' h') = {!!}
    ax-to-path (lagree cspn f) = {!!}
    ax-to-path (ragree cspn f) = {!!}
    ax-to-path (magree cspn f) = {!!}
    ax-to-path (lmagree cspn f g) = {!!}
    ax-to-path (rmagree cspn f g) = {!!}
    ax-to-path (lragree cspn f g) = {!!}
