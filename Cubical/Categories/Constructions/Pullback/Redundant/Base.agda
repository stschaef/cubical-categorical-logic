{-# OPTIONS --safe #-}

{- The universal category C ⊗ D with a redundant bifunctor C , D → C ⊗ D -}
{- Isomorphic (but not definitionally) to the cartesian product -}
{- Credit to Andreas Nuyts for suggesting this approach -}

module Cubical.Categories.Constructions.Pullback.Redundant.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base hiding (Id)
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Data.Graph.Base
open import Cubical.Data.Sum as Sum hiding (rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Quiver.Base
open import Cubical.Categories.Limits.Pullback

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
module _ (C : Category ℓc ℓc') where
  private
    data PBGenerator : Type ((ℓ-max ℓc ℓc')) where
      homl : ∀ {l m r l' : C .ob} →
        C [ l' , l ] → PBGenerator
      homr : ∀ {l m r r' : C .ob} →
        C [ r' , r ] → PBGenerator
      homm : ∀ {l m r m' : C .ob} →
        C [ m , m' ] → PBGenerator
      homlm : ∀ {l m r l' m' : C .ob} →
        C [ l' , l ] → C [ m , m' ] → PBGenerator
      homrm : ∀ {l m r r' m' : C .ob} →
        C [ r' , r ] → C [ m , m' ] → PBGenerator
      homlr : ∀ {l m r l' r' : C .ob} →
        C [ l' , l ] → C [ r' , r ] → PBGenerator
      homlmr : ∀ {l m r l' r' m' : C .ob} →
        C [ l' , l ] → C [ m , m' ] → C [ r' , r ] → PBGenerator


    data PBAx : Type (ℓ-max ℓc ℓc') where
      idPB : ∀ (l m r : C .ob) → PBAx
      seqPB : ∀ {l m r l' m' r' l'' m'' r'' : C .ob} →
              C [ l' , l ] → C [ m , m' ] → C [ r' , r ] →
              C [ l'' , l' ] → C [ m' , m'' ] → C [ r'' , r' ] → PBAx
      lagree : ∀ {l l' : C .ob} → (m r : C .ob) → C [ l' , l ] → PBAx
      ragree : ∀ {r r' : C .ob} → (l m : C .ob) → C [ r' , r ] → PBAx
      magree : ∀ {m m' : C .ob} → (l r : C .ob) → C [ m , m' ] → PBAx
      lmagree : ∀ {l l' m m' : C .ob} → (r : C .ob) → C [ l' , l ] →
                C [ m , m' ] → PBAx
      rmagree : ∀ {r r' m m' : C .ob} → (l : C .ob) → C [ r' , r ] →
                C [ m , m' ] → PBAx
      lragree : ∀ {l l' r r' : C .ob} → (m : C .ob) → C [ l' , l ] →
                C [ r' , r ] → PBAx

    Q : Quiver ℓc (ℓ-max ℓc ℓc')
    Q .fst = C .ob × C .ob × C .ob
    Q .snd .mor = PBGenerator
    Q .snd .dom (homl {l}{m}{r}{l'} f) = l , m , r
    Q .snd .cod (homl {l}{m}{r}{l'} f) = l' , m , r
    Q .snd .dom (homr {l}{m}{r}{r'} f) = l , m , r
    Q .snd .cod (homr {l}{m}{r}{r'} f) = l , m , r'
    Q .snd .dom (homm {l}{m}{r}{m'} f) = l , m , r
    Q .snd .cod (homm {l}{m}{r}{m'} f) = l , m' , r
    Q .snd .dom (homlm {l}{m}{r}{l'}{m'} f g) = l , m , r
    Q .snd .cod (homlm {l}{m}{r}{l'}{m'} f g) = l' , m' , r
    Q .snd .dom (homrm {l}{m}{r}{r'}{m'} f g) = l , m , r
    Q .snd .cod (homrm {l}{m}{r}{r'}{m'} f g) = l , m' , r'
    Q .snd .dom (homlr {l}{m}{r}{l'}{r'} f g) = l , m , r
    Q .snd .cod (homlr {l}{m}{r}{l'}{r'} f g) = l' , m , r'
    Q .snd .dom (homlmr {l}{m}{r}{l'}{r'}{m'} f g h) = l , m , r
    Q .snd .cod (homlmr {l}{m}{r}{l'}{r'}{m'} f g h) = l' , m' , r'

    mkAxHelper :
      PBAx →
        Σ-syntax (FreeCat Q .ob)
        (λ A →
           Σ-syntax (FreeCat Q .ob)
           (λ B → (FreeCat Q [ A , B ]) × (FreeCat Q [ A , B ])))
    mkAxHelper (idPB l m r) =
      _ , _ ,
      (η Q <$g> homlmr (C .id {l}) (C .id {m}) (C .id {r})) ,
      FreeCat Q .id
    mkAxHelper (seqPB f g h f' g' h') =
      _ , _ ,
      (η Q <$g> homlmr (f' ⋆⟨ C ⟩ f) (g ⋆⟨ C ⟩ g') (h' ⋆⟨ C ⟩ h)) ,
      η Q <$g> homlmr f g h ⋆⟨ FreeCat Q ⟩ (η Q <$g> homlmr f' g' h')
    mkAxHelper (lagree m r f) =
      _ , _ ,
      (η Q <$g> homl f) ,
      (η Q <$g> homlmr f (C .id {m}) (C .id {r}))
    mkAxHelper (ragree l m f) =
      _ , _ ,
      (η Q <$g> homr f) ,
      (η Q <$g> homlmr (C .id {l}) (C .id {m}) f)
    mkAxHelper (magree l r f) =
      _ , _ ,
      (η Q <$g> homm f) ,
      (η Q <$g> homlmr (C .id {l}) f (C .id {r}))
    mkAxHelper (lmagree r f g) =
      _ , _ ,
      (η Q <$g> homlm f g) ,
      (η Q <$g> homlmr f g (C .id {r}))
    mkAxHelper (rmagree l f g) =
      _ , _ ,
      (η Q <$g> homrm f g) ,
      (η Q <$g> homlmr (C .id {l}) g f)
    mkAxHelper (lragree m f g) =
      _ , _ ,
      (η Q <$g> homlr f g) ,
      (η Q <$g> homlmr f (C .id {m}) g)

    Ax : Axioms (FreeCat Q) (ℓ-max ℓc ℓc')
    Ax = mkAx (FreeCat Q) PBAx mkAxHelper

  module PbCat = QuoByAx (FreeCat Q) Ax
  PresCat = PbCat.PresentedCat

