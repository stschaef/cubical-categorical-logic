{-# OPTIONS --lossy-unification #-}
{- A 1-category as a bicategory whose 2-cells are `Eq` rather than
   `Path`.  `Eq`'s `refl` is a constructor, so `J` computes on it and
   the unitors and associator are `refl` rather than `isProp` fillers.
   The `Path` version is in `LocallyDiscrete.Base`. -}
module Cubical.Categories.Bicategory.Instances.LocallyDiscrete.Eq where

open import Cubical.Foundations.Prelude
  hiding (_≡_ ; refl ; sym ; _∙_ ; cong ; cong₂ ; transport ; J)
open import Cubical.Foundations.HLevels
import Cubical.Foundations.Prelude as P
open import Cubical.Data.Equality
  using (_≡_ ; refl ; sym ; _∙_ ; ap ; J ; eqToPath ; pathToEq
        ; PathPathEq)
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Terminal
open import Cubical.Categories.HLevels

open import Cubical.Categories.Bicategory.Base

private
  variable
    ℓ ℓ' : Level

open Category
open Functor
open NatTrans
open NatIso
open isIso
open Bicategory

-- A named module, kept OUT of `LocallyDiscreteEq`'s block: defined
-- alongside it, the termination checker treats the whole bicategory
-- as recursive.
module Hom2 (C : Category ℓ ℓ') where
  module C = Category C

  -- 2-cells are `Eq`, and they form a set because `C`'s homs do
  isSetEq : {x y : C.ob} (f g : C.Hom[ x , y ]) → isSet (f ≡ g)
  isSetEq f g =
    subst isSet (PathPathEq {x = f} {y = g})
      (isProp→isSet (C.isSetHom f g))

  -- the hom-category: objects are 1-cells, morphisms are `Eq`s
  HomEq : (x y : C.ob) → Category ℓ' ℓ'
  HomEq x y .ob = C.Hom[ x , y ]
  HomEq x y .Hom[_,_] f g = f ≡ g
  HomEq x y .id = refl
  HomEq x y ._⋆_ = _∙_
  -- `refl ∙ q` reduces, so `⋆IdL` is `refl` outright; the other two
  -- are `refl` after matching the `Eq` constructor
  HomEq x y .⋆IdL p = P.refl
  HomEq x y .⋆IdR p = idR p
    where
    idR : ∀ {f g : C.Hom[ x , y ]} (q : f ≡ g) → Path _ (q ∙ refl) q
    idR refl = P.refl
  HomEq x y .⋆Assoc p q r = assoc p q r
    where
    assoc : ∀ {f g h k : C.Hom[ x , y ]}
      (a : f ≡ g) (b : g ≡ h) (c : h ≡ k)
      → Path _ ((a ∙ b) ∙ c) (a ∙ (b ∙ c))
    assoc refl b c = P.refl
  HomEq x y .isSetHom {f} {g} = isSetEq f g

  -- every equation between 2-cells is a proposition, since `Eq` is
  -- equivalent to a path in a set; this discharges every law
  isProp2 : {x y : C.ob} {f g : C.Hom[ x , y ]} {p q : f ≡ g}
    → Path _ p q
  isProp2 {f = f} {g} {p} {q} =
    subst isProp (PathPathEq {x = f} {y = g}) (C.isSetHom f g) p q

  -- `Eq` composition computes on `refl`, so these are all `refl`
  -- after matching; none needs an `isProp` filler
  ⋆Eq : ∀ {x y z} {a a' : C.Hom[ x , y ]} {b b' : C.Hom[ y , z ]}
    → a ≡ a' → b ≡ b' → (a C.⋆ b) ≡ (a' C.⋆ b')
  ⋆Eq refl refl = refl

  ⋆EqSeq : ∀ {x y z} {a a' a'' : C.Hom[ x , y ]}
    {b b' b'' : C.Hom[ y , z ]}
    (p : a ≡ a') (p' : a' ≡ a'') (q : b ≡ b') (q' : b' ≡ b'')
    → Path _ (⋆Eq (p ∙ p') (q ∙ q')) (⋆Eq p q ∙ ⋆Eq p' q')
  ⋆EqSeq refl p' refl q' = P.refl

  invEq : ∀ {x y} {f g : C.Hom[ x , y ]} (q : f ≡ g)
    → Path _ (q ∙ sym q) refl
  invEq refl = P.refl

  invEq' : ∀ {x y} {f g : C.Hom[ x , y ]} (q : f ≡ g)
    → Path _ (sym q ∙ q) refl
  invEq' refl = P.refl

  -- naturality of a unitor/associator: both sides are `Eq`s between
  -- the same pair of 1-cells, and matching makes them `refl`
  natEq : ∀ {x y} {f g : C.Hom[ x , y ]} (p : f ≡ g)
    {a b : C.Hom[ x , y ]} (u : a ≡ f) (v : g ≡ b)
    → Path _ ((u ∙ p) ∙ v) (u ∙ (p ∙ v))
  natEq p refl v = P.refl


  -- the `id` and `seq` functors, and then each unitor and the
  -- associator as its own top-level definition
  idEq : (x : C.ob) → Functor 𝟙C (HomEq x x)
  idEq x .F-ob _ = C.id
  idEq x .F-hom _ = refl
  idEq x .F-id = P.refl
  idEq x .F-seq _ _ = P.refl

  seqEq : (x y z : C.ob) → Functor (HomEq x y ×C HomEq y z) (HomEq x z)
  seqEq x y z .F-ob (f , g) = f C.⋆ g
  seqEq x y z .F-hom (p , q) = ⋆Eq p q
  seqEq x y z .F-id = P.refl
  seqEq x y z .F-seq (p , q) (p' , q') = ⋆EqSeq p p' q q'

  λIsoEq : (x y : C.ob)
    → NatIso (seqEq x x y ∘F (idEq x ×F 𝟙⟨ HomEq x y ⟩))
             (Snd 𝟙C (HomEq x y))
  λIsoEq x y .trans .N-ob u = pathToEq (C.⋆IdL (u .snd))
  λIsoEq x y .trans .N-hom _ = isProp2
  λIsoEq x y .nIso u .inv = sym (pathToEq (C.⋆IdL (u .snd)))
  λIsoEq x y .nIso u .sec = invEq' (pathToEq (C.⋆IdL (u .snd)))
  λIsoEq x y .nIso u .ret = invEq (pathToEq (C.⋆IdL (u .snd)))

  ρIsoEq : (x y : C.ob)
    → NatIso (seqEq x y y ∘F (𝟙⟨ HomEq x y ⟩ ×F idEq y))
             (Fst (HomEq x y) 𝟙C)
  ρIsoEq x y .trans .N-ob u = pathToEq (C.⋆IdR (u .fst))
  ρIsoEq x y .trans .N-hom _ = isProp2
  ρIsoEq x y .nIso u .inv = sym (pathToEq (C.⋆IdR (u .fst)))
  ρIsoEq x y .nIso u .sec = invEq' (pathToEq (C.⋆IdR (u .fst)))
  ρIsoEq x y .nIso u .ret = invEq (pathToEq (C.⋆IdR (u .fst)))

  αIsoEq : (x y z w : C.ob)
    → NatIso (seqEq x z w ∘F (seqEq x y z ×F 𝟙⟨ HomEq z w ⟩)
                ∘F ×C-assoc (HomEq x y) (HomEq y z) (HomEq z w))
             (seqEq x y w ∘F (𝟙⟨ HomEq x y ⟩ ×F seqEq y z w))
  αIsoEq x y z w .trans .N-ob t =
    pathToEq (C.⋆Assoc (t .fst) (t .snd .fst) (t .snd .snd))
  αIsoEq x y z w .trans .N-hom _ = isProp2
  αIsoEq x y z w .nIso t .inv =
    sym (pathToEq (C.⋆Assoc (t .fst) (t .snd .fst) (t .snd .snd)))
  αIsoEq x y z w .nIso t .sec =
    invEq' (pathToEq (C.⋆Assoc (t .fst) (t .snd .fst) (t .snd .snd)))
  αIsoEq x y z w .nIso t .ret =
    invEq (pathToEq (C.⋆Assoc (t .fst) (t .snd .fst) (t .snd .snd)))

module _ (C : Category ℓ ℓ') where
  open Hom2 C

  LocallyDiscreteEq : Bicategory ℓ ℓ' ℓ'
  LocallyDiscreteEq .ob = C.ob
  LocallyDiscreteEq .Hom[_,_] = HomEq
  LocallyDiscreteEq .id {x} = idEq x
  LocallyDiscreteEq .seq = seqEq
  LocallyDiscreteEq .λU = λIsoEq
  LocallyDiscreteEq .ρU = ρIsoEq
  LocallyDiscreteEq .α = αIsoEq
  LocallyDiscreteEq .triangle _ _ _ _ _ = isProp2
  LocallyDiscreteEq .pentagon _ _ _ _ _ _ _ _ _ = isProp2

  hasPropHomsLDEq : (x y : C.ob)
    → hasPropHoms (Bicategory.Hom[_,_] LocallyDiscreteEq x y)
  hasPropHomsLDEq x y p q = isProp2
