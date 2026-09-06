{-# OPTIONS --lossy-unification #-}
{- The prestack of families of sets, and its Grothendieck construction. -}
module Cubical.Categories.Bicategory.Prestack.Instances.Sets where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism using (iso; isoToIsEquiv)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Instances.Discrete
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Constructions.Op
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Instances.LocallyDiscrete.Base
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Strict
open import Cubical.Categories.Bicategory.Prestack.Fiberwise
open import Cubical.Categories.Bicategory.Prestack.Grothendieck
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Isomorphism
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Sets.Properties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Limits.CartesianV'

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

private
  variable
    ℓ ℓ' ℓd ℓd' ℓe ℓe' : Level

open Category
open Functor
open NatTrans
open LaxFunctor
open Pseudofunctor
open isIso
open Functorᴰ
open Isoᴰ
open UniversalElement
open CartesianCategoryⱽ

-- A category all of whose homs are identities (`DiscreteCategory`,
-- `TerminalCategory`, products of these) supports naturality for free.
module _ {E : Category ℓe ℓe'} {D : Category ℓd ℓd'}
  (idH : {a b : E .ob} (f : E [ a , b ]) → isIdHom {C = E} f)
  {F G : Functor E D} (ν : (a : E .ob) → D [ F .F-ob a , G .F-ob a ])
  where
  private
    module D = Category D
    Nat : (a : E .ob) → Σ[ b ∈ E .ob ] E [ a , b ] → Type ℓd'
    Nat a u = F .F-hom (u .snd) D.⋆ ν (u .fst) ≡ ν a D.⋆ G .F-hom (u .snd)

    base : (a : E .ob) → Nat a (a , E .id)
    base a = cong (D._⋆ ν a) (F .F-id) ∙ D.⋆IdL _
           ∙ sym (D.⋆IdR _) ∙ cong (ν a D.⋆_) (sym (G .F-id))

  natFromIdHoms : NatTrans F G
  natFromIdHoms .N-ob = ν
  natFromIdHoms .N-hom {a} {b} f = subst (Nat a) (idH f) (base a)

idHomDisc : (A : hGroupoid ℓ) {a b : A .fst} (p : a ≡ b)
  → isIdHom {C = DiscreteCategory A} p
idHomDisc A {a} p = isContrSingl a .snd (_ , p)

idHom𝟙 : {a b : 𝟙C .ob} (f : 𝟙C [ a , b ]) → isIdHom {C = 𝟙C} f
idHom𝟙 _ = refl

-- the fibre of `SETᴰ ℓ ℓ'` over X, spelled out
module _ (ℓ ℓ' : Level) where
  FAM : hSet ℓ → Category (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  FAM X .ob = ⟨ X ⟩ → hSet ℓ'
  FAM X .Hom[_,_] P Q = ∀ x → ⟨ P x ⟩ → ⟨ Q x ⟩
  FAM X .id x p = p
  FAM X ._⋆_ f g x p = g x (f x p)
  FAM X .⋆IdL _ = refl
  FAM X .⋆IdR _ = refl
  FAM X .⋆Assoc _ _ _ = refl
  FAM X .isSetHom {y = Q} = isSetΠ λ x → isSetΠ λ _ → Q x .snd

  -- reindexing a family along a function: precomposition, strictly
  -- functorial (`F-id` and `F-seq` are `refl`)
  reindFAM : {X Y : hSet ℓ} → SET ℓ [ X , Y ] → Functor (FAM Y) (FAM X)
  reindFAM f .F-ob P x = P (f x)
  reindFAM f .F-hom g x = g (f x)
  reindFAM f .F-id = refl
  reindFAM f .F-seq _ _ = refl

  private
    LD = LocallyDiscrete (SET ℓ)
    homGpdSET : hSet ℓ → hSet ℓ → hGroupoid ℓ
    homGpdSET X Y =
      (SET ℓ [ X , Y ]) , isSet→isGroupoid (SET ℓ .isSetHom {X} {Y})
    RF : (X Y : hSet ℓ)
      → Functor (DiscreteCategory (homGpdSET Y X)) (FUNCTOR (FAM X) (FAM Y))
    RF X Y = DiscFunc reindFAM

    -- P's action on the structural 2-cells of `LD ^opᴮ`, all of which
    -- are `refl` because `SET`'s category laws are `refl`
    F2refl : {X Y : hSet ℓ} (f : SET ℓ [ Y , X ])
      → RF X Y .F-hom (refl {x = f}) ≡ FUNCTOR (FAM X) (FAM Y) .id
    F2refl {X} {Y} f = RF X Y .F-id

    ν⁰ : (X : hSet ℓ)
      → NatTrans (Id {C = FAM X}) (reindFAM {X} {X} (SET ℓ .id {X}))
    ν⁰ X .N-ob P x p = p
    ν⁰ X .N-hom _ = refl

    ν² : {X Y Z : hSet ℓ} (f : SET ℓ [ Y , X ]) (g : SET ℓ [ Z , Y ])
      → NatTrans (reindFAM {Z} {Y} g ∘F reindFAM {Y} {X} f)
                 (reindFAM {Z} {X} (SET ℓ ._⋆_ {Z} {Y} {X} g f))
    ν² f g .N-ob P x p = p
    ν² f g .N-hom _ = refl

    ν⁰⁻ : (X : hSet ℓ)
      → NatTrans (reindFAM {X} {X} (SET ℓ .id {X})) (Id {C = FAM X})
    ν⁰⁻ X .N-ob P x p = p
    ν⁰⁻ X .N-hom _ = refl

    ν²⁻ : {X Y Z : hSet ℓ} (f : SET ℓ [ Y , X ]) (g : SET ℓ [ Z , Y ])
      → NatTrans (reindFAM {Z} {X} (SET ℓ ._⋆_ {Z} {Y} {X} g f))
                 (reindFAM {Z} {Y} g ∘F reindFAM {Y} {X} f)
    ν²⁻ f g .N-ob P x p = p
    ν²⁻ f g .N-hom _ = refl

  SETPreLax : LaxFunctor (LD ^opᴮ) (CAT {ℓ-max ℓ (ℓ-suc ℓ')} {ℓ-max ℓ ℓ'})
  SETPreLax .F-ob = FAM
  SETPreLax .F-Hom {x} {y} = RF x y
  SETPreLax .F-id {x} = natFromIdHoms idHom𝟙 (λ _ → ν⁰ x)
  SETPreLax .F-seq {x} {y} {z} =
    natFromIdHoms (λ pq → pairIsIdHom (idHomDisc (homGpdSET y x) (pq .fst))
                                      (idHomDisc (homGpdSET z y) (pq .snd)))
      (λ fg → ν² {x} {y} {z} (fg .fst) (fg .snd))
  SETPreLax .lax-λ x y f = makeNatTransPath (cong N-ob (F2refl f))
  SETPreLax .lax-ρ x y f = makeNatTransPath (cong N-ob (F2refl f))
  SETPreLax .lax-α x y z w f g h =
    makeNatTransPath (cong N-ob (F2refl (SET ℓ ._⋆_ {w} {z} {x} h
      (SET ℓ ._⋆_ {z} {y} {x} g f))))

  SETPre : Prestack (LocallyDiscrete (SET ℓ))
    (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  SETPre .laxFunctor = SETPreLax
  SETPre .F-id-isIso {x} _ .inv = ν⁰⁻ x
  SETPre .F-id-isIso _ .sec = makeNatTransPath refl
  SETPre .F-id-isIso _ .ret = makeNatTransPath refl
  SETPre .F-seq-isIso {x} {y} {z} fg .inv = ν²⁻ {x} {y} {z} (fg .fst) (fg .snd)
  SETPre .F-seq-isIso _ .sec = makeNatTransPath refl
  SETPre .F-seq-isIso _ .ret = makeNatTransPath refl

  -- F⁰ and F² are the identity 2-cells on the nose
  isStrictSETPre : isStrictPrestack SETPre
  isStrictSETPre = (λ _ → refl) , (λ _ _ _ → refl)

  -- and strictly so: the fibrewise reindexing equations are `refl`
  strictSETPre-IdL : {X : hSet ℓ} (P : FAM X .ob)
    → strict⋆ᴾIdL isStrictSETPre P ≡ refl
  strictSETPre-IdL _ = refl

  strictSETPre-Assoc : {X Y Z : hSet ℓ}
    (k : SET ℓ [ X , Y ]) (f : SET ℓ [ Y , Z ]) (P : FAM Z .ob)
    → strict⋆ᴾAssoc isStrictSETPre {X} {Y} {Z} k f P ≡ refl
  strictSETPre-Assoc _ _ _ = refl

  private
    module ∫P = Categoryᴰ (∫Pre SETPre)
    module Sᴰ = Categoryᴰ (SETᴰ ℓ ℓ')

  -- `∫Pre SETPre` is `SETᴰ`: same objects, same displayed homs, same
  -- identity and same composition, all definitionally
  ∫SETPre-ob : (X : hSet ℓ) → ∫P.ob[ X ] ≡ Sᴰ.ob[ X ]
  ∫SETPre-ob _ = refl

  ∫SETPre-Hom : {X Y : hSet ℓ} (f : SET ℓ [ X , Y ])
    (P : ∫P.ob[ X ]) (Q : ∫P.ob[ Y ])
    → ∫P.Hom[ f ][ P , Q ] ≡ Sᴰ.Hom[ f ][ P , Q ]
  ∫SETPre-Hom _ _ _ = refl

  ∫SETPre-id : {X : hSet ℓ} {P : ∫P.ob[ X ]} → ∫P.idᴰ {p = P} ≡ Sᴰ.idᴰ
  ∫SETPre-id = refl

  ∫SETPre-⋆ : {X Y Z : hSet ℓ} {f : SET ℓ [ X , Y ]} {g : SET ℓ [ Y , Z ]}
    {P : ∫P.ob[ X ]} {Q : ∫P.ob[ Y ]} {R : ∫P.ob[ Z ]}
    (fᴰ : ∫P.Hom[ f ][ P , Q ]) (gᴰ : ∫P.Hom[ g ][ Q , R ])
    → fᴰ ∫P.⋆ᴰ gᴰ ≡ Sᴰ._⋆ᴰ_ {f = f} {g} {P} {Q} {R} fᴰ gᴰ
  ∫SETPre-⋆ _ _ = refl

  -- an isomorphism of displayed categories, identity on all the data
  ∫SETPreIsoᴰ : Isoᴰ (∫Pre SETPre) (SETᴰ ℓ ℓ')
  ∫SETPreIsoᴰ .funⱽ .F-obᴰ P = P
  ∫SETPreIsoᴰ .funⱽ .F-homᴰ fᴰ = fᴰ
  ∫SETPreIsoᴰ .funⱽ .F-idᴰ = refl
  ∫SETPreIsoᴰ .funⱽ .F-seqᴰ _ _ = refl
  ∫SETPreIsoᴰ .invⱽ .F-obᴰ P = P
  ∫SETPreIsoᴰ .invⱽ .F-homᴰ fᴰ = fᴰ
  ∫SETPreIsoᴰ .invⱽ .F-idᴰ = refl
  ∫SETPreIsoᴰ .invⱽ .F-seqᴰ _ _ = refl
  ∫SETPreIsoᴰ .obSec _ = refl
  ∫SETPreIsoᴰ .obRet _ = refl
  ∫SETPreIsoᴰ .homSec _ = refl
  ∫SETPreIsoᴰ .homRet _ = refl

  -- the data being definitionally equal, they are outright equal
  ∫SETPre≡SETᴰ : ∫Pre SETPre ≡ SETᴰ ℓ ℓ'
  ∫SETPre≡SETᴰ = sameDataᴰ≡ refl refl refl refl

  -- each fibre `FAM X` is cartesian, and reindexing preserves the
  -- structure on the nose, so `∫Pre SETPre` inherits it fibrewise
  private
    termFAM : (X : hSet ℓ) → Terminal (FAM X)
    termFAM X .fst _ = Unit* , isSetUnit*
    termFAM X .snd _ .fst _ _ = tt*
    termFAM X .snd _ .snd _ = refl

    presTermFAM : {X Y : hSet ℓ} (f : SET ℓ [ X , Y ])
      → preservesTerminal (FAM Y) (FAM X) (reindFAM f)
    presTermFAM {X} {Y} f = preserveOnePreservesAll (FAM Y) (FAM X)
      (reindFAM f) (termFAM Y) (termFAM X .snd)

    bpFAM : {X : hSet ℓ} (a b : FAM X .ob) → BinProduct (FAM X) (a , b)
    bpFAM a b .vertex x = _ , isSet× (a x .snd) (b x .snd)
    bpFAM a b .element = (λ x z → z .fst) , (λ x z → z .snd)
    bpFAM a b .universal _ = isoToIsEquiv
      (iso _ (λ uv x z → uv .fst x z , uv .snd x z)
        (λ _ → refl) (λ _ → refl))

    presBPFAM : {X Y : hSet ℓ} (f : SET ℓ [ X , Y ]) (a b : FAM Y .ob)
      → preservesBinProduct (reindFAM f) (bpFAM a b)
    presBPFAM {X} f a b =
      bpFAM {X = X} (λ x → a (f x)) (λ x → b (f x)) .universal

  ∫SETPreCCⱽ : CartesianCategoryⱽ (SET ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  ∫SETPreCCⱽ = ∫PreCartesianCategoryⱽ SETPre termFAM presTermFAM bpFAM
    presBPFAM
