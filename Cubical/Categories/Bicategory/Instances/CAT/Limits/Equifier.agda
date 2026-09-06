{-# OPTIONS --lossy-unification #-}
{- CAT has equifiers: the full subcategory where `θ` and `φ` agree. -}
module Cubical.Categories.Bicategory.Instances.CAT.Limits.Equifier where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.FullSubcategory
open import Cubical.Categories.Equivalence.Base

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Equifier
open import Cubical.Categories.Bicategory.Universal.Base
open import Cubical.Categories.Bicategory.Limits.Terminal
open import Cubical.Categories.Bicategory.Limits.Product
open import Cubical.Categories.Bicategory.Limits.Equifier
open import Cubical.Categories.Bicategory.Instances.CAT.Limits.Inserter

private
  variable
    ℓ ℓ' : Level

open Category
open Functor
open NatTrans
open NatIso
open isIso

module _ {ℓ ℓ' : Level} {C D : Category (ℓ-max ℓ ℓ') ℓ'}
  {F G : Functor C D} (θ φ : NatTrans F G) where
  private
    ℓo : Level
    ℓo = ℓ-max ℓ ℓ'
    module C = Category C
    module D = Category D

    Agree : C .ob → Type ℓ'
    Agree c = θ .N-ob c ≡ φ .N-ob c

  module Eq = EquifierPre {B = CAT {ℓo} {ℓ'}} {a = C} {b = D} θ φ

  EQ : Category ℓo ℓ'
  EQ = FullSubcategory C Agree

  eqι : Functor EQ C
  eqι = FullInclusion C Agree

  open PrestackNotation (EquifierPrestack (CAT {ℓo} {ℓ'}) θ φ)

  eqElem : p[ EQ ]
  eqElem = eqι , makeNatTransPath
    (funExt λ c → cong (F .F-hom C.id D.⋆_) (c .snd))

  private
    pred→ : {X : Category ℓo ℓ'} {H : Functor X C} → Eq.EqPred H
      → (x : X .ob) → Agree (H .F-ob x)
    pred→ {H = H} p x =
        sym (D.⋆IdL _) ∙ cong (D._⋆ θ .N-ob (H .F-ob x)) (sym (F .F-id))
      ∙ cong (λ n → n .N-ob x) p
      ∙ cong (D._⋆ φ .N-ob (H .F-ob x)) (F .F-id) ∙ D.⋆IdL _

  module _ {X : Category ℓo ℓ'} where
    private
      mk : (e : Eq.EqCat X .ob) → Functor X EQ
      mk (H , p) = ToFullSubcategory X C Agree H (pred→ p)

      mkNT : {e e' : Eq.EqCat X .ob} → Eq.EqCat X [ e , e' ]
        → NatTrans (mk e) (mk e')
      mkNT α .N-ob = α .N-ob
      mkNT α .N-hom = α .N-hom

    eqInv : Functor (Eq.EqCat X) (FUNCTOR X EQ)
    eqInv .F-ob = mk
    eqInv .F-hom = mkNT
    eqInv .F-id = makeNatTransPath refl
    eqInv .F-seq _ _ = makeNatTransPath refl

    private
      εNT : (e : Eq.EqCat X .ob) → NatTrans (eqι ∘F mk e) (e .fst)
      εNT e .N-ob x = C.id
      εNT e .N-hom f = C.⋆IdR _ ∙ sym (C.⋆IdL _)

      εNT⁻ : (e : Eq.EqCat X .ob) → NatTrans (e .fst) (eqι ∘F mk e)
      εNT⁻ e .N-ob x = C.id
      εNT⁻ e .N-hom f = C.⋆IdR _ ∙ sym (C.⋆IdL _)

      ηNT : (K : Functor X EQ) → NatTrans K (mk (⟨ eqElem ⟩ X .F-ob K))
      ηNT K .N-ob x = C.id
      ηNT K .N-hom f = C.⋆IdR _ ∙ sym (C.⋆IdL _)

      ηNT⁻ : (K : Functor X EQ) → NatTrans (mk (⟨ eqElem ⟩ X .F-ob K)) K
      ηNT⁻ K .N-ob x = C.id
      ηNT⁻ K .N-hom f = C.⋆IdR _ ∙ sym (C.⋆IdL _)

    εIsoEQ : NatIso (⟨ eqElem ⟩ X ∘F eqInv) 𝟙⟨ Eq.EqCat X ⟩
    εIsoEQ .trans .N-ob = εNT
    εIsoEQ .trans .N-hom α = makeNatTransPath (funExt λ x →
      cong (C._⋆ C.id) (C.⋆IdR _) ∙ C.⋆IdR _ ∙ sym (C.⋆IdL _))
    εIsoEQ .nIso e .inv = εNT⁻ e
    εIsoEQ .nIso e .sec = makeNatTransPath (funExt λ x → C.⋆IdL _)
    εIsoEQ .nIso e .ret = makeNatTransPath (funExt λ x → C.⋆IdL _)

    ηIsoEQ : NatIso 𝟙⟨ FUNCTOR X EQ ⟩ (eqInv ∘F ⟨ eqElem ⟩ X)
    ηIsoEQ .trans .N-ob = ηNT
    ηIsoEQ .trans .N-hom σ =
      makeNatTransPath (funExt λ x → sym (C.⋆IdL _))
    ηIsoEQ .nIso K .inv = ηNT⁻ K
    ηIsoEQ .nIso K .sec = makeNatTransPath (funExt λ x → C.⋆IdL _)
    ηIsoEQ .nIso K .ret = makeNatTransPath (funExt λ x → C.⋆IdL _)

  private
    eqUniversal : (X : Category ℓo ℓ') → WeakInverse (⟨ eqElem ⟩ X)
    eqUniversal X .WeakInverse.invFunc = eqInv
    eqUniversal X .WeakInverse.η = ηIsoEQ
    eqUniversal X .WeakInverse.ε = εIsoEQ

  equifierCAT : Equifierᴮ (CAT {ℓo} {ℓ'}) θ φ
  equifierCAT .BiuniversalElement.vertex = EQ
  equifierCAT .BiuniversalElement.element = eqElem
  equifierCAT .BiuniversalElement.universal = eqUniversal

module _ {ℓ ℓ' : Level} where
  equifiersCAT : hasEquifiersᴮ (CAT {ℓ-max ℓ ℓ'} {ℓ'})
  equifiersCAT θ φ = equifierCAT θ φ
