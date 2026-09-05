{-# OPTIONS --lossy-unification #-}
{- Formal (Street) monads in a bicategory, displayed monads over
   them, and the identification of monads with lax functors out of
   the terminal bicategory. -}
module Cubical.Categories.Bicategory.Monad.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit
open import Cubical.Data.Unit.Properties

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Terminal.More

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Instances.Terminal
open import Cubical.Categories.Bicategory.Constructions.Co
open import Cubical.Categories.Bicategory.Displayed

private
  variable
    ℓ ℓ' ℓ'' : Level

open Functor
open NatTrans
open NatIso
open Category
open isIso

-- 2-cells form a set: the hom-categories are categories.

module _ (C : Bicategory ℓ ℓ' ℓ'') where
  private
    module C = Bicategory C

  record Monad : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
    field
      a : C.0Cell
      t : C.1Cell a a
      η : C.2Cell C.id₁ t
      μ : C.2Cell (t C.⋆₁ t) t

      idL : ((η C.▷w t) C.⋆₂ μ) ≡ C.λ⁺ t
      idR : ((t C.◁w η) C.⋆₂ μ) ≡ C.ρ⁺ t
      μAssoc : (C.α⁺ t t t C.⋆₂ ((t C.◁w μ) C.⋆₂ μ))
             ≡ ((μ C.▷w t) C.⋆₂ μ)

  private
    𝟙ᴮ : Bicategory ℓ-zero ℓ-zero ℓ-zero
    𝟙ᴮ = TerminalBicategory ℓ-zero ℓ-zero ℓ-zero
    module 𝟙ᴮ = Bicategory 𝟙ᴮ

  fromLaxFunctor : LaxFunctor 𝟙ᴮ C → Monad
  fromLaxFunctor F = M where
    module F = LaxFunctor F

    -- `F-Hom` acts on the unique 2-cell `tt*` as the identity.
    F-Hom-tt : F.F-Hom {tt*} {tt*} .F-hom tt* ≡ C.id₂
    F-Hom-tt = F.F-Hom .F-id

    M : Monad
    M .Monad.a = F.F-ob tt*
    M .Monad.t = F.F-1cell tt*
    M .Monad.η = F.F⁰
    M .Monad.μ = F.F² tt* tt*
    M .Monad.idL =
        C.⟨⟩⋆₂⟨ sym (C.⋆₂IdR _) ∙ C.⟨⟩⋆₂⟨ sym F-Hom-tt ⟩ ⟩
      ∙ F.lax-λ tt* tt* tt*
    M .Monad.idR =
        C.⟨⟩⋆₂⟨ sym (C.⋆₂IdR _) ∙ C.⟨⟩⋆₂⟨ sym F-Hom-tt ⟩ ⟩
      ∙ F.lax-ρ tt* tt* tt*
    M .Monad.μAssoc =
        sym (F.lax-α tt* tt* tt* tt* tt* tt* tt*)
      ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ F-Hom-tt ⟩ ∙ C.⋆₂IdR _ ⟩

  toLaxFunctor : Monad → LaxFunctor 𝟙ᴮ C
  toLaxFunctor M = F where
    module M = Monad M

    -- 𝟙ᴮ has a single 0-cell, so one functor serves at every (x , y).
    MFH : Functor (UnitCategory ℓ-zero ℓ-zero) C.Hom[ M.a , M.a ]
    MFH .F-ob _ = M.t
    MFH .F-hom _ = C.id₂
    MFH .F-id = refl
    MFH .F-seq _ _ = sym (C.⋆₂IdL _)

    F : LaxFunctor 𝟙ᴮ C
    F .LaxFunctor.F-ob _ = M.a
    F .LaxFunctor.F-Hom = MFH
    F .LaxFunctor.F-id .N-ob _ = M.η
    F .LaxFunctor.F-id .N-hom f =
        cong (λ g → C.id .F-hom g C.⋆₂ M.η)
             (isOfHLevelUnit* 2 tt* tt* f refl)
      ∙ C.⟨ C.id .F-id ⟩⋆₂⟨⟩
      ∙ C.⋆₂IdL _
      ∙ sym (C.⋆₂IdR _)
    F .LaxFunctor.F-seq .N-ob _ = M.μ
    F .LaxFunctor.F-seq .N-hom _ =
      C.⟨ C.⋆ₕId ⟩⋆₂⟨⟩ ∙ C.⋆₂IdL _ ∙ sym (C.⋆₂IdR _)
    F .LaxFunctor.lax-λ tt* tt* tt* =
      C.⟨⟩⋆₂⟨ C.⋆₂IdR _ ⟩ ∙ M.idL
    F .LaxFunctor.lax-ρ tt* tt* tt* =
      C.⟨⟩⋆₂⟨ C.⋆₂IdR _ ⟩ ∙ M.idR
    F .LaxFunctor.lax-α tt* tt* tt* tt* tt* tt* tt* =
      C.⟨⟩⋆₂⟨ C.⋆₂IdR _ ⟩ ∙ sym M.μAssoc

  -- The data fields agree definitionally; the laws are paths in a set.
  fromLaxFunctor∘toLaxFunctor :
    (M : Monad) → fromLaxFunctor (toLaxFunctor M) ≡ M
  fromLaxFunctor∘toLaxFunctor M i = record
    { a = M.a
    ; t = M.t
    ; η = M.η
    ; μ = M.μ
    ; idL = Bicategory.isSet2Cell C _ _
        (fromLaxFunctor (toLaxFunctor M) .Monad.idL) M.idL i
    ; idR = Bicategory.isSet2Cell C _ _
        (fromLaxFunctor (toLaxFunctor M) .Monad.idR) M.idR i
    ; μAssoc = Bicategory.isSet2Cell C _ _
        (fromLaxFunctor (toLaxFunctor M) .Monad.μAssoc) M.μAssoc i
    }
    where module M = Monad M

  -- `F-Hom` is reconstructed via `Functor≡` from its `F-id`, since
  -- `Unit*` has eta and so every 2-cell of 𝟙ᴮ is `tt*`.
  toLaxFunctor∘fromLaxFunctor :
    (F : LaxFunctor 𝟙ᴮ C) → toLaxFunctor (fromLaxFunctor F) ≡ F
  toLaxFunctor∘fromLaxFunctor F = path
    where
      module F = LaxFunctor F
      Fa : C.0Cell
      Fa = F.F-ob tt*

      G : LaxFunctor 𝟙ᴮ C
      G = toLaxFunctor (fromLaxFunctor F)
      module G = LaxFunctor G

      F-Hom-path : G.F-Hom {tt*} {tt*} ≡ F.F-Hom {tt*} {tt*}
      F-Hom-path = Functor≡ (λ _ → refl) (λ _ → sym (F.F-Hom .F-id))

      F-Hom-i : I → Functor (UnitCategory ℓ-zero ℓ-zero) C.Hom[ Fa , Fa ]
      F-Hom-i i = F-Hom-path i

      F-id-path : PathP (λ i → NatTrans (C.id {Fa}) (F-Hom-i i ∘F 𝟙ᴮ.id))
                        (G.F-id {tt*}) (F.F-id {tt*})
      F-id-path =
        makeNatTransPathP refl (cong (_∘F 𝟙ᴮ.id) F-Hom-path)
          (λ i x → F.F-id .N-ob x)

      F-seq-path : PathP (λ i → NatTrans
          (C.seq Fa Fa Fa ∘F (F-Hom-i i ×F F-Hom-i i))
          (F-Hom-i i ∘F 𝟙ᴮ.seq tt* tt* tt*))
        (G.F-seq {tt*} {tt*} {tt*}) (F.F-seq {tt*} {tt*} {tt*})
      F-seq-path =
        makeNatTransPathP
          (cong (λ H → C.seq Fa Fa Fa ∘F (H ×F H)) F-Hom-path)
          (cong (_∘F 𝟙ᴮ.seq tt* tt* tt*) F-Hom-path)
          (λ i p → F.F-seq .N-ob p)

      -- `LaxFunctor` is no-eta, so the path is given by copatterns;
      -- the coherence families are spelled out so their metas resolve.
      path : G ≡ F
      path i .LaxFunctor.F-ob _ = Fa
      path i .LaxFunctor.F-Hom {tt*} {tt*} = F-Hom-path i
      path i .LaxFunctor.F-id {tt*} = F-id-path i
      path i .LaxFunctor.F-seq {tt*} {tt*} {tt*} = F-seq-path i
      path i .LaxFunctor.lax-λ tt* tt* f =
        isProp→PathP
          (λ j → Bicategory.isSet2Cell C
            ((F-id-path j .N-ob tt* C.▷w F-Hom-path j .F-ob f)
              C.⋆₂ (F-seq-path j .N-ob (tt* , f)
                C.⋆₂ F-Hom-path j .F-hom tt*))
            (C.λ⁺ (F-Hom-path j .F-ob f)))
          (G.lax-λ tt* tt* f) (F.lax-λ tt* tt* f) i
      path i .LaxFunctor.lax-ρ tt* tt* f =
        isProp→PathP
          (λ j → Bicategory.isSet2Cell C
            ((F-Hom-path j .F-ob f C.◁w F-id-path j .N-ob tt*)
              C.⋆₂ (F-seq-path j .N-ob (f , tt*)
                C.⋆₂ F-Hom-path j .F-hom tt*))
            (C.ρ⁺ (F-Hom-path j .F-ob f)))
          (G.lax-ρ tt* tt* f) (F.lax-ρ tt* tt* f) i
      path i .LaxFunctor.lax-α tt* tt* tt* tt* f g h =
        isProp→PathP
          (λ j → Bicategory.isSet2Cell C
            ((F-seq-path j .N-ob (f , g) C.▷w F-Hom-path j .F-ob h)
              C.⋆₂ (F-seq-path j .N-ob (tt* , h)
                C.⋆₂ F-Hom-path j .F-hom tt*))
            (C.α⁺ (F-Hom-path j .F-ob f) (F-Hom-path j .F-ob g)
                  (F-Hom-path j .F-ob h)
              C.⋆₂ ((F-Hom-path j .F-ob f
                      C.◁w F-seq-path j .N-ob (g , h))
                C.⋆₂ F-seq-path j .N-ob (f , tt*))))
          (G.lax-α tt* tt* tt* tt* f g h)
          (F.lax-α tt* tt* tt* tt* f g h) i

  LaxFunctorIsoMonad : Iso (LaxFunctor 𝟙ᴮ C) Monad
  LaxFunctorIsoMonad .Iso.fun = fromLaxFunctor
  LaxFunctorIsoMonad .Iso.inv = toLaxFunctor
  LaxFunctorIsoMonad .Iso.sec = fromLaxFunctor∘toLaxFunctor
  LaxFunctorIsoMonad .Iso.ret = toLaxFunctor∘fromLaxFunctor

{- Notation for a formal monad: the composites and whiskered cells its
   laws are stated in.  `ComonadNotation` below is this module at
   `C ^coᴮ`, re-exported under the dual names. -}
module MonadNotation {C : Bicategory ℓ ℓ' ℓ''} (M : Monad C) where
  private
    module C = Bicategory C
  open Monad M public

  t² : C.1Cell a a
  t² = t C.⋆₁ t

  t³L : C.1Cell a a
  t³L = t² C.⋆₁ t

  t³R : C.1Cell a a
  t³R = t C.⋆₁ t²

  -- Structural cells at the carrier.
  λt : C.2Cell (C.id₁ C.⋆₁ t) t
  λt = C.λ⁺ t

  λt⁻ : C.2Cell t (C.id₁ C.⋆₁ t)
  λt⁻ = C.λ⁻ t

  ρt : C.2Cell (t C.⋆₁ C.id₁) t
  ρt = C.ρ⁺ t

  ρt⁻ : C.2Cell t (t C.⋆₁ C.id₁)
  ρt⁻ = C.ρ⁻ t

  αt : C.2Cell t³L t³R
  αt = C.α⁺ t t t

  αt⁻ : C.2Cell t³R t³L
  αt⁻ = C.α⁻ t t t

  -- Unit and multiplication, whiskered by the carrier.
  ηt : C.2Cell (C.id₁ C.⋆₁ t) t²
  ηt = η C.▷w t

  tη : C.2Cell (t C.⋆₁ C.id₁) t²
  tη = t C.◁w η

  μt : C.2Cell t³L t²
  μt = μ C.▷w t

  tμ : C.2Cell t³R t²
  tμ = t C.◁w μ

  -- The laws, in that notation.
  idL' : (ηt C.⋆₂ μ) ≡ λt
  idL' = idL

  idR' : (tη C.⋆₂ μ) ≡ ρt
  idR' = idR

  μAssoc' : (αt C.⋆₂ (tμ C.⋆₂ μ)) ≡ (μt C.⋆₂ μ)
  μAssoc' = μAssoc

  -- An idempotent monad is one whose multiplication is invertible.
  isIdempotent : Type ℓ''
  isIdempotent = Cubical.Categories.Category.isIso C.Hom[ a , a ] μ



-- `_^coᴮ` reverses the 2-cells, which is where a formal monad's unit
-- and multiplication live, so it is the monad/comonad duality here.
-- (For `TwoMonad`, whose unit and multiplication are 1-cells of
-- `Lax(K,K)`, the duality is `_^opᴮ` instead.)
Comonad : Bicategory ℓ ℓ' ℓ'' → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
Comonad K = Monad (K ^coᴮ)

{- `MonadNotation` at `K ^coᴮ`, re-exported under the dual names.  The
   carrier and the whiskerings are `K`'s on the nose, so only the
   2-cells turn around. -}
module ComonadNotation {K : Bicategory ℓ ℓ' ℓ''} (W : Comonad K) where
  private
    module K = Bicategory K
    module M = MonadNotation W
  open M public using (a; t; t²; t³L; t³R)

  -- Taken at `K`, not re-exported: `M`'s `λt` is `K.λ⁻` and vice versa.
  λt : K.2Cell (K.id₁ K.⋆₁ t) t
  λt = K.λ⁺ t

  λt⁻ : K.2Cell t (K.id₁ K.⋆₁ t)
  λt⁻ = K.λ⁻ t

  ρt : K.2Cell (t K.⋆₁ K.id₁) t
  ρt = K.ρ⁺ t

  ρt⁻ : K.2Cell t (t K.⋆₁ K.id₁)
  ρt⁻ = K.ρ⁻ t

  ε : K.2Cell t K.id₁
  ε = M.η

  δ : K.2Cell t t²
  δ = M.μ

  αw : K.2Cell t³R t³L
  αw = M.αt

  αw⁻ : K.2Cell t³L t³R
  αw⁻ = M.αt⁻

  εt : K.2Cell t² (K.id₁ K.⋆₁ t)
  εt = M.ηt

  tε : K.2Cell t² (t K.⋆₁ K.id₁)
  tε = M.tη

  δt : K.2Cell t² t³L
  δt = M.μt

  tδ : K.2Cell t² t³R
  tδ = M.tμ

  counitL : (δ K.⋆₂ εt) ≡ λt⁻
  counitL = M.idL'

  counitR : (δ K.⋆₂ tε) ≡ ρt⁻
  counitR = M.idR'

  δAssoc : ((δ K.⋆₂ tδ) K.⋆₂ αw) ≡ (δ K.⋆₂ δt)
  δAssoc = M.μAssoc'

  isIdempotent : Type ℓ''
  isIdempotent = M.isIdempotent

-- A monad in a displayed bicategory lying over a monad in the base:
-- the data sits over M's data and the laws are PathPs over M's laws.
module _ {ℓᴰ ℓᴰ' ℓᴰ'' : Level} {C : Bicategory ℓ ℓ' ℓ''}
  (Cᴰ : Bicategoryᴰ C ℓᴰ ℓᴰ' ℓᴰ'') (M : Monad C)
  where
  private
    module C = Bicategory C
    module Cᴰ = Bicategoryᴰ Cᴰ
    module M = Monad M

  record Monadᴰ : Type (ℓ-max ℓᴰ (ℓ-max ℓᴰ' ℓᴰ'')) where
    field
      aᴰ : Cᴰ.ob[ M.a ]
      tᴰ : Cᴰ.1Cellᴰ aᴰ aᴰ M.t
      ηᴰ : Cᴰ.2Cellᴰ Cᴰ.id₁ᴰ tᴰ M.η
      μᴰ : Cᴰ.2Cellᴰ (tᴰ Cᴰ.⋆₁ᴰ tᴰ) tᴰ M.μ

      idLᴰ : PathP
        (λ i → Cᴰ.2Cellᴰ (Cᴰ.id₁ᴰ Cᴰ.⋆₁ᴰ tᴰ) tᴰ (M.idL i))
        ((ηᴰ Cᴰ.▷wᴰ tᴰ) Cᴰ.⋆₂ᴰ μᴰ)
        (Cᴰ.λ⁺ᴰ tᴰ)

      idRᴰ : PathP
        (λ i → Cᴰ.2Cellᴰ (tᴰ Cᴰ.⋆₁ᴰ Cᴰ.id₁ᴰ) tᴰ (M.idR i))
        ((tᴰ Cᴰ.◁wᴰ ηᴰ) Cᴰ.⋆₂ᴰ μᴰ)
        (Cᴰ.ρ⁺ᴰ tᴰ)

      μAssocᴰ : PathP
        (λ i → Cᴰ.2Cellᴰ ((tᴰ Cᴰ.⋆₁ᴰ tᴰ) Cᴰ.⋆₁ᴰ tᴰ) tᴰ (M.μAssoc i))
        (Cᴰ.α⁺ᴰ tᴰ tᴰ tᴰ Cᴰ.⋆₂ᴰ ((tᴰ Cᴰ.◁wᴰ μᴰ) Cᴰ.⋆₂ᴰ μᴰ))
        ((μᴰ Cᴰ.▷wᴰ tᴰ) Cᴰ.⋆₂ᴰ μᴰ)
