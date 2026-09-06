{-# OPTIONS --lossy-unification #-}
{- CAT has inserters: the inserter of `F G : C → D` is `DIALG F G`. -}
module Cubical.Categories.Bicategory.Instances.CAT.Limits.Inserter where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Equivalence.Base
open import Cubical.Categories.Displayed.Instances.Dialgebras

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Inserter
open import Cubical.Categories.Bicategory.Universal.Base
open import Cubical.Categories.Bicategory.Limits.Inserter
open import Cubical.Categories.Bicategory.Limits.Comma

private
  variable
    ℓC ℓC' ℓD ℓD' ℓX ℓX' : Level

open Category
open Functor
open NatTrans
open NatIso
open isIso

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F G : Functor C D) where
  private
    module C = Category C
    module D = Category D

  -- the cone: the forgetful functor and its structure 2-cell
  dialgπ : Functor (DIALG F G) C
  dialgπ .F-ob = fst
  dialgπ .F-hom = fst
  dialgπ .F-id = refl
  dialgπ .F-seq _ _ = refl

  dialgθ : NatTrans (F ∘F dialgπ) (G ∘F dialgπ)
  dialgθ .N-ob = snd
  dialgθ .N-hom (f , p) = sym p

  -- the naturality square a 2-cell into the inserter must satisfy
  DialgSq : {X : Category ℓX ℓX'} {H H' : Functor X C}
    (θ : NatTrans (F ∘F H) (G ∘F H)) (θ' : NatTrans (F ∘F H') (G ∘F H'))
    (α : NatTrans H H') → Type (ℓ-max ℓX ℓD')
  DialgSq {X = X} θ θ' α = (x : X .ob)
    → θ .N-ob x D.⋆ G .F-hom (α .N-ob x)
      ≡ F .F-hom (α .N-ob x) D.⋆ θ' .N-ob x

  module _ {X : Category ℓX ℓX'} where
    toDialg : (H : Functor X C) (θ : NatTrans (F ∘F H) (G ∘F H))
      → Functor X (DIALG F G)
    toDialg H θ .F-ob x = H .F-ob x , θ .N-ob x
    toDialg H θ .F-hom f = H .F-hom f , sym (θ .N-hom f)
    toDialg H θ .F-id =
      ΣPathP (H .F-id , isProp→PathP (λ _ → D.isSetHom _ _) _ _)
    toDialg H θ .F-seq f g =
      ΣPathP (H .F-seq f g , isProp→PathP (λ _ → D.isSetHom _ _) _ _)

    toDialgNT : {H H' : Functor X C} {θ : NatTrans (F ∘F H) (G ∘F H)}
      {θ' : NatTrans (F ∘F H') (G ∘F H')} (α : NatTrans H H')
      → DialgSq θ θ' α → NatTrans (toDialg H θ) (toDialg H' θ')
    toDialgNT α sq .N-ob x = α .N-ob x , sq x
    toDialgNT α sq .N-hom f =
      ΣPathP (α .N-hom f , isProp→PathP (λ _ → D.isSetHom _ _) _ _)

module _ {ℓ ℓ' : Level} {C D : Category (ℓ-max ℓ ℓ') ℓ'}
  (F G : Functor C D) where
  private
    ℓo : Level
    ℓo = ℓ-max ℓ ℓ'
    module D = Category D
  module Ins = InserterPre {B = CAT {ℓo} {ℓ'}} {a = C} {b = D} F G

  reindθ≡ : {X : Category ℓo ℓ'} (H : Functor X (DIALG F G)) (x : X .ob)
    → Ins.reindθ H (dialgθ F G) .N-ob x ≡ (H .F-ob x) .snd
  reindθ≡ H x =
      D.⋆IdL _ ∙ D.⋆IdR _
    ∙ cong (D._⋆ (H .F-ob x .snd)) (F .F-id) ∙ D.⋆IdL _

  module _ {X : Category ℓo ℓ'} {H H' : Functor X C}
    {θ : NatTrans (F ∘F H) (G ∘F H)} {θ' : NatTrans (F ∘F H') (G ∘F H')}
    {α : NatTrans H H'} where

    sq→ins : DialgSq F G θ θ' α → Ins.InsCond θ θ' α
    sq→ins sq = makeNatTransPath (funExt λ x →
        cong (D._⋆ θ' .N-ob x) (D.⋆IdR _)
      ∙ sym (sq x)
      ∙ cong (θ .N-ob x D.⋆_) (sym (D.⋆IdR _)))

    ins→sq : Ins.InsCond θ θ' α → DialgSq F G θ θ' α
    ins→sq c x =
        cong (θ .N-ob x D.⋆_) (sym (D.⋆IdR _))
      ∙ sym (cong (λ n → n .N-ob x) c)
      ∙ cong (D._⋆ θ' .N-ob x) (D.⋆IdR _)

  private
    isPropDialgHom : {c c' : C .ob} {θ : D [ F .F-ob c , G .F-ob c ]}
      {θ' : D [ F .F-ob c' , G .F-ob c' ]} (f : C [ c , c' ])
      → isProp (θ D.⋆ G .F-hom f ≡ F .F-hom f D.⋆ θ')
    isPropDialgHom f = D.isSetHom _ _

  module _ {X : Category ℓo ℓ'} where
    insInv : Functor (Ins.InsCat X) (FUNCTOR X (DIALG F G))
    insInv .F-ob (H , θ) = toDialg F G H θ
    insInv .F-hom (α , c) = toDialgNT F G α (ins→sq c)
    insInv .F-id = makeNatTransPath (funExt λ x →
      Σ≡Prop isPropDialgHom refl)
    insInv .F-seq _ _ = makeNatTransPath (funExt λ x →
      Σ≡Prop isPropDialgHom refl)

  open PrestackNotation (InserterPrestack (CAT {ℓo} {ℓ'}) F G)

  dialgElem : p[ DIALG F G ]
  dialgElem = dialgπ F G , dialgθ F G

  private
    module C = Category C

    -- every comparison 2-cell below has identity components, so its
    -- dialgebra square is just an equation between structure maps
    idSq : {c : C .ob} (θ θ' : D [ F .F-ob c , G .F-ob c ]) → θ ≡ θ'
      → θ D.⋆ G .F-hom C.id ≡ F .F-hom C.id D.⋆ θ'
    idSq θ θ' p =
        cong (θ D.⋆_) (G .F-id) ∙ D.⋆IdR θ ∙ p
      ∙ sym (D.⋆IdL θ') ∙ cong (D._⋆ θ') (sym (F .F-id))

  module _ {X : Category ℓo ℓ'} where
    private
      πNT : (H : Functor X C) (θ : NatTrans (F ∘F H) (G ∘F H))
        → NatTrans (dialgπ F G ∘F toDialg F G H θ) H
      πNT H θ .N-ob x = C.id
      πNT H θ .N-hom f = C.⋆IdR _ ∙ sym (C.⋆IdL _)

      πNT⁻ : (H : Functor X C) (θ : NatTrans (F ∘F H) (G ∘F H))
        → NatTrans H (dialgπ F G ∘F toDialg F G H θ)
      πNT⁻ H θ .N-ob x = C.id
      πNT⁻ H θ .N-hom f = C.⋆IdR _ ∙ sym (C.⋆IdL _)

    εIso : NatIso (⟨ dialgElem ⟩ X ∘F insInv) 𝟙⟨ Ins.InsCat X ⟩
    εIso .NatIso.trans .N-ob (H , θ) =
      πNT H θ , sq→ins (λ x → idSq _ _ (reindθ≡ (toDialg F G H θ) x))
    εIso .NatIso.trans .N-hom (α , c) = Ins.InsHom≡ (makeNatTransPath
      (funExt λ x → cong (C._⋆ C.id) (C.⋆IdR _) ∙ C.⋆IdR _
                  ∙ sym (C.⋆IdL _)))
    εIso .NatIso.nIso (H , θ) .isIso.inv =
      πNT⁻ H θ , sq→ins (λ x → idSq _ _ (sym (reindθ≡ (toDialg F G H θ) x)))
    εIso .NatIso.nIso (H , θ) .isIso.sec =
      Ins.InsHom≡ (makeNatTransPath (funExt λ x → C.⋆IdL _))
    εIso .NatIso.nIso (H , θ) .isIso.ret =
      Ins.InsHom≡ (makeNatTransPath (funExt λ x → C.⋆IdL _))

    private
      ηNT : (H : Functor X (DIALG F G)) → NatTrans H
        (toDialg F G (dialgπ F G ∘F H) (Ins.reindθ H (dialgθ F G)))
      ηNT H .N-ob x = C.id , idSq _ _ (sym (reindθ≡ H x))
      ηNT H .N-hom f = Σ≡Prop isPropDialgHom (C.⋆IdR _ ∙ sym (C.⋆IdL _))

      ηNT⁻ : (H : Functor X (DIALG F G))
        → NatTrans (toDialg F G (dialgπ F G ∘F H) (Ins.reindθ H (dialgθ F G)))
                   H
      ηNT⁻ H .N-ob x = C.id , idSq _ _ (reindθ≡ H x)
      ηNT⁻ H .N-hom f = Σ≡Prop isPropDialgHom (C.⋆IdR _ ∙ sym (C.⋆IdL _))

    ηIso : NatIso 𝟙⟨ FUNCTOR X (DIALG F G) ⟩ (insInv ∘F ⟨ dialgElem ⟩ X)
    ηIso .NatIso.trans .N-ob = ηNT
    ηIso .NatIso.trans .N-hom σ = makeNatTransPath
      (funExt λ x → Σ≡Prop isPropDialgHom (sym (C.⋆IdL _)))
    ηIso .NatIso.nIso H .isIso.inv = ηNT⁻ H
    ηIso .NatIso.nIso H .isIso.sec = makeNatTransPath
      (funExt λ x → Σ≡Prop isPropDialgHom (C.⋆IdL _))
    ηIso .NatIso.nIso H .isIso.ret = makeNatTransPath
      (funExt λ x → Σ≡Prop isPropDialgHom (C.⋆IdL _))

  private
    dialgUniversal : (X : Category ℓo ℓ') → WeakInverse (⟨ dialgElem ⟩ X)
    dialgUniversal X .WeakInverse.invFunc = insInv
    dialgUniversal X .WeakInverse.η = ηIso
    dialgUniversal X .WeakInverse.ε = εIso

  inserterCAT : Inserterᴮ (CAT {ℓo} {ℓ'}) F G
  inserterCAT .BiuniversalElement.vertex = DIALG F G
  inserterCAT .BiuniversalElement.element = dialgElem
  inserterCAT .BiuniversalElement.universal = dialgUniversal

module _ {ℓ ℓ' : Level} where
  insertersCAT : hasInsertersᴮ (CAT {ℓ-max ℓ ℓ'} {ℓ'})
  insertersCAT F G = inserterCAT F G

  -- comma objects come for free
  commaObjectsCAT : hasCommaObjectsᴮ (CAT {ℓ-max ℓ ℓ'} {ℓ'})
  commaObjectsCAT = commaFromInsertersᴮ _ insertersCAT

  -- the two unit cases
  algInserter : (C : Category (ℓ-max ℓ ℓ') ℓ') (F : Functor C C)
    → insertersCAT {a = C} {b = C} F (Id {C = C})
        .BiuniversalElement.vertex ≡ F-ALG {C = C} F
  algInserter C F = refl

  coalgInserter : (C : Category (ℓ-max ℓ ℓ') ℓ') (F : Functor C C)
    → insertersCAT {a = C} {b = C} (Id {C = C}) F
        .BiuniversalElement.vertex ≡ F-COALG {C = C} F
  coalgInserter C F = refl
