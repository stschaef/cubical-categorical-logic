
-- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}


module Cubical.Categories.Presheaf.UnivEltProd where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism


open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Preorder

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Equivalence
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.NaturalTransformation


open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Properties
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Instances.Sets
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Functor.Base
open import Cubical.Foundations.Equiv

open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Data.Unit

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓC ℓC' ℓD ℓD' ℓC₁ ℓC₁' ℓD₁ ℓD₁' : Level


open Category
open Functor
open UniversalElement


-- Product of Hsets
_×hs_ : {ℓS ℓS' : Level} → hSet ℓS -> hSet ℓS' -> hSet (ℓ-max ℓS ℓS')
(A , isSetA) ×hs (B , isSetB) = A × B , isSet× isSetA isSetB

-- Product of presheaves
_×Psh_ :
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {ℓS ℓS' : Level} → Presheaf C ℓS -> Presheaf D ℓS' ->
  Presheaf (C ×C D) (ℓ-max ℓS ℓS')
(P ×Psh Q) .F-ob (c , d) =
  (P .F-ob c) ×hs (Q .F-ob d)
(P ×Psh Q) .F-hom {(c , d)} {(c' , d')} (f , g) (x , y) =
  (P .F-hom f x) , (Q .F-hom g y)
(P ×Psh Q) .F-id {c , d} =
  funExt λ {(x , y) -> ≡-× (funExt⁻ (P .F-id) x) (funExt⁻ (Q .F-id) y)}
(P ×Psh Q) .F-seq {c , d} {c' , d'} {c'' , d''} (f , g) (f' , g') =
  funExt (λ { (x , y) -> ≡-× (funExt⁻ (P .F-seq f f') x) (funExt⁻ (Q .F-seq g g') y) })

-- Universal element of the product of presheaves
_×UE_ :
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {ℓS ℓS' : Level} {P : Presheaf C ℓS} {Q : Presheaf D ℓS'} ->
  UniversalElement C P -> UniversalElement D Q ->
  UniversalElement (C ×C D) (_×Psh_ {C = C}{D = D}{ℓS = ℓS}{ℓS' = ℓS'} P Q)
(ηP ×UE ηQ) .vertex = (ηP .vertex) , (ηQ .vertex)
(ηP ×UE ηQ) .element = ηP .element , ηQ .element
(ηP ×UE ηQ) .universal (c , d) .equiv-proof (x , y) .fst .fst =
  ((ηP .universal c .equiv-proof x .fst .fst) ,
  (ηQ .universal d .equiv-proof y .fst .fst))
(ηP ×UE ηQ) .universal (c , d) .equiv-proof (x , y) .fst .snd =
  ≡-× (ηP .universal c .equiv-proof x .fst .snd)
      (ηQ .universal d .equiv-proof y .fst .snd)
_×UE_ {P = P} {Q = Q} ηP ηQ .universal (c , d) .equiv-proof (x , y) .snd ((f , g) , t) = Σ≡Prop
  (λ {(f , g) -> isSet×
    (P .F-ob c .snd) (Q .F-ob d .snd)
    (P .F-hom f (ηP .element) , Q .F-hom g (ηQ .element)) (x , y)})
  (≡-× (cong fst (ηP .universal c .equiv-proof x .snd (f , cong fst t)))
       (cong fst (ηQ .universal d .equiv-proof y .snd (g , cong snd t))))

_×RightAdjointAt'_ :
  {ℓC ℓC' ℓD ℓD' ℓC₁ ℓC₁' ℓD₁ ℓD₁' : Level}
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {C₁ : Category ℓC₁ ℓC₁'}{D₁ : Category ℓD₁ ℓD₁'}
  {F : Functor C D} {F₁ : Functor C₁ D₁} {d : D .ob} {d₁ : D₁ .ob} →
  RightAdjointAt' C D F d → RightAdjointAt' C₁ D₁ F₁ d₁ →
  RightAdjointAt' (C ×C C₁) (D ×C D₁) (F ×F F₁) (d , d₁)
_×RightAdjointAt'_ {_}{_}{_}{_}{_}{_}{_}{_}{C}{D}{C₁}{D₁}{F}{F₁}{d}{d₁} x y =
   transport
     (cong
       (λ a → UniversalElement (C ×C C₁) a)
       the-presheaves-agree)
     (_×UE_ {P = the-left-presheaf} {Q = the-right-presheaf} x y)
  where
  the-left-presheaf : Functor (C ^op) (SET _)
  the-left-presheaf = (D [-, d ]) ∘F (F ^opF)
  the-right-presheaf : Functor (C₁ ^op) (SET _)
  the-right-presheaf = (D₁ [-, d₁ ]) ∘F (F₁ ^opF)

  the-presheaves-agree : (the-left-presheaf ×Psh the-right-presheaf) ≡
                           funcComp ((D ×C D₁) [-, d , d₁ ]) ((F ×F F₁) ^opF)
  the-presheaves-agree =
    Functor≡
      (λ c → refl)
      (λ f → refl)

record catEndo : Typeω  where
  field
    the-level-lift : Level → Level
    the-level-lift' : Level → Level
    Cat-ob : {ℓ ℓ' : Level} → Category ℓ ℓ' → Category (the-level-lift ℓ) (the-level-lift' ℓ')
    Cat-hom : {ℓC ℓC' ℓD ℓD' : Level} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
              → (G : Functor C D) → Functor (Cat-ob C) (Cat-ob D)
    Cat-id : {ℓC ℓC' : Level} {C : Category ℓC ℓC'} → Cat-hom {ℓC}{ℓC'}{ℓC}{ℓC'}{C}{C} Id ≡ Id
    Cat-seq : {ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level}
              {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {E : Category ℓE ℓE'}
              {F : Functor C D} {G : Functor D E}
              → Cat-hom (G ∘F F) ≡ Cat-hom G ∘F Cat-hom F

open catEndo
prodInShape :
  {ℓC ℓC' ℓD ℓD' : Level}
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {shape : catEndo}
  (F : Functor C (shape .Cat-ob C)) (G : Functor D (shape .Cat-ob D))
  → Functor (C ×C D) (shape .Cat-ob (C ×C D))
prodInShape {_} {_} {_} {_} {_} {_} {shape} F G .F-ob x = {!!}
prodInShape {_} {_} {_} {_} {_} {_} {shape} F G .F-hom = {!!}
prodInShape {_} {_} {_} {_} {_} {_} {shape} F G .F-id = {!!}
prodInShape {_} {_} {_} {_} {_} {_} {shape} F G .F-seq = {!!}


_×RightAdjointAt'Prod_ :
  {ℓC ℓC' ℓD ℓD' : Level}
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {shape : {ℓ ℓ' : Level} → Category ℓ ℓ' → Category ℓ ℓ'}
  {F : Functor C (shape C)} {G : Functor D (shape D)}
  {cc : (shape C) .ob} {dd : (shape D) .ob} →
  RightAdjointAt' C (shape C) F cc → RightAdjointAt' D (shape D) G dd →
  RightAdjointAt' (C ×C D) (shape (C ×C D)) {!!} {!!}
_×RightAdjointAt'Prod_ = {!!}


_×RightAdjoint'_ :
  {ℓC ℓC' ℓD ℓD' ℓC₁ ℓC₁' ℓD₁ ℓD₁' : Level}
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {C₁ : Category ℓC₁ ℓC₁'}{D₁ : Category ℓD₁ ℓD₁'}
  {F : Functor C D} {F₁ : Functor C₁ D₁} →
  RightAdjoint' C D F → RightAdjoint' C₁ D₁ F₁ →
  RightAdjoint' (C ×C C₁) (D ×C D₁) (F ×F F₁)
_×RightAdjoint'_ {_}{_}{_}{_}{_}{_}{_}{_}{C}{D}{C₁}{D₁}{F}{F₁} x y =
  λ (d , d₁) → x d ×RightAdjointAt' y d₁

-- Constant presheaf over C ×C D equals the product of
-- constant presheaves over C and D
Const-product : ∀ {C D : Category ℓ ℓ'} {x : hSet ℓ''} ->
  (Constant (C ×C D) (SET ℓ'') (x ×hs x)) ≡
  (_×Psh_ {C = C ^op} {D = D ^op} (Constant C (SET ℓ'') x) (Constant D (SET ℓ'') x))
Const-product = Functor≡
  (λ {(c , d) -> refl })
  λ f -> refl

-- Product and composition
--
×Psh-comp : {B C D E : Category ℓ ℓ'} ->
  (H : Functor ((C ×C C) ^op) E) -> H ∘F ((𝟙⟨ C ⟩ ,F 𝟙⟨ C ⟩) ^opF) ≡ H ∘F (Δ C ^opF)
×Psh-comp = λ H -> refl

module Terminal (C D : Category ℓ ℓ') where

  unit-ob : hSet ℓ-zero
  unit-ob = (Unit , isSetUnit)

  unit-ob-iso : unit-ob ≡ unit-ob ×hs unit-ob
  unit-ob-iso = Σ≡Prop (λ x -> isPropIsSet) unit-iso
    where
      unit-iso : Unit ≡ Unit × Unit
      unit-iso = isoToPath (iso (λ _ -> tt , tt) (λ _ -> tt) (λ _ -> refl) (λ _ -> refl))

  term-prod : Terminal' C -> Terminal' D -> Terminal' (C ×C D)
  term-prod tC tD = transport eq' (tC ×UE tD)
    where
      eq' : _
      eq' = (λ i -> UniversalElement (C ×C D) (Const-product {C = C ^op} {D = D ^op} {x = unit-ob} (~ i))) ∙
           (λ i -> UniversalElement (C ×C D) (Constant ((C ×C D) ^op) (SET ℓ-zero) (unit-ob-iso (~ i))))

module Product (C : Category ℓC ℓC') (D : Category ℓD ℓD') (bpC : BinProducts' C) (bpD : BinProducts' D) where
  open NatIso
  open NatTrans
  open isEquivalence


  -- Establish the following equivalence of categories
  -- TODO there a better way to do this where we show that ×C associates and then we just use that
  -- swapArgs is an equivalence on the middle two arguments
  permute : ((C ×C C) ×C (D ×C D)) ≃ᶜ ((C ×C D) ×C (C ×C D))
  permute ._≃ᶜ_.func .F-ob x = ((x .fst .fst) , (x .snd .fst)) , ((x .fst .snd) , (x .snd .snd))
  permute ._≃ᶜ_.func .F-hom x = ((x .fst .fst) , (x .snd .fst)) , ((x .fst .snd) , (x .snd .snd))
  permute ._≃ᶜ_.func .F-id = refl
  permute ._≃ᶜ_.func .F-seq f g = refl
  permute ._≃ᶜ_.isEquiv .invFunc .F-ob x = ((x .fst .fst) , (x .snd .fst)) , ((x .fst .snd) , (x .snd .snd))
  permute ._≃ᶜ_.isEquiv .invFunc .F-hom x = ((x .fst .fst) , (x .snd .fst)) , ((x .fst .snd) , (x .snd .snd))
  permute ._≃ᶜ_.isEquiv .invFunc .F-id = refl
  permute ._≃ᶜ_.isEquiv .invFunc .F-seq f g = refl
  permute ._≃ᶜ_.isEquiv .η .trans .N-ob x = id ((C ×C C) ×C (D ×C D)) {x = x}
  permute ._≃ᶜ_.isEquiv .η .trans .N-hom f = (⋆IdR ((C ×C C) ×C (D ×C D)) f) ∙ sym (⋆IdL ((C ×C C) ×C (D ×C D)) f)
  permute ._≃ᶜ_.isEquiv .η .nIso x .isIso.inv = id (((C ×C C) ×C (D ×C D))) {x = x}
  permute ._≃ᶜ_.isEquiv .η .nIso x .isIso.sec = ⋆IdL ((C ×C C) ×C (D ×C D)) _
  permute ._≃ᶜ_.isEquiv .η .nIso x .isIso.ret = ⋆IdR ((C ×C C) ×C (D ×C D)) _
  permute ._≃ᶜ_.isEquiv .ε .trans .N-ob x = id ((C ×C D) ×C (C ×C D)) {x = x}
  permute ._≃ᶜ_.isEquiv .ε .trans .N-hom f = ⋆IdR ((C ×C D) ×C (C ×C D)) _ ∙ sym (⋆IdL ((C ×C D) ×C (C ×C D)) _)
  permute ._≃ᶜ_.isEquiv .ε .nIso x .isIso.inv = id (((C ×C D) ×C (C ×C D))) {x = x}
  permute ._≃ᶜ_.isEquiv .ε .nIso x .isIso.sec = ⋆IdL ((C ×C D) ×C (C ×C D)) _
  permute ._≃ᶜ_.isEquiv .ε .nIso x .isIso.ret = ⋆IdR ((C ×C D) ×C (C ×C D)) _

  _ : permute ._≃ᶜ_.func ∘F (Δ C ×F Δ D) ≡ (Δ (C ×C D))
  _ = Functor≡ (λ _ → refl) (λ _ → refl)

  record IsoOfCats
    {ℓD ℓD' ℓD₁ ℓD₁' : Level}
    (D : Category ℓD ℓD') (D₁ : Category ℓD₁ ℓD₁') : Type ((ℓ-max (ℓ-max ℓD ℓD') (ℓ-max ℓD₁ ℓD₁'))) where
    field
      func : Functor D D₁
      inv : Functor D₁ D
      sec : inv ∘F func ≡ Id
      ret : func ∘F inv ≡ Id


  theRightAdjointAt'WhiskFun :
   {ℓC ℓC' ℓD ℓD' ℓD₁ ℓD₁' : Level}
   {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {D₁ : Category ℓD₁ ℓD₁'}
   {F : Functor C D} {d : D .ob} →
   (iso-of-cats : IsoOfCats D D₁) →
    RightAdjointAt' C D F d →
    RightAdjointAt' C D₁
      ((iso-of-cats .IsoOfCats.func) ∘F F)
      ((iso-of-cats .IsoOfCats.func) ⟅ d ⟆)
  theRightAdjointAt'WhiskFun {_} {_} {_} {_} {_} {_} {C} {D} {D₁} {F} {d} iso-of-cats x =
    representationToUniversalElement
      C (funcComp (D₁ [-, iso-of-cats .IsoOfCats.func ⟅ d ⟆ ])
        (funcComp (iso-of-cats .IsoOfCats.func) F ^opF))
      ((x .vertex) ,
      the-psh-iso
      )
      where
      the-x-repr = universalElementToRepresentation C (funcComp (D [-, d ]) (F ^opF)) x

      the-psh-iso : PshIso C (C [-, x .vertex ])
                      (funcComp (D₁ [-, iso-of-cats .IsoOfCats.func ⟅ d ⟆ ])
                       (funcComp (iso-of-cats .IsoOfCats.func) F ^opF))
      the-psh-iso .trans .N-ob c z =
        lift (iso-of-cats .IsoOfCats.func .F-hom (lower (the-x-repr .snd .trans .N-ob c (lift (lower z)))))
      the-psh-iso .trans .N-hom f =
        funExt (λ z →
          {!!} ∙
          cong
          (λ a → lift (iso-of-cats .IsoOfCats.func .F-hom (lower (a (lift (lower z))))))
          (the-x-repr .snd .trans .N-hom f) ∙
          {!!}
        )
      the-psh-iso .nIso = {!!}
  -- theRightAdjointAt'WhiskFun {_} {_} {_} {_} {_} {_} {C} {D} {D₁} {F} {d} iso-of-cats x .vertex =
  --   x .vertex
  -- theRightAdjointAt'WhiskFun {_} {_} {_} {_} {_} {_} {C} {D} {D₁} {F} {d} iso-of-cats x .element =
  --   iso-of-cats .IsoOfCats.func ⟪ x .element ⟫
  -- theRightAdjointAt'WhiskFun {_} {_} {_} {_} {_} {_} {C} {D} {D₁} {F} {d} iso-of-cats x .universal A .equiv-proof y .fst .fst =
  --   x .universal A .equiv-proof
  --     (transport (
  --        cong₂
  --          (λ a b → D [ a , b ])
  --          (cong (λ a → (a .F-ob ((F ^opF) .F-ob A))) (iso-of-cats .IsoOfCats.sec))
  --          (cong (λ a → a .F-ob d) (iso-of-cats .IsoOfCats.sec) )
  --         )
  --        (iso-of-cats .IsoOfCats.inv ⟪ y ⟫))
  --     .fst .fst
  -- theRightAdjointAt'WhiskFun {_} {_} {_} {_} {_} {_} {C} {D} {D₁} {F} {d} iso-of-cats x .universal A .equiv-proof y .fst .snd =
  --   {!refl!} ∙
  --   (cong
  --   (λ a → iso-of-cats .IsoOfCats.func ⟪ a ⟫)
  --   (x .universal A .equiv-proof (transport (
  --        cong₂
  --          (λ a b → D [ a , b ])
  --          (cong (λ a → (a .F-ob ((F ^opF) .F-ob A))) (iso-of-cats .IsoOfCats.sec))
  --          (cong (λ a → a .F-ob d) (iso-of-cats .IsoOfCats.sec) )
  --         )
  --        (iso-of-cats .IsoOfCats.inv ⟪ y ⟫)) .fst .snd)) ∙
  --   {!!}

    -- transport
    -- (cong₂
      -- (λ a b → ?)
      -- (cong (λ a → (a .F-ob ((F ^opF) .F-ob A))) (iso-of-cats .IsoOfCats.sec))
        -- (cong (λ a → a .F-ob d) (iso-of-cats .IsoOfCats.sec) )
    -- )

    -- (x .universal A .equiv-proof (transport (
    --      cong₂
    --        (λ a b → D [ a , b ])
    --        (cong (λ a → (a .F-ob ((F ^opF) .F-ob A))) (iso-of-cats .IsoOfCats.sec))
    --        (cong (λ a → a .F-ob d) (iso-of-cats .IsoOfCats.sec) )
    --       )
    --      (iso-of-cats .IsoOfCats.inv ⟪ y ⟫)) .fst .snd)
         
  theRightAdjointAt'WhiskFun {_} {_} {_} {_} {_} {_} {C} {D} {D₁} {F} {d} iso-of-cats x .universal A .equiv-proof y .snd = {!!}

  bp-prod : RightAdjoint' (C ×C D) ((C ×C C) ×C (D ×C D)) (Δ C ×F Δ D)
  bp-prod = bpC ×RightAdjoint' bpD
