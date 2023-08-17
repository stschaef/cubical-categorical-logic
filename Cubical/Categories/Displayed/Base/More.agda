{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.Base.More where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport hiding (pathToIso)
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor

open import Cubical.Tactics.CategorySolver.Reflection

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  open Functor

  Fst : Functor (∫C Cᴰ) C
  Fst .F-ob = fst
  Fst .F-hom = fst
  Fst .F-id = refl
  Fst .F-seq =
    λ f g → cong {x = f ⋆⟨ ∫C Cᴰ ⟩ g} fst refl

  open Category C
  open Categoryᴰ Cᴰ
  open isIso
  record isIsoᴰ {x y : ob}{f : C [ x , y ]}(fIsIso : isIso C f)
         {xᴰ}{yᴰ} (fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]): Type ℓCᴰ'
    where
    constructor isisoᴰ
    field
      inv : Cᴰ [ fIsIso .inv ][ yᴰ , xᴰ ]
      sec : inv ⋆ᴰ fᴰ ≡[ fIsIso .sec ] idᴰ
      ret : fᴰ ⋆ᴰ inv ≡[ fIsIso .ret ] idᴰ

  open isIsoᴰ

  isPropIsIsoᴰ : ∀ {x y}{f : C [ x , y ]}{fIsIso : isIso C f}
                   {xᴰ yᴰ}(fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ])
                → isProp (isIsoᴰ fIsIso fᴰ)
  isPropIsIsoᴰ {x} {y} {f} {fIsIso} {xᴰ} {yᴰ} fᴰ p q =
    λ i →
    isisoᴰ
      (the-inv-path i) (the-sec-path i) (the-ret-path i)
    where
    the-hom-path : {x y : ob} {f g : C [ x , y ]}
      {xᴰ : ob[ x ]}{yᴰ : ob[ y ]} → (f ≡ g) →
      (Cᴰ [ f ][ xᴰ , yᴰ ]) ≡ (Cᴰ [ g ][ xᴰ , yᴰ ])
    the-hom-path p = cong (λ v → Cᴰ [ v ][ _ , _ ]) p

    the-fIsIsoInv-path : fIsIso .inv ≡ fIsIso .inv
    the-fIsIsoInv-path =
      sym (⋆IdL _)
      ∙ (λ i → fIsIso .sec (~ i) ⋆⟨ C ⟩ fIsIso .inv)
      ∙ ⋆Assoc _ _ _
      ∙ (λ i → fIsIso .inv ⋆ fIsIso .ret i)
      ∙ ⋆IdR _

    the-inv-pathP : PathP (λ i → the-hom-path the-fIsIsoInv-path i)
                    (p .inv) (q .inv)
    the-inv-pathP =
      compPathP' {B = the-B} (symP (⋆IdLᴰ (p .inv)))
        (compPathP' {B = the-B} (symP (congP (λ i a → a ⋆ᴰ p .inv) (q .sec)))
          (compPathP' {B = the-B} (⋆Assocᴰ (q .inv) fᴰ (p .inv))
            (compPathP' {B = the-B} (congP (λ i a → q .inv ⋆ᴰ a) (p .ret))
              (⋆IdRᴰ (q .inv)))))
      where
      the-B = Cᴰ [_][ yᴰ , xᴰ ]

    path-is-over-refl : the-hom-path the-fIsIsoInv-path ≡ refl
    path-is-over-refl =
      cong (λ a → (cong (λ v → Cᴰ [ v ][ yᴰ , xᴰ ]) a))
          (isSetHom (fIsIso .inv) (fIsIso .inv) the-fIsIsoInv-path refl)

    the-inv-path : p .inv ≡ q .inv
    the-inv-path =
      sym (transportRefl (p .inv)) ∙
      cong (λ a → transport a (p .inv)) (sym path-is-over-refl) ∙
      fromPathP the-inv-pathP

    the-sec-path :
      PathP (λ i → (the-inv-path i ⋆ᴰ fᴰ) ≡[ fIsIso .sec ] idᴰ)
        (p .sec) (q .sec)
    the-sec-path =
      isProp→PathP
        (λ i → isOfHLevelPathP' 1 isSetHomᴰ _ _)
        (p .sec)
        (q .sec)

    the-ret-path :
      PathP (λ i → (fᴰ ⋆ᴰ the-inv-path i) ≡[ fIsIso .ret ] idᴰ)
        (p .ret) (q .ret)
    the-ret-path =
      isProp→PathP
        (λ i → isOfHLevelPathP' 1 isSetHomᴰ _ _)
        (p .ret)
        (q .ret)

  CatᴰIso : ∀ {x y}(iso : CatIso C x y)(xᴰ : ob[ x ])(yᴰ : ob[ y ]) → Type ℓCᴰ'
  CatᴰIso iso xᴰ yᴰ = Σ[ fᴰ ∈ Cᴰ [ iso .fst ][ xᴰ , yᴰ ] ] isIsoᴰ (iso .snd) fᴰ

  conservative : Type _
  conservative = ∀ {x y} {f : C [ x , y ]}{xᴰ yᴰ} (fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ])
               → (fIsIso : isIso C f)
               → isIsoᴰ fIsIso fᴰ
               

  idCatᴰIso : ∀ {x}{xᴰ : ob[ x ]} → CatᴰIso idCatIso xᴰ xᴰ
  idCatᴰIso .fst = idᴰ
  idCatᴰIso .snd .isIsoᴰ.inv = idᴰ
  idCatᴰIso .snd .isIsoᴰ.sec = ⋆IdLᴰ _
  idCatᴰIso .snd .isIsoᴰ.ret = ⋆IdLᴰ _

  pathᴰToIsoᴰ : ∀ {x y}{xᴰ : ob[ x ]}{yᴰ : ob[ y ]}
              → {p : x ≡ y}
              → PathP (λ i → ob[ p i ]) xᴰ yᴰ
              → CatᴰIso (pathToIso p) xᴰ yᴰ
  pathᴰToIsoᴰ{xᴰ = xᴰ} {p = p} pᴰ =
    JDep (λ y p yᴰ q → CatᴰIso (pathToIso p) xᴰ yᴰ)
      (transport (λ i → CatᴰIso (pathToIso-refl (~ i)) xᴰ xᴰ) idCatᴰIso)
      p
      pᴰ

  -- Note: the 1lab has an alternative definition that they say is
  -- much easier to work with.
  isUnivalentᴰ : Type (ℓ-max (ℓ-max ℓC ℓCᴰ) ℓCᴰ')
  isUnivalentᴰ = ∀ {x}{y} (xᴰ : ob[ x ])(yᴰ : ob[ y ])(p : x ≡ y) →
    isEquiv (pathᴰToIsoᴰ {xᴰ = xᴰ}{yᴰ = yᴰ}{p = p})

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  open Category
  private
    module Cᴰ = Categoryᴰ Cᴰ

  

  base-path-irr : ∀ {x y xᴰ yᴰ} {f g : C [ x , y ]}
                → {fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]}
                → {p : f ≡ g}
                → {gᴰ : Cᴰ.Hom[ g ][ xᴰ , yᴰ ]}
                → {q : f ≡ g}
                → fᴰ Cᴰ.≡[ p ] gᴰ
                → fᴰ Cᴰ.≡[ q ] gᴰ
  base-path-irr {fᴰ = fᴰ}{p}{gᴰ}{q} = transport λ i →
    fᴰ Cᴰ.≡[ C .isSetHom _ _ p q i ] gᴰ

  open Categoryᴰ
  _^opᴰ : Categoryᴰ (C ^op) ℓCᴰ ℓCᴰ'
  _^opᴰ .ob[_] x = Cᴰ.ob[ x ]
  _^opᴰ .Hom[_][_,_] f xᴰ yᴰ = Cᴰ.Hom[ f ][ yᴰ , xᴰ ]
  _^opᴰ .idᴰ = Cᴰ.idᴰ
  _^opᴰ ._⋆ᴰ_ fᴰ gᴰ = gᴰ Cᴰ.⋆ᴰ fᴰ
  _^opᴰ .⋆IdLᴰ = Cᴰ .⋆IdRᴰ
  _^opᴰ .⋆IdRᴰ = Cᴰ .⋆IdLᴰ
  _^opᴰ .⋆Assocᴰ fᴰ gᴰ hᴰ = symP (Cᴰ.⋆Assocᴰ _ _ _)
  _^opᴰ .isSetHomᴰ = Cᴰ .isSetHomᴰ

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {F : Functor C D} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  where
  open Functorᴰ
  _^opFᴰ : Functorᴰ (F ^opF) (Cᴰ ^opᴰ) (Dᴰ ^opᴰ)
  _^opFᴰ .F-obᴰ = Fᴰ .F-obᴰ
  _^opFᴰ .F-homᴰ = Fᴰ .F-homᴰ
  _^opFᴰ .F-idᴰ = Fᴰ .F-idᴰ
  _^opFᴰ .F-seqᴰ fᴰ gᴰ = Fᴰ .F-seqᴰ gᴰ fᴰ
