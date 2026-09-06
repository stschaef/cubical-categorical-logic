{-# OPTIONS --lossy-unification #-}
{- The Grothendieck construction: a prestack on `LocallyDiscrete C` is
   an indexed category over C, and `∫Pre` presents it as a `Categoryᴰ`. -}
module Cubical.Categories.Bicategory.Prestack.Grothendieck where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Reindex.Base
open import Cubical.Categories.Displayed.Isomorphism

open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Instances.LocallyDiscrete.Base
open import Cubical.Foundations.Isomorphism renaming (isIso to isIsoFun)
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Reindex

private
  variable
    ℓ ℓ' ℓd ℓd' ℓp ℓp' : Level

open Functor
open UniversalElementⱽ'
open UniversalElement
open Functorᴰ
open Isoᴰ
open NatTrans
open PshHom
open isIso

module _ {C : Category ℓ ℓ'} (P : Prestack (LocallyDiscrete C) ℓp ℓp')
  where
  private
    module C = Category C
    module Pf = Pseudofunctor P
  open PrestackNotation {B = LocallyDiscrete C} P

  -- P's action on a path between 1-cells, taken at a point
  θ : {c c' : C.ob} {f g : C [ c , c' ]} → f ≡ g → (e : p[ c' ])
    → P⟨ c ⟩ [ f ⋆ᴾ e , g ⋆ᴾ e ]
  θ p e = Pf.F-2cell p .N-ob e

  θRefl : {c c' : C.ob} {f : C [ c , c' ]} (e : p[ c' ])
    → θ {f = f} refl e ≡ Pᶜ.id
  θRefl e = cong (λ n → n .N-ob e) (Pf.F-Hom .F-id)

  Homᴳ : {c c' : C.ob} → C [ c , c' ] → p[ c ] → p[ c' ] → Type ℓp'
  Homᴳ {c} f xᴰ yᴰ = P⟨ c ⟩ [ xᴰ , f ⋆ᴾ yᴰ ]

  idᴳ : {c : C.ob} {xᴰ : p[ c ]} → Homᴳ C.id xᴰ xᴰ
  idᴳ {xᴰ = xᴰ} = ⋆ᴾIdL xᴰ .snd .inv

  _⋆ᴳ_ : {c c' c'' : C.ob} {f : C [ c , c' ]} {g : C [ c' , c'' ]}
    {xᴰ : p[ c ]} {yᴰ : p[ c' ]} {zᴰ : p[ c'' ]}
    → Homᴳ f xᴰ yᴰ → Homᴳ g yᴰ zᴰ → Homᴳ (f C.⋆ g) xᴰ zᴰ
  _⋆ᴳ_ {f = f} {g} {zᴰ = zᴰ} fᴰ gᴰ =
    fᴰ Pᶜ.⋆ (reind f .F-hom gᴰ Pᶜ.⋆ ⋆ᴾAssoc f g zᴰ .fst)

  -- a displayed path over `p` is a fibrewise equation twisted by `θ p`
  hmPathP : {c c' : C.ob} {f g : C [ c , c' ]} (p : f ≡ g)
    {xᴰ : p[ c ]} {e : p[ c' ]} (m : Homᴳ f xᴰ e) (n : Homᴳ g xᴰ e)
    → m Pᶜ.⋆ θ p e ≡ n
    → PathP (λ i → Homᴳ (p i) xᴰ e) m n
  hmPathP {c} {c'} {f} p {xᴰ} {e} m =
    J (λ g' p' → (n : Homᴳ g' xᴰ e) → m Pᶜ.⋆ θ p' e ≡ n
        → PathP (λ i → Homᴳ (p' i) xᴰ e) m n)
      (λ n h → sym (Pᶜ.⋆IdR m) ∙ cong (m Pᶜ.⋆_) (sym (θRefl e)) ∙ h)
      p

  substHom : {c c' : C.ob} {f g : C [ c , c' ]} (p : f ≡ g)
    {xᴰ : p[ c ]} {e : p[ c' ]} (m : Homᴳ f xᴰ e)
    → subst (λ h → Homᴳ h xᴰ e) p m ≡ m Pᶜ.⋆ θ p e
  substHom p m = fromPathP (hmPathP p m _ refl)

  laxρ-pt : {c c' : C.ob} (f : C [ c , c' ]) (e : p[ c' ])
    → (Pᶜ.id Pᶜ.⋆ Pf.F⁰ .N-ob (f ⋆ᴾ e))
        Pᶜ.⋆ (⋆ᴾAssoc C.id f e .fst Pᶜ.⋆ θ (C.⋆IdL f) e)
      ≡ Pᶜ.id
  laxρ-pt f e = cong (λ n → n .N-ob e) (Pf.lax-ρ _ _ f)

  laxλ-pt : {c c' : C.ob} (f : C [ c , c' ]) (e : p[ c' ])
    → (reind f .F-hom (Pf.F⁰ .N-ob e) Pᶜ.⋆ Pᶜ.id)
        Pᶜ.⋆ (⋆ᴾAssoc f C.id e .fst Pᶜ.⋆ θ (C.⋆IdR f) e)
      ≡ Pᶜ.id
  laxλ-pt f e = cong (λ n → n .N-ob e) (Pf.lax-λ _ _ f)

  laxα-pt : {c0 c1 c2 c3 : C.ob}
    (u : C [ c0 , c1 ]) (v : C [ c1 , c2 ]) (w : C [ c2 , c3 ])
    (e : p[ c3 ])
    → (reind u .F-hom (⋆ᴾAssoc v w e .fst) Pᶜ.⋆ Pᶜ.id)
        Pᶜ.⋆ (⋆ᴾAssoc u (v C.⋆ w) e .fst
              Pᶜ.⋆ θ (sym (C.⋆Assoc u v w)) e)
      ≡ Pᶜ.id
        Pᶜ.⋆ ((reind u .F-hom (reind v .F-hom Pᶜ.id)
               Pᶜ.⋆ ⋆ᴾAssoc u v (w ⋆ᴾ e) .fst)
              Pᶜ.⋆ ⋆ᴾAssoc (u C.⋆ v) w e .fst)
  laxα-pt u v w e = cong (λ n → n .N-ob e) (Pf.lax-α _ _ _ _ w v u)

  ⋆IdLᴳ : {c c' : C.ob} {f : C [ c , c' ]} {xᴰ : p[ c ]} {yᴰ : p[ c' ]}
    (fᴰ : Homᴳ f xᴰ yᴰ)
    → PathP (λ i → Homᴳ (C.⋆IdL f i) xᴰ yᴰ) (idᴳ ⋆ᴳ fᴰ) fᴰ
  ⋆IdLᴳ {f = f} {xᴰ} {yᴰ} fᴰ = hmPathP (C.⋆IdL f) _ _ (
      Pᶜ.⋆Assoc η (r Pᶜ.⋆ A) t
    ∙ cong (λ m → η Pᶜ.⋆ m) (Pᶜ.⋆Assoc r A t)
    ∙ sym (Pᶜ.⋆Assoc η r (A Pᶜ.⋆ t))
    ∙ cong (λ m → m Pᶜ.⋆ (A Pᶜ.⋆ t)) (sym (Pf.F⁰ .N-hom fᴰ))
    ∙ Pᶜ.⋆Assoc fᴰ η' (A Pᶜ.⋆ t)
    ∙ cong (λ m → fᴰ Pᶜ.⋆ m)
        (cong (λ m → m Pᶜ.⋆ (A Pᶜ.⋆ t)) (sym (Pᶜ.⋆IdL η')) ∙ laxρ-pt f yᴰ)
    ∙ Pᶜ.⋆IdR fᴰ)
    where
    η = Pf.F⁰ .N-ob xᴰ
    η' = Pf.F⁰ .N-ob (f ⋆ᴾ yᴰ)
    r = reind C.id .F-hom fᴰ
    A = ⋆ᴾAssoc C.id f yᴰ .fst
    t = θ (C.⋆IdL f) yᴰ

  ⋆IdRᴳ : {c c' : C.ob} {f : C [ c , c' ]} {xᴰ : p[ c ]} {yᴰ : p[ c' ]}
    (fᴰ : Homᴳ f xᴰ yᴰ)
    → PathP (λ i → Homᴳ (C.⋆IdR f i) xᴰ yᴰ) (fᴰ ⋆ᴳ idᴳ) fᴰ
  ⋆IdRᴳ {f = f} {xᴰ} {yᴰ} fᴰ = hmPathP (C.⋆IdR f) _ _ (
      Pᶜ.⋆Assoc fᴰ (F Pᶜ.⋆ A) t
    ∙ cong (λ m → fᴰ Pᶜ.⋆ m) (Pᶜ.⋆Assoc F A t)
    ∙ cong (λ m → fᴰ Pᶜ.⋆ m)
        (cong (λ m → m Pᶜ.⋆ (A Pᶜ.⋆ t)) (sym (Pᶜ.⋆IdR F)) ∙ laxλ-pt f yᴰ)
    ∙ Pᶜ.⋆IdR fᴰ)
    where
    F = reind f .F-hom (Pf.F⁰ .N-ob yᴰ)
    A = ⋆ᴾAssoc f C.id yᴰ .fst
    t = θ (C.⋆IdR f) yᴰ

  laxα' : {c0 c1 c2 c3 : C.ob}
    (u : C [ c0 , c1 ]) (v : C [ c1 , c2 ]) (w : C [ c2 , c3 ])
    (e : p[ c3 ])
    → reind u .F-hom (⋆ᴾAssoc v w e .fst)
        Pᶜ.⋆ (⋆ᴾAssoc u (v C.⋆ w) e .fst Pᶜ.⋆ θ (sym (C.⋆Assoc u v w)) e)
      ≡ ⋆ᴾAssoc u v (w ⋆ᴾ e) .fst Pᶜ.⋆ ⋆ᴾAssoc (u C.⋆ v) w e .fst
  laxα' u v w e =
      cong (λ m → m Pᶜ.⋆ (B4 Pᶜ.⋆ t)) (sym (Pᶜ.⋆IdR B3))
    ∙ laxα-pt u v w e
    ∙ Pᶜ.⋆IdL _
    ∙ cong (λ m → (m Pᶜ.⋆ B1) Pᶜ.⋆ B2)
        (cong (reind u .F-hom) (reind v .F-id) ∙ reind u .F-id)
    ∙ cong (λ m → m Pᶜ.⋆ B2) (Pᶜ.⋆IdL B1)
    where
    B3 = reind u .F-hom (⋆ᴾAssoc v w e .fst)
    B4 = ⋆ᴾAssoc u (v C.⋆ w) e .fst
    t = θ (sym (C.⋆Assoc u v w)) e
    B1 = ⋆ᴾAssoc u v (w ⋆ᴾ e) .fst
    B2 = ⋆ᴾAssoc (u C.⋆ v) w e .fst

  ⋆Assocᴳ : {c0 c1 c2 c3 : C.ob}
    {u : C [ c0 , c1 ]} {v : C [ c1 , c2 ]} {w : C [ c2 , c3 ]}
    {x0 : p[ c0 ]} {x1 : p[ c1 ]} {x2 : p[ c2 ]} {x3 : p[ c3 ]}
    (uᴰ : Homᴳ u x0 x1) (vᴰ : Homᴳ v x1 x2) (wᴰ : Homᴳ w x2 x3)
    → PathP (λ i → Homᴳ (C.⋆Assoc u v w i) x0 x3)
        ((uᴰ ⋆ᴳ vᴰ) ⋆ᴳ wᴰ) (uᴰ ⋆ᴳ (vᴰ ⋆ᴳ wᴰ))
  ⋆Assocᴳ {u = u} {v} {w} {x0} {x1} {x2} {x3} uᴰ vᴰ wᴰ =
    symP (hmPathP (sym (C.⋆Assoc u v w)) _ _ (
        cong (λ m → (uᴰ Pᶜ.⋆ (m Pᶜ.⋆ B4)) Pᶜ.⋆ t)
          ( reind u .F-seq vᴰ (cv Pᶜ.⋆ B3)
          ∙ cong (λ m → b Pᶜ.⋆ m) (reind u .F-seq cv B3))
      ∙ Pᶜ.⋆Assoc uᴰ ((b Pᶜ.⋆ (c Pᶜ.⋆ d)) Pᶜ.⋆ B4) t
      ∙ cong (λ m → uᴰ Pᶜ.⋆ m) (Pᶜ.⋆Assoc (b Pᶜ.⋆ (c Pᶜ.⋆ d)) B4 t)
      ∙ cong (λ m → uᴰ Pᶜ.⋆ m) (Pᶜ.⋆Assoc b (c Pᶜ.⋆ d) (B4 Pᶜ.⋆ t))
      ∙ cong (λ m → uᴰ Pᶜ.⋆ (b Pᶜ.⋆ m)) (Pᶜ.⋆Assoc c d (B4 Pᶜ.⋆ t))
      ∙ cong (λ m → uᴰ Pᶜ.⋆ (b Pᶜ.⋆ (c Pᶜ.⋆ m))) (laxα' u v w x3)
      ∙ cong (λ m → uᴰ Pᶜ.⋆ (b Pᶜ.⋆ m)) (sym (Pᶜ.⋆Assoc c B1 B2))
      ∙ cong (λ m → uᴰ Pᶜ.⋆ (b Pᶜ.⋆ (m Pᶜ.⋆ B2))) (Pf.F² v u .N-hom wᴰ)
      ∙ cong (λ m → uᴰ Pᶜ.⋆ (b Pᶜ.⋆ m)) (Pᶜ.⋆Assoc A1 e2 B2)
      ∙ cong (λ m → uᴰ Pᶜ.⋆ m) (sym (Pᶜ.⋆Assoc b A1 (e2 Pᶜ.⋆ B2)))
      ∙ sym (Pᶜ.⋆Assoc uᴰ (b Pᶜ.⋆ A1) (e2 Pᶜ.⋆ B2))))
    where
    b = reind u .F-hom vᴰ
    cv = reind v .F-hom wᴰ
    c = reind u .F-hom cv
    B3 = ⋆ᴾAssoc v w x3 .fst
    d = reind u .F-hom B3
    B4 = ⋆ᴾAssoc u (v C.⋆ w) x3 .fst
    t = θ (sym (C.⋆Assoc u v w)) x3
    B1 = ⋆ᴾAssoc u v (w ⋆ᴾ x3) .fst
    B2 = ⋆ᴾAssoc (u C.⋆ v) w x3 .fst
    A1 = ⋆ᴾAssoc u v x2 .fst
    e2 = reind (u C.⋆ v) .F-hom wᴰ

  -- objects over c are objects of P⟨ c ⟩; morphisms over f : c → c'
  -- are morphisms xᴰ → f ⋆ᴾ yᴰ in P⟨ c ⟩
  ∫Pre : Categoryᴰ C ℓp ℓp'
  ∫Pre .Categoryᴰ.ob[_] c = p[ c ]
  ∫Pre .Categoryᴰ.Hom[_][_,_] = Homᴳ
  ∫Pre .Categoryᴰ.idᴰ = idᴳ
  ∫Pre .Categoryᴰ._⋆ᴰ_ = _⋆ᴳ_
  ∫Pre .Categoryᴰ.⋆IdLᴰ = ⋆IdLᴳ
  ∫Pre .Categoryᴰ.⋆IdRᴰ = ⋆IdRᴳ
  ∫Pre .Categoryᴰ.⋆Assocᴰ = ⋆Assocᴳ
  ∫Pre .Categoryᴰ.isSetHomᴰ = Pᶜ.isSetHom
-- Reindexing a displayed category along `F` agrees with reindexing the
-- corresponding prestack along `LocallyDiscreteF F`.
  private
    ∫P = ∫Pre
    module ∫P = Categoryᴰ ∫P
    module F = Fibers ∫P

  -- postcomposing with a fibrewise iso is a bijection on displayed homs
  private
    postIso : {Γ : C.ob} {Γᴰ a b : p[ Γ ]} (m : CatIso P⟨ Γ ⟩ a b)
      → Iso (P⟨ Γ ⟩ [ Γᴰ , a ]) (P⟨ Γ ⟩ [ Γᴰ , b ])
    postIso m .Iso.fun h = h Pᶜ.⋆ m .fst
    postIso m .Iso.inv h = h Pᶜ.⋆ m .snd .isIso.inv
    postIso m .Iso.sec h = Pᶜ.⋆Assoc _ _ _
      ∙ cong (h Pᶜ.⋆_) (m .snd .isIso.sec) ∙ Pᶜ.⋆IdR h
    postIso m .Iso.ret h = Pᶜ.⋆Assoc _ _ _
      ∙ cong (h Pᶜ.⋆_) (m .snd .isIso.ret) ∙ Pᶜ.⋆IdR h

  -- `∫Pre P` is always a fibration: the lift of `f` at `yᴰ` is `f ⋆ᴾ yᴰ`
  module _ {x y : C.ob} (f : C [ x , y ]) (yᴰ : p[ y ]) where
    private
      Q : Presheafⱽ y ∫P ℓp'
      Q = ∫P [-][-, yᴰ ]
      module Q = PresheafᴰNotation ∫P (C [-, y ]) Q

      Spec : Presheafⱽ x ∫P ℓp'
      Spec = CartesianLiftPshSpec (C [-, y ]) ∫P Q f
      module Spec = PresheafᴰNotation ∫P (C [-, x ]) Spec

      ε : ∫P.Hom[ f ][ f ⋆ᴾ yᴰ , yᴰ ]
      ε = Pᶜ.id

      elem : Spec.p[ C.id ][ f ⋆ᴾ yᴰ ]
      elem = F.reind (sym (C.⋆IdL f)) ε

      key : (Γ : C.ob) (Γᴰ : p[ Γ ]) (g : C [ Γ , x ])
        (gᴰ : ∫P.Hom[ g ][ Γᴰ , f ⋆ᴾ yᴰ ])
        → yoRecⱽ Spec elem .N-ob (Γ , Γᴰ , g) gᴰ
          ≡ postIso (⋆ᴾAssoc g f yᴰ) .Iso.fun gᴰ
      key Γ Γᴰ g gᴰ = F.rectify (F.≡out
          ( (F.≡in (cong (λ e → Q .F-hom (g , gᴰ , e) elem)
                     (C.isSetHom _ _ _ (cong (g C.⋆_) (C.⋆IdL f)))))
          ∙ Q.⋆ᴰ-reind gᴰ (cong (g C.⋆_) (C.⋆IdL f)) elem
          ∙ F.reind-filler⁻ refl
          ∙ F.⟨ refl ⟩⋆⟨ F.reind-filler⁻ (sym (C.⋆IdL f)) ⟩))
        ∙ cong (gᴰ Pᶜ.⋆_)
            (cong (Pᶜ._⋆ ⋆ᴾAssoc g f yᴰ .fst) (reind g .F-id)
             ∙ Pᶜ.⋆IdL _)

    ∫PreCartesianLift : CartesianLift ∫P f yᴰ
    ∫PreCartesianLift = REPRⱽ lift'
      where
      lift' : UniversalElementⱽ' ∫P x Spec
      lift' .vertexⱽ = f ⋆ᴾ yᴰ
      lift' .elementⱽ = elem
      lift' .universalⱽ (Γ , Γᴰ , g) =
        subst isIsoFun (sym (funExt (key Γ Γᴰ g)))
          (IsoToIsIso (postIso (⋆ᴾAssoc g f yᴰ)))

  ∫PreFibration : isFibration ∫P
  ∫PreFibration yᴰ _ f = ∫PreCartesianLift f yᴰ

module _ {C : Category ℓ ℓ'} {D : Category ℓd ℓd'} (F : Functor C D)
  (P : Prestack (LocallyDiscrete D) ℓp ℓp')
  where
  private
    module C = Category C
    module F = Functor F

    ∫F : Categoryᴰ C ℓp ℓp'
    ∫F = reindex (∫Pre P) F

    ∫R : Categoryᴰ C ℓp ℓp'
    ∫R = ∫Pre (reindexPrestack (LocallyDiscreteF F) P)

    module ∫F = Categoryᴰ ∫F
    module ∫R = Categoryᴰ ∫R

  open PrestackNotation {B = LocallyDiscrete D} P

  reindexOb : (c : C.ob) → ∫F.ob[ c ] ≡ ∫R.ob[ c ]
  reindexOb _ = refl

  reindexHom : {c c' : C.ob} (f : C [ c , c' ])
    (xᴰ : ∫F.ob[ c ]) (yᴰ : ∫F.ob[ c' ])
    → ∫F.Hom[ f ][ xᴰ , yᴰ ] ≡ ∫R.Hom[ f ][ xᴰ , yᴰ ]
  reindexHom _ _ _ = refl

  reindexIsSetHom : {c c' : C.ob} {f : C [ c , c' ]}
    {xᴰ : ∫F.ob[ c ]} {yᴰ : ∫F.ob[ c' ]}
    → ∫F.isSetHomᴰ {f = f} {xᴰ} {yᴰ} ≡ ∫R.isSetHomᴰ
  reindexIsSetHom = refl

  -- the two structure maps differ: `reindex` transports, the prestack
  -- composite postcomposes with P's action on the same 2-cell
  reindexId : {c : C.ob} {xᴰ : ∫F.ob[ c ]}
    → ∫F.idᴰ {p = xᴰ} ≡ ∫R.idᴰ {p = xᴰ}
  reindexId = substHom P (sym F.F-id) _

  reindexSeq : {c c' c'' : C.ob} {f : C [ c , c' ]} {g : C [ c' , c'' ]}
    {xᴰ : ∫F.ob[ c ]} {yᴰ : ∫F.ob[ c' ]} {zᴰ : ∫F.ob[ c'' ]}
    (fᴰ : ∫F.Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : ∫F.Hom[ g ][ yᴰ , zᴰ ])
    → fᴰ ∫F.⋆ᴰ gᴰ ≡ fᴰ ∫R.⋆ᴰ gᴰ
  reindexSeq {f = f} {g} {zᴰ = zᴰ} fᴰ gᴰ =
      substHom P (sym (F.F-seq f g)) _
    ∙ Pᶜ.⋆Assoc fᴰ (r Pᶜ.⋆ A) t
    ∙ cong (λ m → fᴰ Pᶜ.⋆ m) (Pᶜ.⋆Assoc r A t)
    where
    r = reind (F.F-hom f) .F-hom gᴰ
    A = ⋆ᴾAssoc (F.F-hom f) (F.F-hom g) zᴰ .fst
    t = θ P (sym (F.F-seq f g)) zᴰ

  -- hence an isomorphism of displayed categories over C: the identity
  -- on objects and on displayed morphisms, both ways
  reindex∫Isoᴰ : Isoᴰ ∫F ∫R
  reindex∫Isoᴰ .funⱽ .F-obᴰ xᴰ = xᴰ
  reindex∫Isoᴰ .funⱽ .F-homᴰ fᴰ = fᴰ
  reindex∫Isoᴰ .funⱽ .F-idᴰ = reindexId
  reindex∫Isoᴰ .funⱽ .F-seqᴰ = reindexSeq
  reindex∫Isoᴰ .invⱽ .F-obᴰ xᴰ = xᴰ
  reindex∫Isoᴰ .invⱽ .F-homᴰ fᴰ = fᴰ
  reindex∫Isoᴰ .invⱽ .F-idᴰ = sym reindexId
  reindex∫Isoᴰ .invⱽ .F-seqᴰ fᴰ gᴰ = sym (reindexSeq fᴰ gᴰ)
  reindex∫Isoᴰ .obSec _ = refl
  reindex∫Isoᴰ .obRet _ = refl
  reindex∫Isoᴰ .homSec _ = refl
  reindex∫Isoᴰ .homRet _ = refl

  -- and, the data agreeing definitionally, an outright path
  reindex∫≡ : ∫F ≡ ∫R
  reindex∫≡ = sameDataᴰ≡ refl refl (λ i → reindexId i)
    (λ i fᴰ gᴰ → reindexSeq fᴰ gᴰ i)
