module Cubical.Categories.Isomorphism.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.BinProduct

open import Cubical.Categories.Isomorphism

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor
open isIso
module _ {C : Category ℓC ℓC'} where
  ⋆InvLMove⁻ : {x y z : C .ob}
    (f : CatIso C x y)
    {g : C [ y , z ]}{h : C [ x , z ]}
    → g ≡ f .snd .inv ⋆⟨ C ⟩ h
    → f .fst ⋆⟨ C ⟩ g ≡ h
  ⋆InvLMove⁻ f {g = g} {h = h} p =
    cong (λ a → f .fst ⋆⟨ C ⟩ a) p ∙
    sym (C .⋆Assoc _ _ _) ∙
    cong (λ a → a ⋆⟨ C ⟩ h) (f .snd .ret) ∙
    C .⋆IdL _

  ⋆InvRMove⁻ : {x y z : C .ob}
    (f : CatIso C y z)
    {g : C [ x , y ]}{h : C [ x , z ]}
    → g ≡ h ⋆⟨ C ⟩ f .snd .inv
    → g ⋆⟨ C ⟩ f .fst ≡ h
  ⋆InvRMove⁻ f {g = g} {h = h} p =
    cong (λ a → a ⋆⟨ C ⟩ f .fst) p ∙
    C .⋆Assoc _ _ _ ∙
    cong (λ a → h ⋆⟨ C ⟩ a) (f .snd .sec) ∙
    C .⋆IdR _

  ⋆InvsFlipSq : {w x y z : C .ob}
    (e : CatIso C w x)
    {g : C [ w , y ]}
    {h : C [ x , z ]}
    (f : CatIso C y z)
    → e .fst ⋆⟨ C ⟩ h ≡ g ⋆⟨ C ⟩ f .fst
    → h ⋆⟨ C ⟩ f .snd .inv ≡ e .snd .inv ⋆⟨ C ⟩ g
  ⋆InvsFlipSq e {g} {h} f p =
    ⋆InvLMove e
      (sym (C .⋆Assoc _ _ _)
      ∙ sym (⋆InvRMove f (sym p)))

  ⋆InvsFlipSq⁻ : {w x y z : C .ob}
    (e : CatIso C w x)
    {g : C [ w , y ]}
    {h : C [ x , z ]}
    (f : CatIso C y z)
    → h ⋆⟨ C ⟩ f .snd .inv ≡ e .snd .inv ⋆⟨ C ⟩ g
    → e .fst ⋆⟨ C ⟩ h ≡ g ⋆⟨ C ⟩ f .fst
  ⋆InvsFlipSq⁻ e f p = ⋆InvLMove⁻ e
    ( sym (⋆InvRMove⁻ f (sym p))
    ∙ C .⋆Assoc _ _ _)

module _ {C : Category ℓC ℓC'} where
  private
    module C = Category C

  step-CatIso : (a : C.ob) {b c : C.ob} → CatIso C b c → CatIso C a b → CatIso C a c
  step-CatIso _ g f = ⋆Iso f g

  infixr  2 step-CatIso
  syntax step-CatIso a b f = a CatIso⟨ f ⟩ b

  _∎CatIso : ∀ (c : C.ob) → CatIso C c c
  c ∎CatIso = idCatIso

  infix   3 _∎CatIso

module _ {C : Category ℓC ℓC'} where
  ⋆IsIso : {x y z : C .ob} {f : C [ x , y ]} {g : C [ y , z ]}
    → Cubical.Categories.Category.isIso C f
    → Cubical.Categories.Category.isIso C g
    → Cubical.Categories.Category.isIso C (f ⋆⟨ C ⟩ g)
  ⋆IsIso p q = ⋆Iso (_ , p) (_ , q) .snd

  idIsIso : {x : C .ob}
    → Cubical.Categories.Category.isIso C (C .Category.id {x})
  idIsIso = idCatIso .snd

-- A morphism is an identity when its codomain is its domain, coherently:
-- a path in the co-singleton of morphisms out of `a`.
module _ {C : Category ℓC ℓC'} where
  isIdHom : {a b : C .ob} → C [ a , b ] → Type (ℓ-max ℓC ℓC')
  isIdHom {a} {b} f = Path (Σ[ c ∈ C .ob ] C [ a , c ]) (a , C .id) (b , f)

  idIsIdHom : {a : C .ob} → isIdHom (C .id {a})
  idIsIdHom = refl

  ⋆IsIdHom : {a b c : C .ob} {f : C [ a , b ]} {g : C [ b , c ]}
    → isIdHom f → isIdHom g → isIdHom (f ⋆⟨ C ⟩ g)
  ⋆IsIdHom {a} {b} {c} {f} {g} p =
    J (λ u _ → {d : C .ob} {h : C [ u .fst , d ]}
             → isIdHom h → isIdHom (u .snd ⋆⟨ C ⟩ h))
      base p {c} {g}
    where
    base : {d : C .ob} {h : C [ a , d ]}
      → isIdHom h → isIdHom (C .id ⋆⟨ C ⟩ h)
    base {h = h} q =
        cong (a ,_) (sym (C .⋆IdL (C .id)))
      ∙ cong (λ u → (u .fst , C .id ⋆⟨ C ⟩ u .snd)) q

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D) where
  F-isIdHom : {a b : C .ob} {f : C [ a , b ]}
    → isIdHom {C = C} f → isIdHom {C = D} (F .F-hom f)
  F-isIdHom {a} p =
      cong (λ m → (F .F-ob a , m)) (sym (F .F-id))
    ∙ cong (λ u → (F .F-ob (u .fst) , F .F-hom (u .snd))) p

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  pairIsIdHom : {a a' : C .ob} {b b' : D .ob}
    {f : C [ a , a' ]} {g : D [ b , b' ]}
    → isIdHom {C = C} f → isIdHom {C = D} g
    → isIdHom {C = C ×C D} (f , g)
  pairIsIdHom p q =
    cong₂ (λ u v → ((u .fst , v .fst) , (u .snd , v .snd))) p q
