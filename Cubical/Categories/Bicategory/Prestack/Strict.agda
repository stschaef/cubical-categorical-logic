{-# OPTIONS --lossy-unification #-}
{- Strict prestacks: the ones whose F⁰ and F² are identity 2-cells. -}
module Cubical.Categories.Bicategory.Prestack.Strict where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Functor.Identity
open import Cubical.Categories.Bicategory.Functor.Composition
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.Transformation.Composition
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Morphism
open import Cubical.Categories.Bicategory.Prestack.Constant
open import Cubical.Categories.Bicategory.Prestack.Hom
open import Cubical.Categories.Bicategory.Prestack.BinProduct
open import Cubical.Categories.Bicategory.Prestack.Reindex

private
  variable
    ℓ ℓ' ℓ'' ℓp ℓp' ℓc ℓc' ℓd ℓd' : Level
    ℓa ℓa' ℓa'' ℓb ℓb' ℓb'' ℓe ℓe' ℓe'' : Level

open Functor
open NatTrans

-- A morphism is an identity when its codomain is its domain, coherently:
-- a path in the co-singleton of morphisms out of `a`.
module _ {C : Category ℓc ℓc'} where
  private module C = Category C

  isIdHom : {a b : C.ob} → C [ a , b ] → Type (ℓ-max ℓc ℓc')
  isIdHom {a} {b} f = Path (Σ[ c ∈ C.ob ] C [ a , c ]) (a , C.id) (b , f)

  idIsIdHom : {a : C.ob} → isIdHom (C.id {a})
  idIsIdHom = refl

  ⋆IsIdHom : {a b c : C.ob} {f : C [ a , b ]} {g : C [ b , c ]}
    → isIdHom f → isIdHom g → isIdHom (f C.⋆ g)
  ⋆IsIdHom {a} {b} {c} {f} {g} p =
    J (λ u _ → {d : C.ob} {h : C [ u .fst , d ]}
             → isIdHom h → isIdHom (u .snd C.⋆ h))
      base p {c} {g}
    where
    base : {d : C.ob} {h : C [ a , d ]}
      → isIdHom h → isIdHom (C.id C.⋆ h)
    base {h = h} q =
        cong (a ,_) (sym (C.⋆IdL C.id))
      ∙ cong (λ u → (u .fst , C.id C.⋆ u .snd)) q

module _ {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} (F : Functor C D) where
  private
    module C = Category C

  F-isIdHom : {a b : C.ob} {f : C [ a , b ]}
    → isIdHom {C = C} f → isIdHom {C = D} (F .F-hom f)
  F-isIdHom {a} p =
      cong (λ m → (F .F-ob a , m)) (sym (F .F-id))
    ∙ cong (λ u → (F .F-ob (u .fst) , F .F-hom (u .snd))) p

module _ {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} where
  pairIsIdHom : {a a' : Category.ob C} {b b' : Category.ob D}
    {f : C [ a , a' ]} {g : D [ b , b' ]}
    → isIdHom {C = C} f → isIdHom {C = D} g
    → isIdHom {C = C ×C D} (f , g)
  pairIsIdHom p q =
    cong₂ (λ u v → ((u .fst , v .fst) , (u .snd , v .snd))) p q

module _ {B : Bicategory ℓ ℓ' ℓ''} (P : Prestack B ℓp ℓp') where
  private
    module B = Bicategory B
    module PN = PrestackNotation P

  -- Componentwise, not `P.F⁰ ≡ idTrans`: `Functor` is `no-eta-equality`,
  -- so `reind B.id₁ ≡ Id` is never `refl`, and the fibrewise equations
  -- `B.id₁ ⋆ᴾ e ≡ e` are what the gluing arguments actually consume.
  isStrictPrestack : Type _
  isStrictPrestack =
      (∀ {x : B.0Cell} (e : PN.p[ x ])
        → isIdHom {C = PN.P⟨ x ⟩} (PN.P.F⁰ .N-ob e))
    × (∀ {x y a : B.0Cell} (k : B.1Cell x y) (f : B.1Cell y a)
         (e : PN.p[ a ]) → isIdHom {C = PN.P⟨ x ⟩} (PN.P.F² f k .N-ob e))

module _ (B : Bicategory ℓ ℓ' ℓ'') (C : Category ℓp ℓp') where
  isStrictConstPrestack : isStrictPrestack (ConstPrestack B C)
  isStrictConstPrestack = (λ _ → refl) , (λ _ _ _ → refl)

module _ {B : Bicategory ℓ ℓ' ℓ''} (P Q : Prestack B ℓp ℓp') where
  isStrict×Pre : isStrictPrestack P → isStrictPrestack Q
    → isStrictPrestack (P ×Pre Q)
  isStrict×Pre (p⁰ , p²) (q⁰ , q²) =
      (λ e → pairIsIdHom (p⁰ (e .fst)) (q⁰ (e .snd)))
    , (λ k f e → pairIsIdHom (p² k f (e .fst)) (q² k f (e .snd)))

-- `Hom B a` has F⁰ = λ⁻ and F² = α⁻, so it is strict exactly when those
-- structural 2-cells of `B` are identities. The right unitor is not used.
module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private module B = Bicategory B

  hasIdλ : Type _
  hasIdλ = ∀ {x y} (f : B.1Cell x y) → isIdHom {C = B.Hom[ x , y ]} (B.λ⁻ f)

  hasIdα : Type _
  hasIdα = ∀ {x y z w} (f : B.1Cell x y) (g : B.1Cell y z)
    (h : B.1Cell z w) → isIdHom {C = B.Hom[ x , w ]} (B.α⁻ f g h)

  isStrictHom : hasIdλ → hasIdα → (a : B.0Cell)
    → isStrictPrestack (Hom B a)
  isStrictHom sλ sα a = (λ f → sλ f) , (λ k f g → sα k f g)

module _ {A : Bicategory ℓa ℓa' ℓa''} {B : Bicategory ℓb ℓb' ℓb''}
  (F : Pseudofunctor A B) where
  private
    module A = Bicategory A
    module B = Bicategory B
    module F = Pseudofunctor F

  isStrictPs : Type _
  isStrictPs =
      (∀ {x : A.ob} → isIdHom {C = B.Hom[ F.F-ob x , F.F-ob x ]} (F.F⁰ {x}))
    × (∀ {x y z : A.ob} (f : A.1Cell x y) (g : A.1Cell y z)
        → isIdHom {C = B.Hom[ F.F-ob x , F.F-ob z ]} (F.F² f g))

  module _ (P : Prestack B ℓp ℓp') where
    private
      module P = Pseudofunctor P
      module PN = PrestackNotation P

      -- reindexing along an identity 2-cell of B is an identity, fibrewise
      P2 : {x y : B.ob} {f g : B.1Cell y x} (α : B.2Cell f g)
        → isIdHom {C = B.Hom[ y , x ]} α
        → (e : PN.p[ x ]) → isIdHom {C = PN.P⟨ y ⟩} (P.F-2cell α .N-ob e)
      P2 {x} {y} α s e =
        F-isIdHom (evalAtF {C = PN.P⟨ y ⟩} {D = PN.P⟨ x ⟩} e)
                  (F-isIdHom P.F-Hom s)

    isStrictReindex : isStrictPs → isStrictPrestack P
      → isStrictPrestack (reindexPrestack F P)
    isStrictReindex sF (p⁰ , p²) =
        (λ {x} e → ⋆IsIdHom {C = PN.P⟨ F.F-ob x ⟩}
                              (p⁰ e) (P2 F.F⁰ (sF .fst) e))
      , (λ {x} k f e → ⋆IsIdHom {C = PN.P⟨ F.F-ob x ⟩}
                            (p² (F.F-1cell k) (F.F-1cell f) e)
                            (P2 (F.F² k f) (sF .snd k f) e))

module _ (B : Bicategory ℓb ℓb' ℓb'') where
  isStrictIdᴮ : isStrictPs (Idᴮ B)
  isStrictIdᴮ = refl , (λ _ _ → refl)

module _ {A : Bicategory ℓa ℓa' ℓa''} {B : Bicategory ℓb ℓb' ℓb''}
         {E : Bicategory ℓe ℓe' ℓe''}
         (G : Pseudofunctor B E) (F : Pseudofunctor A B) where
  private
    module E = Bicategory E
    module G = Pseudofunctor G
    module F = Pseudofunctor F

  isStrict∘Ps : isStrictPs G → isStrictPs F → isStrictPs (G ∘Ps F)
  isStrict∘Ps (g⁰ , g²) (f⁰ , f²) =
      (λ {x} → ⋆IsIdHom {C = E.Hom[ G.F-ob (F.F-ob x) , G.F-ob (F.F-ob x) ]}
                 g⁰ (F-isIdHom G.F-Hom f⁰))
    , (λ {x} {y} {z} f g →
        ⋆IsIdHom {C = E.Hom[ G.F-ob (F.F-ob x) , G.F-ob (F.F-ob z) ]}
          (g² _ _) (F-isIdHom G.F-Hom (f² f g)))

-- What strictness buys: the fibrewise reindexing equations hold on the
-- nose, and the structural isos are the identities over them.
module _ {B : Bicategory ℓ ℓ' ℓ''} {P : Prestack B ℓp ℓp'}
  (str : isStrictPrestack P) where
  private
    module B = Bicategory B
    module PN = PrestackNotation P

  strict⋆ᴾIdL : {x : B.0Cell} (e : PN.p[ x ]) → e ≡ B.id₁ PN.⋆ᴾ e
  strict⋆ᴾIdL e = cong fst (str .fst e)

  strict⋆ᴾAssoc : {x y a : B.0Cell} (k : B.1Cell x y) (f : B.1Cell y a)
    (e : PN.p[ a ]) → k PN.⋆ᴾ (f PN.⋆ᴾ e) ≡ (k B.⋆₁ f) PN.⋆ᴾ e
  strict⋆ᴾAssoc k f e = cong fst (str .snd k f e)

-- CAT's associators are componentwise identities, and whiskering
-- preserves componentwise identities: this is what makes the
-- componentwise notion closed under pasting.
module _ {X Y Z : Category ℓp ℓp'} where
  private
    module CATᴮ = Bicategory (CAT {ℓp} {ℓp'})

  ▷wIsIdHom : {F F' : Functor X Y} {θ : NatTrans F F'} (K : Functor Y Z)
    (e : Category.ob X) → isIdHom {C = Y} (θ .N-ob e)
    → isIdHom {C = Z} ((θ CATᴮ.▷w K) .N-ob e)
  ▷wIsIdHom K e s = ⋆IsIdHom {C = Z} (F-isIdHom K s) (idIsIdHom {C = Z})

  ◁wIsIdHom : (K : Functor X Y) {G G' : Functor Y Z} {θ : NatTrans G G'}
    (e : Category.ob X) → isIdHom {C = Z} (θ .N-ob (K .F-ob e))
    → isIdHom {C = Z} ((K CATᴮ.◁w θ) .N-ob e)
  ◁wIsIdHom K {G = G} e s =
    ⋆IsIdHom {C = Z} (F-isIdHom G (idIsIdHom {C = Y})) s

module _ {W X Y Z : Category ℓp ℓp'} where
  private
    module CATᴮ = Bicategory (CAT {ℓp} {ℓp'})

  α⁺IsIdHom : (F : Functor W X) (G : Functor X Y) (H : Functor Y Z)
    (e : Category.ob W) → isIdHom {C = Z} (CATᴮ.α⁺ F G H .N-ob e)
  α⁺IsIdHom F G H e = refl

  α⁻IsIdHom : (F : Functor W X) (G : Functor X Y) (H : Functor Y Z)
    (e : Category.ob W) → isIdHom {C = Z} (CATᴮ.α⁻ F G H .N-ob e)
  α⁻IsIdHom F G H e = refl

module _ {B : Bicategory ℓ ℓ' ℓ''} {P Q : Prestack B ℓp ℓp'} where
  private
    module B = Bicategory B
    module PN = PrestackNotation P
    module QN = PrestackNotation Q

  isStrictPrestackHom : PrestackHom P Q → Type _
  isStrictPrestackHom σ = {x y : B.0Cell} (f : B.1Cell y x)
    (e : PN.p[ x ])
    → isIdHom {C = QN.P⟨ y ⟩} (LaxNatTrans.N-hom σ f .N-ob e)

module _ {B : Bicategory ℓ ℓ' ℓ''} {P Q R : Prestack B ℓp ℓp'}
  (σ : PrestackHom P Q) (τ : PrestackHom Q R) where
  private
    module PN = PrestackNotation P
    module QN = PrestackNotation Q
    module RN = PrestackNotation R
    module σ = LaxNatTrans σ
    module τ = LaxNatTrans τ

  isStrictSeqPrestackHom : isStrictPrestackHom {P = P} {Q = Q} σ
    → isStrictPrestackHom {P = Q} {Q = R} τ
    → isStrictPrestackHom {P = P} {Q = R} (seqLaxNatTrans σ τ)
  isStrictSeqPrestackHom sσ sτ {x} {y} f e =
    ⋆IsIdHom {C = RN.P⟨ y ⟩}
      (α⁻IsIdHom (PN.reind f) (σ.N-1cell y) (τ.N-1cell y) e)
      (⋆IsIdHom {C = RN.P⟨ y ⟩}
        (▷wIsIdHom {θ = σ.N-hom f} (τ.N-1cell y) e (sσ f e))
        (⋆IsIdHom {C = RN.P⟨ y ⟩}
          (α⁺IsIdHom (σ.N-1cell x) (QN.reind f) (τ.N-1cell y) e)
          (⋆IsIdHom {C = RN.P⟨ y ⟩}
            (◁wIsIdHom (σ.N-1cell x) {θ = τ.N-hom f} e
              (sτ f (σ.N-1cell x .F-ob e)))
            (α⁻IsIdHom (σ.N-1cell x) (τ.N-1cell x) (RN.reind f) e))))
