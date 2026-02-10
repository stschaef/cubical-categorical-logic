{-# OPTIONS --lossy-unification #-}
module Gluing.Forded.CartesianClosedCategory.Normalization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥ using (⊥)
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base

open import Cubical.Categories.Constructions.Free.CartesianClosedCategory.Forded as FCCC
open import Cubical.Categories.Constructions.Free.CartesianClosedCategory.Quiver
import Cubical.Categories.Constructions.Free.CartesianCategory.Forded as FCC
import Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver as PQ

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Limits.CartesianV' as V'
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
import Cubical.Categories.Displayed.Instances.Terminal.Base as Unitᴰ
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base
  hiding (PRESHEAFᴰ)
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves.Base as PshBase
  using (PRESHEAFᴰ; PSHAssoc)
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves.Cartesian
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves.CartesianClosed
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianClosedV
  using (EqCCCⱽ→CCCⱽ)
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.StrictHom
open import Cubical.Categories.Presheaf.Nerve using (Nerve; Nerve-pres-bp)
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Data.Quiver.Base

private
  variable ℓQ ℓQ' : Level

open Category
open Functor
open Categoryᴰ
open Section
open PshHomStrict
open PshHom

module _ (Q₀ : Quiver ℓQ ℓQ') where
  private
    Q : ×⇒Quiver ℓQ ℓQ'
    Q = Quiver→×⇒Quiver Q₀
    module Q = ×⇒Quiver Q
    module Q₀ = QuiverOver (Q₀ .snd)

  FREECCC : CartesianClosedCategory _ _
  FREECCC = FCCC.FreeCartesianClosedCategory Q

  private
    module CCC = CartesianClosedCategory FREECCC
    C = CCC.C
    ℓ = ℓ-max ℓQ ℓQ'

    -- Local aliases to avoid mixfix parsing issues with module param Q
    pair' : ∀ {Γ Δ Δ'} → C [ Γ , Δ ] → C [ Γ , Δ' ] → C [ Γ , Δ × Δ' ]
    pair' = ⟨_,_⟩' Q

  -- §1: Category of renamings
  --
  -- Defined before Nf/Ne so the `emb` constructor can reference Ren.
  --
  -- Ren is the free cartesian category on Q.obExpr (the CCC type
  -- expressions), with no generators. Its morphisms are built solely
  -- from the cartesian structure: id, π₁, π₂, ⟨-,-⟩, !.
  --
  -- The embedding ⊆ : Ren → C maps renamings to their CCC counterparts.
  private
    ×Q-Ren : PQ.×Quiver ℓQ ℓQ'
    ×Q-Ren .PQ.×Quiver.ob = Q.obExpr
    ×Q-Ren .PQ.×Quiver.Q .QuiverOver.mor = Lift ⊥
    ×Q-Ren .PQ.×Quiver.Q .QuiverOver.dom (lift ())
    ×Q-Ren .PQ.×Quiver.Q .QuiverOver.cod (lift ())

  Ren : CartesianCategory _ _
  Ren = FCC.FreeCartesianCategory ×Q-Ren

  private
    |Ren| = CartesianCategory.C Ren

  ⊆ : Functor |Ren| C
  ⊆ = FCC.rec ×Q-Ren CCC.CC (FCC.mkElimInterpᴰ (λ A → A) (λ { (lift ()) }))

  -- §2: β-normal η-long forms as a property of morphisms
  --
  -- The key constructor is `emb`: any renaming (embedded via ⊆) is
  -- neutral. This replaces the traditional `var` and makes the
  -- renaming action trivial: emb σ renamed by ρ = emb (ρ ⋆ σ).
  mutual
    data Nf : {Γ A : Q.obExpr} → C [ Γ , A ] → Type ℓ where
      ne : ∀ {Γ o} {e : C [ Γ , ↑ o ]}
         → Ne e → Nf e
      lam : ∀ {Γ A B} (body : C [ Γ × A , B ])
          → (e : C [ Γ , A ⇒ B ])
          → lam' Q body Eq.≡ e
          → Nf body
          → Nf e
      pair : ∀ {Γ A B} (a : C [ Γ , A ]) (b : C [ Γ , B ])
           → (e : C [ Γ , A × B ])
           → pair' a b Eq.≡ e
           → Nf a → Nf b
           → Nf e
      unit : ∀ {Γ}
           → (e : C [ Γ , ⊤ ])
           → !ₑ' Q Eq.≡ e
           → Nf e

    data Ne : {Γ A : Q.obExpr} → C [ Γ , A ] → Type ℓ where
      -- Any renaming is neutral
      emb : ∀ {Δ' Δ : |Ren| .ob} (σ : |Ren| [ Δ' , Δ ])
          → (e : C [ ⊆ ⟅ Δ' ⟆ , ⊆ ⟅ Δ ⟆ ])
          → ⊆ ⟪ σ ⟫ Eq.≡ e
          → Ne e
      -- Quiver generator
      gen : ∀ (t : Q.mor) {Γ A}
          → (pΓ : Q.dom t Eq.≡ Γ) (pA : Q.cod t Eq.≡ A)
          → (e : C [ Γ , A ])
          → genₑ t pΓ pA Eq.≡ e
          → Ne e
      -- Application: e ≡ ⟨ n , m ⟩' ⋆ eval'
      app : ∀ {Γ A B} (n : C [ Γ , A ⇒ B ]) (m : C [ Γ , A ])
          → (e : C [ Γ , B ])
          → (pair' n m ⋆⟨ C ⟩ eval' Q) Eq.≡ e
          → Ne n → Nf m
          → Ne e
      fstNe : ∀ {Γ A B} (n : C [ Γ , A × B ])
            → (e : C [ Γ , A ])
            → (n ⋆⟨ C ⟩ π₁' Q) Eq.≡ e
            → Ne n
            → Ne e
      sndNe : ∀ {Γ A B} (n : C [ Γ , A × B ])
            → (e : C [ Γ , B ])
            → (n ⋆⟨ C ⟩ π₂' Q) Eq.≡ e
            → Ne n
            → Ne e
      appGen : ∀ (t : Q.mor) {Γ} (n : C [ Γ , Q.dom t ])
             → (e : C [ Γ , Q.cod t ])
             → (n ⋆⟨ C ⟩ genₑ t Eq.refl Eq.refl) Eq.≡ e
             → Ne n
             → Ne e

  -- §3: Renaming action on Nf/Ne
  --
  -- Defined by mutual induction. The emb case is composition of
  -- renamings; all other cases push the renaming inside.
  private
    ⋆Assoc-eq : ∀ {Γ Δ A B} (f : C [ Γ , Δ ]) (g : C [ Δ , A ]) (h : C [ A , B ])
              → (f ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ h Eq.≡ f ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ h)
    ⋆Assoc-eq f g h = Eq.pathToEq (C .⋆Assoc f g h)

    -- Ren object constructors
    module QR = PQ.×Quiver ×Q-Ren

    -- Extended renaming: σ⁺ = ⟨ π₁ ⋆ σ , π₂ ⟩ in Ren
    ext-ren : ∀ {Δ' Δ : |Ren| .ob} (A : Q.obExpr)
            → (σ : |Ren| [ Δ' , Δ ])
            → |Ren| [ QR._×_ Δ' (QR.↑ A) , QR._×_ Δ (QR.↑ A) ]
    ext-ren {Δ'} {Δ} A σ = bp₂._,p_ (bp₁.π₁ ⋆⟨ |Ren| ⟩ σ) bp₁.π₂
      where
        module bp₁ = BinProductNotation (CartesianCategory.bp Ren (Δ' , QR.↑ A))
        module bp₂ = BinProductNotation (CartesianCategory.bp Ren (Δ  , QR.↑ A))

    pair-natural : ∀ {Γ Δ A B} (f : C [ Γ , Δ ]) (a : C [ Δ , A ]) (b : C [ Δ , B ])
                 → f ⋆⟨ C ⟩ pair' a b ≡ pair' (f ⋆⟨ C ⟩ a) (f ⋆⟨ C ⟩ b)
    pair-natural f a b =
      ×η Eq.refl (f ⋆⟨ C ⟩ pair' a b)
      ∙ cong₂ (λ x y → pair' x y)
          (C .⋆Assoc f (pair' a b) (π₁' Q) ∙ cong (f ⋆⟨ C ⟩_) ×β₁)
          (C .⋆Assoc f (pair' a b) (π₂' Q) ∙ cong (f ⋆⟨ C ⟩_) ×β₂)

    -- Curry naturality: f ⋆ Λ(body) ≡ Λ((f × id) ⋆ body)
    -- where f × id = ⟨ π₁ ⋆ f , π₂ ⟩
    -- Proof: by λη, f ⋆ Λ body = Λ(⟨π₁⋆(f⋆Λ body),π₂⟩ ⋆ eval).
    -- Then ⟨π₁⋆(f⋆Λ body),π₂⟩ = ⟨π₁⋆f,π₂⟩ ⋆ ⟨π₁⋆Λ body,π₂⟩ (by ×η+×β)
    -- and ⟨π₁⋆Λ body,π₂⟩ ⋆ eval = body (by λβ).
    lam-natural : ∀ {Γ Δ A B} (f : C [ Γ , Δ ]) (body : C [ Δ × A , B ])
                → f ⋆⟨ C ⟩ lam' Q body ≡ lam' Q (pair' (π₁' Q ⋆⟨ C ⟩ f) (π₂' Q) ⋆⟨ C ⟩ body)
    lam-natural {A = A} f body =
      λη Eq.refl (f ⋆⟨ C ⟩ lam' Q body)
      ∙ cong (lam' Q)
          (cong (_⋆⟨ C ⟩ eval' Q) step₁
           ∙ C .⋆Assoc fxid (pair' (π₁' Q ⋆⟨ C ⟩ lam' Q body) (π₂' Q)) (eval' Q)
           ∙ cong (fxid ⋆⟨ C ⟩_) (λβ Eq.refl body))
      where
        fxid = pair' (π₁' Q ⋆⟨ C ⟩ f) (π₂' Q {Δ = A})

        -- ⟨ π₁⋆f , π₂ ⟩ ⋆ (π₁ ⋆ Λbody) = π₁ ⋆ (f ⋆ Λbody)
        comp₁ : fxid ⋆⟨ C ⟩ (π₁' Q ⋆⟨ C ⟩ lam' Q body) ≡ π₁' Q ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ lam' Q body)
        comp₁ = sym (C .⋆Assoc fxid (π₁' Q) (lam' Q body))
              ∙ cong (_⋆⟨ C ⟩ lam' Q body) ×β₁
              ∙ C .⋆Assoc (π₁' Q) f (lam' Q body)

        -- ⟨ π₁⋆(f⋆Λbody) , π₂ ⟩ = ⟨ π₁⋆f , π₂ ⟩ ⋆ ⟨ π₁⋆Λbody , π₂ ⟩
        step₁ : pair' (π₁' Q ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ lam' Q body)) (π₂' Q)
               ≡ fxid ⋆⟨ C ⟩ pair' (π₁' Q ⋆⟨ C ⟩ lam' Q body) (π₂' Q)
        step₁ = sym (pair-natural fxid (π₁' Q ⋆⟨ C ⟩ lam' Q body) (π₂' Q)
                      ∙ cong₂ (λ x y → pair' x y) comp₁ ×β₂)

  mutual
    ren-Nf : ∀ {Δ' Δ : |Ren| .ob} {A} {e : C [ ⊆ ⟅ Δ ⟆ , A ]}
           → (σ : |Ren| [ Δ' , Δ ])
           → Nf e → Nf (⊆ ⟪ σ ⟫ ⋆⟨ C ⟩ e)
    ren-Nf σ (ne n) = ne (ren-Ne σ n)
    ren-Nf σ (lam {A = A'} body ._ Eq.refl nf-body) =
      lam (⊆ ⟪ ext-ren A' σ ⟫ ⋆⟨ C ⟩ body) _
        (Eq.pathToEq (sym (lam-natural (⊆ ⟪ σ ⟫) body)))
        (ren-Nf (ext-ren A' σ) nf-body)
    ren-Nf σ (pair a b ._ Eq.refl nf-a nf-b) =
      pair (⊆ ⟪ σ ⟫ ⋆⟨ C ⟩ a) (⊆ ⟪ σ ⟫ ⋆⟨ C ⟩ b) _
        (Eq.pathToEq (sym (pair-natural (⊆ ⟪ σ ⟫) a b)))
        (ren-Nf σ nf-a) (ren-Nf σ nf-b)
    ren-Nf σ (unit ._ Eq.refl) =
      unit _ (Eq.pathToEq (sym (⊤η Eq.refl _)))

    ren-Ne : ∀ {Δ' Δ : |Ren| .ob} {A} {e : C [ ⊆ ⟅ Δ ⟆ , A ]}
           → (σ : |Ren| [ Δ' , Δ ])
           → Ne e → Ne (⊆ ⟪ σ ⟫ ⋆⟨ C ⟩ e)
    ren-Ne σ (emb σ' ._ Eq.refl) =
      emb (σ ⋆⟨ |Ren| ⟩ σ') _ Eq.refl
    ren-Ne σ (gen t Eq.refl Eq.refl ._ Eq.refl) =
      appGen t (⊆ ⟪ σ ⟫) _ Eq.refl (emb σ _ Eq.refl)
    ren-Ne σ (app n m ._ Eq.refl ne-n nf-m) =
      app (⊆ ⟪ σ ⟫ ⋆⟨ C ⟩ n) (⊆ ⟪ σ ⟫ ⋆⟨ C ⟩ m) _
        (Eq.pathToEq (cong (_⋆⟨ C ⟩ eval' Q) (sym (pair-natural (⊆ ⟪ σ ⟫) n m))
                      ∙ C .⋆Assoc (⊆ ⟪ σ ⟫) (pair' n m) (eval' Q)))
        (ren-Ne σ ne-n) (ren-Nf σ nf-m)
    ren-Ne σ (fstNe n ._ Eq.refl ne-n) =
      fstNe (⊆ ⟪ σ ⟫ ⋆⟨ C ⟩ n) _ (⋆Assoc-eq (⊆ ⟪ σ ⟫) n (π₁' Q)) (ren-Ne σ ne-n)
    ren-Ne σ (sndNe n ._ Eq.refl ne-n) =
      sndNe (⊆ ⟪ σ ⟫ ⋆⟨ C ⟩ n) _ (⋆Assoc-eq (⊆ ⟪ σ ⟫) n (π₂' Q)) (ren-Ne σ ne-n)
    ren-Ne σ (appGen t n ._ Eq.refl ne-n) =
      appGen t (⊆ ⟪ σ ⟫ ⋆⟨ C ⟩ n) _ (⋆Assoc-eq (⊆ ⟪ σ ⟫) n (genₑ t Eq.refl Eq.refl)) (ren-Ne σ ne-n)

    -- η-expand a neutral term to a normal form at any type
    ne-to-nf : ∀ (A : Q.obExpr) {Δ : |Ren| .ob} {e : C [ ⊆ ⟅ Δ ⟆ , A ]}
             → Ne e → Nf e
    ne-to-nf (↑ o) n = ne n
    ne-to-nf ⊤ n = unit _ (Eq.pathToEq (sym (⊤η Eq.refl _)))
    ne-to-nf (A × B) n =
      pair _ _ _ (Eq.pathToEq (sym (×η Eq.refl _)))
        (ne-to-nf A (fstNe _ _ Eq.refl n))
        (ne-to-nf B (sndNe _ _ Eq.refl n))
    ne-to-nf (A ⇒ B) {Δ} n =
      lam body _ (Eq.pathToEq (sym (λη Eq.refl _)))
        (ne-to-nf B (app _ _ _ Eq.refl (ren-Ne wk n) (ne-to-nf A (emb v _ Eq.refl))))
      where
        module bp = BinProductNotation (CartesianCategory.bp Ren (Δ , QR.↑ A))
        wk = bp.π₁
        v  = bp.π₂
        body = pair' (⊆ ⟪ wk ⟫ ⋆⟨ C ⟩ _) (⊆ ⟪ v ⟫) ⋆⟨ C ⟩ eval' Q

  -- §4: Displayed presheaves of normal/neutral forms
  --
  -- NfPsh A is displayed over nerve ⟅ A ⟆ with fiber Nf e.
  -- NePsh A is displayed over nerve ⟅ A ⟆ with fiber Ne e.

  nerve : Functor C (PRESHEAF |Ren| ℓ)
  nerve = Nerve ⊆

  private
    Renᴰ : Categoryᴰ |Ren| ℓ-zero ℓ-zero
    Renᴰ = Unitᴰ.Unitᴰ |Ren|

    PSHᴰ = PRESHEAFᴰ Renᴰ ℓ ℓ

    module PSHᴰ = Categoryᴰ PSHᴰ

  NfPsh : ∀ (A : Q.obExpr) → PSHᴰ.ob[ nerve ⟅ A ⟆ ]
  NfPsh A .F-ob (_ , _ , e) .fst = Nf e
  NfPsh A .F-ob (_ , _ , e) .snd = {!!}
  NfPsh A .F-hom (σ , _ , Eq.refl) nf = ren-Nf σ nf
  NfPsh A .F-id = {!!}
  NfPsh A .F-seq _ _ = {!!}

  NePsh : ∀ (A : Q.obExpr) → PSHᴰ.ob[ nerve ⟅ A ⟆ ]
  NePsh A .F-ob (_ , _ , e) .fst = Ne e
  NePsh A .F-ob (_ , _ , e) .snd = {!!}
  NePsh A .F-hom (σ , _ , Eq.refl) ne = ren-Ne σ ne
  NePsh A .F-id = {!!}
  NePsh A .F-seq _ _ = {!!}

  private
    PSH-CC : CartesianCategory _ _
    PSH-CC = Cartesian-PRESHEAF |Ren| ℓ

    PSHᴰCartesianⱽEq : isCartesianⱽ PSHAssoc PSHᴰ
    PSHᴰCartesianⱽEq = isCartesianⱽPSHᴰ

    PSHᴰCartesianⱽ : V'.CartesianCategoryⱽ (PRESHEAF |Ren| ℓ) _ _
    PSHᴰCartesianⱽ = EqCCⱽ→CCⱽ PSHAssoc PSHᴰ PSHᴰCartesianⱽEq

    PSHᴰCᴰ : Categoryᴰ (PRESHEAF |Ren| ℓ) _ _
    PSHᴰCᴰ = V'.CartesianCategoryⱽ.Cᴰ PSHᴰCartesianⱽ

    PSHᴰCartesianClosedⱽ : CartesianClosedCategoryⱽ PSH-CC _ _
    PSHᴰCartesianClosedⱽ = CCCⱽPSHᴰ {Cᴰ = Renᴰ}

    nerve-pres-bp : preservesProvidedBinProducts nerve
      (CartesianCategory.bp CCC.CC)
    nerve-pres-bp = Nerve-pres-bp ⊆ (CartesianCategory.bp CCC.CC)

  -- §5: The normalization section
  S : Section nerve PSHᴰCᴰ
  S = FCCC.elimLocal Q
        (nerve , nerve-pres-bp) PSHᴰCartesianClosedⱽ
        (mkElimInterpᴰ OB HOM)
    where
    OB : (o : Q.ob) → PSHᴰ.ob[ nerve ⟅ ↑ o ⟆ ]
    OB = NfPsh ∘ ↑_

    HOM : ∀ g → _
    HOM g .N-ob (_ , _ , f) (ne n) =
      ne (appGen g f _ Eq.refl n)
    HOM g .N-hom _ _ _ _ _ _ = {!!}

  -- §6: The normalization theorem
  --
  -- To extract Nf e from the section S, we need:
  -- 1. A starting element in S .F-obᴰ Γ at the identity
  -- 2. Apply S .F-homᴰ e to transport to the codomain fiber
  -- 3. Extract Nf from S .F-obᴰ A (trivial at base type)
  --
  -- Steps 1 and 3 require reflect/reify on the elimOb fibers.
  -- For now, we leave this as a hole.
  normalize : ∀ {Γ A} → (e : C [ Γ , A ]) → Nf e
  normalize {Γ} {A} e = {!!}
