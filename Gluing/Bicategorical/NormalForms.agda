{-# OPTIONS --lossy-unification #-}
{-
  Normal and neutral forms for the free cartesian closed category on
  a quiver, as a presheaf-style family over a category `Ren` of
  contexts and renamings.

  Contexts are lists of types and a renaming is a function on
  variables, so every law of `Ren` is `refl`.
-}
module Gluing.Bicategorical.NormalForms where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sum as Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.Sigma renaming (_×_ to _×ₛ_)
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Quiver.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
import Cubical.Categories.Instances.Free.CartesianClosedCategory.Forded
  as FCCC
open import Gluing.Bicategorical.CanonicityCore using (module Exp)

open import
  Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
open CCCExpr renaming (_×_ to _×ᵗ_ ; ⊤ to ⊤ᵗ ; _⇒_ to _⇒ᵗ_)

private
  variable ℓQ ℓQ' : Level

open Category

module NF (Q : Quiver ℓQ ℓQ') (isSetOb : isSet (Q .fst)) where
  private module Q = QuiverOver (Q .snd)

  Ty : Type ℓQ
  Ty = CCCExpr (Q .fst)

  -- `Ty` is a set: the standard encode/decode over the constructors
  private
    Cover : Ty → Ty → Type ℓQ
    Cover (↑ o) (↑ o') = o ≡ o'
    Cover (A ×ᵗ B) (A' ×ᵗ B') = Cover A A' ×ₛ Cover B B'
    Cover ⊤ᵗ ⊤ᵗ = Unit*
    Cover (A ⇒ᵗ B) (A' ⇒ᵗ B') = Cover A A' ×ₛ Cover B B'
    Cover _ _ = ⊥*

    isPropCover : (A B : Ty) → isProp (Cover A B)
    isPropCover (↑ o) (↑ o') = isSetOb o o'
    isPropCover (↑ o) (A' ×ᵗ B') = isProp⊥*
    isPropCover (↑ o) ⊤ᵗ = isProp⊥*
    isPropCover (↑ o) (A' ⇒ᵗ B') = isProp⊥*
    isPropCover (A ×ᵗ B) (↑ o') = isProp⊥*
    isPropCover (A ×ᵗ B) (A' ×ᵗ B') =
      isProp× (isPropCover A A') (isPropCover B B')
    isPropCover (A ×ᵗ B) ⊤ᵗ = isProp⊥*
    isPropCover (A ×ᵗ B) (A' ⇒ᵗ B') = isProp⊥*
    isPropCover ⊤ᵗ (↑ o') = isProp⊥*
    isPropCover ⊤ᵗ (A' ×ᵗ B') = isProp⊥*
    isPropCover ⊤ᵗ ⊤ᵗ = isPropUnit*
    isPropCover ⊤ᵗ (A' ⇒ᵗ B') = isProp⊥*
    isPropCover (A ⇒ᵗ B) (↑ o') = isProp⊥*
    isPropCover (A ⇒ᵗ B) (A' ×ᵗ B') = isProp⊥*
    isPropCover (A ⇒ᵗ B) ⊤ᵗ = isProp⊥*
    isPropCover (A ⇒ᵗ B) (A' ⇒ᵗ B') =
      isProp× (isPropCover A A') (isPropCover B B')

    reflCover : (A : Ty) → Cover A A
    reflCover (↑ o) = refl
    reflCover (A ×ᵗ B) = reflCover A , reflCover B
    reflCover ⊤ᵗ = tt*
    reflCover (A ⇒ᵗ B) = reflCover A , reflCover B

    decode : (A B : Ty) → Cover A B → A ≡ B
    decode (↑ o) (↑ o') c = cong ↑_ c
    decode (A ×ᵗ B) (A' ×ᵗ B') c =
      cong₂ _×ᵗ_ (decode A A' (c .fst)) (decode B B' (c .snd))
    decode ⊤ᵗ ⊤ᵗ c = refl
    decode (A ⇒ᵗ B) (A' ⇒ᵗ B') c =
      cong₂ _⇒ᵗ_ (decode A A' (c .fst)) (decode B B' (c .snd))

    decodeRefl : (A : Ty) → decode A A (reflCover A) ≡ refl
    decodeRefl (↑ o) = refl
    decodeRefl (A ×ᵗ B) i j =
      decodeRefl A i j ×ᵗ decodeRefl B i j
    decodeRefl ⊤ᵗ = refl
    decodeRefl (A ⇒ᵗ B) i j =
      decodeRefl A i j ⇒ᵗ decodeRefl B i j

    encode : (A B : Ty) → A ≡ B → Cover A B
    encode A B p = subst (Cover A) p (reflCover A)

    decodeEncode : (A B : Ty) (p : A ≡ B) → decode A B (encode A B p) ≡ p
    decodeEncode A B p =
      J (λ B' p' → decode A B' (encode A B' p') ≡ p')
        (cong (decode A A) (substRefl {B = Cover A} (reflCover A))
         ∙ decodeRefl A) p

  isSetTy : isSet Ty
  isSetTy A B = isOfHLevelRetract 1 (encode A B) (decode A B)
    (decodeEncode A B) (isPropCover A B)

  Ctx : Type ℓQ
  Ctx = List Ty

  isSetCtx : isSet Ctx
  isSetCtx = isOfHLevelList 0 isSetTy

  -- variables, by recursion on the context
  Var : Ctx → Ty → Type ℓQ
  Var [] A = ⊥*
  Var (B ∷ Γ) A = (B ≡ A) ⊎ Var Γ A

  isSetVar : (Γ : Ctx) (A : Ty) → isSet (Var Γ A)
  isSetVar [] A = isProp→isSet isProp⊥*
  isSetVar (B ∷ Γ) A =
    isSet⊎ (isProp→isSet (isSetTy B A)) (isSetVar Γ A)

  -- contexts and renamings; all the laws hold definitionally
  Ren : Category ℓQ ℓQ
  Ren .ob = Ctx
  Ren .Hom[_,_] Γ Δ = ∀ A → Var Δ A → Var Γ A
  Ren .id _ v = v
  Ren ._⋆_ ρ σ A v = ρ A (σ A v)
  Ren .⋆IdL _ = refl
  Ren .⋆IdR _ = refl
  Ren .⋆Assoc _ _ _ = refl
  Ren .isSetHom = isSetΠ2 (λ A _ → isSetVar _ A)

  idRen : ∀ {Γ} → Ren [ Γ , Γ ]
  idRen _ v = v

  wkRen : ∀ {Γ A} → Ren [ A ∷ Γ , Γ ]
  wkRen _ = inr

  liftRen : ∀ {Δ Γ A} → Ren [ Δ , Γ ] → Ren [ A ∷ Δ , A ∷ Γ ]
  liftRen ρ A (inl p) = inl p
  liftRen ρ A (inr v) = inr (ρ _ v)

  -- neutral and normal forms, mutually
  data Ne (Γ : Ctx) : Ty → Type (ℓ-max ℓQ ℓQ')
  data Nf (Γ : Ctx) : Ty → Type (ℓ-max ℓQ ℓQ')

  data Ne Γ where
    var : ∀ {A} → Var Γ A → Ne Γ A
    appₙ : ∀ {A B} → Ne Γ (A ⇒ᵗ B) → Nf Γ A → Ne Γ B
    π₁ₙ : ∀ {A B} → Ne Γ (A ×ᵗ B) → Ne Γ A
    π₂ₙ : ∀ {A B} → Ne Γ (A ×ᵗ B) → Ne Γ B
    genₙ : (g : Q.mor) → Nf Γ (↑ (Q.dom g)) → Ne Γ (↑ (Q.cod g))

  data Nf Γ where
    ne : ∀ {o} → Ne Γ (↑ o) → Nf Γ (↑ o)
    ttₙ : Nf Γ ⊤ᵗ
    pairₙ : ∀ {A B} → Nf Γ A → Nf Γ B → Nf Γ (A ×ᵗ B)
    lamₙ : ∀ {A B} → Nf (A ∷ Γ) B → Nf Γ (A ⇒ᵗ B)

  renNe : ∀ {Δ Γ A} → Ren [ Δ , Γ ] → Ne Γ A → Ne Δ A
  renNf : ∀ {Δ Γ A} → Ren [ Δ , Γ ] → Nf Γ A → Nf Δ A
  renNe ρ (var v) = var (ρ _ v)
  renNe ρ (appₙ n m) = appₙ (renNe ρ n) (renNf ρ m)
  renNe ρ (π₁ₙ n) = π₁ₙ (renNe ρ n)
  renNe ρ (π₂ₙ n) = π₂ₙ (renNe ρ n)
  renNe ρ (genₙ g m) = genₙ g (renNf ρ m)
  renNf ρ (ne n) = ne (renNe ρ n)
  renNf ρ ttₙ = ttₙ
  renNf ρ (pairₙ m m') = pairₙ (renNf ρ m) (renNf ρ m')
  renNf ρ (lamₙ m) = lamₙ (renNf (liftRen ρ) m)

  liftRenId : ∀ {Γ A} → liftRen {Γ} {Γ} {A} idRen ≡ idRen
  liftRenId {Γ} {A} = funExt₂ lem
    where
    lem : ∀ B (v : Var (A ∷ Γ) B) → liftRen {A = A} idRen B v ≡ v
    lem B (inl p) = refl
    lem B (inr v) = refl

  liftRenSeq : ∀ {Θ Δ Γ A} (ρ : Ren [ Θ , Δ ]) (σ : Ren [ Δ , Γ ])
    → liftRen {A = A} (ρ ⋆⟨ Ren ⟩ σ)
      ≡ liftRen {A = A} ρ ⋆⟨ Ren ⟩ liftRen {A = A} σ
  liftRenSeq {A = A} ρ σ = funExt₂ lem
    where
    lem : ∀ B v → liftRen {A = A} (ρ ⋆⟨ Ren ⟩ σ) B v
                  ≡ (liftRen {A = A} ρ ⋆⟨ Ren ⟩ liftRen {A = A} σ) B v
    lem B (inl p) = refl
    lem B (inr v) = refl

  renNeId : ∀ {Γ A} (n : Ne Γ A) → renNe idRen n ≡ n
  renNfId : ∀ {Γ A} (m : Nf Γ A) → renNf idRen m ≡ m
  renNeId (var v) = refl
  renNeId (appₙ n m) = cong₂ appₙ (renNeId n) (renNfId m)
  renNeId (π₁ₙ n) = cong π₁ₙ (renNeId n)
  renNeId (π₂ₙ n) = cong π₂ₙ (renNeId n)
  renNeId (genₙ g m) = cong (genₙ g) (renNfId m)
  renNfId (ne n) = cong ne (renNeId n)
  renNfId ttₙ = refl
  renNfId (pairₙ m m') = cong₂ pairₙ (renNfId m) (renNfId m')
  renNfId (lamₙ m) =
    cong lamₙ (cong (λ r → renNf r m) liftRenId ∙ renNfId m)

  renNeSeq : ∀ {Θ Δ Γ A} (ρ : Ren [ Θ , Δ ]) (σ : Ren [ Δ , Γ ])
    (n : Ne Γ A) → renNe (ρ ⋆⟨ Ren ⟩ σ) n ≡ renNe ρ (renNe σ n)
  renNfSeq : ∀ {Θ Δ Γ A} (ρ : Ren [ Θ , Δ ]) (σ : Ren [ Δ , Γ ])
    (m : Nf Γ A) → renNf (ρ ⋆⟨ Ren ⟩ σ) m ≡ renNf ρ (renNf σ m)
  renNeSeq ρ σ (var v) = refl
  renNeSeq ρ σ (appₙ n m) =
    cong₂ appₙ (renNeSeq ρ σ n) (renNfSeq ρ σ m)
  renNeSeq ρ σ (π₁ₙ n) = cong π₁ₙ (renNeSeq ρ σ n)
  renNeSeq ρ σ (π₂ₙ n) = cong π₂ₙ (renNeSeq ρ σ n)
  renNeSeq ρ σ (genₙ g m) = cong (genₙ g) (renNfSeq ρ σ m)
  renNfSeq ρ σ (ne n) = cong ne (renNeSeq ρ σ n)
  renNfSeq ρ σ ttₙ = refl
  renNfSeq ρ σ (pairₙ m m') =
    cong₂ pairₙ (renNfSeq ρ σ m) (renNfSeq ρ σ m')
  renNfSeq ρ σ (lamₙ m) = cong lamₙ
    (cong (λ r → renNf r m) (liftRenSeq ρ σ)
     ∙ renNfSeq (liftRen ρ) (liftRen σ) m)

  -- the free cartesian closed category on `Q`, and the reading of
  -- contexts, variables and normal forms back into it
  private
    ×⇒Q = Quiver→×⇒Quiver Q

  FREECCC : CartesianClosedCategory ℓQ (ℓ-max ℓQ ℓQ')
  FREECCC = FCCC.FreeCartesianClosedCategory ×⇒Q

  private
    module 𝒞 = CartesianClosedCategory FREECCC
    module E = Exp FREECCC

  ⟦_⟧c : Ctx → Ty
  ⟦ [] ⟧c = ⊤ᵗ
  ⟦ A ∷ Γ ⟧c = ⟦ Γ ⟧c ×ᵗ A

  ⌜_⌝v : ∀ {Γ A} → Var Γ A → 𝒞.Hom[ ⟦ Γ ⟧c , A ]
  ⌜_⌝v {Γ = B ∷ Γ} (inl p) =
    subst (λ X → 𝒞.Hom[ ⟦ B ∷ Γ ⟧c , X ]) p (𝒞.π₂ {a = ⟦ Γ ⟧c} {b = B})
  ⌜_⌝v {Γ = B ∷ Γ} (inr v) = 𝒞.π₁ {a = ⟦ Γ ⟧c} {b = B} 𝒞.⋆ ⌜ v ⌝v

  ⌜_⌝ne : ∀ {Γ A} → Ne Γ A → 𝒞.Hom[ ⟦ Γ ⟧c , A ]
  ⌜_⌝nf : ∀ {Γ A} → Nf Γ A → 𝒞.Hom[ ⟦ Γ ⟧c , A ]
  ⌜ var v ⌝ne = ⌜ v ⌝v
  ⌜ appₙ {A} {B} n m ⌝ne =
    𝒞._,p_ {a = A ⇒ᵗ B} {b = A} ⌜ n ⌝ne ⌜ m ⌝nf 𝒞.⋆ 𝒞.app {c = A} {d = B}
  ⌜ π₁ₙ {A} {B} n ⌝ne = ⌜ n ⌝ne 𝒞.⋆ 𝒞.π₁ {a = A} {b = B}
  ⌜ π₂ₙ {A} {B} n ⌝ne = ⌜ n ⌝ne 𝒞.⋆ 𝒞.π₂ {a = A} {b = B}
  ⌜ genₙ g m ⌝ne = ⌜ m ⌝nf 𝒞.⋆ FCCC.↑ₑ ×⇒Q g
  ⌜ ne n ⌝nf = ⌜ n ⌝ne
  ⌜ ttₙ ⌝nf = 𝒞.!t
  ⌜ pairₙ {A} {B} m m' ⌝nf = 𝒞._,p_ {a = A} {b = B} ⌜ m ⌝nf ⌜ m' ⌝nf
  ⌜ lamₙ {A} {B} m ⌝nf = 𝒞.lda {c = A} {d = B} ⌜ m ⌝nf

  ⌜_⌝r : ∀ {Δ Γ} → Ren [ Δ , Γ ] → 𝒞.Hom[ ⟦ Δ ⟧c , ⟦ Γ ⟧c ]
  ⌜_⌝r {Γ = []} ρ = 𝒞.!t
  ⌜_⌝r {Γ = A ∷ Γ} ρ =
    𝒞._,p_ {a = ⟦ Γ ⟧c} {b = A}
      ⌜ (λ B v → ρ B (inr v)) ⌝r ⌜ ρ A (inl refl) ⌝v

  private
    ,p-comp : ∀ {Θ Γ} {A B : Ty} (m : 𝒞.Hom[ Θ , Γ ])
      (a : 𝒞.Hom[ Γ , A ]) (b : 𝒞.Hom[ Γ , B ])
      → m 𝒞.⋆ 𝒞._,p_ {a = A} {b = B} a b
        ≡ 𝒞._,p_ {a = A} {b = B} (m 𝒞.⋆ a) (m 𝒞.⋆ b)
    ,p-comp m a b = 𝒞.,p-extensionality
      (𝒞.⋆Assoc _ _ _ ∙ cong (m 𝒞.⋆_) 𝒞.×β₁ ∙ sym 𝒞.×β₁)
      (𝒞.⋆Assoc _ _ _ ∙ cong (m 𝒞.⋆_) 𝒞.×β₂ ∙ sym 𝒞.×β₂)

    ldaPull : ∀ {Θ Γ A B} (m : 𝒞.Hom[ Θ , Γ ])
      (b : 𝒞.Hom[ Γ ×ᵗ A , B ])
      → 𝒞.lda {c = A} {d = B} (E.pl {A = A} m 𝒞.⋆ b)
        ≡ m 𝒞.⋆ 𝒞.lda {c = A} {d = B} b
    ldaPull m b = E.ldaExt
      ( E.ldaβ _
      ∙ cong (E.pl m 𝒞.⋆_) (sym (E.ldaβ b))
      ∙ sym (E.appOfSeq m (𝒞.lda b)))

  wkR : ∀ {Δ Γ A} → Ren [ Δ , Γ ] → Ren [ A ∷ Δ , Γ ]
  wkR ρ B v = inr (ρ B v)

  ⌜⌝r-wk : ∀ {Δ Γ A} (ρ : Ren [ Δ , Γ ])
    → ⌜ wkR {A = A} ρ ⌝r ≡ 𝒞.π₁ {a = ⟦ Δ ⟧c} {b = A} 𝒞.⋆ ⌜ ρ ⌝r
  ⌜⌝r-wk {Γ = []} ρ = 𝒞.𝟙extensionality
  ⌜⌝r-wk {Γ = B ∷ Γ} ρ =
      𝒞.⟨ ⌜⌝r-wk (λ C v → ρ C (inr v)) ⟩,p⟨ refl ⟩
    ∙ sym (,p-comp 𝒞.π₁ _ _)

  ⌜⌝v-inl : ∀ {Γ A} → ⌜ inl {B = Var Γ A} refl ⌝v ≡ 𝒞.π₂ {a = ⟦ Γ ⟧c} {b = A}
  ⌜⌝v-inl {Γ} {A} = substRefl {B = λ X → 𝒞.Hom[ ⟦ A ∷ Γ ⟧c , X ]} 𝒞.π₂

  varNat : ∀ {Δ Γ A} (ρ : Ren [ Δ , Γ ]) (v : Var Γ A)
    → ⌜ ρ A v ⌝v ≡ ⌜ ρ ⌝r 𝒞.⋆ ⌜ v ⌝v
  varNat {Γ = B ∷ Γ} ρ (inl p) = lem p
    where
    lem : ∀ {A} (p : B ≡ A)
      → ⌜ ρ A (inl p) ⌝v ≡ ⌜ ρ ⌝r 𝒞.⋆ ⌜ inl {B = Var Γ A} p ⌝v
    lem = J (λ A p → ⌜ ρ A (inl p) ⌝v
                     ≡ ⌜ ρ ⌝r 𝒞.⋆ ⌜ inl {B = Var Γ A} p ⌝v)
      (sym 𝒞.×β₂ ∙ cong (⌜ ρ ⌝r 𝒞.⋆_) (sym ⌜⌝v-inl))
  varNat {Γ = B ∷ Γ} ρ (inr v) =
      varNat (λ C w → ρ C (inr w)) v
    ∙ cong (𝒞._⋆ ⌜ v ⌝v) (sym 𝒞.×β₁)
    ∙ 𝒞.⋆Assoc _ _ _

  ⌜⌝r-id : ∀ {Γ} → ⌜ idRen {Γ} ⌝r ≡ 𝒞.id
  ⌜⌝r-id {[]} = 𝒞.𝟙extensionality
  ⌜⌝r-id {A ∷ Γ} = 𝒞.,p≡ {a = ⟦ Γ ⟧c} {b = A} {g = 𝒞.id}
    ( ⌜⌝r-wk {A = A} idRen
    ∙ cong (𝒞.π₁ {a = ⟦ Γ ⟧c} {b = A} 𝒞.⋆_) (⌜⌝r-id {Γ})
    ∙ 𝒞.⋆IdR _ ∙ sym (𝒞.⋆IdL _))
    (⌜⌝v-inl ∙ sym (𝒞.⋆IdL _))

  ⌜⌝r-seq : ∀ {Θ Δ Γ} (ρ : Ren [ Θ , Δ ]) (σ : Ren [ Δ , Γ ])
    → ⌜ ρ ⋆⟨ Ren ⟩ σ ⌝r ≡ ⌜ ρ ⌝r 𝒞.⋆ ⌜ σ ⌝r
  ⌜⌝r-seq {Γ = []} ρ σ = 𝒞.𝟙extensionality
  ⌜⌝r-seq {Γ = A ∷ Γ} ρ σ =
      𝒞.⟨ ⌜⌝r-seq ρ (λ C v → σ C (inr v)) ⟩,p⟨ varNat ρ (σ A (inl refl)) ⟩
    ∙ sym (,p-comp ⌜ ρ ⌝r _ _)

  ⌜⌝r-lift : ∀ {Δ Γ A} (ρ : Ren [ Δ , Γ ])
    → ⌜ liftRen {A = A} ρ ⌝r ≡ E.pl {A = A} ⌜ ρ ⌝r
  ⌜⌝r-lift ρ = 𝒞.⟨ ⌜⌝r-wk ρ ⟩,p⟨ ⌜⌝v-inl ⟩

  neNat : ∀ {Δ Γ A} (ρ : Ren [ Δ , Γ ]) (n : Ne Γ A)
    → ⌜ renNe ρ n ⌝ne ≡ ⌜ ρ ⌝r 𝒞.⋆ ⌜ n ⌝ne
  nfNat : ∀ {Δ Γ A} (ρ : Ren [ Δ , Γ ]) (m : Nf Γ A)
    → ⌜ renNf ρ m ⌝nf ≡ ⌜ ρ ⌝r 𝒞.⋆ ⌜ m ⌝nf
  neNat ρ (var v) = varNat ρ v
  neNat ρ (appₙ n m) =
      cong (𝒞._⋆ 𝒞.app) (𝒞.⟨ neNat ρ n ⟩,p⟨ nfNat ρ m ⟩)
    ∙ cong (𝒞._⋆ 𝒞.app) (sym (,p-comp ⌜ ρ ⌝r _ _))
    ∙ 𝒞.⋆Assoc _ _ _
  neNat ρ (π₁ₙ n) = cong (𝒞._⋆ 𝒞.π₁) (neNat ρ n) ∙ 𝒞.⋆Assoc _ _ _
  neNat ρ (π₂ₙ n) = cong (𝒞._⋆ 𝒞.π₂) (neNat ρ n) ∙ 𝒞.⋆Assoc _ _ _
  neNat ρ (genₙ g m) =
    cong (𝒞._⋆ FCCC.↑ₑ ×⇒Q g) (nfNat ρ m) ∙ 𝒞.⋆Assoc _ _ _
  nfNat ρ (ne n) = neNat ρ n
  nfNat ρ ttₙ = 𝒞.𝟙extensionality
  nfNat ρ (pairₙ m m') =
    𝒞.⟨ nfNat ρ m ⟩,p⟨ nfNat ρ m' ⟩ ∙ sym (,p-comp ⌜ ρ ⌝r _ _)
  nfNat ρ (lamₙ m) =
      cong 𝒞.lda
        (nfNat (liftRen ρ) m ∙ cong (𝒞._⋆ ⌜ m ⌝nf) (⌜⌝r-lift ρ))
    ∙ ldaPull ⌜ ρ ⌝r ⌜ m ⌝nf

  -- `Ne` and `Nf` are sets.  `Nf`'s constructors are already
  -- separated by the type index, so only the mutual family needs the
  -- indexed W-type encoding.
  module _ (isSetMor : isSet Q.mor) where
    private
      X : Type ℓQ
      X = Bool ×ₛ Ctx ×ₛ Ty

      Shape : X → Type (ℓ-max ℓQ ℓQ')
      Shape (true , Γ , A) =
        Var Γ A
        ⊎ (Ty
        ⊎ (Ty
        ⊎ (Ty
        ⊎ (Σ[ g ∈ Q.mor ] (↑ (Q.cod g) ≡ A)))))
      Shape (false , Γ , A) =
        (Σ[ o ∈ Q .fst ] (↑ o ≡ A))
        ⊎ (((⊤ᵗ ≡ A) ×ₛ Unit* {ℓ = ℓQ'})
        ⊎ ((Σ[ A₁ ∈ Ty ] Σ[ A₂ ∈ Ty ] (A₁ ×ᵗ A₂ ≡ A))
        ⊎ (Σ[ A₁ ∈ Ty ] Σ[ A₂ ∈ Ty ] (A₁ ⇒ᵗ A₂ ≡ A))))

      Ar : (x : X) → Shape x → Type
      Ar (true , Γ , A) (inl _) = ⊥
      Ar (true , Γ , A) (inr (inl _)) = Bool
      Ar (true , Γ , A) (inr (inr (inl _))) = Unit
      Ar (true , Γ , A) (inr (inr (inr (inl _)))) = Unit
      Ar (true , Γ , A) (inr (inr (inr (inr _)))) = Unit
      Ar (false , Γ , A) (inl _) = Unit
      Ar (false , Γ , A) (inr (inl _)) = ⊥
      Ar (false , Γ , A) (inr (inr (inl _))) = Bool
      Ar (false , Γ , A) (inr (inr (inr _))) = Unit

      ix : (x : X) (s : Shape x) → Ar x s → X
      ix (true , Γ , A) (inr (inl A₀)) true = true , Γ , A₀ ⇒ᵗ A
      ix (true , Γ , A) (inr (inl A₀)) false = false , Γ , A₀
      ix (true , Γ , A) (inr (inr (inl B))) _ = true , Γ , A ×ᵗ B
      ix (true , Γ , A) (inr (inr (inr (inl B)))) _ = true , Γ , B ×ᵗ A
      ix (true , Γ , A) (inr (inr (inr (inr (g , _))))) _ =
        false , Γ , ↑ (Q.dom g)
      ix (false , Γ , A) (inl (o , _)) _ = true , Γ , ↑ o
      ix (false , Γ , A) (inr (inr (inl (A₁ , A₂ , _)))) true = false , Γ , A₁
      ix (false , Γ , A) (inr (inr (inl (A₁ , A₂ , _)))) false = false , Γ , A₂
      ix (false , Γ , A) (inr (inr (inr (A₁ , A₂ , _)))) _ = false , A₁ ∷ Γ , A₂

      W : X → Type (ℓ-max ℓQ ℓQ')
      W = IW Shape Ar ix

      isSetShape : (x : X) → isSet (Shape x)
      isSetShape (true , Γ , A) =
        isSet⊎ (isSetVar Γ A)
          (isSet⊎ isSetTy (isSet⊎ isSetTy (isSet⊎ isSetTy
            (isSetΣ isSetMor (λ _ → isProp→isSet (isSetTy _ _))))))
      isSetShape (false , Γ , A) =
        isSet⊎ (isSetΣ isSetOb (λ _ → isProp→isSet (isSetTy _ _)))
          (isSet⊎ (isSet× (isProp→isSet (isSetTy _ _)) isSetUnit*)
            (isSet⊎
              (isSetΣ isSetTy (λ _ →
                isSetΣ isSetTy (λ _ → isProp→isSet (isSetTy _ _))))
              (isSetΣ isSetTy (λ _ →
                isSetΣ isSetTy (λ _ → isProp→isSet (isSetTy _ _))))))

      enNe : ∀ {Γ A} → Ne Γ A → W (true , Γ , A)
      enNf : ∀ {Γ A} → Nf Γ A → W (false , Γ , A)
      enNe (var v) = node (inl v) (λ ())
      enNe (appₙ {A₀} n m) = node (inr (inl A₀))
        (λ { true → enNe n ; false → enNf m })
      enNe (π₁ₙ {B = B} n) = node (inr (inr (inl B))) (λ _ → enNe n)
      enNe (π₂ₙ {A = B} n) =
        node (inr (inr (inr (inl B)))) (λ _ → enNe n)
      enNe (genₙ g m) =
        node (inr (inr (inr (inr (g , refl))))) (λ _ → enNf m)
      enNf (ne {o} n) = node (inl (o , refl)) (λ _ → enNe n)
      enNf ttₙ = node (inr (inl (refl , tt*))) (λ ())
      enNf (pairₙ {A₁} {A₂} m m') = node (inr (inr (inl (A₁ , A₂ , refl))))
        (λ { true → enNf m ; false → enNf m' })
      enNf (lamₙ {A₁} {A₂} m) =
        node (inr (inr (inr (A₁ , A₂ , refl)))) (λ _ → enNf m)

      deNe : ∀ {Γ A} → W (true , Γ , A) → Ne Γ A
      deNf : ∀ {Γ A} → W (false , Γ , A) → Nf Γ A
      deNe (node (inl v) sub) = var v
      deNe (node (inr (inl A₀)) sub) =
        appₙ (deNe (sub true)) (deNf (sub false))
      deNe (node (inr (inr (inl B))) sub) = π₁ₙ (deNe (sub tt))
      deNe (node (inr (inr (inr (inl B)))) sub) = π₂ₙ (deNe (sub tt))
      deNe {Γ} (node (inr (inr (inr (inr (g , p))))) sub) =
        subst (Ne Γ) p (genₙ g (deNf (sub tt)))
      deNf {Γ} (node (inl (o , p)) sub) =
        subst (Nf Γ) p (ne (deNe (sub tt)))
      deNf {Γ} (node (inr (inl (p , _))) sub) = subst (Nf Γ) p ttₙ
      deNf {Γ} (node (inr (inr (inl (A₁ , A₂ , p)))) sub) =
        subst (Nf Γ) p (pairₙ (deNf (sub true)) (deNf (sub false)))
      deNf {Γ} (node (inr (inr (inr (A₁ , A₂ , p)))) sub) =
        subst (Nf Γ) p (lamₙ (deNf (sub tt)))

      retNe : ∀ {Γ A} (n : Ne Γ A) → deNe (enNe n) ≡ n
      retNf : ∀ {Γ A} (m : Nf Γ A) → deNf (enNf m) ≡ m
      retNe (var v) = refl
      retNe (appₙ n m) = cong₂ appₙ (retNe n) (retNf m)
      retNe (π₁ₙ n) = cong π₁ₙ (retNe n)
      retNe (π₂ₙ n) = cong π₂ₙ (retNe n)
      retNe (genₙ g m) =
        transportRefl _ ∙ cong (genₙ g) (retNf m)
      retNf (ne n) = transportRefl _ ∙ cong ne (retNe n)
      retNf ttₙ = transportRefl _
      retNf (pairₙ m m') =
        transportRefl _ ∙ cong₂ pairₙ (retNf m) (retNf m')
      retNf (lamₙ m) = transportRefl _ ∙ cong lamₙ (retNf m)

    isSetNe : ∀ {Γ A} → isSet (Ne Γ A)
    isSetNe = isSetRetract enNe deNe retNe
      (isOfHLevelSuc-IW 1 isSetShape _)

    isSetNf : ∀ {Γ A} → isSet (Nf Γ A)
    isSetNf = isSetRetract enNf deNf retNf
      (isOfHLevelSuc-IW 1 isSetShape _)
