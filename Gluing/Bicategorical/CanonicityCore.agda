{-# OPTIONS --lossy-unification #-}
{-
  The doctrine-generic core of canonicity via `rec` into the Artin
  comma category.

  `Gluing.Bicategorical.RecCanonicity` (free CCC) and
  `Gluing.Bicategorical.BiCCCRecCanonicity` (free BiCCC) run the same
  argument.  Everything portable lives here, and nothing here mentions
  a syntax, a glue, or the interpretation functor: the comparison
  isomorphisms and naturality squares that the free category's
  uniqueness principle demands are lemmas about a pair of isomorphisms
  in ANY cartesian closed category.  An instance supplies them by
  definitional unification, which is why the two proofs coincided
  textually.
-}
module Gluing.Bicategorical.CanonicityCore where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd)

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.BiCartesianClosed.Base
open import Cubical.Categories.Limits.Terminal.More

import Gluing.Canonicity as GC

private
  variable
    ℓ ℓ' : Level

{-
  The exponential comparison.  `Exp` is parameterised by a cartesian
  closed category only; `TA`/`TB` below are arbitrary objects, so the
  functor whose action they are never appears.
-}
module Exp (𝒞 : CartesianClosedCategory ℓ ℓ') where
  open CartesianClosedCategory 𝒞

  -- the two half-maps out of a product, and both at once
  pl : ∀ {X Y A} → Hom[ X , Y ] → Hom[ X × A , Y × A ]
  pl {X = X} {Y = Y} {A = A} m =
    _,p_ {a = Y} {b = A} (π₁ {a = X} {b = A} ⋆ m) (π₂ {a = X} {b = A})

  pr : ∀ {X A B} → Hom[ A , B ] → Hom[ X × A , X × B ]
  pr {X = X} {A = A} {B = B} n =
    _,p_ {a = X} {b = B} (π₁ {a = X} {b = A}) (π₂ {a = X} {b = A} ⋆ n)

  pb : ∀ {X Y A B} → Hom[ X , Y ] → Hom[ A , B ] → Hom[ X × A , Y × B ]
  pb {X = X} {Y = Y} {A = A} {B = B} m n = _,p_ {a = Y} {b = B}
    (π₁ {a = X} {b = A} ⋆ m) (π₂ {a = X} {b = A} ⋆ n)

  pl⋆pl : ∀ {X Y Z A} (m : Hom[ X , Y ]) (m' : Hom[ Y , Z ])
    → pl {A = A} m ⋆ pl {A = A} m' ≡ pl {A = A} (m ⋆ m')
  pl⋆pl m m' = ,p-extensionality
    ( ⋆Assoc _ _ _ ∙ ⟨ refl ⟩⋆⟨ ×β₁ ⟩
    ∙ sym (⋆Assoc _ _ _) ∙ ⟨ ×β₁ ⟩⋆⟨ refl ⟩
    ∙ ⋆Assoc _ _ _ ∙ sym ×β₁)
    ( ⋆Assoc _ _ _ ∙ ⟨ refl ⟩⋆⟨ ×β₂ ⟩ ∙ ×β₂ ∙ sym ×β₂)

  pr⋆pr : ∀ {X A B C} (u : Hom[ A , B ]) (v : Hom[ B , C ])
    → pr {X = X} u ⋆ pr {X = X} v ≡ pr {X = X} (u ⋆ v)
  pr⋆pr u v = ,p-extensionality
    ( ⋆Assoc _ _ _ ∙ ⟨ refl ⟩⋆⟨ ×β₁ ⟩ ∙ ×β₁ ∙ sym ×β₁)
    ( ⋆Assoc _ _ _ ∙ ⟨ refl ⟩⋆⟨ ×β₂ ⟩
    ∙ sym (⋆Assoc _ _ _) ∙ ⟨ ×β₂ ⟩⋆⟨ refl ⟩
    ∙ ⋆Assoc _ _ _ ∙ sym ×β₂)

  plId : ∀ {X A} → pl {X = X} {A = A} id ≡ id
  plId = ,p-extensionality
    (×β₁ ∙ ⋆IdR _ ∙ sym (⋆IdL _))
    (×β₂ ∙ sym (⋆IdL _))

  prId : ∀ {X A} → pr {X = X} {A = A} id ≡ id
  prId = ,p-extensionality
    (×β₁ ∙ sym (⋆IdL _))
    (×β₂ ∙ ⋆IdR _ ∙ sym (⋆IdL _))

  pl⋆pr : ∀ {X Y A B} (m : Hom[ X , Y ]) (n : Hom[ A , B ])
    → pl {A = A} m ⋆ pr {X = Y} n ≡ pb m n
  pl⋆pr m n = ,p-extensionality
    ( ⋆Assoc _ _ _ ∙ ⟨ refl ⟩⋆⟨ ×β₁ ⟩ ∙ ×β₁ ∙ sym ×β₁)
    ( ⋆Assoc _ _ _ ∙ ⟨ refl ⟩⋆⟨ ×β₂ ⟩
    ∙ sym (⋆Assoc _ _ _) ∙ ⟨ ×β₂ ⟩⋆⟨ refl ⟩ ∙ sym ×β₂)

  pr⋆pl : ∀ {X Y A B} (m : Hom[ X , Y ]) (n : Hom[ A , B ])
    → pr {X = X} n ⋆ pl {A = B} m ≡ pb m n
  pr⋆pl m n = ,p-extensionality
    ( ⋆Assoc _ _ _ ∙ ⟨ refl ⟩⋆⟨ ×β₁ ⟩
    ∙ sym (⋆Assoc _ _ _) ∙ ⟨ ×β₁ ⟩⋆⟨ refl ⟩ ∙ sym ×β₁)
    ( ⋆Assoc _ _ _ ∙ ⟨ refl ⟩⋆⟨ ×β₂ ⟩ ∙ ×β₂ ∙ sym ×β₂)

  pr⋆pb : ∀ {X Y A B C} (m : Hom[ X , Y ])
    (n : Hom[ A , B ]) (n' : Hom[ B , C ])
    → pr {X = X} n ⋆ pb m n' ≡ pb m (n ⋆ n')
  pr⋆pb m n n' = ,p-extensionality
    ( ⋆Assoc _ _ _ ∙ ⟨ refl ⟩⋆⟨ ×β₁ ⟩
    ∙ sym (⋆Assoc _ _ _) ∙ ⟨ ×β₁ ⟩⋆⟨ refl ⟩ ∙ sym ×β₁)
    ( ⋆Assoc _ _ _ ∙ ⟨ refl ⟩⋆⟨ ×β₂ ⟩
    ∙ sym (⋆Assoc _ _ _) ∙ ⟨ ×β₂ ⟩⋆⟨ refl ⟩
    ∙ ⋆Assoc _ _ _ ∙ sym ×β₂)

  pbId : ∀ {X Y A} (m : Hom[ X , Y ]) → pb {A = A} m id ≡ pl m
  pbId m = ,p-extensionality
    (×β₁ ∙ sym ×β₁)
    (×β₂ ∙ ⋆IdR _ ∙ sym ×β₂)

  appOf : ∀ {X A B} → Hom[ X , A ⇒ B ] → Hom[ X × A , B ]
  appOf m = pl m ⋆ app

  ldaβ : ∀ {X A B} (h : Hom[ X × A , B ])
    → appOf (lda {c = A} {d = B} h) ≡ h
  ldaβ {A = A} {B = B} h = ⇒ue.β A B

  ldaExt : ∀ {X A B} {m n : Hom[ X , A ⇒ B ]} → appOf m ≡ appOf n → m ≡ n
  ldaExt {A = A} {B = B} = ⇒ue.extensionality A B

  appOfSeq : ∀ {X Y A B} (m : Hom[ X , Y ]) (n : Hom[ Y , A ⇒ B ])
    → appOf (m ⋆ n) ≡ pl m ⋆ appOf n
  appOfSeq m n = cong (_⋆ app) (sym (pl⋆pl m n)) ∙ ⋆Assoc _ _ _

  -- the action of the internal hom on a pair of maps
  conj : ∀ {A B A' B'} → Hom[ A' , A ] → Hom[ B , B' ]
       → Hom[ A ⇒ B , A' ⇒ B' ]
  conj {A = A} {B = B} {A' = A'} {B' = B'} u v =
    lda {c = A'} {d = B'} ((pr {X = A ⇒ B} u ⋆ app {c = A} {d = B}) ⋆ v)

  conj⋆conj : ∀ {A B A' B' A'' B''}
    (u : Hom[ A' , A ]) (v : Hom[ B , B' ])
    (u' : Hom[ A'' , A' ]) (v' : Hom[ B' , B'' ])
    → conj u v ⋆ conj u' v' ≡ conj (u' ⋆ u) (v ⋆ v')
  conj⋆conj u v u' v' = ldaExt
    ( appOfSeq (conj u v) (conj u' v')
    ∙ ⟨ refl ⟩⋆⟨ ldaβ _ ⟩
    ∙ sym (⋆Assoc _ _ _)
    ∙ ⟨ sym (⋆Assoc _ _ _) ⟩⋆⟨ refl ⟩
    ∙ ⟨ ⟨ pl⋆pr (conj u v) u' ∙ sym (pr⋆pl (conj u v) u') ⟩⋆⟨ refl ⟩
      ⟩⋆⟨ refl ⟩
    ∙ ⟨ ⋆Assoc _ _ _ ⟩⋆⟨ refl ⟩
    ∙ ⟨ ⟨ refl ⟩⋆⟨ ldaβ _ ⟩ ⟩⋆⟨ refl ⟩
    ∙ ⟨ sym (⋆Assoc _ _ _) ⟩⋆⟨ refl ⟩
    ∙ ⟨ ⟨ sym (⋆Assoc _ _ _) ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩
    ∙ ⟨ ⟨ ⟨ pr⋆pr u' u ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩
    ∙ ⋆Assoc _ _ _
    ∙ sym (ldaβ _))

  conjId : ∀ {A B} → conj (id {x = A}) (id {x = B}) ≡ id
  conjId = ldaExt
    ( ldaβ _ ∙ ⋆IdR _ ∙ ⟨ prId ⟩⋆⟨ refl ⟩ ∙ ⋆IdL _
    ∙ sym (⋆IdL _) ∙ ⟨ sym plId ⟩⋆⟨ refl ⟩)

  {-
    `TA`, `TB` are the values of a functor at `A`, `B` in the use
    sites; here they are just objects, and the comparison is built
    from the two isomorphisms alone.
  -}
  module ⇒At {TA TB A B : ob}
    (f : CatIso C TA A) (g : CatIso C TB B) where

    ff = f .fst
    fi = f .snd .isIso.inv
    gf = g .fst
    gi = g .snd .isIso.inv

    E : Hom[ TA ⇒ TB , A ⇒ B ]
    E = conj fi gf

    Einv : Hom[ A ⇒ B , TA ⇒ TB ]
    Einv = conj ff gi

    expIso : CatIso C (TA ⇒ TB) (A ⇒ B)
    expIso = E , isiso Einv
      ( conj⋆conj ff gi fi gf
      ∙ cong₂ (conj {A = A} {B = B} {A' = A} {B' = B})
          (f .snd .isIso.sec) (g .snd .isIso.sec)
      ∙ conjId)
      ( conj⋆conj fi gf ff gi
      ∙ cong₂ (conj {A = TA} {B = TB} {A' = TA} {B' = TB})
          (f .snd .isIso.ret) (g .snd .isIso.ret)
      ∙ conjId)

    evalSq : app {c = TA} {d = TB} ⋆ gf ≡ pb E ff ⋆ app {c = A} {d = B}
    evalSq =
        ⟨ sym (⋆IdL _) ⟩⋆⟨ refl ⟩
      ∙ ⟨ ⟨ sym prId ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩
      ∙ ⟨ ⟨ cong prTA (sym (f .snd .isIso.ret)) ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩
      ∙ ⟨ ⟨ sym (pr⋆pr ff fi) ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩
      ∙ ⟨ ⋆Assoc _ _ _ ⟩⋆⟨ refl ⟩
      ∙ ⋆Assoc _ _ _
      ∙ ⟨ refl ⟩⋆⟨ sym (ldaβ _) ⟩
      ∙ sym (⋆Assoc _ _ _)
      ∙ ⟨ pr⋆pl E ff ⟩⋆⟨ refl ⟩
      where
      prTA : Hom[ TA , TA ] → Hom[ (TA ⇒ TB) × TA , (TA ⇒ TB) × TA ]
      prTA = pr {X = TA ⇒ TB} {A = TA} {B = TA}

    {-
      The λ-square.  `Th` is the induction hypothesis' morphism: at a
      use site it is `T ⟪ h ⟫`, and `lda Th` is `T ⟪ lda h ⟫` because
      the interpretation is strict for `lda`.
    -}
    lamSq : ∀ {TΓ Γ} (γ : CatIso C TΓ Γ) (h : Hom[ Γ × A , B ])
      (Th : Hom[ TΓ × TA , TB ])
      → Th ⋆ gf ≡ pb (γ .fst) ff ⋆ h
      → lda {c = TA} {d = TB} Th ⋆ E ≡ γ .fst ⋆ lda {c = A} {d = B} h
    lamSq {TΓ = TΓ} {Γ = Γ} γ h Th sq = ldaExt
      ( appOfSeq (lda {c = TA} {d = TB} Th) E
      ∙ ⟨ refl ⟩⋆⟨ ldaβ _ ⟩
      ∙ sym (⋆Assoc _ _ _)
      ∙ ⟨ sym (⋆Assoc _ _ _) ⟩⋆⟨ refl ⟩
      ∙ ⟨ ⟨ pl⋆pr _ fi ∙ sym (pr⋆pl _ fi) ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩
      ∙ ⟨ ⋆Assoc _ _ _ ⟩⋆⟨ refl ⟩
      ∙ ⟨ ⟨ refl ⟩⋆⟨ ldaβ Th ⟩ ⟩⋆⟨ refl ⟩
      ∙ ⋆Assoc _ _ _
      ∙ ⟨ refl ⟩⋆⟨ sq ⟩
      ∙ sym (⋆Assoc _ _ _)
      ∙ ⟨ pr⋆pb (γ .fst) fi ff ⟩⋆⟨ refl ⟩
      ∙ ⟨ cong pbγ (f .snd .isIso.sec) ⟩⋆⟨ refl ⟩
      ∙ ⟨ pbId (γ .fst) ⟩⋆⟨ refl ⟩
      ∙ ⟨ refl ⟩⋆⟨ sym (ldaβ h) ⟩
      ∙ sym (appOfSeq (γ .fst) (lda {c = A} {d = B} h)))
      where
      pbγ : Hom[ A , A ] → Hom[ TΓ × A , Γ × A ]
      pbγ z = pb (γ .fst) z

{-
  The coproduct comparison, for a doctrine that has sums.  As above,
  `TA`/`TB` are arbitrary objects and no functor occurs.
-}
module Sum (𝒞 : BiCartesianClosedCategory ℓ ℓ') where
  open BiCartesianClosedCategory 𝒞

  module +At {TA TB A B : ob}
    (f : CatIso C TA A) (g : CatIso C TB B) where

    ff = f .fst
    fi = f .snd .isIso.inv
    gf = g .fst
    gi = g .snd .isIso.inv

    fwd : Hom[ TA + TB , A + B ]
    fwd = [_,p_] {a = TA} {b = TB}
      (ff ⋆ σ₁ {a = A} {b = B}) (gf ⋆ σ₂ {a = A} {b = B})

    bwd : Hom[ A + B , TA + TB ]
    bwd = [_,p_] {a = A} {b = B}
      (fi ⋆ σ₁ {a = TA} {b = TB}) (gi ⋆ σ₂ {a = TA} {b = TB})

    +isoSec : bwd ⋆ fwd ≡ id
    +isoSec = [-,p-]-extensionality
      ( sym (⋆Assoc _ _ _) ∙ ⟨ +β₁ ⟩⋆⟨ refl ⟩
      ∙ ⋆Assoc _ _ _ ∙ ⟨ refl ⟩⋆⟨ +β₁ ⟩
      ∙ sym (⋆Assoc _ _ _) ∙ ⟨ f .snd .isIso.sec ⟩⋆⟨ refl ⟩
      ∙ ⋆IdL _ ∙ sym (⋆IdR _))
      ( sym (⋆Assoc _ _ _) ∙ ⟨ +β₂ ⟩⋆⟨ refl ⟩
      ∙ ⋆Assoc _ _ _ ∙ ⟨ refl ⟩⋆⟨ +β₂ ⟩
      ∙ sym (⋆Assoc _ _ _) ∙ ⟨ g .snd .isIso.sec ⟩⋆⟨ refl ⟩
      ∙ ⋆IdL _ ∙ sym (⋆IdR _))

    +isoRet : fwd ⋆ bwd ≡ id
    +isoRet = [-,p-]-extensionality
      ( sym (⋆Assoc _ _ _) ∙ ⟨ +β₁ ⟩⋆⟨ refl ⟩
      ∙ ⋆Assoc _ _ _ ∙ ⟨ refl ⟩⋆⟨ +β₁ ⟩
      ∙ sym (⋆Assoc _ _ _) ∙ ⟨ f .snd .isIso.ret ⟩⋆⟨ refl ⟩
      ∙ ⋆IdL _ ∙ sym (⋆IdR _))
      ( sym (⋆Assoc _ _ _) ∙ ⟨ +β₂ ⟩⋆⟨ refl ⟩
      ∙ ⋆Assoc _ _ _ ∙ ⟨ refl ⟩⋆⟨ +β₂ ⟩
      ∙ sym (⋆Assoc _ _ _) ∙ ⟨ g .snd .isIso.ret ⟩⋆⟨ refl ⟩
      ∙ ⋆IdL _ ∙ sym (⋆IdR _))

    sumIso : CatIso C (TA + TB) (A + B)
    sumIso = fwd , isiso bwd +isoSec +isoRet

    -- `Th₁`, `Th₂` are the induction hypotheses' morphisms; at a use
    -- site their copairing is the image of the copairing.
    cocaseSq : ∀ {TΓ Γ} (γ : CatIso C TΓ Γ)
      (h₁ : Hom[ A , Γ ]) (h₂ : Hom[ B , Γ ])
      (Th₁ : Hom[ TA , TΓ ]) (Th₂ : Hom[ TB , TΓ ])
      → Th₁ ⋆ γ .fst ≡ ff ⋆ h₁
      → Th₂ ⋆ γ .fst ≡ gf ⋆ h₂
      → [_,p_] {a = TA} {b = TB} Th₁ Th₂ ⋆ γ .fst
        ≡ fwd ⋆ [_,p_] {a = A} {b = B} h₁ h₂
    cocaseSq γ h₁ h₂ Th₁ Th₂ sq₁ sq₂ = [-,p-]-extensionality
      ( sym (⋆Assoc _ _ _) ∙ ⟨ +β₁ ⟩⋆⟨ refl ⟩ ∙ sq₁
      ∙ ⟨ refl ⟩⋆⟨ sym +β₁ ⟩
      ∙ sym (⋆Assoc _ _ _) ∙ ⟨ sym +β₁ ⟩⋆⟨ refl ⟩ ∙ ⋆Assoc _ _ _)
      ( sym (⋆Assoc _ _ _) ∙ ⟨ +β₂ ⟩⋆⟨ refl ⟩ ∙ sq₂
      ∙ ⟨ refl ⟩⋆⟨ sym +β₂ ⟩
      ∙ sym (⋆Assoc _ _ _) ∙ ⟨ sym +β₂ ⟩⋆⟨ refl ⟩ ∙ ⋆Assoc _ _ _)

{-
  The canonicity argument itself, for the two generating sorts.
  Nothing here mentions the interpretation functor: what the argument
  consumes is a component of the natural isomorphism at each sort,
  together with a reification -- an inhabitant of the sort's intended
  meaning whose numeral, composed with that component, is the term.
  That is exactly what the comma category's first projection supplies,
  and it is all it supplies.
-}
module BoolNat {C : Category ℓ ℓ'} (term : Terminal' C) where
  open Category C
  open TerminalNotation term

  -- every generator's naturality square at the terminal object
  genSq⊤ : (u : Hom[ 𝟙 , 𝟙 ]) {X : ob} (e : Hom[ 𝟙 , X ])
    → e ⋆ id ≡ u ⋆ e
  genSq⊤ u e = ⋆IdR _
    ∙ sym (cong (_⋆ e) (GC.⊤→⊤IsId term u) ∙ ⋆IdL e)

  module Gens (N B : ob)
    ([t] [f] : Hom[ 𝟙 , B ])
    ([ze] : Hom[ 𝟙 , N ]) ([su] : Hom[ N , N ]) where

    ＂_＂ : ℕ → Hom[ 𝟙 , N ]
    ＂ zero ＂ = [ze]
    ＂ suc n ＂ = ＂ n ＂ ⋆ [su]

    fromBool : Bool → Hom[ 𝟙 , B ]
    fromBool b = if b then [t] else [f]

    numeralsFixed : (η : Hom[ N , N ])
      → [ze] ⋆ η ≡ [ze] → [su] ⋆ η ≡ η ⋆ [su]
      → (n : ℕ) → ＂ n ＂ ⋆ η ≡ ＂ n ＂
    numeralsFixed η ηze ηsu zero = ηze
    numeralsFixed η ηze ηsu (suc n) =
        ⋆Assoc _ _ _
      ∙ cong (＂ n ＂ ⋆_) ηsu
      ∙ sym (⋆Assoc _ _ _)
      ∙ cong (_⋆ [su]) (numeralsFixed η ηze ηsu n)

    booleansFixed : (θ : Hom[ B , B ])
      → [t] ⋆ θ ≡ [t] → [f] ⋆ θ ≡ [f]
      → (b : Bool) → fromBool b ⋆ θ ≡ fromBool b
    booleansFixed θ θtr θfl true = θtr
    booleansFixed θ θtr θfl false = θfl

    module Canonicity
      (ηnat : Hom[ N , N ]) (ηbool : Hom[ B , B ])
      (ηze : [ze] ⋆ ηnat ≡ [ze]) (ηsu : [su] ⋆ ηnat ≡ ηnat ⋆ [su])
      (ηt : [t] ⋆ ηbool ≡ [t]) (ηf : [f] ⋆ ηbool ≡ [f])
      (reifyNat : (e : Hom[ 𝟙 , N ]) → Σ[ n ∈ ℕ ] ＂ n ＂ ⋆ ηnat ≡ e)
      (reifyBool : (e : Hom[ 𝟙 , B ])
        → Σ[ b ∈ Bool ] fromBool b ⋆ ηbool ≡ e)
      (evalBool : Hom[ 𝟙 , B ] → Bool)
      (evalBool-t : evalBool [t] ≡ true)
      (evalBool-f : evalBool [f] ≡ false)
      (evalNat : Hom[ 𝟙 , N ] → ℕ)
      (evalNat-num : (n : ℕ) → evalNat ＂ n ＂ ≡ n)
      where

      canonicalize-nat : (e : Hom[ 𝟙 , N ]) → fiber ＂_＂ e
      canonicalize-nat e = reifyNat e .fst
        , sym (numeralsFixed ηnat ηze ηsu (reifyNat e .fst))
        ∙ reifyNat e .snd

      canonicalize-bool : (e : Hom[ 𝟙 , B ]) → (e ≡ [t]) ⊎ (e ≡ [f])
      canonicalize-bool e = go (reifyBool e .fst) (reifyBool e .snd)
        where
        key : (b : Bool) → fromBool b ⋆ ηbool ≡ e → e ≡ fromBool b
        key b q = sym q ∙ booleansFixed ηbool ηt ηf b

        go : (b : Bool) → fromBool b ⋆ ηbool ≡ e
          → (e ≡ [t]) ⊎ (e ≡ [f])
        go true q = inl (key true q)
        go false q = inr (key false q)

      canonicity-bool : Iso (Hom[ 𝟙 , B ]) Bool
      canonicity-bool = GC.BoolIso.canonicity-bool [t] [f] evalBool
        evalBool-t evalBool-f canonicalize-bool

      canonicity-nat : Iso (Hom[ 𝟙 , N ]) ℕ
      canonicity-nat = GC.NatIso.canonicity-nat ＂_＂ evalNat evalNat-num
        canonicalize-nat
