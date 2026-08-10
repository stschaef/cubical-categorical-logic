-- The signature of a category, as a generalized algebraic theory.
--
-- This is the example `SortedSig` cannot express: `Hom` is a sort whose
-- index telescope mentions an earlier sort, and `id` is an operation
-- whose result sort depends on its argument.
module Cubical.Algebra.Theory.GAT.Instances.Category where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Algebra.Theory.GAT.Signature

private
  -- the three index variables of `_⋆_`
  data Thr : Type where
    A B C : Thr

  -- a `Hom` spine: `hm x y` is the sort `Hom x y`
  hm : {D : Type} → D → D → Bool → D
  hm x y true = x
  hm x y false = y

-- Ob : U
Γ₁ : Sig {ℓ-zero} {ℓ-zero}
Γ₁ = ◇ ▹ sortD ⊥ (λ ())

private
  Ob₁ : SortSym Γ₁
  Ob₁ = inr tt

-- Hom : (a b : Ob) → U
Γ₂ : Sig {ℓ-zero} {ℓ-zero}
Γ₂ = Γ₁ ▹ sortD Bool (λ _ → Ob₁ , λ ())

Ob : SortSym Γ₂
Ob = inl Ob₁

Hom : SortSym Γ₂
Hom = inr tt

-- `Hom` really does have two indices, and its telescope is well formed
-- on the nose.
_ : sortIdx {Γ = Γ₂} Hom ≡ Bool
_ = refl

_ : wfTel {Γ = Γ₂} (sortTel {Γ = Γ₂} Hom)
_ = λ _ ()

-- id : (a : Ob) → Hom a a
Γ₃ : Sig {ℓ-zero} {ℓ-zero}
Γ₃ = Γ₂ ▹ opD Unit (λ _ → Ob , λ ()) ⊥ (λ ()) (λ ()) (λ ())
       (Hom , λ _ → tt)

-- _⋆_ : (a b c : Ob) (f : Hom a b) (g : Hom b c) → Hom a c
Γ₄ : Sig {ℓ-zero} {ℓ-zero}
Γ₄ = Γ₃ ▹ opD Thr (λ _ → Ob , λ ()) Bool (λ _ → ⊥) (λ _ ())
       (λ { true → Hom , hm A B ; false → Hom , hm B C })
       (Hom , hm A C)

idOp : OpSym Γ₄
idOp = inl (inr tt)

⋆Op : OpSym Γ₄
⋆Op = inr tt

private
  open TermsOf Γ₄ using (ivar; avar; app)

  -- Two `Hom` spines that agree at both indices are equal.  Every ford
  -- below is discharged by `homEq refl refl`: the spine a node computes
  -- and the spine one writes always agree pointwise, they just do not
  -- agree definitionally, because neither `Bool` nor `Thr` has eta.
  homEq : {D : Type} {sp sp' : sortIdx {Γ = Γ₄} Hom → D}
    → sp true ≡ sp' true → sp false ≡ sp' false
    → Path (Srt Γ₄ D) (Hom , sp) (Hom , sp')
  homEq {sp = sp} {sp' = sp'} p q i =
    Hom , funExt {f = sp} {g = sp'} (λ { true → p ; false → q }) i

  ford : {D : Type} {sp sp' : sortIdx {Γ = Γ₄} Hom → D}
    → sp true ≡ sp' true → sp false ≡ sp' false
    → Eq._≡_ {A = Srt Γ₄ D} (Hom , sp) (Hom , sp')
  ford p q = Eq.pathToEq (homEq p q)

  -- the context of the unit laws: indices `a = true`, `b = false`, and
  -- one argument `f : Hom a b`
  ΘL : Tel Γ₄ Bool
  ΘL _ = Ob , λ ()

  Largs : Unit → Srt Γ₄ Bool
  Largs _ = Hom , λ i → i

-- ⋆IdL : (a b : Ob) (f : Hom a b) → id a ⋆ f ≡ f
private
  -- `_⋆_` at `a ↦ a`, `b ↦ a`, `c ↦ b`
  ρL : Thr → Bool
  ρL A = true
  ρL B = true
  ρL C = false

  -- `id a : Hom a a`; its result sort is already the one `id` produces,
  -- so this ford is `Eq.refl`
  idA : Term Γ₄ ΘL Unit Largs (Hom , λ i → true)
  idA = app idOp (λ _ → true) (λ ()) (λ ())
    (Hom , λ i → true) Eq.refl (λ ())

  idA⋆f : Term Γ₄ ΘL Unit Largs (Hom , λ i → i)
  idA⋆f = app ⋆Op ρL
    (λ { true → Hom , (λ i → true) ; false → Hom , (λ i → i) })
    (λ { true → ford refl refl ; false → ford refl refl })
    (Hom , λ i → i) (ford refl refl)
    (λ { true → idA ; false → avar tt })

Γ₅ : Sig {ℓ-zero} {ℓ-zero}
Γ₅ = Γ₄ ▹ eqnD Bool ΘL Unit Largs (Hom , λ i → i) idA⋆f (avar tt)

-- ⋆IdR : (a b : Ob) (f : Hom a b) → f ⋆ id b ≡ f
private
  -- `_⋆_` at `a ↦ a`, `b ↦ b`, `c ↦ b`
  ρR : Thr → Bool
  ρR A = true
  ρR B = false
  ρR C = false

  idB : Term Γ₄ ΘL Unit Largs (Hom , λ i → false)
  idB = app idOp (λ _ → false) (λ ()) (λ ())
    (Hom , λ i → false) Eq.refl (λ ())

  f⋆idB : Term Γ₄ ΘL Unit Largs (Hom , λ i → i)
  f⋆idB = app ⋆Op ρR
    (λ { true → Hom , (λ i → i) ; false → Hom , (λ i → false) })
    (λ { true → ford refl refl ; false → ford refl refl })
    (Hom , λ i → i) (ford refl refl)
    (λ { true → avar tt ; false → idB })

Γ₆ : Sig {ℓ-zero} {ℓ-zero}
Γ₆ = Γ₅ ▹ eqnD Bool ΘL Unit Largs (Hom , λ i → i) f⋆idB (avar tt)

-- ⋆Assoc : (a b c d : Ob) (f : Hom a b) (g : Hom b c) (h : Hom c d)
--        → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)
private
  data Fou : Type where
    a4 b4 c4 d4 : Fou

  data Arg3 : Type where
    fv gv hv : Arg3

  ΘA : Tel Γ₆ Fou
  ΘA _ = Ob , λ ()

  Aargs : Arg3 → Srt Γ₆ Fou
  Aargs fv = Hom , hm a4 b4
  Aargs gv = Hom , hm b4 c4
  Aargs hv = Hom , hm c4 d4

  open TermsOf Γ₆ using () renaming (avar to avarA; app to appA)

  ρ₁ ρ₂ ρ₃ ρ₄ : Thr → Fou
  ρ₁ A = a4
  ρ₁ B = b4
  ρ₁ C = c4
  ρ₂ A = a4
  ρ₂ B = c4
  ρ₂ C = d4
  ρ₃ A = b4
  ρ₃ B = c4
  ρ₃ C = d4
  ρ₄ A = a4
  ρ₄ B = b4
  ρ₄ C = d4

  AssocSrt : Srt Γ₆ Fou
  AssocSrt = Hom , hm a4 d4

  f⋆g : Term Γ₆ ΘA Arg3 Aargs (Hom , hm a4 c4)
  f⋆g = appA ⋆Op ρ₁ (λ j → Aargs (if j then fv else gv))
    (λ { true → ford refl refl ; false → ford refl refl })
    (Hom , hm a4 c4) (ford refl refl)
    (λ { true → avarA fv ; false → avarA gv })

  g⋆h : Term Γ₆ ΘA Arg3 Aargs (Hom , hm b4 d4)
  g⋆h = appA ⋆Op ρ₃ (λ j → Aargs (if j then gv else hv))
    (λ { true → ford refl refl ; false → ford refl refl })
    (Hom , hm b4 d4) (ford refl refl)
    (λ { true → avarA gv ; false → avarA hv })

  lhsA : Term Γ₆ ΘA Arg3 Aargs AssocSrt
  lhsA = appA ⋆Op ρ₂
    (λ { true → Hom , hm a4 c4 ; false → Hom , hm c4 d4 })
    (λ { true → ford refl refl ; false → ford refl refl })
    AssocSrt (ford refl refl)
    (λ { true → f⋆g ; false → avarA hv })

  rhsA : Term Γ₆ ΘA Arg3 Aargs AssocSrt
  rhsA = appA ⋆Op ρ₄
    (λ { true → Hom , hm a4 b4 ; false → Hom , hm b4 d4 })
    (λ { true → ford refl refl ; false → ford refl refl })
    AssocSrt (ford refl refl)
    (λ { true → avarA fv ; false → g⋆h })

CatSig : Sig {ℓ-zero} {ℓ-zero}
CatSig = Γ₆ ▹ eqnD Fou ΘA Arg3 Aargs AssocSrt lhsA rhsA

-- ------------------------------------------------------------------
-- `CatSig` is well formed
-- ------------------------------------------------------------------
--
-- Every obligation is either vacuous -- `sortIdx Ob` is `⊥`, so a
-- condition about an `Ob`-sorted variable has nothing to say -- or an
-- equation between two spines out of `⊥`, which agree pointwise but
-- not definitionally, since Agda has no eta for `⊥`.  So `obFord`, not
-- `Eq.refl`.  This is harmless: the resulting transports occur only
-- inside `SrtC`, which is a proposition, and `coeS-irr` says they do
-- not depend on which proof was supplied.

open import Cubical.Algebra.Theory.GAT.Model

private
  obFord : {D : Type} {f g : sortIdx {Γ = CatSig} Ob → D}
    → Eq._≡_ {A = Srt CatSig D} (Ob , f) (Ob , g)
  obFord {D} {f} {g} =
    Eq.pathToEq (λ i → Ob , funExt {f = f} {g = g} (λ ()) i)

CatWf : Wf CatSig
CatWf .Wf.wfSortTel (inl (inr tt)) = λ ()
CatWf .Wf.wfSortTel (inr tt) = λ _ ()
CatWf .Wf.wfOpTel (inl (inr tt)) = λ _ ()
CatWf .Wf.wfOpTel (inr tt) = λ _ ()
CatWf .Wf.wfOpArg (inl (inr tt)) ()
CatWf .Wf.wfOpArg (inr tt) true = λ _ → obFord
CatWf .Wf.wfOpArg (inr tt) false = λ _ → obFord
CatWf .Wf.wfOpRes (inl (inr tt)) = λ _ → obFord
CatWf .Wf.wfOpRes (inr tt) = λ _ → obFord
CatWf .Wf.wfEqnTel (inl (inl (inr tt))) = λ _ ()
CatWf .Wf.wfEqnTel (inl (inr tt)) = λ _ ()
CatWf .Wf.wfEqnTel (inr tt) = λ _ ()
CatWf .Wf.wfEqnArg (inl (inl (inr tt))) tt = λ _ → obFord
CatWf .Wf.wfEqnArg (inl (inr tt)) tt = λ _ → obFord
CatWf .Wf.wfEqnArg (inr tt) fv = λ _ → obFord
CatWf .Wf.wfEqnArg (inr tt) gv = λ _ → obFord
CatWf .Wf.wfEqnArg (inr tt) hv = λ _ → obFord
CatWf .Wf.wfEqnRes (inl (inl (inr tt))) = λ _ → obFord
CatWf .Wf.wfEqnRes (inl (inr tt)) = λ _ → obFord
CatWf .Wf.wfEqnRes (inr tt) = λ _ → obFord
CatWf .Wf.wfEqnLhs (inl (inl (inr tt))) =
  (λ _ → obFord) , λ { true → (λ _ → obFord) , (λ ()) ; false → tt* }
CatWf .Wf.wfEqnLhs (inl (inr tt)) =
  (λ _ → obFord) , λ { true → tt* ; false → (λ _ → obFord) , (λ ()) }
CatWf .Wf.wfEqnLhs (inr tt) =
  (λ _ → obFord)
  , λ { true → (λ _ → obFord) , (λ { true → tt* ; false → tt* })
      ; false → tt* }
CatWf .Wf.wfEqnRhs (inl (inl (inr tt))) = tt*
CatWf .Wf.wfEqnRhs (inl (inr tt)) = tt*
CatWf .Wf.wfEqnRhs (inr tt) =
  (λ _ → obFord)
  , λ { true → tt*
      ; false → (λ _ → obFord) , (λ { true → tt* ; false → tt* }) }
