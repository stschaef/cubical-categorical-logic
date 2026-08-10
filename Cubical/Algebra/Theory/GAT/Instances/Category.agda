-- The signature of a category, as a generalized algebraic theory.
--
-- This is the example `SortedSig` cannot express: `Hom` is a sort whose
-- index telescope mentions an earlier sort, and `id` is an operation
-- whose result sort depends on its argument.
module Cubical.Algebra.Theory.GAT.Instances.Category where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Bool using (Bool; true; false)
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
Γ₃ = Γ₂ ▹ opD Unit (λ _ → Ob , λ ()) ⊥ (λ ()) (Hom , λ _ → tt)

-- _⋆_ : (a b c : Ob) (f : Hom a b) (g : Hom b c) → Hom a c
Γ₄ : Sig {ℓ-zero} {ℓ-zero}
Γ₄ = Γ₃ ▹ opD Thr (λ _ → Ob , λ ()) Bool
       (λ { true → Hom , hm A B ; false → Hom , hm B C })
       (Hom , hm A C)

idOp : OpSym Γ₄
idOp = inl (inr tt)

⋆Op : OpSym Γ₄
⋆Op = inr tt

private
  open TermsOf Γ₄ using (ivar; avar; app)

  -- the context of ⋆IdL: two object indices `a = true`, `b = false`,
  -- and one argument `f : Hom a b`
  ΘL : Tel Γ₄ Bool
  ΘL _ = Ob , λ ()

  Largs : Unit → Srt Γ₄ Bool
  Largs _ = Hom , λ i → i

  -- the instantiation of `_⋆_` at `a ↦ a`, `b ↦ a`, `c ↦ b`
  ρL : Thr → Bool
  ρL A = true
  ρL B = true
  ρL C = false

  -- `Bool` and `Thr` have no definitional eta, so the spine a node
  -- *computes* (`λ i → ρ (sp i)`) is never syntactically the spine one
  -- *writes*, even when the two agree at every index.  This is the same
  -- wrinkle `Sorted.Free.Closing.opCong` exists to paper over.  `Srt`
  -- is a set, so re-typing a term along the pointwise path is
  -- harmless; a layer of smart constructors would insert these.
  reSrt : {S T : Srt Γ₄ Bool} → S ≡ T
    → Term Γ₄ ΘL Unit Largs S → Term Γ₄ ΘL Unit Largs T
  reSrt = subst (Term Γ₄ ΘL Unit Largs)

  homPath : {sp sp' : Bool → Bool} → ((i : Bool) → sp i ≡ sp' i)
    → Path (Srt Γ₄ Bool) (Hom , sp) (Hom , sp')
  homPath h i = Hom , funExt h i

  ptwise : {sp sp' : Bool → Bool} → sp true ≡ sp' true → sp false ≡ sp' false
    → (i : Bool) → sp i ≡ sp' i
  ptwise p q true = p
  ptwise p q false = q

  -- `id a`, at the spine `_⋆_` demands of its first argument
  idA : Term Γ₄ ΘL Unit Largs (Hom , λ i → ρL (hm A B i))
  idA = reSrt (homPath (ptwise refl refl)) (app idOp (λ _ → true) (λ ()))

  -- `f`, at the spine `_⋆_` demands of its second argument
  fB : Term Γ₄ ΘL Unit Largs (Hom , λ i → ρL (hm B C i))
  fB = reSrt (homPath (ptwise refl refl)) (avar tt)

  -- the sort `Hom a b`, in the form the `_⋆_` node produces
  HomAB : Srt Γ₄ Bool
  HomAB = Hom , λ i → ρL (hm A C i)

  -- `id a ⋆ f : Hom a b`
  idA⋆f : Term Γ₄ ΘL Unit Largs HomAB
  idA⋆f = app ⋆Op ρL (λ { true → idA ; false → fB })

  fA : Term Γ₄ ΘL Unit Largs HomAB
  fA = reSrt (homPath (ptwise refl refl)) (avar tt)

-- ⋆IdL : (a b : Ob) (f : Hom a b) → id a ⋆ f ≡ f
CatSig : Sig {ℓ-zero} {ℓ-zero}
CatSig = Γ₄ ▹ eqnD Bool ΘL Unit Largs HomAB idA⋆f fA
