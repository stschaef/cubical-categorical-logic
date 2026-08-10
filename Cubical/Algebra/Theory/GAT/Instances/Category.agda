-- The signature of a category, as a generalized algebraic theory.
--
-- This is the example `SortedSig` cannot express: `Hom` is a sort whose
-- index telescope mentions an earlier sort, and `id` is an operation
-- whose result sort depends on its argument.
module Cubical.Algebra.Theory.GAT.Instances.Category where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq
import Cubical.Data.FinData as F

open F using (Fin)

open import Cubical.Algebra.Theory.GAT.Signature

private
  -- Spines, written in declaration order: `pair x y` sends the first
  -- declared index to `x` and the second to `y`.  De Bruijn puts the
  -- most recently declared variable at `F.zero`, so the clauses are
  -- reversed.
  pair : {A : Type} → A → A → Fin 2 → A
  pair x y F.zero = y
  pair x y (F.suc _) = x

  triple : {A : Type} → A → A → A → Fin 3 → A
  triple x y z F.zero = z
  triple x y z (F.suc F.zero) = y
  triple x y z (F.suc (F.suc _)) = x

-- Ob : U
Γ₁ : Sig {ℓ-zero}
Γ₁ = ◇ ▹ sortD {n = 0} tt*

private
  Ob₁ : SortSym Γ₁
  Ob₁ = inr tt

-- Hom : (a b : Ob) → U
Γ₂ : Sig {ℓ-zero}
Γ₂ = Γ₁ ▹ sortD {n = 2} ((tt* , (Ob₁ , λ ())) , (Ob₁ , λ ()))

Ob : SortSym Γ₂
Ob = inl Ob₁

Hom : SortSym Γ₂
Hom = inr tt

-- `Hom` really does have two indices, and its telescope is well formed
-- on the nose.
_ : sortArity {Γ = Γ₂} Hom ≡ 2
_ = refl

_ : wfTel {Γ = Γ₂} (sortTel {Γ = Γ₂} Hom)
_ = (tt , λ ()) , λ ()

-- id : (a : Ob) → Hom a a
Γ₃ : Sig {ℓ-zero}
Γ₃ = Γ₂ ▹ opD (tt* , (Ob , λ ())) ⊥ (λ ()) (Hom , λ _ → F.zero)

private
  Ob₃ : SortSym Γ₃
  Ob₃ = Ob

  Hom₃ : SortSym Γ₃
  Hom₃ = Hom

  -- de Bruijn: `F.zero` is the most recently declared variable
  a₃ b₃ c₃ : Fin 3
  c₃ = F.zero
  b₃ = F.suc F.zero
  a₃ = F.suc (F.suc F.zero)

-- _⋆_ : (a b c : Ob) (f : Hom a b) (g : Hom b c) → Hom a c
Γ₄ : Sig {ℓ-zero}
Γ₄ = Γ₃ ▹ opD (((tt* , (Ob₃ , λ ())) , (Ob₃ , λ ())) , (Ob₃ , λ ()))
       Bool
       (λ { true → Hom₃ , pair a₃ b₃ ; false → Hom₃ , pair b₃ c₃ })
       (Hom₃ , pair a₃ c₃)

idOp : OpSym Γ₄
idOp = inl (inr tt)

⋆Op : OpSym Γ₄
⋆Op = inr tt

private
  Ob₄ : SortSym Γ₄
  Ob₄ = Ob

  Hom₄ : SortSym Γ₄
  Hom₄ = Hom

  -- context of ⋆IdL: indices (a b : Ob), one argument f : Hom a b
  ΘL : Tel Γ₄ 2
  ΘL = ((tt* , (Ob₄ , λ ())) , (Ob₄ , λ ()))

  aL bL : Fin 2
  bL = F.zero
  aL = F.suc F.zero

  Largs : Unit → Srt Γ₄ 2
  Largs _ = Hom₄ , pair aL bL

  open TermsOf Γ₄ using (ivar; avar; app)

  -- `Fin` has no definitional eta, so the spine a node *computes* --
  -- `λ i → ρ (sp i)` -- is never syntactically the spine one *writes*,
  -- even when the two agree at every index.  This is the same wrinkle
  -- `Sorted.Free.Closing.opCong` exists to paper over.  `Srt` is a set,
  -- so re-typing a term along the pointwise path is harmless; a layer
  -- of smart constructors would insert these.
  reSrt : {A B : Srt Γ₄ 2} → A ≡ B
    → Term Γ₄ ΘL Unit Largs A → Term Γ₄ ΘL Unit Largs B
  reSrt = subst (Term Γ₄ ΘL Unit Largs)

  spine≡ : {sp sp' : Fin 2 → Fin 2} → ((i : Fin 2) → sp i ≡ sp' i)
    → Path (Srt Γ₄ 2) (Hom₄ , sp) (Hom₄ , sp')
  spine≡ h i = Hom₄ , funExt h i

  -- `id a : Hom a a`, at the spine the `⋆` node demands of its first
  -- argument
  idA : Term Γ₄ ΘL Unit Largs
    (Hom₄ , λ i → triple aL aL bL (pair a₃ b₃ i))
  idA = reSrt (spine≡ (λ { F.zero → refl ; (F.suc _) → refl }))
    (app idOp (λ _ → aL) (λ ()))

  -- `f : Hom a b`, at the spine the `⋆` node demands of its second
  -- argument
  fB : Term Γ₄ ΘL Unit Largs
    (Hom₄ , λ i → triple aL aL bL (pair b₃ c₃ i))
  fB = reSrt (spine≡ (λ { F.zero → refl ; (F.suc _) → refl })) (avar tt)

  -- the sort `Hom a b`, in the form the `⋆` node produces
  HomAB : Srt Γ₄ 2
  HomAB = Hom₄ , λ i → triple aL aL bL (pair a₃ c₃ i)

  -- `id a ⋆ f : Hom a b`
  idA⋆f : Term Γ₄ ΘL Unit Largs HomAB
  idA⋆f = app ⋆Op (triple aL aL bL) (λ { true → idA ; false → fB })

  fA : Term Γ₄ ΘL Unit Largs HomAB
  fA = reSrt (spine≡ (λ { F.zero → refl ; (F.suc _) → refl })) (avar tt)

-- ⋆IdL : (a b : Ob) (f : Hom a b) → id a ⋆ f ≡ f
CatSig : Sig {ℓ-zero}
CatSig = Γ₄ ▹ eqnD ΘL Unit Largs HomAB idA⋆f fA
