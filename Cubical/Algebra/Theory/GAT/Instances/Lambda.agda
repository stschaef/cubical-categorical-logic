-- The untyped lambda calculus as a SECOND-ORDER theory, embedded.
--
-- `lam` binds:  lam : (Tm ⊢ Tm) → Tm.  It is declared as an `SOOp` and
-- translated by `soExt` into three first-order declarations -- the sort
-- `Abs` of abstractions, `inst` which instantiates one, and `lam`
-- itself, which now takes an abstraction.  `app` is an ordinary
-- first-order operation alongside.
--
-- The point of the exercise is the last line: the category of models is
-- `MOD`, already built and already strict.  Nothing about second-order
-- syntax needed new semantics.
module Cubical.Algebra.Theory.GAT.Instances.Lambda where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit

open import Cubical.Categories.Category

open import Cubical.Algebra.Theory.GAT.Signature
open import Cubical.Algebra.Theory.GAT.SecondOrder
open import Cubical.Algebra.Theory.GAT.Model

-- Tm : U
Γ₀ : Sig {ℓ-zero} {ℓ-zero}
Γ₀ = ◇ ▹ sortD ⊥ (λ ())

private
  Tm₀ : SortSym Γ₀
  Tm₀ = inr tt

-- lam : (Tm ⊢ Tm) → Tm, as a second-order operation
lamSO : SOOp Γ₀
lamSO .SOOp.Var = ⊥
lamSO .SOOp.Tele = λ ()
lamSO .SOOp.Bnd = Unit
lamSO .SOOp.bndSrt _ = Tm₀ , λ ()
lamSO .SOOp.bodySrt = Tm₀ , λ ()
lamSO .SOOp.resSrt = Tm₀ , λ ()

-- Abs : U, inst : Abs → Tm → Tm, lam : Abs → Tm
Γ₁ : Sig {ℓ-zero} {ℓ-zero}
Γ₁ = soExt Γ₀ lamSO

Tm : SortSym Γ₁
Tm = inl (inr tt)

Abs : SortSym Γ₁
Abs = inr tt

instOp : OpSym Γ₁
instOp = inl (inr tt)

lamOp : OpSym Γ₁
lamOp = inr tt

-- app : Tm → Tm → Tm, an ordinary first-order operation
LamSig : Sig {ℓ-zero} {ℓ-zero}
LamSig = Γ₁ ▹ opD ⊥ (λ ()) Bool (λ _ → ⊥) (λ _ ())
  (λ _ → Tm , λ ()) (Tm , λ ())

appOp : OpSym LamSig
appOp = inr tt

-- ------------------------------------------------------------------
-- Well-formedness, and the category of models
-- ------------------------------------------------------------------
--
-- Every sort of the translation has an empty index set, so every
-- obligation is absurd.

LamWf : Wf LamSig
LamWf .Wf.wfSortTel (inl (inr tt)) = λ ()
LamWf .Wf.wfSortTel (inr tt) = λ ()
LamWf .Wf.wfOpTel (inl (inl (inr tt))) = λ ()
LamWf .Wf.wfOpTel (inl (inr tt)) = λ ()
LamWf .Wf.wfOpTel (inr tt) = λ ()
LamWf .Wf.wfOpArg (inl (inl (inr tt))) (inl _) = λ ()
LamWf .Wf.wfOpArg (inl (inl (inr tt))) (inr _) = λ ()
LamWf .Wf.wfOpArg (inl (inr tt)) _ = λ ()
LamWf .Wf.wfOpArg (inr tt) _ = λ ()
LamWf .Wf.wfOpRes (inl (inl (inr tt))) = λ ()
LamWf .Wf.wfOpRes (inl (inr tt)) = λ ()
LamWf .Wf.wfOpRes (inr tt) = λ ()
LamWf .Wf.wfEqnTel ()
LamWf .Wf.wfEqnArg ()
LamWf .Wf.wfEqnRes ()
LamWf .Wf.wfEqnLhs ()
LamWf .Wf.wfEqnRhs ()

-- the category of models of the second-order theory
LAM : (ℓX : Level) → Category _ _
LAM ℓX = MOD LamSig LamWf ℓX

-- Its laws are definitional, but nothing needs restating here:
-- `MOD⋆IdL`, `MOD⋆IdR` and `MOD⋆Assoc` in `GAT.Model` are `refl` for
-- EVERY signature, so in particular for this one.  That is the whole
-- payoff of translating rather than reinterpreting -- a second-order
-- theory gets the first-order category of models, strictness included,
-- with no new proof obligations.
