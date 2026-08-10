-- Second-order operations, embedded by translation.
--
-- A binding argument cannot be interpreted directly: `lam`'s argument
-- `Tm A → Tm B` is contravariant in the model, so `f : M → N` cannot
-- push it forward and SET-valued second-order models do not form a
-- category.  `GAT.Presheaf` does not help either: its models are
-- fibrewise, and exponentials in presheaves are not pointwise.
--
-- So a second-order operation is *translated* into first-order
-- declarations, which is what the semantics is anyway.  A binding
-- argument with bound variables `B` becomes
--
--   Abs  : (Θ) → U                      -- the abstractions
--   inst : (Θ) → Abs → (b : B) → bS b → a
--   o    : (Θ) → Abs → r
--
-- `Abs` is structure rather than the literal function space, which is
-- exactly the first-order presentation of a second-order theory: an
-- algebra with abstraction operators.  The user pins it down by adding
-- the theory's own equations (β, η) as ordinary `eqnD`s.
--
-- The payoff is that the category of models is not new work: it is
-- `MOD` of the translation, with the strictness already proved.
module Cubical.Algebra.Theory.GAT.SecondOrder where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit; tt; Unit*; tt*)

open import Cubical.Algebra.Theory.GAT.Signature

private
  variable
    ℓI ℓA : Level

  -- the empty type at an arbitrary level; the translated declarations
  -- are first order, so none of them binds anything
  data Emp {ℓ : Level} : Type ℓ where

-- A second-order operation over `Γ`: an index telescope, one binding
-- argument whose bound variables are `B` at sorts `bS`, a body sort `a`
-- and a result sort `r`.
record SOOp {ℓI ℓA : Level} (Γ : Sig {ℓI} {ℓA})
  : Type (ℓ-suc (ℓ-max ℓI ℓA)) where
  field
    Var : Type ℓI
    Tele : Tel Γ Var
    Bnd : Type ℓA
    bndSrt : Bnd → Srt Γ Var
    bodySrt : Srt Γ Var
    resSrt : Srt Γ Var

open SOOp

module _ {ℓI ℓA : Level} (Γ : Sig {ℓI} {ℓA}) (so : SOOp Γ) where

  private
    -- 1. the sort of abstractions, indexed like the operation
    dAbs : Decl Γ
    dAbs = sortD (so .Var) (so .Tele)

    Γ₁ : Sig {ℓI} {ℓA}
    Γ₁ = Γ ▹ dAbs

    wk₁ : {V : Type ℓI} → Srt Γ V → Srt Γ₁ V
    wk₁ = wkSrt {Γ = Γ} {d = dAbs}

    -- `Abs` applied to its own index variables
    AbsSrt : Srt Γ₁ (so .Var)
    AbsSrt = inr tt , λ v → v

    -- 2. instantiation: an abstraction and one argument per bound
    -- variable, yielding the body sort
    instArgs : Unit* {ℓA} ⊎ so .Bnd → Srt Γ₁ (so .Var)
    instArgs (inl _) = AbsSrt
    instArgs (inr b) = wk₁ (so .bndSrt b)

    dInst : Decl Γ₁
    dInst = opD (so .Var) (wkTel {Γ = Γ} {d = dAbs} (so .Tele))
      (Unit* {ℓA} ⊎ so .Bnd) (λ _ → Emp) (λ _ ())
      instArgs (wk₁ (so .bodySrt))

    Γ₂ : Sig {ℓI} {ℓA}
    Γ₂ = Γ₁ ▹ dInst

    wk₂ : {V : Type ℓI} → Srt Γ₁ V → Srt Γ₂ V
    wk₂ = wkSrt {Γ = Γ₁} {d = dInst}

  -- 3. the operation itself, first order: it takes an abstraction
  soExt : Sig {ℓI} {ℓA}
  soExt = Γ₂ ▹ opD (so .Var)
    (wkTel {Γ = Γ₁} {d = dInst} (wkTel {Γ = Γ} {d = dAbs} (so .Tele)))
    (Unit* {ℓA}) (λ _ → Emp) (λ _ ())
    (λ _ → wk₂ AbsSrt)
    (wk₂ (wk₁ (so .resSrt)))

  -- the three symbols the translation introduces
  absSym : SortSym soExt
  absSym = inr tt

  instSym : OpSym soExt
  instSym = inl (inr tt)

  opSym : OpSym soExt
  opSym = inr tt
