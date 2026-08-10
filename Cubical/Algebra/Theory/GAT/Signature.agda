-- Signatures of generalized algebraic theories.
--
-- The generalization of `Cubical.Algebra.Theory.Sorted`'s `SortedSig` +
-- `SortedEqns`: a sort is no longer an element of a fixed type `S`, it
-- is a *symbol applied to a spine of arguments*, and the arguments are
-- terms of previously declared sorts.  `Hom : Ob → Ob → U` and
-- `id : (a : Ob) → Hom a a` are the two things `SortedSig` cannot say.
--
-- Three design choices, each of which buys a definitional law:
--
--  * Sort spines are *variables*, not general terms ("A-normal form").
--    Substitution into a sort is then postcomposition of a variable
--    map, so `A ⟨ ρ ⟩ ⟨ ρ' ⟩` and `A ⟨ ρ' ∘ ρ ⟩` are `refl` and the
--    fusion lemma that blocks intrinsic dependent syntax never arises.
--    General arguments are recovered by an intermediate variable and an
--    equation, exactly as in A-normal form for programs.
--
--  * Index scopes are `Fin`-scoped, so a raw sort depends only on the
--    *length* of the telescope it lives over.  Weakening a signature
--    therefore preserves arities definitionally.
--
--  * Sorts and terms are raw; well-formedness of a spine (that the
--    variable supplied for an index really has the sort that index
--    demands) is a separate `Eq`-valued predicate, discharged by
--    `Eq.refl` in every concrete signature.  This is the same fording
--    `Sorted.Displayed.Base`'s `Opsᶠᴰ` uses, for the same reason: it
--    keeps transports out of the definitions that have to compute.
--
-- Operation *argument* lists stay infinitary (`Type ℓA`, as in
-- `SortedSig.arities`); only the index telescope of a sort is finite.
module Cubical.Algebra.Theory.GAT.Signature where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq
import Cubical.Data.FinData as F

open F using (Fin)

private
  variable
    ℓS ℓO ℓA : Level

-- ------------------------------------------------------------------
-- Raw sorts and telescopes over an abstract table of sort symbols
-- ------------------------------------------------------------------

module RawSorts (Sy : Type ℓS) (ar : Sy → ℕ) where

  -- weakening of a de Bruijn index; `Fin` is structural so this is the
  -- only variable manipulation the whole development needs.
  wkF : {n : ℕ} → Fin n → Fin (suc n)
  wkF F.zero = F.zero
  wkF (F.suc i) = F.suc (wkF i)

  -- A raw sort in a scope of `n` variables: a symbol together with a
  -- variable for each of its indices.
  Srt : ℕ → Type ℓS
  Srt n = Σ[ S ∈ Sy ] (Fin (ar S) → Fin n)

  -- Reindexing along a variable map.  This is postcomposition, so it is
  -- strictly functorial: `A ⟨ ρ ⟩ ⟨ ρ' ⟩` is *syntactically*
  -- `A ⟨ ρ' ∘ ρ ⟩`.
  infixl 8 _⟨_⟩
  _⟨_⟩ : {m n : ℕ} → Srt m → (Fin m → Fin n) → Srt n
  (S , sp) ⟨ ρ ⟩ = S , λ i → ρ (sp i)

  ⟨⟩-id : {n : ℕ} (A : Srt n) → A ⟨ (λ i → i) ⟩ ≡ A
  ⟨⟩-id A = refl

  ⟨⟩-∘ : {m n p : ℕ} (A : Srt m) (ρ : Fin m → Fin n) (ρ' : Fin n → Fin p)
    → A ⟨ ρ ⟩ ⟨ ρ' ⟩ ≡ A ⟨ (λ i → ρ' (ρ i)) ⟩
  ⟨⟩-∘ A ρ ρ' = refl

  -- A telescope of `n` index variables: the `i`th entry is a sort in
  -- the scope of the `i` variables before it.
  Tel : ℕ → Type ℓS
  Tel zero = Unit*
  Tel (suc n) = Tel n × Srt n

  -- the sort of a variable, weakened into the full scope
  lookup : {n : ℕ} → Tel n → Fin n → Srt n
  lookup {suc n} (Θ , A) F.zero = A ⟨ wkF ⟩
  lookup {suc n} (Θ , A) (F.suc i) = lookup Θ i ⟨ wkF ⟩

-- ------------------------------------------------------------------
-- Raw terms over an abstract table of operation symbols
-- ------------------------------------------------------------------
--
-- A declaration's variable context splits into an *index* part -- the
-- variables that appear in sort spines, which form a dependent
-- telescope -- and an *argument* part, whose sorts live over the index
-- part but which nothing depends on.  That split is not a restriction:
-- an index variable's sort only mentions earlier index variables, so
-- the indices can always be floated to the front.

module RawTerms (Sy : Type ℓS) (ar : Sy → ℕ)
  (Op : Type ℓO) (opAr : Op → ℕ)
  (opIx : Op → Type ℓA)
  (opArgS : (o : Op) → opIx o → RawSorts.Srt Sy ar (opAr o))
  (opRes : (o : Op) → RawSorts.Srt Sy ar (opAr o))
  where

  open RawSorts Sy ar

  data Tm {n : ℕ} (Θ : Tel n) (I : Type ℓA) (as : I → Srt n)
    : Srt n → Type (ℓ-max (ℓ-max ℓS ℓO) ℓA) where
    ivar : (i : Fin n) → Tm Θ I as (lookup Θ i)
    avar : (i : I) → Tm Θ I as (as i)
    app : (o : Op) (ρ : Fin (opAr o) → Fin n)
      → ((j : opIx o) → Tm Θ I as (opArgS o j ⟨ ρ ⟩))
      → Tm Θ I as (opRes o ⟨ ρ ⟩)

-- ------------------------------------------------------------------
-- Signatures as telescopes of declarations
-- ------------------------------------------------------------------
--
-- `SortSym`, `OpSym` and the tables that go with them are computed by
-- recursion on the signature, so that `Srt Γ n` and `Tel Γ n` are
-- ordinary raw syntax over the symbols declared so far.  Weakening
-- along `Γ ▹ d` leaves arities alone *definitionally*, which is what
-- makes `wkSrt` a relabelling rather than a transport.

module _ {ℓA : Level} where

  data Sig : Type (ℓ-suc ℓA)
  data Decl (Γ : Sig) : Type (ℓ-suc ℓA)

  SortSym : Sig → Type
  sortArity : {Γ : Sig} → SortSym Γ → ℕ
  OpSym : Sig → Type
  opArity : {Γ : Sig} → OpSym Γ → ℕ
  opIx : {Γ : Sig} → OpSym Γ → Type ℓA

  Srt : (Γ : Sig) → ℕ → Type
  Tel : (Γ : Sig) → ℕ → Type

  opArgS : {Γ : Sig} (o : OpSym Γ) → opIx o → Srt Γ (opArity o)
  opRes : {Γ : Sig} (o : OpSym Γ) → Srt Γ (opArity o)

  Term : (Γ : Sig) {n : ℕ} (Θ : Tel Γ n) (I : Type ℓA)
    (as : I → Srt Γ n) → Srt Γ n → Type ℓA

  infixl 5 _▹_

  data Sig where
    ◇ : Sig
    _▹_ : (Γ : Sig) → Decl Γ → Sig

  data Decl Γ where
    -- a sort symbol with a telescope of index arguments
    sortD : {n : ℕ} (Θ : Tel Γ n) → Decl Γ
    -- an operation: index telescope `Θ`, argument family `as`, result
    -- sort `r`.  `I` is an arbitrary type, so arities stay infinitary.
    opD : {n : ℕ} (Θ : Tel Γ n) (I : Type ℓA) (as : I → Srt Γ n)
      (r : Srt Γ n) → Decl Γ
    -- an equation between two terms of a common sort
    eqnD : {n : ℕ} (Θ : Tel Γ n) (I : Type ℓA) (as : I → Srt Γ n)
      (r : Srt Γ n) (t u : Term Γ Θ I as r) → Decl Γ

  -- weakening along a signature extension.  `sortArity` and `opArity`
  -- are unchanged by `▹`, so this is a relabelling of symbols and never
  -- a transport.
  wkSrt : {Γ : Sig} {d : Decl Γ} {n : ℕ} → Srt Γ n → Srt (Γ ▹ d) n
  wkTel : {Γ : Sig} {d : Decl Γ} {n : ℕ} → Tel Γ n → Tel (Γ ▹ d) n

  Srt Γ = RawSorts.Srt (SortSym Γ) (λ S → sortArity {Γ} S)
  Tel Γ = RawSorts.Tel (SortSym Γ) (λ S → sortArity {Γ} S)
  Term Γ = RawTerms.Tm (SortSym Γ) (λ S → sortArity {Γ} S)
    (OpSym Γ) (λ o → opArity {Γ} o) (λ o → opIx {Γ} o)
    (λ o → opArgS {Γ} o) (λ o → opRes {Γ} o)

  SortSym ◇ = ⊥
  SortSym (Γ ▹ sortD _) = SortSym Γ ⊎ Unit
  SortSym (Γ ▹ opD _ _ _ _) = SortSym Γ
  SortSym (Γ ▹ eqnD _ _ _ _ _ _) = SortSym Γ

  sortArity {Γ ▹ sortD _} (inl S) = sortArity {Γ} S
  sortArity {Γ ▹ sortD {n} _} (inr _) = n
  sortArity {Γ ▹ opD _ _ _ _} S = sortArity {Γ} S
  sortArity {Γ ▹ eqnD _ _ _ _ _ _} S = sortArity {Γ} S

  OpSym ◇ = ⊥
  OpSym (Γ ▹ sortD _) = OpSym Γ
  OpSym (Γ ▹ opD _ _ _ _) = OpSym Γ ⊎ Unit
  OpSym (Γ ▹ eqnD _ _ _ _ _ _) = OpSym Γ

  opArity {Γ ▹ sortD _} o = opArity {Γ} o
  opArity {Γ ▹ opD _ _ _ _} (inl o) = opArity {Γ} o
  opArity {Γ ▹ opD {n} _ _ _ _} (inr _) = n
  opArity {Γ ▹ eqnD _ _ _ _ _ _} o = opArity {Γ} o

  opIx {Γ ▹ sortD _} o = opIx {Γ} o
  opIx {Γ ▹ opD _ _ _ _} (inl o) = opIx {Γ} o
  opIx {Γ ▹ opD _ I _ _} (inr _) = I
  opIx {Γ ▹ eqnD _ _ _ _ _ _} o = opIx {Γ} o

  wkSrt {d = sortD _} (S , sp) = inl S , sp
  wkSrt {d = opD _ _ _ _} A = A
  wkSrt {d = eqnD _ _ _ _ _ _} A = A

  wkTel {n = zero} _ = tt*
  wkTel {Γ} {d} {n = suc n} (Θ , A) = wkTel {Γ} {d} Θ , wkSrt {Γ} {d} A

  opArgS {Γ ▹ sortD Θ} o j = wkSrt {Γ} {sortD Θ} (opArgS {Γ} o j)
  opArgS {Γ ▹ opD Θ I as r} (inl o) j =
    wkSrt {Γ} {opD Θ I as r} (opArgS {Γ} o j)
  opArgS {Γ ▹ opD _ _ as _} (inr _) j = as j
  opArgS {Γ ▹ eqnD Θ I as r t u} o j =
    wkSrt {Γ} {eqnD Θ I as r t u} (opArgS {Γ} o j)

  opRes {Γ ▹ sortD Θ} o = wkSrt {Γ} {sortD Θ} (opRes {Γ} o)
  opRes {Γ ▹ opD Θ I as r} (inl o) = wkSrt {Γ} {opD Θ I as r} (opRes {Γ} o)
  opRes {Γ ▹ opD _ _ _ r} (inr _) = r
  opRes {Γ ▹ eqnD Θ I as r t u} o = wkSrt {Γ} {eqnD Θ I as r t u} (opRes {Γ} o)

-- ------------------------------------------------------------------
-- Term constructors for a fixed signature
-- ------------------------------------------------------------------

module TermsOf {ℓA : Level} (Γ : Sig {ℓA}) where
  open RawTerms (SortSym Γ) (sortArity {Γ = Γ}) (OpSym Γ)
    (opArity {Γ = Γ}) (opIx {Γ = Γ}) (opArgS {Γ = Γ}) (opRes {Γ = Γ})
    public

-- ------------------------------------------------------------------
-- The index telescopes of the declared symbols
-- ------------------------------------------------------------------

module _ {ℓA : Level} where

  sortTel : {Γ : Sig {ℓA}} (S : SortSym Γ) → Tel Γ (sortArity {Γ = Γ} S)
  sortTel {Γ ▹ sortD Θ} (inl S) =
    wkTel {Γ = Γ} {d = sortD Θ} (sortTel {Γ = Γ} S)
  sortTel {Γ ▹ sortD Θ} (inr _) = wkTel {Γ = Γ} {d = sortD Θ} Θ
  sortTel {Γ ▹ opD Θ I as r} S =
    wkTel {Γ = Γ} {d = opD Θ I as r} (sortTel {Γ = Γ} S)
  sortTel {Γ ▹ eqnD Θ I as r t u} S =
    wkTel {Γ = Γ} {d = eqnD Θ I as r t u} (sortTel {Γ = Γ} S)

  opTel : {Γ : Sig {ℓA}} (o : OpSym Γ) → Tel Γ (opArity {Γ = Γ} o)
  opTel {Γ ▹ sortD Θ} o = wkTel {Γ = Γ} {d = sortD Θ} (opTel {Γ = Γ} o)
  opTel {Γ ▹ opD Θ I as r} (inl o) =
    wkTel {Γ = Γ} {d = opD Θ I as r} (opTel {Γ = Γ} o)
  opTel {Γ ▹ opD Θ I as r} (inr _) = wkTel {Γ = Γ} {d = opD Θ I as r} Θ
  opTel {Γ ▹ eqnD Θ I as r t u} o =
    wkTel {Γ = Γ} {d = eqnD Θ I as r t u} (opTel {Γ = Γ} o)

-- ------------------------------------------------------------------
-- Well-formedness
-- ------------------------------------------------------------------
--
-- A raw sort `(S , sp)` over `Θ` is well formed when the variable
-- supplied for each index of `S` really has the sort that index
-- demands.  This is stated with `Eq._≡_`, so discharging it in a
-- concrete signature is `Eq.refl`, and interpreting a well-formed sort
-- in a model is an `Eq.transport` that computes away.

module _ {ℓA : Level} {Γ : Sig {ℓA}} where

  open RawSorts (SortSym Γ) (sortArity {Γ = Γ}) using (lookup; _⟨_⟩) public

  wfSrt : {n : ℕ} (Θ : Tel Γ n) (A : Srt Γ n) → Type
  wfSrt Θ (S , sp) = (i : Fin (sortArity {Γ = Γ} S))
    → lookup Θ (sp i) Eq.≡ lookup (sortTel {Γ = Γ} S) i ⟨ sp ⟩

  wfTel : {n : ℕ} (Θ : Tel Γ n) → Type
  wfTel {zero} _ = Unit
  wfTel {suc n} (Θ , A) = wfTel Θ × wfSrt Θ A

  -- A variable map is a context morphism when it preserves sorts; this
  -- is what a term's `app` node needs of its index spine.
  wfRen : {m n : ℕ} (Θ : Tel Γ n) (Ξ : Tel Γ m)
    (ρ : Fin m → Fin n) → Type
  wfRen {m} Θ Ξ ρ = (i : Fin m) → lookup Θ (ρ i) Eq.≡ lookup Ξ i ⟨ ρ ⟩
