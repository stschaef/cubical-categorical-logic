-- Signatures of generalized algebraic theories.
--
-- The generalization of `Cubical.Algebra.Theory.Sorted`'s `SortedSig` +
-- `SortedEqns`: a sort is no longer an element of a fixed type `S`, it
-- is a *symbol applied to a spine of arguments*.  `Hom : Ob → Ob → U`
-- and `id : (a : Ob) → Hom a a` are the two things `SortedSig` cannot
-- say.
--
-- Three design choices, each of which buys a definitional law:
--
--  * Sort spines are *variables*, not general terms ("A-normal form").
--    Reindexing a sort is then postcomposition of a variable map, so
--    `⟨⟩-id` and `⟨⟩-∘` are `refl` and the fusion lemma that blocks
--    intrinsic dependent syntax never arises.  General arguments are
--    recovered by an intermediate variable and an equation.
--
--  * A telescope over a type `V` of variables is just an assignment
--    `V → Srt V` of a sort to each variable.  There is no order and no
--    length: the dependency between index variables is carried entirely
--    by the spines.  Index arities are therefore arbitrary types, as
--    operation arities already were.  Nothing needs a well-founded
--    order because the semantics (`GAT.Model`) is flat -- carriers are
--    indexed by sort symbols and dependency is carried by display maps,
--    so no environment is ever built by recursion over a telescope.
--
--  * Sorts and terms are raw; well-formedness of a spine (that the
--    variable supplied for an index really has the sort that index
--    demands) is a separate `Eq`-valued predicate, discharged by
--    `Eq.refl` in every concrete signature.  This is the same fording
--    `Sorted.Displayed.Base`'s `Opsᶠᴰ` uses, for the same reason: it
--    keeps transports out of the definitions that have to compute.
module Cubical.Algebra.Theory.GAT.Signature where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

private
  variable
    ℓS ℓO ℓI ℓA : Level

-- ------------------------------------------------------------------
-- Raw sorts and telescopes over an abstract table of sort symbols
-- ------------------------------------------------------------------

module RawSorts (Sy : Type ℓS) (idx : Sy → Type ℓI) where

  -- A raw sort in a scope `V`: a symbol together with a variable for
  -- each of its indices.
  Srt : Type ℓI → Type (ℓ-max ℓS ℓI)
  Srt V = Σ[ S ∈ Sy ] (idx S → V)

  -- Reindexing.  This is postcomposition, so it is strictly
  -- functorial: `A ⟨ ρ ⟩ ⟨ ρ' ⟩` is *syntactically* `A ⟨ ρ' ∘ ρ ⟩`.
  infixl 8 _⟨_⟩
  _⟨_⟩ : {V W : Type ℓI} → Srt V → (V → W) → Srt W
  A ⟨ ρ ⟩ = A .fst , λ i → ρ (A .snd i)

  ⟨⟩-id : {V : Type ℓI} (A : Srt V) → A ⟨ (λ v → v) ⟩ ≡ A
  ⟨⟩-id A = refl

  ⟨⟩-∘ : {U V W : Type ℓI} (A : Srt U) (ρ : U → V) (ρ' : V → W)
    → A ⟨ ρ ⟩ ⟨ ρ' ⟩ ≡ A ⟨ (λ u → ρ' (ρ u)) ⟩
  ⟨⟩-∘ A ρ ρ' = refl

  -- A telescope of index variables.
  Tel : Type ℓI → Type (ℓ-max ℓS ℓI)
  Tel V = V → Srt V

-- ------------------------------------------------------------------
-- Raw terms over an abstract table of operation symbols
-- ------------------------------------------------------------------
--
-- A declaration's variable context splits into an *index* part -- the
-- variables that appear in sort spines -- and an *argument* part, whose
-- sorts live over the index part but which nothing depends on.

module RawTerms (Sy : Type ℓS) (idx : Sy → Type ℓI)
  (Op : Type ℓO) (opVar : Op → Type ℓI) (opIx : Op → Type ℓA)
  (opArgS : (o : Op) → opIx o → RawSorts.Srt Sy idx (opVar o))
  (opRes : (o : Op) → RawSorts.Srt Sy idx (opVar o))
  where

  open RawSorts Sy idx

  data Tm {V : Type ℓI} (Θ : Tel V) (I : Type ℓA) (as : I → Srt V)
    : Srt V → Type (ℓ-max (ℓ-max (ℓ-max ℓS ℓO) ℓI) ℓA) where
    ivar : (v : V) → Tm Θ I as (Θ v)
    avar : (i : I) → Tm Θ I as (as i)
    app : (o : Op) (ρ : opVar o → V)
      → ((j : opIx o) → Tm Θ I as (opArgS o j ⟨ ρ ⟩))
      → Tm Θ I as (opRes o ⟨ ρ ⟩)

-- ------------------------------------------------------------------
-- Signatures as telescopes of declarations
-- ------------------------------------------------------------------

module _ {ℓI ℓA : Level} where

  data Sig : Type (ℓ-suc (ℓ-max ℓI ℓA))
  data Decl (Γ : Sig) : Type (ℓ-suc (ℓ-max ℓI ℓA))

  SortSym : Sig → Type
  sortIdx : {Γ : Sig} → SortSym Γ → Type ℓI
  OpSym : Sig → Type
  opVar : {Γ : Sig} → OpSym Γ → Type ℓI
  opIx : {Γ : Sig} → OpSym Γ → Type ℓA

  Srt : (Γ : Sig) → Type ℓI → Type ℓI
  Tel : (Γ : Sig) → Type ℓI → Type ℓI

  opArgS : {Γ : Sig} (o : OpSym Γ) → opIx o → Srt Γ (opVar o)
  opRes : {Γ : Sig} (o : OpSym Γ) → Srt Γ (opVar o)

  Term : (Γ : Sig) {V : Type ℓI} (Θ : Tel Γ V) (I : Type ℓA)
    (as : I → Srt Γ V) → Srt Γ V → Type (ℓ-max ℓI ℓA)

  infixl 5 _▹_

  data Sig where
    ◇ : Sig
    _▹_ : (Γ : Sig) → Decl Γ → Sig

  data Decl Γ where
    -- a sort symbol with a telescope of index arguments
    sortD : (V : Type ℓI) (Θ : Tel Γ V) → Decl Γ
    -- an operation: index telescope `Θ`, argument family `as`, result
    -- sort `r`
    opD : (V : Type ℓI) (Θ : Tel Γ V) (I : Type ℓA) (as : I → Srt Γ V)
      (r : Srt Γ V) → Decl Γ
    -- an equation between two terms of a common sort
    eqnD : (V : Type ℓI) (Θ : Tel Γ V) (I : Type ℓA) (as : I → Srt Γ V)
      (r : Srt Γ V) (t u : Term Γ Θ I as r) → Decl Γ

  -- Weakening along a signature extension.  `sortIdx` and `opVar` are
  -- unchanged by `▹`, so this is a relabelling of symbols, never a
  -- transport.
  wkSrt : {Γ : Sig} {d : Decl Γ} {V : Type ℓI} → Srt Γ V → Srt (Γ ▹ d) V
  wkTel : {Γ : Sig} {d : Decl Γ} {V : Type ℓI} → Tel Γ V → Tel (Γ ▹ d) V

  Srt Γ = RawSorts.Srt (SortSym Γ) (λ S → sortIdx {Γ} S)
  Tel Γ = RawSorts.Tel (SortSym Γ) (λ S → sortIdx {Γ} S)
  Term Γ = RawTerms.Tm (SortSym Γ) (λ S → sortIdx {Γ} S)
    (OpSym Γ) (λ o → opVar {Γ} o) (λ o → opIx {Γ} o)
    (λ o → opArgS {Γ} o) (λ o → opRes {Γ} o)

  SortSym ◇ = ⊥
  SortSym (Γ ▹ sortD _ _) = SortSym Γ ⊎ Unit
  SortSym (Γ ▹ opD _ _ _ _ _) = SortSym Γ
  SortSym (Γ ▹ eqnD _ _ _ _ _ _ _) = SortSym Γ

  sortIdx {Γ ▹ sortD _ _} (inl S) = sortIdx {Γ} S
  sortIdx {Γ ▹ sortD V _} (inr _) = V
  sortIdx {Γ ▹ opD _ _ _ _ _} S = sortIdx {Γ} S
  sortIdx {Γ ▹ eqnD _ _ _ _ _ _ _} S = sortIdx {Γ} S

  OpSym ◇ = ⊥
  OpSym (Γ ▹ sortD _ _) = OpSym Γ
  OpSym (Γ ▹ opD _ _ _ _ _) = OpSym Γ ⊎ Unit
  OpSym (Γ ▹ eqnD _ _ _ _ _ _ _) = OpSym Γ

  opVar {Γ ▹ sortD _ _} o = opVar {Γ} o
  opVar {Γ ▹ opD _ _ _ _ _} (inl o) = opVar {Γ} o
  opVar {Γ ▹ opD V _ _ _ _} (inr _) = V
  opVar {Γ ▹ eqnD _ _ _ _ _ _ _} o = opVar {Γ} o

  opIx {Γ ▹ sortD _ _} o = opIx {Γ} o
  opIx {Γ ▹ opD _ _ _ _ _} (inl o) = opIx {Γ} o
  opIx {Γ ▹ opD _ _ I _ _} (inr _) = I
  opIx {Γ ▹ eqnD _ _ _ _ _ _ _} o = opIx {Γ} o

  wkSrt {d = sortD _ _} A = inl (A .fst) , A .snd
  wkSrt {d = opD _ _ _ _ _} A = A
  wkSrt {d = eqnD _ _ _ _ _ _ _} A = A

  wkTel {Γ} {d} Θ v = wkSrt {Γ} {d} (Θ v)

  opArgS {Γ ▹ sortD V Θ} o j = wkSrt {Γ} {sortD V Θ} (opArgS {Γ} o j)
  opArgS {Γ ▹ opD V Θ I as r} (inl o) j =
    wkSrt {Γ} {opD V Θ I as r} (opArgS {Γ} o j)
  opArgS {Γ ▹ opD _ _ _ as _} (inr _) j = as j
  opArgS {Γ ▹ eqnD V Θ I as r t u} o j =
    wkSrt {Γ} {eqnD V Θ I as r t u} (opArgS {Γ} o j)

  opRes {Γ ▹ sortD V Θ} o = wkSrt {Γ} {sortD V Θ} (opRes {Γ} o)
  opRes {Γ ▹ opD V Θ I as r} (inl o) =
    wkSrt {Γ} {opD V Θ I as r} (opRes {Γ} o)
  opRes {Γ ▹ opD _ _ _ _ r} (inr _) = r
  opRes {Γ ▹ eqnD V Θ I as r t u} o =
    wkSrt {Γ} {eqnD V Θ I as r t u} (opRes {Γ} o)

-- ------------------------------------------------------------------
-- Term constructors for a fixed signature
-- ------------------------------------------------------------------

module TermsOf {ℓI ℓA : Level} (Γ : Sig {ℓI} {ℓA}) where
  open RawTerms (SortSym Γ) (sortIdx {Γ = Γ}) (OpSym Γ)
    (opVar {Γ = Γ}) (opIx {Γ = Γ}) (opArgS {Γ = Γ}) (opRes {Γ = Γ})
    public

-- ------------------------------------------------------------------
-- The index telescopes of the declared symbols
-- ------------------------------------------------------------------

module _ {ℓI ℓA : Level} where

  sortTel : {Γ : Sig {ℓI} {ℓA}} (S : SortSym Γ) → Tel Γ (sortIdx {Γ = Γ} S)
  sortTel {Γ ▹ sortD V Θ} (inl S) =
    wkTel {Γ = Γ} {d = sortD V Θ} (sortTel {Γ = Γ} S)
  sortTel {Γ ▹ sortD V Θ} (inr _) = wkTel {Γ = Γ} {d = sortD V Θ} Θ
  sortTel {Γ ▹ opD V Θ I as r} S =
    wkTel {Γ = Γ} {d = opD V Θ I as r} (sortTel {Γ = Γ} S)
  sortTel {Γ ▹ eqnD V Θ I as r t u} S =
    wkTel {Γ = Γ} {d = eqnD V Θ I as r t u} (sortTel {Γ = Γ} S)

  opTel : {Γ : Sig {ℓI} {ℓA}} (o : OpSym Γ) → Tel Γ (opVar {Γ = Γ} o)
  opTel {Γ ▹ sortD V Θ} o = wkTel {Γ = Γ} {d = sortD V Θ} (opTel {Γ = Γ} o)
  opTel {Γ ▹ opD V Θ I as r} (inl o) =
    wkTel {Γ = Γ} {d = opD V Θ I as r} (opTel {Γ = Γ} o)
  opTel {Γ ▹ opD V Θ I as r} (inr _) = wkTel {Γ = Γ} {d = opD V Θ I as r} Θ
  opTel {Γ ▹ eqnD V Θ I as r t u} o =
    wkTel {Γ = Γ} {d = eqnD V Θ I as r t u} (opTel {Γ = Γ} o)

-- ------------------------------------------------------------------
-- Well-formedness
-- ------------------------------------------------------------------
--
-- A raw sort `(S , sp)` over `Θ` is well formed when the variable
-- supplied for each index of `S` really has the sort that index
-- demands.  Stated with `Eq._≡_`, so discharging it in a concrete
-- signature is `Eq.refl` and interpreting it is an `Eq.transport` that
-- computes away.

module _ {ℓI ℓA : Level} {Γ : Sig {ℓI} {ℓA}} where

  open RawSorts (SortSym Γ) (sortIdx {Γ = Γ}) using (_⟨_⟩) public

  wfSrt : {V : Type ℓI} (Θ : Tel Γ V) (A : Srt Γ V) → Type ℓI
  wfSrt Θ A = (i : sortIdx {Γ = Γ} (A .fst))
    → Θ (A .snd i) Eq.≡ sortTel {Γ = Γ} (A .fst) i ⟨ A .snd ⟩

  wfTel : {V : Type ℓI} (Θ : Tel Γ V) → Type ℓI
  wfTel {V} Θ = (v : V) → wfSrt Θ (Θ v)

  -- A variable map is a context morphism when it preserves sorts; this
  -- is what a term's `app` node needs of its index spine.
  wfRen : {V W : Type ℓI} (Θ : Tel Γ V) (Ξ : Tel Γ W)
    (ρ : W → V) → Type ℓI
  wfRen {W = W} Θ Ξ ρ = (w : W) → Θ (ρ w) Eq.≡ Ξ w ⟨ ρ ⟩
