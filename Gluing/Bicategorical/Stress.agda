{-# OPTIONS --lossy-unification #-}
{-
  Stress tests for the normalizer of
  `Gluing.Bicategorical.RecNormalization`: Church arithmetic in the
  free cartesian closed category over the walking-arrow quiver,
  culminating in Church-encoded Fibonacci.

  Every check compares a COMPUTED normal form against a written-out
  LITERAL.  Comparing two computed normal forms to each other forces
  the glue on both sides and is known not to terminate, which is also
  why `solveCCC!` is not used here.

  MEASUREMENTS.  Wall clock for `agda +RTS -M16G` on a warm build,
  one check per run; `base` is this file with every check deleted,
  and it is what the import graph alone costs.  MUT/GC/res are the
  GHC runtime's mutator time, collector time and peak residency.

  Every row is a STRUCTURAL check, `nf f ≡ literal`, except the one
  row marked `size`; see the paragraph below for what that is and
  why it is weaker.

    check                          wall     MUT     GC    max res
    base (imports only)             4.0s    3.0s   0.7s    0.6 GB
    numerals c0 c3 c5               4.3s      --     --        --
    add 2 3 = 5                     4.6s      --     --        --
    mul 2 3 = 6                     4.7s      --     --        --
    twice ⋆ twice = four            4.6s      --     --        --
    c 1597                          5.7s    3.9s   1.5s    0.8 GB
    add 800 797 = 1597              5.5s    3.9s   1.5s    0.8 GB
    mul 40 40 = 1600                5.6s    4.0s   1.5s    0.8 GB
    swap-iterate 17 at N × N        3.9s    3.1s   0.7s    0.6 GB
    fib 10 = 55                     5.1s      --     --        --
    fib 12 = 144                    5.8s    3.5s   1.8s    1.5 GB
    fib 14 = 377                    7.1s    4.1s   2.8s    1.5 GB
    fib 15 = 610                   11.8s    5.5s   5.1s    2.9 GB
    fib 15, size only     (size)    9.6s    5.0s   4.0s    2.7 GB
    fib 16 = 987                   27.5s   10.6s  10.7s    5.7 GB
    fib 17 = 1597                  32.1s   12.1s  12.9s    5.6 GB
    fib 18 = 2584                 111.7s      --     --        --
    fib 19 = 4181                 >600s (killed)

  WHAT IS SLOW.  Not the conversion checker.  The instrument is a
  size comparison: `sizeNf (nf (fib 15)) ≡ sizeNf (nfCh 610)` forces
  exactly the same normal form but then compares two natural
  numbers instead of two type-indexed trees.  Its mutator time is
  unchanged, 5.0s against 5.5s, so the tree comparison contributes
  nothing and all of the cost is evaluating `normalize`.

  A size comparison is STRICTLY WEAKER than structural equality --
  distinct normal forms can have the same size -- so it is used only
  as an instrument and never as the statement of an arithmetic fact.
  Every arithmetic claim in the table and in this file is checked
  structurally.

  Nor is it the size of the ANSWER, and nor is it the depth of
  `reify`: a numeral with 1597 applications costs 1.4s over base
  whether it is written out, added or multiplied, and iterating a
  non-growing function 17 times at the pair type `N × N` -- which
  drives `reify` and `reflect` at a product of function types -- is
  free.  What costs is the total number of normal-form nodes built
  ACROSS the computation: `fib k` builds about `fib (k+2)` of them,
  at roughly 1 MB of peak residency each.

  Past about 2000 nodes that residency is what ends the run: at
  `fib 17` the collector takes 24s of the 32s elapsed, with a 9.5s
  maximum pause, at 45% productivity.  Nothing is stuck -- every
  definition reduces and the mutator time itself grows about
  linearly in the node count -- the normalizer is retaining a
  megabyte of glue per node it emits.

  Only the checks that run in about a second over base are kept
  below -- `fib 10` is the last rung in the file -- since this file
  is rebuilt by every `make check`.  Everything from `fib 12` up was
  measured and removed.
-}
module Gluing.Bicategorical.Stress where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Sum
open import Cubical.Data.Unit

open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.CartesianClosed.Base

open import
  Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
  using (↑_ ; CCCExpr)
open CCCExpr renaming (_×_ to _×ᵗ_ ; ⊤ to ⊤ᵗ ; _⇒_ to _⇒ᵗ_)

open import Gluing.Bicategorical.NormalForms
open import Gluing.Bicategorical.RecNormalization
  using (Q ; isSetOb ; isSetMor ; T ; normalize)

open NF Q isSetOb

private
  module 𝒞 = CartesianClosedCategory FREECCC

  Tob : Ty → Ty
  Tob = Functor.F-ob (T Q isSetOb isSetMor)

  nf : {A B : Ty} → 𝒞.Hom[ A , B ] → Nf (Tob A ∷ []) (Tob B)
  nf = normalize Q isSetOb isSetMor

  infixl 8 _·ₐ_
  _·ₐ_ : {Γ A B : Ty} → 𝒞.Hom[ Γ , A ⇒ᵗ B ] → 𝒞.Hom[ Γ , A ]
      → 𝒞.Hom[ Γ , B ]
  u ·ₐ v = 𝒞._,p_ u v 𝒞.⋆ 𝒞.app

  X : Ty
  X = ↑ tt

--------------------------------------------------------------------
-- Church numerals, generic in the type they iterate at: a numeral
-- is a global element, `⊤ → (P ⇒ P) ⇒ (P ⇒ P)`.
--------------------------------------------------------------------

  module Num (P : Ty) where
    Nm : Ty
    Nm = (P ⇒ᵗ P) ⇒ᵗ (P ⇒ᵗ P)

    Γ₂ : Ty
    Γ₂ = (⊤ᵗ ×ᵗ (P ⇒ᵗ P)) ×ᵗ P

    fv : 𝒞.Hom[ Γ₂ , P ⇒ᵗ P ]
    fv = 𝒞.π₁ 𝒞.⋆ 𝒞.π₂

    xv : 𝒞.Hom[ Γ₂ , P ]
    xv = 𝒞.π₂

    itr : ℕ → 𝒞.Hom[ Γ₂ , P ]
    itr zero = xv
    itr (suc n) = fv ·ₐ itr n

    ch : ℕ → 𝒞.Hom[ ⊤ᵗ , Nm ]
    ch n = 𝒞.lda (𝒞.lda (itr n))

  N : Ty
  N = Num.Nm X

  c : ℕ → 𝒞.Hom[ ⊤ᵗ , N ]
  c = Num.ch X

  -- the literal normal forms: `\f. \x. f (f (... x))`
  nfIter : ℕ → Nf (X ∷ (X ⇒ᵗ X) ∷ ⊤ᵗ ∷ []) X
  nfIter zero = ne (var (inl refl))
  nfIter (suc n) = ne (appₙ (var (inr (inl refl))) (nfIter n))

  nfCh : ℕ → Nf (⊤ᵗ ∷ []) N
  nfCh n = lamₙ (lamₙ (nfIter n))

  -- RUNG 1: the numerals themselves.
  _ : nf (c 0) ≡ nfCh 0
  _ = refl

  _ : nf (c 3) ≡ nfCh 3
  _ = refl

  _ : nf (c 5) ≡ nfCh 5
  _ = refl

--------------------------------------------------------------------
-- RUNG 2: addition.  `add m n = \f. \x. m f (n f x)`.
--------------------------------------------------------------------

  Γa : Ty
  Γa = ((N ×ᵗ N) ×ᵗ (X ⇒ᵗ X)) ×ᵗ X

  mv : 𝒞.Hom[ Γa , N ]
  mv = 𝒞.π₁ 𝒞.⋆ 𝒞.π₁ 𝒞.⋆ 𝒞.π₁

  nv : 𝒞.Hom[ Γa , N ]
  nv = 𝒞.π₁ 𝒞.⋆ 𝒞.π₁ 𝒞.⋆ 𝒞.π₂

  fa : 𝒞.Hom[ Γa , X ⇒ᵗ X ]
  fa = 𝒞.π₁ 𝒞.⋆ 𝒞.π₂

  xa : 𝒞.Hom[ Γa , X ]
  xa = 𝒞.π₂

  add : 𝒞.Hom[ N ×ᵗ N , N ]
  add = 𝒞.lda (𝒞.lda (mv ·ₐ fa ·ₐ (nv ·ₐ fa ·ₐ xa)))

  addT : ℕ → ℕ → 𝒞.Hom[ ⊤ᵗ , N ]
  addT m n = 𝒞._,p_ (c m) (c n) 𝒞.⋆ add

  _ : nf (addT 2 3) ≡ nfCh 5
  _ = refl

--------------------------------------------------------------------
-- RUNG 3: multiplication.  `mul m n = \f. \x. m (n f) x`.
--------------------------------------------------------------------

  mul : 𝒞.Hom[ N ×ᵗ N , N ]
  mul = 𝒞.lda (𝒞.lda (mv ·ₐ (nv ·ₐ fa) ·ₐ xa))

  mulT : ℕ → ℕ → 𝒞.Hom[ ⊤ᵗ , N ]
  mulT m n = 𝒞._,p_ (c m) (c n) 𝒞.⋆ mul

  _ : nf (mulT 2 3) ≡ nfCh 6
  _ = refl

--------------------------------------------------------------------
-- The `RecNormalization` formulation, for calibration: numerals as
-- endomorphisms of `X ⇒ X`, so the domain is higher order and the
-- initial environment must be reflected at an arrow type.  Costs the
-- same as the closed formulation above.
--------------------------------------------------------------------

  Γe : Ty
  Γe = (X ⇒ᵗ X) ×ᵗ X

  itrE : ℕ → 𝒞.Hom[ Γe , X ]
  itrE zero = 𝒞.π₂
  itrE (suc n) = 𝒞.π₁ ·ₐ itrE n

  chE : ℕ → 𝒞.Hom[ X ⇒ᵗ X , X ⇒ᵗ X ]
  chE n = 𝒞.lda (itrE n)

  nfE : ℕ → Nf ((X ⇒ᵗ X) ∷ []) (X ⇒ᵗ X)
  nfE n = lamₙ (go n) where
    go : ℕ → Nf (X ∷ (X ⇒ᵗ X) ∷ []) X
    go zero = ne (var (inl refl))
    go (suc k) = ne (appₙ (var (inr (inl refl))) (go k))

  _ : nf (chE 2 𝒞.⋆ chE 2) ≡ nfE 4
  _ = refl

--------------------------------------------------------------------
-- RUNG 4: Fibonacci by pair iteration.  The numeral is taken at the
-- PAIR type `N × N`, which a simply typed CCC allows.  `fib k`
-- normalizes to the numeral `fib k`, so the answer has `fib k`
-- applications and the computation builds about `fib (k+2)` nodes.
--------------------------------------------------------------------

  P : Ty
  P = N ×ᵗ N

  step : 𝒞.Hom[ ⊤ᵗ , P ⇒ᵗ P ]
  step = 𝒞.lda (𝒞._,p_ (pv 𝒞.⋆ 𝒞.π₂) (pv 𝒞.⋆ add)) where
    pv : 𝒞.Hom[ ⊤ᵗ ×ᵗ P , P ]
    pv = 𝒞.π₂

  start : 𝒞.Hom[ ⊤ᵗ , P ]
  start = 𝒞._,p_ (c 0) (c 1)

  fib : ℕ → 𝒞.Hom[ ⊤ᵗ , N ]
  fib k = (Num.ch P k ·ₐ step ·ₐ start) 𝒞.⋆ 𝒞.π₁

  _ : nf (fib 5) ≡ nfCh 5
  _ = refl

  _ : nf (fib 10) ≡ nfCh 55
  _ = refl

--------------------------------------------------------------------
-- Iterating a NON-growing function at the same pair type, to show
-- that the depth of `reify` is not what costs: seventeen swaps are
-- free where seventeen Fibonacci steps are not.
--------------------------------------------------------------------

  swapP : 𝒞.Hom[ ⊤ᵗ , P ⇒ᵗ P ]
  swapP = 𝒞.lda (𝒞._,p_ (pv 𝒞.⋆ 𝒞.π₂) (pv 𝒞.⋆ 𝒞.π₁)) where
    pv : 𝒞.Hom[ ⊤ᵗ ×ᵗ P , P ]
    pv = 𝒞.π₂

  _ : nf ((Num.ch P 17 ·ₐ swapP ·ₐ start) 𝒞.⋆ 𝒞.π₁) ≡ nfCh 1
  _ = refl

--------------------------------------------------------------------
-- The size of a normal form, used to separate the normalizer from
-- the conversion checker: `sizeNf (nf f) ≡ sizeNf lit` forces the
-- whole normal form but compares two numerals, not two indexed
-- trees, and costs the same.
--------------------------------------------------------------------

  sizeNe : {Γ : Ctx} {A : Ty} → Ne Γ A → ℕ
  sizeNf : {Γ : Ctx} {A : Ty} → Nf Γ A → ℕ

  sizeNe (var _) = 1
  sizeNe (appₙ n m) = suc (sizeNe n + sizeNf m)
  sizeNe (π₁ₙ n) = suc (sizeNe n)
  sizeNe (π₂ₙ n) = suc (sizeNe n)
  sizeNe (genₙ _ m) = suc (sizeNf m)

  sizeNf (ne n) = sizeNe n
  sizeNf ttₙ = 1
  sizeNf (pairₙ m₁ m₂) = suc (sizeNf m₁ + sizeNf m₂)
  sizeNf (lamₙ m) = suc (sizeNf m)

  -- WEAKER than the structural check of `fib 10` above, which is
  -- what actually certifies the arithmetic; this one only measures.
  _ : sizeNf (nf (fib 10)) ≡ sizeNf (nfCh 55)
  _ = refl
