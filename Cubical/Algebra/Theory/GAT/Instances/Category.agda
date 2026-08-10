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
  retype : {S T : Srt Γ₄ Bool} → S ≡ T
    → Term Γ₄ ΘL Unit Largs S → Term Γ₄ ΘL Unit Largs T
  retype = subst (Term Γ₄ ΘL Unit Largs)

  homPath : {sp sp' : Bool → Bool} → ((i : Bool) → sp i ≡ sp' i)
    → Path (Srt Γ₄ Bool) (Hom , sp) (Hom , sp')
  homPath h i = Hom , funExt h i

  ptwise : {sp sp' : Bool → Bool} → sp true ≡ sp' true → sp false ≡ sp' false
    → (i : Bool) → sp i ≡ sp' i
  ptwise p q true = p
  ptwise p q false = q

  -- `id a`, at the spine `_⋆_` demands of its first argument
  idA : Term Γ₄ ΘL Unit Largs (Hom , λ i → ρL (hm A B i))
  idA = retype (homPath (ptwise refl refl)) (app idOp (λ _ → true) (λ ()))

  -- `f`, at the spine `_⋆_` demands of its second argument
  fB : Term Γ₄ ΘL Unit Largs (Hom , λ i → ρL (hm B C i))
  fB = retype (homPath (ptwise refl refl)) (avar tt)

  -- the sort `Hom a b`, in the form the `_⋆_` node produces
  HomAB : Srt Γ₄ Bool
  HomAB = Hom , λ i → ρL (hm A C i)

  -- `id a ⋆ f : Hom a b`
  idA⋆f : Term Γ₄ ΘL Unit Largs HomAB
  idA⋆f = app ⋆Op ρL (λ { true → idA ; false → fB })

  fA : Term Γ₄ ΘL Unit Largs HomAB
  fA = retype (homPath (ptwise refl refl)) (avar tt)

-- ⋆IdL : (a b : Ob) (f : Hom a b) → id a ⋆ f ≡ f
Γ₅ : Sig {ℓ-zero} {ℓ-zero}
Γ₅ = Γ₄ ▹ eqnD Bool ΘL Unit Largs HomAB idA⋆f fA

-- ⋆IdR : (a b : Ob) (f : Hom a b) → f ⋆ id b ≡ f
private
  -- `_⋆_` at `a ↦ a`, `b ↦ b`, `c ↦ b`
  ρR : Thr → Bool
  ρR A = true
  ρR B = false
  ρR C = false

  -- `f`, at the spine `_⋆_` demands of its first argument
  fA' : Term Γ₄ ΘL Unit Largs (Hom , λ i → ρR (hm A B i))
  fA' = retype (homPath (ptwise refl refl)) (avar tt)

  -- `id b`, at the spine `_⋆_` demands of its second argument
  idB : Term Γ₄ ΘL Unit Largs (Hom , λ i → ρR (hm B C i))
  idB = retype (homPath (ptwise refl refl))
    (app idOp (λ _ → false) (λ ()))

  HomAB' : Srt Γ₄ Bool
  HomAB' = Hom , λ i → ρR (hm A C i)

  f⋆idB : Term Γ₄ ΘL Unit Largs HomAB'
  f⋆idB = app ⋆Op ρR (λ { true → fA' ; false → idB })

  fA'' : Term Γ₄ ΘL Unit Largs HomAB'
  fA'' = retype (homPath (ptwise refl refl)) (avar tt)

Γ₆ : Sig {ℓ-zero} {ℓ-zero}
Γ₆ = Γ₅ ▹ eqnD Bool ΘL Unit Largs HomAB' f⋆idB fA''

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

  retypeA : {S T : Srt Γ₆ Fou} → S ≡ T
    → Term Γ₆ ΘA Arg3 Aargs S → Term Γ₆ ΘA Arg3 Aargs T
  retypeA = subst (Term Γ₆ ΘA Arg3 Aargs)

  homPathA : {sp sp' : Bool → Fou} → ((i : Bool) → sp i ≡ sp' i)
    → Path (Srt Γ₆ Fou) (Hom , sp) (Hom , sp')
  homPathA h i = Hom , funExt h i

  ptwiseA : {sp sp' : Bool → Fou}
    → sp true ≡ sp' true → sp false ≡ sp' false → (i : Bool) → sp i ≡ sp' i
  ptwiseA p q true = p
  ptwiseA p q false = q

  -- the four instantiations of `_⋆_`
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

  -- (f ⋆ g) ⋆ h
  f⋆g : Term Γ₆ ΘA Arg3 Aargs (Hom , λ i → ρ₁ (hm A C i))
  f⋆g = appA ⋆Op ρ₁
    (λ { true → retypeA (homPathA (ptwiseA refl refl)) (avarA fv)
       ; false → retypeA (homPathA (ptwiseA refl refl)) (avarA gv) })

  AssocSrt : Srt Γ₆ Fou
  AssocSrt = Hom , λ i → ρ₂ (hm A C i)

  lhsA : Term Γ₆ ΘA Arg3 Aargs AssocSrt
  lhsA = appA ⋆Op ρ₂
    (λ { true → retypeA (homPathA (ptwiseA refl refl)) f⋆g
       ; false → retypeA (homPathA (ptwiseA refl refl)) (avarA hv) })

  -- f ⋆ (g ⋆ h)
  g⋆h : Term Γ₆ ΘA Arg3 Aargs (Hom , λ i → ρ₃ (hm A C i))
  g⋆h = appA ⋆Op ρ₃
    (λ { true → retypeA (homPathA (ptwiseA refl refl)) (avarA gv)
       ; false → retypeA (homPathA (ptwiseA refl refl)) (avarA hv) })

  rhsA : Term Γ₆ ΘA Arg3 Aargs AssocSrt
  rhsA = retypeA (homPathA (ptwiseA refl refl)) (appA ⋆Op ρ₄
    (λ { true → retypeA (homPathA (ptwiseA refl refl)) (avarA fv)
       ; false → retypeA (homPathA (ptwiseA refl refl)) g⋆h }))

CatSig : Sig {ℓ-zero} {ℓ-zero}
CatSig = Γ₆ ▹ eqnD Fou ΘA Arg3 Aargs AssocSrt lhsA rhsA

-- ------------------------------------------------------------------
-- `CatSig` is well formed
-- ------------------------------------------------------------------
--
-- The conditions on `Ob`-sorted variables are indexed by `sortIdx Ob =
-- ⊥`, hence vacuous.  The conditions on `Hom`-sorted variables are NOT
-- `Eq.refl`, though: they compare the spine `λ ()` with the spine
-- `λ k → ρ ((λ ()) k)`, two functions out of `⊥` which agree pointwise
-- but are not definitionally equal, because Agda has no eta for `⊥`.
-- They are discharged by `funExt` instead.  This is harmless -- the
-- resulting transports occur only inside `SrtC`, which is a
-- proposition, and `coeS-irr` says they do not depend on the proof --
-- but it does correct the claim that well-formedness is always
-- `Eq.refl`.

open import Cubical.Algebra.Theory.GAT.Model

-- `Ob`-sorted raw sorts differ only in a spine out of `⊥`
obSrt≡ : {D : Type} (f g : sortIdx {Γ = CatSig} Ob → D)
  → Path (Srt CatSig D) (Ob , f) (Ob , g)
obSrt≡ f g i = Ob , funExt {f = f} {g = g} (λ ()) i

-- The operation-level obligations, all discharged.
catWfSortTel : (S : SortSym CatSig)
  → wfTel {Γ = CatSig} (sortTel {Γ = CatSig} S)
catWfSortTel (inl (inr tt)) = λ ()
catWfSortTel (inr tt) = λ _ ()

catWfOpTel : (o : OpSym CatSig) → wfTel {Γ = CatSig} (opTel {Γ = CatSig} o)
catWfOpTel (inl (inr tt)) = λ _ ()
catWfOpTel (inr tt) = λ _ ()

catWfOpArg : (o : OpSym CatSig) (j : opIx {Γ = CatSig} o)
  → wfSrt {Γ = CatSig} (opTel {Γ = CatSig} o) (opArgS {Γ = CatSig} o j)
catWfOpArg (inl (inr tt)) ()
catWfOpArg (inr tt) true = λ _ → Eq.pathToEq (obSrt≡ _ _)
catWfOpArg (inr tt) false = λ _ → Eq.pathToEq (obSrt≡ _ _)

catWfOpRes : (o : OpSym CatSig)
  → wfSrt {Γ = CatSig} (opTel {Γ = CatSig} o) (opRes {Γ = CatSig} o)
catWfOpRes (inl (inr tt)) = λ _ → Eq.pathToEq (obSrt≡ _ _)
catWfOpRes (inr tt) = λ _ → Eq.pathToEq (obSrt≡ _ _)

-- NOT YET DISCHARGED: the equation-level obligations, and the blocker
-- is structural rather than incidental.
--
-- `wfTm` is defined by recursion on the term, but the terms above are
-- built with `retype`, i.e. `subst`, to bridge spines that agree
-- pointwise without agreeing definitionally.  A `subst`-wrapped term is
-- a `transp`, not a constructor, so `wfTm` gets stuck on it -- and so
-- would `eval`.  The bridges were forced by the same missing eta that
-- made `catWfOpArg` need `funExt`.
--
-- The fix is to stop deriving well-formedness by recursion and carry it
-- in the syntax: give `RawTerms` the operation telescope as a further
-- parameter, so that `app` can store its own `wfRen` proof.  `wfRen`
-- needs only reindexing, not `sortTel`, so this does not enlarge the
-- mutual block.  `wfTm` then disappears.  `eval` would still be stuck
-- on a substituted term, which is the remaining reason to want spines
-- that compare definitionally.
