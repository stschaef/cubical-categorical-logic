{-# OPTIONS --lossy-unification #-}
-- Models of a generalized algebraic theory, and the category they form.
--
-- The tower is the one `Cubical.Algebra.Theory.Sorted` builds, with one
-- new layer:
--
--     FAM (SortSym Γ)  →  PRᴰ  →  ALGᴰ  (→ EQNSᴰ)
--
-- `FAM` is reused verbatim: a carrier is still a family of sets indexed
-- by the sort *symbols*.  What is new is `PRᴰ`, the layer of *display
-- maps* -- for each symbol `S` and each index `i` of `S`, a projection
-- `⟨X S⟩ → ⟨X (sortTel S i .fst)⟩`.  Dependency is carried by these
-- projections rather than by indexing the carrier, which is what lets
-- the whole tower stay flat: no environment is ever built by recursion
-- over a telescope, so telescopes need no order and index arities may
-- be arbitrary types.
--
-- Operations are then total on their honest domain: `_⋆_` takes `f`,
-- `g` *and a proof that they are composable*, so there are no junk
-- values and a homomorphism is exactly a functor.  The compatibility
-- proof is what would ordinarily break strictness -- composing two
-- homomorphisms has to name a middle compatibility proof, and the two
-- bracketings of `⋆Assocᴰ` would build it differently.  The fix is the
-- one `Sorted.Theories` uses for sort coherences: carry the *pushing*
-- of compatibility as a field of the homomorphism (`push`) rather than
-- deriving it.  Composition then composes pushes by function
-- composition, so `⋆IdLᴰ`, `⋆IdRᴰ` and `⋆Assocᴰ` are all `refl`.
-- Carrying it costs nothing: `SrtC` is a proposition, so `push` is
-- determined, and `pushOf` below constructs it from the ordinary
-- projection-preservation condition.
module Cubical.Algebra.Theory.GAT.Model where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty using (isProp⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Sum.Properties using (isSet⊎)
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Displayed.Instances.TotalCategory

open import Cubical.Algebra.Theory.Sorted using (FAM)
open import Cubical.Algebra.Theory.GAT.Signature

-- ------------------------------------------------------------------
-- Sort symbols form a set
-- ------------------------------------------------------------------
--
-- Needed because `SrtC` is stated with a transport along a
-- well-formedness proof: two proofs of the same sort equation must
-- induce the same transport, or a term could not be re-typed at the
-- well-formedness proof its context demands.

isSetSortSym : {ℓI ℓA : Level} (Γ : Sig {ℓI} {ℓA}) → isSet (SortSym Γ)
isSetSortSym ◇ = isProp→isSet isProp⊥
isSetSortSym (Γ ▹ sortD _ _) = isSet⊎ (isSetSortSym Γ) isSetUnit
isSetSortSym (Γ ▹ opD _ _ _ _ _ _ _) = isSetSortSym Γ
isSetSortSym (Γ ▹ eqnD _ _ _ _ _ _ _) = isSetSortSym Γ

module _ {ℓI ℓA : Level} (Γ : Sig {ℓI} {ℓA}) where

  private
    ix : SortSym Γ → Type ℓI
    ix = sortIdx {Γ = Γ}

    ST : (S : SortSym Γ) → Tel Γ (ix S)
    ST = sortTel {Γ = Γ}

    OT : (o : OpSym Γ) → Tel Γ (opVar {Γ = Γ} o)
    OT = opTel {Γ = Γ}

    ET : (e : EqnSym Γ) → Tel Γ (eqnVar {Γ = Γ} e)
    ET = eqnTel {Γ = Γ}

    module S = TermsOf Γ

  -- ----------------------------------------------------------------
  -- Well-formedness of a signature
  -- ----------------------------------------------------------------

  record Wf : Type (ℓ-max ℓI ℓA) where
    field
      wfSortTel : (S : SortSym Γ) → wfTel {Γ = Γ} (ST S)
      wfOpTel : (o : OpSym Γ) → wfTel {Γ = Γ} (OT o)
      wfOpArg : (o : OpSym Γ) (j : opIx {Γ = Γ} o)
        → wfSrt {Γ = Γ} (OT o) (opArgS {Γ = Γ} o j)
      wfOpRes : (o : OpSym Γ)
        → wfSrt {Γ = Γ} (OT o) (opRes {Γ = Γ} o)
      wfEqnTel : (e : EqnSym Γ) → wfTel {Γ = Γ} (ET e)
      wfEqnArg : (e : EqnSym Γ) (j : eqnIx {Γ = Γ} e)
        → wfSrt {Γ = Γ} (ET e) (eqnArgS {Γ = Γ} e j)
      wfEqnRes : (e : EqnSym Γ)
        → wfSrt {Γ = Γ} (ET e) (eqnRes {Γ = Γ} e)
      wfEqnLhs : (e : EqnSym Γ)
        → wfTm {Γ = Γ} (ET e) (eqnLhs {Γ = Γ} e)
      wfEqnRhs : (e : EqnSym Γ)
        → wfTm {Γ = Γ} (ET e) (eqnRhs {Γ = Γ} e)

  open Wf

  module _ (wf : Wf) (ℓX : Level) where

    -- --------------------------------------------------------------
    -- Carriers: `FAM` on the sort symbols, unchanged from `Sorted`
    -- --------------------------------------------------------------

    CAR : Category (ℓ-suc ℓX) ℓX
    CAR = FAM (SortSym Γ) ℓX

    private
      Ob* = Category.ob CAR

      Hom* : Ob* → Ob* → Type ℓX
      Hom* X Y = Category.Hom[_,_] CAR X Y

    Car : Ob* → SortSym Γ → Type ℓX
    Car X S = ⟨ X S ⟩

    -- Transport along a well-formedness proof.  `Eq.refl` in every
    -- concrete signature, so this is the identity on the nose there.
    coeS : (X : Ob*) {V : Type ℓI} {A B : Srt Γ V}
      → A Eq.≡ B → Car X (A .fst) → Car X (B .fst)
    coeS X p = Eq.transport (λ A → Car X (A .fst)) p

    -- --------------------------------------------------------------
    -- Display maps, and the compatibility they induce
    -- --------------------------------------------------------------

    Prs : Ob* → Type (ℓ-max ℓI ℓX)
    Prs X = (S : SortSym Γ) (i : ix S) → Car X S → Car X (ST S i .fst)

    -- `a` sits over the environment `γ` at the sort `A`: each
    -- projection of `a` is the element `A`'s spine names for it.
    SrtC : (X : Ob*) (pr : Prs X) {V : Type ℓI}
      (Θ : Tel Γ V) (A : Srt Γ V) (wA : wfSrt {Γ = Γ} Θ A)
      (γ : (v : V) → Car X (Θ v .fst)) (a : Car X (A .fst))
      → Type (ℓ-max ℓI ℓX)
    SrtC X pr Θ A wA γ a = (i : ix (A .fst))
      → coeS X (wA i) (γ (A .snd i)) ≡ pr (A .fst) i a

    isPropSrtC : (X : Ob*) (pr : Prs X) {V : Type ℓI}
      (Θ : Tel Γ V) (A : Srt Γ V) (wA : wfSrt {Γ = Γ} Θ A)
      (γ : (v : V) → Car X (Θ v .fst)) (a : Car X (A .fst))
      → isProp (SrtC X pr Θ A wA γ a)
    isPropSrtC X pr Θ A wA γ a p q k i =
      X (ST (A .fst) i .fst) .snd
        (coeS X (wA i) (γ (A .snd i))) (pr (A .fst) i a)
        (p i) (q i) k

    EnvC : (X : Ob*) (pr : Prs X) {V : Type ℓI}
      (Θ : Tel Γ V) (w : wfTel {Γ = Γ} Θ)
      (γ : (v : V) → Car X (Θ v .fst)) → Type (ℓ-max ℓI ℓX)
    EnvC X pr {V} Θ w γ = (v : V) → SrtC X pr Θ (Θ v) (w v) γ (γ v)

    -- --------------------------------------------------------------
    -- The layer of display maps
    -- --------------------------------------------------------------

    -- The ordinary homomorphism condition on display maps, forded in
    -- the style of `Sorted`'s `ALGᴰ`.
    PresPr : (X Y : Ob*) (f : Hom* X Y) (pr : Prs X) (pr' : Prs Y)
      → Type (ℓ-max ℓI ℓX)
    PresPr X Y f pr pr' = (S : SortSym Γ) (i : ix S)
      (x : Car X S) (y : Car X (ST S i .fst)) → y ≡ pr S i x
      → f (ST S i .fst) y ≡ pr' S i (f S x)

    -- The pushing of compatibility, carried as data so that
    -- composition is composition of functions.
    Push : (X Y : Ob*) (f : Hom* X Y) (pr : Prs X) (pr' : Prs Y)
      → Type (ℓ-max (ℓ-suc ℓI) ℓX)
    Push X Y f pr pr' = {V : Type ℓI} (Θ : Tel Γ V) (A : Srt Γ V)
      (wA : wfSrt {Γ = Γ} Θ A)
      (γ : (v : V) → Car X (Θ v .fst)) (a : Car X (A .fst))
      → SrtC X pr Θ A wA γ a
      → SrtC Y pr' Θ A wA (λ v → f (Θ v .fst) (γ v)) (f (A .fst) a)

    -- `coeS` is natural in the family map, so `Push` is not extra
    -- information: it is derivable from `PresPr`.  Carrying it anyway
    -- is what makes composition strict.
    private
      coeS-nat : (X Y : Ob*) (f : Hom* X Y)
        {V : Type ℓI} {A B : Srt Γ V} (p : A Eq.≡ B)
        (z : Car X (A .fst))
        → coeS Y p (f (A .fst) z) ≡ f (B .fst) (coeS X p z)
      coeS-nat X Y f Eq.refl z = refl

    pushOf : (X Y : Ob*) (f : Hom* X Y) (pr : Prs X) (pr' : Prs Y)
      → PresPr X Y f pr pr' → Push X Y f pr pr'
    pushOf X Y f pr pr' P Θ A wA γ a c i =
      coeS-nat X Y f (wA i) (γ (A .snd i))
      ∙ P (A .fst) i a (coeS X (wA i) (γ (A .snd i))) (c i)

    PRᴰ : Categoryᴰ CAR (ℓ-max ℓI ℓX) (ℓ-max (ℓ-suc ℓI) ℓX)
    PRᴰ .Categoryᴰ.ob[_] X =
      Σ[ pr ∈ Prs X ] ((S : SortSym Γ) (x : Car X S)
        → EnvC X pr (ST S) (wf .wfSortTel S) (λ i → pr S i x))
    PRᴰ .Categoryᴰ.Hom[_][_,_] {x = X} {y = Y} f prc prc' =
      PresPr X Y f (prc .fst) (prc' .fst)
      × Push X Y f (prc .fst) (prc' .fst)
    PRᴰ .Categoryᴰ.idᴰ = (λ S i x y eq → eq) , (λ Θ A wA γ a c → c)
    PRᴰ .Categoryᴰ._⋆ᴰ_ {f = f} (P , p) (Q , q) =
      (λ S i x y eq → Q S i (f S x) (f (ST S i .fst) y) (P S i x y eq))
      , (λ Θ A wA γ a c →
          q Θ A wA (λ v → f (Θ v .fst) (γ v)) (f (A .fst) a)
            (p Θ A wA γ a c))
    PRᴰ .Categoryᴰ.⋆IdLᴰ _ = refl
    PRᴰ .Categoryᴰ.⋆IdRᴰ _ = refl
    PRᴰ .Categoryᴰ.⋆Assocᴰ _ _ _ = refl
    PRᴰ .Categoryᴰ.isSetHomᴰ {x = X} {y = Y} {f = f}
      {xᴰ = prc} {yᴰ = prc'} = isProp→isSet isPropHom
      where
      isPropPres : isProp (PresPr X Y f (prc .fst) (prc' .fst))
      isPropPres p q k S j x y eq = Y (ST S j .fst) .snd
        (f (ST S j .fst) y) (prc' .fst S j (f S x)) (p S j x y eq)
        (q S j x y eq) k

      isPropPush : isProp (Push X Y f (prc .fst) (prc' .fst))
      isPropPush p q k Θ A wA γ a c =
        isPropSrtC Y (prc' .fst) Θ A wA (λ v → f (Θ v .fst) (γ v))
          (f (A .fst) a) (p Θ A wA γ a c) (q Θ A wA γ a c) k

      isPropHom : isProp (PresPr X Y f (prc .fst) (prc' .fst)
        × Push X Y f (prc .fst) (prc' .fst))
      isPropHom u v k =
        isPropPres (u .fst) (v .fst) k , isPropPush (u .snd) (v .snd) k

    PR : Category _ _
    PR = ∫C PRᴰ

    -- --------------------------------------------------------------
    -- The layer of operations
    -- --------------------------------------------------------------
    --
    -- An operation takes an environment for its index telescope, the
    -- arguments, and *proofs that they fit together* -- `_⋆_` takes
    -- `f`, `g` and the compatibility of `cod f` with `dom g`.  So it is
    -- total on its honest domain and there are no junk values.

    Env : (X : Ob*) (o : OpSym Γ) → Type (ℓ-max ℓI ℓX)
    Env X o = (v : opVar {Γ = Γ} o) → Car X (OT o v .fst)

    Args : (X : Ob*) (o : OpSym Γ) → Type (ℓ-max ℓA ℓX)
    Args X o = (j : opIx {Γ = Γ} o) → Car X (opArgS {Γ = Γ} o j .fst)

    ArgsC : (X : Ob*) (pr : Prs X) (o : OpSym Γ) (γ : Env X o)
      (x : Args X o) → Type (ℓ-max (ℓ-max ℓI ℓA) ℓX)
    ArgsC X pr o γ x = (j : opIx {Γ = Γ} o)
      → SrtC X pr (OT o) (opArgS {Γ = Γ} o j) (wf .wfOpArg o j) γ (x j)

    private
      Ob** = Category.ob PR

      car : Ob** → Ob*
      car M = M .fst

      prs : (M : Ob**) → Prs (car M)
      prs M = M .snd .fst

    Ops : (M : Ob**) → Type (ℓ-max (ℓ-max ℓI ℓA) ℓX)
    Ops M = (o : OpSym Γ) (γ : Env (car M) o)
      (cγ : EnvC (car M) (prs M) (OT o) (wf .wfOpTel o) γ)
      (x : Args (car M) o) (cx : ArgsC (car M) (prs M) o γ x)
      → Car (car M) (opRes {Γ = Γ} o .fst)

    -- the result of an operation sits at the result sort
    OpsTyped : (M : Ob**) (α : Ops M) → Type (ℓ-max (ℓ-max ℓI ℓA) ℓX)
    OpsTyped M α = (o : OpSym Γ) (γ : Env (car M) o)
      (cγ : EnvC (car M) (prs M) (OT o) (wf .wfOpTel o) γ)
      (x : Args (car M) o) (cx : ArgsC (car M) (prs M) o γ x)
      → SrtC (car M) (prs M) (OT o) (opRes {Γ = Γ} o) (wf .wfOpRes o) γ
          (α o γ cγ x cx)

    -- the pushes of an environment and of an argument tuple along a
    -- homomorphism; both are the hom's own `push`, so they compose by
    -- composition of functions
    module _ {M N : Ob**} (h : Category.Hom[_,_] PR M N) where
      private
        f = h .fst
        pu = h .snd .snd

      pushEnv : (o : OpSym Γ) (γ : Env (car M) o)
        → EnvC (car M) (prs M) (OT o) (wf .wfOpTel o) γ
        → EnvC (car N) (prs N) (OT o) (wf .wfOpTel o)
            (λ v → f (OT o v .fst) (γ v))
      pushEnv o γ cγ v =
        pu (OT o) (OT o v) (wf .wfOpTel o v) γ (γ v) (cγ v)

      pushArgs : (o : OpSym Γ) (γ : Env (car M) o) (x : Args (car M) o)
        → ArgsC (car M) (prs M) o γ x
        → ArgsC (car N) (prs N) o (λ v → f (OT o v .fst) (γ v))
            (λ j → f (opArgS {Γ = Γ} o j .fst) (x j))
      pushArgs o γ x cx j =
        pu (OT o) (opArgS {Γ = Γ} o j) (wf .wfOpArg o j) γ (x j) (cx j)

    ALGᴰ : Categoryᴰ PR (ℓ-max (ℓ-max ℓI ℓA) ℓX)
      (ℓ-max (ℓ-max ℓI ℓA) ℓX)
    ALGᴰ .Categoryᴰ.ob[_] M = Σ[ α ∈ Ops M ] OpsTyped M α
    ALGᴰ .Categoryᴰ.Hom[_][_,_] {x = M} {y = N} h αc βc =
      (o : OpSym Γ) (γ : Env (car M) o)
      (cγ : EnvC (car M) (prs M) (OT o) (wf .wfOpTel o) γ)
      (x : Args (car M) o) (cx : ArgsC (car M) (prs M) o γ x)
      (y : Car (car M) (opRes {Γ = Γ} o .fst))
      → y ≡ αc .fst o γ cγ x cx
      → h .fst (opRes {Γ = Γ} o .fst) y
        ≡ βc .fst o (λ v → h .fst (OT o v .fst) (γ v)) (pushEnv h o γ cγ)
            (λ j → h .fst (opArgS {Γ = Γ} o j .fst) (x j))
            (pushArgs h o γ x cx)
    ALGᴰ .Categoryᴰ.idᴰ o γ cγ x cx y eq = eq
    ALGᴰ .Categoryᴰ._⋆ᴰ_ {f = h} Φ Ψ o γ cγ x cx y eq =
      Ψ o (λ v → h .fst (OT o v .fst) (γ v)) (pushEnv h o γ cγ)
        (λ j → h .fst (opArgS {Γ = Γ} o j .fst) (x j))
        (pushArgs h o γ x cx)
        (h .fst (opRes {Γ = Γ} o .fst) y) (Φ o γ cγ x cx y eq)
    ALGᴰ .Categoryᴰ.⋆IdLᴰ _ = refl
    ALGᴰ .Categoryᴰ.⋆IdRᴰ _ = refl
    ALGᴰ .Categoryᴰ.⋆Assocᴰ _ _ _ = refl
    ALGᴰ .Categoryᴰ.isSetHomᴰ {y = N} {f = h} {yᴰ = βc} =
      isProp→isSet (λ p q k o γ cγ x cx y eq →
        car N (opRes {Γ = Γ} o .fst) .snd
          (h .fst (opRes {Γ = Γ} o .fst) y)
          (βc .fst o (λ v → h .fst (OT o v .fst) (γ v))
            (pushEnv h o γ cγ)
            (λ j → h .fst (opArgS {Γ = Γ} o j .fst) (x j))
            (pushArgs h o γ x cx))
          (p o γ cγ x cx y eq) (q o γ cγ x cx y eq) k)

    -- the category of models of the signature, ignoring its equations
    ALG : Category _ _
    ALG = ∫C (∫Cᴰ PRᴰ ALGᴰ)

    -- --------------------------------------------------------------
    -- The category laws of `ALG` are definitional
    -- --------------------------------------------------------------
    --
    -- Both displayed layers have `refl` laws and `FAM`'s are `refl`,
    -- so the total category's are too.  This is the point of carrying
    -- `push` as data: with compatibility pushed by a derived function
    -- instead, `⋆Assoc` would only hold propositionally.

    private
      module A = Category ALG

    ALG⋆IdL : {M N : A.ob} (h : A.Hom[ M , N ]) → A.id A.⋆ h ≡ h
    ALG⋆IdL h = refl

    ALG⋆IdR : {M N : A.ob} (h : A.Hom[ M , N ]) → h A.⋆ A.id ≡ h
    ALG⋆IdR h = refl

    ALG⋆Assoc : {M N O P : A.ob} (h : A.Hom[ M , N ]) (k : A.Hom[ N , O ])
      (l : A.Hom[ O , P ]) → (h A.⋆ k) A.⋆ l ≡ h A.⋆ (k A.⋆ l)
    ALG⋆Assoc h k l = refl

    -- --------------------------------------------------------------
    -- Re-typing a compatibility proof
    -- --------------------------------------------------------------

    private
      coeSym : (X : Ob*) {S T : SortSym Γ} → S Eq.≡ T → Car X S → Car X T
      coeSym X p = Eq.transport (λ S → Car X S) p

      coeS-sym : (X : Ob*) {V : Type ℓI} {A B : Srt Γ V} (p : A Eq.≡ B)
        (z : Car X (A .fst))
        → coeS X p z ≡ coeSym X (Eq.ap fst p) z
      coeS-sym X Eq.refl z = refl

      isPropEqSym : {S T : SortSym Γ} → isProp (S Eq.≡ T)
      isPropEqSym {S} {T} p q =
        sym (Eq.pathToEq-eqToPath p)
        ∙ cong Eq.pathToEq
            (isSetSortSym Γ S T (Eq.eqToPath p) (Eq.eqToPath q))
        ∙ Eq.pathToEq-eqToPath q

    -- transports along a sort equation do not depend on its proof
    coeS-irr : (X : Ob*) {V : Type ℓI} {A B : Srt Γ V}
      (p q : A Eq.≡ B) (z : Car X (A .fst)) → coeS X p z ≡ coeS X q z
    coeS-irr X p q z = coeS-sym X p z
      ∙ cong (λ r → coeSym X r z) (isPropEqSym (Eq.ap fst p) (Eq.ap fst q))
      ∙ sym (coeS-sym X q z)

    reC : (X : Ob*) (pr : Prs X) {V : Type ℓI} (Θ : Tel Γ V)
      {A : Srt Γ V} (wA wA' : wfSrt {Γ = Γ} Θ A)
      (γ : (v : V) → Car X (Θ v .fst)) (a : Car X (A .fst))
      → SrtC X pr Θ A wA γ a → SrtC X pr Θ A wA' γ a
    reC X pr Θ wA wA' γ a c i = coeS-irr X (wA' i) (wA i) _ ∙ c i

    -- the transport of a compatibility proof along a sort equation
    coeC : (X : Ob*) (pr : Prs X) {V : Type ℓI} (Θ : Tel Γ V)
      {A B : Srt Γ V} (p : A Eq.≡ B)
      (wA : wfSrt {Γ = Γ} Θ A) (wB : wfSrt {Γ = Γ} Θ B)
      (γ : (v : V) → Car X (Θ v .fst)) (a : Car X (A .fst))
      → SrtC X pr Θ A wA γ a → SrtC X pr Θ B wB γ (coeS X p a)
    coeC X pr Θ Eq.refl wA wB γ a c = reC X pr Θ wA wB γ a c

    -- --------------------------------------------------------------
    -- Change of context along a context morphism
    -- --------------------------------------------------------------

    private
      coeS-⟨⟩ : (X : Ob*) {V W : Type ℓI} (ρ : W → V)
        {B0 : Srt Γ V} {B C : Srt Γ W}
        (p : B0 Eq.≡ reSrt {Γ = Γ} ρ B) (q : B Eq.≡ C)
        (z : Car X (B0 .fst))
        → coeS X (p Eq.∙ reSrt≡ {Γ = Γ} ρ q) z ≡ coeS X q (coeS X p z)
      coeS-⟨⟩ X ρ Eq.refl Eq.refl z = refl

    module _ (X : Ob*) (pr : Prs X) {V W : Type ℓI}
      {Θ : Tel Γ V} {Ξ : Tel Γ W} (ρ : W → V)
      (wρ : wfRen {Γ = Γ} Θ Ξ ρ) {A : Srt Γ W}
      (wA : wfSrt {Γ = Γ} Ξ A) (γ : (v : V) → Car X (Θ v .fst))
      (a : Car X (A .fst)) where

      private
        γ⟨⟩ : (u : W) → Car X (Ξ u .fst)
        γ⟨⟩ u = coeS X (wρ u) (γ (ρ u))

      transC→ : SrtC X pr Ξ A wA γ⟨⟩ a
        → SrtC X pr Θ (reSrt {Γ = Γ} ρ A)
            (wfSrt⟨⟩ {Γ = Γ} {Θ = Θ} {Ξ = Ξ} {A = A} ρ wρ wA) γ a
      transC→ c i = coeS-⟨⟩ X ρ (wρ (A .snd i)) (wA i) _ ∙ c i

      transC← : SrtC X pr Θ (reSrt {Γ = Γ} ρ A)
          (wfSrt⟨⟩ {Γ = Γ} {Θ = Θ} {Ξ = Ξ} {A = A} ρ wρ wA) γ a
        → SrtC X pr Ξ A wA γ⟨⟩ a
      transC← c i = sym (coeS-⟨⟩ X ρ (wρ (A .snd i)) (wA i) _) ∙ c i

    -- --------------------------------------------------------------
    -- Evaluation of terms in a model
    -- --------------------------------------------------------------

    module _ (M : Category.ob ALG) where

      private
        X : Ob*
        X = M .fst

        M* : Ob**
        M* = M .fst , M .snd .fst

        pr : Prs X
        pr = M .snd .fst .fst

        α : Ops M*
        α = M .snd .snd .fst

        typed : OpsTyped M* α
        typed = M .snd .snd .snd

      -- A term evaluates to an element together with a proof that it
      -- sits at its sort.  Both are needed: the proof is what the next
      -- operation up demands of its arguments.
      eval : {V : Type ℓI} (Θ : Tel Γ V) (w : wfTel {Γ = Γ} Θ)
        {I : Type ℓA} {as : I → Srt Γ V}
        (was : (j : I) → wfSrt {Γ = Γ} Θ (as j))
        (γ : (v : V) → Car X (Θ v .fst)) (cγ : EnvC X pr Θ w γ)
        (x : (j : I) → Car X (as j .fst))
        (cx : (j : I) → SrtC X pr Θ (as j) (was j) γ (x j))
        {A : Srt Γ V} (wA : wfSrt {Γ = Γ} Θ A)
        (t : Term Γ Θ I as A) (wt : wfTm {Γ = Γ} Θ t)
        → Σ[ a ∈ Car X (A .fst) ] SrtC X pr Θ A wA γ a
      eval Θ w was γ cγ x cx wA (S.ivar v) wt =
        γ v , reC X pr Θ (w v) wA γ (γ v) (cγ v)
      eval Θ w was γ cγ x cx wA (S.avar j) wt =
        x j , reC X pr Θ (was j) wA γ (x j) (cx j)
      eval Θ w was γ cγ x cx wA (S.app o ρ Bs pB A pA ts) (wρ , wts) =
        coeS X (Eq.sym pA) res
        , coeC X pr Θ (Eq.sym pA)
            (wfSrt⟨⟩ {Γ = Γ} {Θ = Θ} {Ξ = OT o} {A = opRes {Γ = Γ} o}
              ρ wρ (wf .wfOpRes o))
            wA γ res
            (transC→ X pr ρ wρ {A = opRes {Γ = Γ} o} (wf .wfOpRes o) γ res
              (typed o γ' cγ' vals cvals))
        where
        γ' : (v : opVar {Γ = Γ} o) → Car X (OT o v .fst)
        γ' v = coeS X (wρ v) (γ (ρ v))

        cγ' : EnvC X pr (OT o) (wf .wfOpTel o) γ'
        cγ' v = transC← X pr ρ wρ {A = OT o v} (wf .wfOpTel o v) γ (γ' v)
          (coeC X pr Θ (wρ v) (w (ρ v))
            (wfSrt⟨⟩ {Γ = Γ} {Θ = Θ} {Ξ = OT o} {A = OT o v}
              ρ wρ (wf .wfOpTel o v))
            γ (γ (ρ v)) (cγ (ρ v)))

        -- the well-formedness of the forded argument sort, obtained by
        -- moving the canonical one back along the ford
        wBs : (j : opIx {Γ = Γ} o) → wfSrt {Γ = Γ} Θ (Bs j)
        wBs j = Eq.transport (λ B → wfSrt {Γ = Γ} Θ B) (Eq.sym (pB j))
          (wfSrt⟨⟩ {Γ = Γ} {Θ = Θ} {Ξ = OT o} {A = opArgS {Γ = Γ} o j}
            ρ wρ (wf .wfOpArg o j))

        rec : (j : opIx {Γ = Γ} o)
          → Σ[ a ∈ Car X (Bs j .fst) ] SrtC X pr Θ (Bs j) (wBs j) γ a
        rec j = eval Θ w was γ cγ x cx (wBs j) (ts j) (wts j)

        vals : (j : opIx {Γ = Γ} o) → Car X (opArgS {Γ = Γ} o j .fst)
        vals j = coeS X (pB j) (rec j .fst)

        cvals : ArgsC X pr o γ' vals
        cvals j = transC← X pr ρ wρ {A = opArgS {Γ = Γ} o j}
          (wf .wfOpArg o j) γ (vals j)
          (coeC X pr Θ (pB j) (wBs j)
            (wfSrt⟨⟩ {Γ = Γ} {Θ = Θ} {Ξ = OT o} {A = opArgS {Γ = Γ} o j}
              ρ wρ (wf .wfOpArg o j))
            γ (rec j .fst) (rec j .snd))

        res : Car X (opRes {Γ = Γ} o .fst)
        res = α o γ' cγ' vals cvals

    -- --------------------------------------------------------------
    -- The layer of equations
    -- --------------------------------------------------------------
    --
    -- Homomorphisms carry no data here, exactly as in `Sorted`'s
    -- `EQNSᴰ`, so this layer cannot disturb the laws.

    Eqns : (M : Category.ob ALG) → Type (ℓ-max (ℓ-max ℓI ℓA) ℓX)
    Eqns M = (e : EqnSym Γ)
      (γ : (v : eqnVar {Γ = Γ} e) → Car (M .fst) (ET e v .fst))
      (cγ : EnvC (M .fst) (M .snd .fst .fst) (ET e) (wf .wfEqnTel e) γ)
      (x : (j : eqnIx {Γ = Γ} e)
         → Car (M .fst) (eqnArgS {Γ = Γ} e j .fst))
      (cx : (j : eqnIx {Γ = Γ} e)
          → SrtC (M .fst) (M .snd .fst .fst) (ET e)
              (eqnArgS {Γ = Γ} e j) (wf .wfEqnArg e j) γ (x j))
      → eval M (ET e) (wf .wfEqnTel e) (wf .wfEqnArg e) γ cγ x cx
            (wf .wfEqnRes e) (eqnLhs {Γ = Γ} e) (wf .wfEqnLhs e) .fst
        ≡ eval M (ET e) (wf .wfEqnTel e) (wf .wfEqnArg e) γ cγ x cx
            (wf .wfEqnRes e) (eqnRhs {Γ = Γ} e) (wf .wfEqnRhs e) .fst

    EQNSᴰ : Categoryᴰ ALG (ℓ-max (ℓ-max ℓI ℓA) ℓX) ℓ-zero
    EQNSᴰ .Categoryᴰ.ob[_] M = Eqns M
    EQNSᴰ .Categoryᴰ.Hom[_][_,_] _ _ _ = Unit
    EQNSᴰ .Categoryᴰ.idᴰ = tt
    EQNSᴰ .Categoryᴰ._⋆ᴰ_ _ _ = tt
    EQNSᴰ .Categoryᴰ.⋆IdLᴰ _ = refl
    EQNSᴰ .Categoryᴰ.⋆IdRᴰ _ = refl
    EQNSᴰ .Categoryᴰ.⋆Assocᴰ _ _ _ = refl
    EQNSᴰ .Categoryᴰ.isSetHomᴰ = isProp→isSet (λ _ _ → refl)

    -- the category of models of the theory
    MODᴰ : Categoryᴰ CAR _ _
    MODᴰ = ∫Cᴰ (∫Cᴰ PRᴰ ALGᴰ) EQNSᴰ

    MOD : Category _ _
    MOD = ∫C MODᴰ

    private
      module Mo = Category MOD

    MOD⋆IdL : {M N : Mo.ob} (h : Mo.Hom[ M , N ]) → Mo.id Mo.⋆ h ≡ h
    MOD⋆IdL h = refl

    MOD⋆IdR : {M N : Mo.ob} (h : Mo.Hom[ M , N ]) → h Mo.⋆ Mo.id ≡ h
    MOD⋆IdR h = refl

    MOD⋆Assoc : {M N O P : Mo.ob} (h : Mo.Hom[ M , N ]) (k : Mo.Hom[ N , O ])
      (l : Mo.Hom[ O , P ]) → (h Mo.⋆ k) Mo.⋆ l ≡ h Mo.⋆ (k Mo.⋆ l)
    MOD⋆Assoc h k l = refl
