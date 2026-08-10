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

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Displayed.Instances.TotalCategory

open import Cubical.Algebra.Theory.Sorted using (FAM)
open import Cubical.Algebra.Theory.GAT.Signature

module _ {ℓI ℓA : Level} (Γ : Sig {ℓI} {ℓA}) where

  private
    ix : SortSym Γ → Type ℓI
    ix = sortIdx {Γ = Γ}

    ST : (S : SortSym Γ) → Tel Γ (ix S)
    ST = sortTel {Γ = Γ}

    OT : (o : OpSym Γ) → Tel Γ (opVar {Γ = Γ} o)
    OT = opTel {Γ = Γ}

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
