-- The core of a category with families, as a generalized algebraic
-- theory: `Con`, `Ty` over a context, `Tm` over a context AND a type.
--
-- This is the depth-2 case, and it is the reason the framework exists.
-- `Tm`'s index telescope is itself dependent: its second variable `A`
-- has sort `Ty Γ`, which mentions its first variable `Γ`.  `CatSig`
-- never stresses this -- `Hom`'s two indices are both `Ob`-sorted, and
-- `Ob` has no indices of its own.
--
-- It is also what a SOGAT compiles to.  A second-order theory's
-- binders are not expressible directly -- see `GAT.Presheaf`, whose
-- models are fibrewise and therefore first order -- but the
-- first-order theory of contexts and substitutions that a SOGAT
-- translates to is an ordinary GAT, and this file is the start of it.
module Cubical.Algebra.Theory.GAT.Instances.CwF where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Algebra.Theory.GAT.Signature

-- Con : U
Γ₁ : Sig {ℓ-zero} {ℓ-zero}
Γ₁ = ◇ ▹ sortD ⊥ (λ ())

private
  Con₁ : SortSym Γ₁
  Con₁ = inr tt

-- Ty : (Γ : Con) → U
Γ₂ : Sig {ℓ-zero} {ℓ-zero}
Γ₂ = Γ₁ ▹ sortD Unit (λ _ → Con₁ , λ ())

private
  Con₂ : SortSym Γ₂
  Con₂ = inl Con₁

  Ty₂ : SortSym Γ₂
  Ty₂ = inr tt

-- Tm : (Γ : Con) (A : Ty Γ) → U
--
-- `true` is the context variable and `false` the type variable; the
-- type variable's sort `Ty` is applied to the context variable, so the
-- telescope is genuinely dependent.
Γ₃ : Sig {ℓ-zero} {ℓ-zero}
Γ₃ = Γ₂ ▹ sortD Bool
  (λ { true → Con₂ , λ () ; false → Ty₂ , λ _ → true })

Con : SortSym Γ₃
Con = inl Con₂

Ty : SortSym Γ₃
Ty = inl Ty₂

Tm : SortSym Γ₃
Tm = inr tt

-- _▹_ : (Γ : Con) (A : Ty Γ) → Con, over the same dependent telescope
CwFSig : Sig {ℓ-zero} {ℓ-zero}
CwFSig = Γ₃ ▹ opD Bool
  (λ { true → Con , λ () ; false → Ty , λ _ → true })
  ⊥ (λ ()) (Con , λ ())

extOp : OpSym CwFSig
extOp = inr tt

-- ------------------------------------------------------------------
-- The dependent telescope is well formed
-- ------------------------------------------------------------------

private
  -- two sorts at the same symbol differ only in a spine out of `⊥`
  emptyFord : {D : Type} (S : SortSym CwFSig)
    (e : sortIdx {Γ = CwFSig} S → ⊥)
    {f g : sortIdx {Γ = CwFSig} S → D}
    → Eq._≡_ {A = Srt CwFSig D} (S , f) (S , g)
  emptyFord S e {f} {g} = Eq.pathToEq
    (λ i → S , funExt {f = f} {g = g} (λ k → ⊥rec (e k)) i)

-- `Tm` has two indices, and its telescope really is the dependent one
_ : sortIdx {Γ = CwFSig} Tm ≡ Bool
_ = refl

_ : sortTel {Γ = CwFSig} Tm false ≡ (Ty , λ _ → true)
_ = refl

-- and it is well formed: the obligation at the type variable says that
-- the variable supplied for `Ty`'s context index really is a `Con`
tmTelWf : wfTel {Γ = CwFSig} (sortTel {Γ = CwFSig} Tm)
tmTelWf true = λ ()
tmTelWf false = λ _ → emptyFord Con (λ ())

tyTelWf : wfTel {Γ = CwFSig} (sortTel {Γ = CwFSig} Ty)
tyTelWf _ = λ ()

conTelWf : wfTel {Γ = CwFSig} (sortTel {Γ = CwFSig} Con)
conTelWf ()

extTelWf : wfTel {Γ = CwFSig} (opTel {Γ = CwFSig} extOp)
extTelWf true = λ ()
extTelWf false = λ _ → emptyFord Con (λ ())

extResWf : wfSrt {Γ = CwFSig} (opTel {Γ = CwFSig} extOp)
  (opRes {Γ = CwFSig} extOp)
extResWf ()
