{-# OPTIONS --lossy-unification #-}
-- Presheaf-valued models of a generalized algebraic theory.
--
-- The port is cheap, and for a reason worth stating: `Presheaf C ℓX` is
-- `Functor (C ^op) (SET ℓX)`, so `P S ⟅ c ⟆` is *literally* an
-- `hSet ℓX`, and `λ S → P S ⟅ c ⟆` is literally an object of `CAR`.
-- The whole SET tower -- `PRᴰ`, `ALGᴰ`, `Eqns` -- can therefore be
-- reused at each stage `c` with no generalization at all.
--
-- So, following `Sorted.Presheaf.Base`, a presheaf-valued model is a
-- *fibrewise* model whose restriction maps are homomorphisms, and a
-- homomorphism of such is a bare family of fibrewise homomorphisms --
-- naturality already lives in the base, `FAMPSH`, whose laws are `refl`
-- because `PshHomStrict` is forded.  Since the fibrewise conditions are
-- the ones the SET tower already ships, and those compose strictly,
-- every law here is `refl` too.
module Cubical.Algebra.Theory.GAT.Presheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base

open import Cubical.Algebra.Theory.Sorted.Presheaf.Base using (FAMPSH)
open import Cubical.Algebra.Theory.GAT.Signature
open import Cubical.Algebra.Theory.GAT.Model

private
  variable
    ℓI ℓA ℓC ℓC' ℓX : Level

open Category
open PshHomStrict

module _ {ℓI ℓA : Level} {Γ : Sig {ℓI} {ℓA}} (wf : Wf Γ)
  (C : Category ℓC ℓC') (ℓX : Level) where

  private
    -- the fibre of a family of presheaves at a stage: an object of the
    -- base of the SET tower, on the nose
    fib : (SortSym Γ → Presheaf C ℓX) → C .ob → SortSym Γ → hSet ℓX
    fib P c S = P S ⟅ c ⟆

    module Pr = Categoryᴰ (PRᴰ Γ wf ℓX)
    module Al = Categoryᴰ (ALGᴰ Γ wf ℓX)

  record PshMod (P : SortSym Γ → Presheaf C ℓX)
    : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max (ℓ-max (ℓ-suc ℓI) ℓA) (ℓ-suc ℓX))) where
    field
      prs : (c : C .ob) → Pr.ob[ fib P c ]
      alg : (c : C .ob) → Al.ob[ fib P c , prs c ]
      sat : (c : C .ob) → Eqns Γ wf ℓX (fib P c , prs c , alg c)
      restrPr : {c c' : C .ob} (f : C [ c , c' ])
        → Pr.Hom[ (λ S → P S ⟪ f ⟫) ][ prs c' , prs c ]
      restrOp : {c c' : C .ob} (f : C [ c , c' ])
        → Al.Hom[ (λ S → P S ⟪ f ⟫) , restrPr f ][ alg c' , alg c ]

  open PshMod

  -- A homomorphism is a bare family of fibrewise homomorphisms.
  PshModHomo : {P Q : SortSym Γ → Presheaf C ℓX}
    (α : (S : SortSym Γ) → PshHomStrict (P S) (Q S))
    (B : PshMod P) (D : PshMod Q)
    → Type (ℓ-max ℓC (ℓ-max (ℓ-suc ℓI) (ℓ-max ℓA ℓX)))
  PshModHomo α B D = (c : C .ob)
    → Σ[ ϕ ∈ Pr.Hom[ (λ S → α S .N-ob c) ][ B .prs c , D .prs c ] ]
        Al.Hom[ (λ S → α S .N-ob c) , ϕ ][ B .alg c , D .alg c ]

  MODPSHᴰ : Categoryᴰ (FAMPSH (SortSym Γ) C ℓX)
    (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max (ℓ-max (ℓ-suc ℓI) ℓA) (ℓ-suc ℓX)))
    (ℓ-max ℓC (ℓ-max (ℓ-suc ℓI) (ℓ-max ℓA ℓX)))
  MODPSHᴰ .Categoryᴰ.ob[_] P = PshMod P
  MODPSHᴰ .Categoryᴰ.Hom[_][_,_] α B D = PshModHomo α B D
  MODPSHᴰ .Categoryᴰ.idᴰ {x = P} {p = B} c =
    Pr.idᴰ {x = fib P c} {p = B .prs c}
    , Al.idᴰ {x = fib P c , B .prs c} {p = B .alg c}
  MODPSHᴰ .Categoryᴰ._⋆ᴰ_ {x = P} {y = Q} {z = R} {f = α} {g = β}
    {xᴰ = B} {yᴰ = D} {zᴰ = E} ϕ ψ c =
    Pr._⋆ᴰ_ {x = fib P c} {y = fib Q c} {z = fib R c}
      {f = λ S → α S .N-ob c} {g = λ S → β S .N-ob c}
      {xᴰ = B .prs c} {yᴰ = D .prs c} {zᴰ = E .prs c}
      (ϕ c .fst) (ψ c .fst)
    , Al._⋆ᴰ_ {x = fib P c , B .prs c} {y = fib Q c , D .prs c}
      {z = fib R c , E .prs c}
      {f = (λ S → α S .N-ob c) , ϕ c .fst}
      {g = (λ S → β S .N-ob c) , ψ c .fst}
      {xᴰ = B .alg c} {yᴰ = D .alg c} {zᴰ = E .alg c}
      (ϕ c .snd) (ψ c .snd)
  MODPSHᴰ .Categoryᴰ.⋆IdLᴰ _ = refl
  MODPSHᴰ .Categoryᴰ.⋆IdRᴰ _ = refl
  MODPSHᴰ .Categoryᴰ.⋆Assocᴰ _ _ _ = refl
  MODPSHᴰ .Categoryᴰ.isSetHomᴰ {x = P} {y = Q} {f = α} {xᴰ = B} {yᴰ = D} =
    isSetΠ (λ c → isSetΣ
      (Pr.isSetHomᴰ {x = fib P c} {y = fib Q c}
        {f = λ S → α S .N-ob c} {xᴰ = B .prs c} {yᴰ = D .prs c})
      (λ ϕ → Al.isSetHomᴰ {x = fib P c , B .prs c}
        {y = fib Q c , D .prs c} {f = (λ S → α S .N-ob c) , ϕ}
        {xᴰ = B .alg c} {yᴰ = D .alg c}))

  -- the category of presheaf-valued models of the theory
  MODPSH : Category _ _
  MODPSH = ∫C MODPSHᴰ

  private
    module Mp = Category MODPSH

  MODPSH⋆IdL : {M N : Mp.ob} (h : Mp.Hom[ M , N ]) → Mp.id Mp.⋆ h ≡ h
  MODPSH⋆IdL h = refl

  MODPSH⋆IdR : {M N : Mp.ob} (h : Mp.Hom[ M , N ]) → h Mp.⋆ Mp.id ≡ h
  MODPSH⋆IdR h = refl

  MODPSH⋆Assoc : {M N O P : Mp.ob} (h : Mp.Hom[ M , N ])
    (k : Mp.Hom[ N , O ]) (l : Mp.Hom[ O , P ])
    → (h Mp.⋆ k) Mp.⋆ l ≡ h Mp.⋆ (k Mp.⋆ l)
  MODPSH⋆Assoc h k l = refl
