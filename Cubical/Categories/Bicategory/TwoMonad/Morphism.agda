{-# OPTIONS --lossy-unification #-}
{-
  Identity and composition of lax morphisms of pseudoalgebras, the
  data `Bicategory.TwoMonad.Algebra` does not supply.

  Both are complete: `idAlgHom` and `seqAlgHom`, together with
  `idCellIsIso`/`seqCellIsIso` saying that identities and composites of
  pseudo morphisms are pseudo.
-}
module Cubical.Categories.Bicategory.TwoMonad.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Properties.Coherence
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Functor.Properties
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.TwoMonad.Base
open import Cubical.Categories.Bicategory.TwoMonad.Algebra

private
  variable
    ℓ ℓ' ℓ'' : Level

open Category
open NatIso
open LaxNatTrans
open Modification
open isIso
open PseudoAlgebra
open AlgHom

module _ {K : Bicategory ℓ ℓ' ℓ''} (M : TwoMonad K) where
  private
    module K = Bicategory K
    module M = TwoMonad M
    module T = Pseudofunctor M.T

    Tob = T₀ M
    T1 = T₁ M
    T2 = T₂ M
    η1 = ηc M
    μ1 = μc M

    κ⁰ : {x : K.0Cell} → K.2Cell K.id₁ (T1 (K.id₁ {x}))
    κ⁰ = T.F⁰

    κ⁰i : {x : K.0Cell} → K.2Cell (T1 (K.id₁ {x})) K.id₁
    κ⁰i = κ⁰⁻ M.T

  -- The identity lax morphism on a pseudoalgebra.
  module _ (A : PseudoAlgebra M) where
    private
      c = A .carrier
      a = A .act
      n = η1 c
      u = A .actUnit

    idCell : K.2Cell (T1 K.id₁ K.⋆₁ a) (a K.⋆₁ K.id₁)
    idCell = (κ⁰i K.▷w a) K.⋆₂ K.λ⁺ a K.⋆₂ K.ρ⁻ a

    -- `η`'s lax-unit law, with the identity functor's trivial `F⁰`
    -- cancelled.
    ηhomId : M.η .N-hom (K.id₁ {c})
      ≡ K.λ⁺ n K.⋆₂ K.ρ⁻ n K.⋆₂ (n K.◁w κ⁰)
    ηhomId = sym (K.⋆₂IdL _) ∙ K.⟨ sym (K.▷wId n) ⟩⋆₂⟨⟩
           ∙ M.η .lax-id c

    private
      κ⁰collapse : {x : K.0Cell} (p : K.1Cell x (Tob c))
        → (p K.◁w (κ⁰ K.▷w a)) K.⋆₂ (p K.◁w (κ⁰i K.▷w a)) ≡ K.id₂
      κ⁰collapse p =
          sym (◁wSeq K p _ _)
        ∙ p K.◁⟨ sym (▷wSeq K κ⁰ κ⁰i a)
               ∙ K.⟨ T.F-id-isIso tt* .ret ⟩▷ a
               ∙ K.▷wId a ⟩
        ∙ K.◁wId p

      ρcollapse : {x : K.0Cell} (p : K.1Cell x (Tob c))
        → (K.ρ⁻ p K.▷w a) K.⋆₂ (K.ρ⁺ p K.▷w a) ≡ K.id₂
      ρcollapse {x} p =
          sym (▷wSeq K _ _ a)
        ∙ K.⟨ K.ρU x (Tob c) .nIso (p , tt*) .sec ⟩▷ a
        ∙ K.▷wId a

    -- The tail shared by both algebra axioms for `idCell`: whatever
    -- 1-cell `p` ends at `T c`, the four cells below cancel down to a
    -- single unitor.
    idTail : {x : K.0Cell} (p : K.1Cell x (Tob c))
      →   (K.ρ⁻ p K.▷w a)
          K.⋆₂ ((p K.◁w κ⁰) K.▷w a)
          K.⋆₂ K.α⁺ p (T1 K.id₁) a
          K.⋆₂ (p K.◁w idCell)
        ≡ (p K.◁w K.ρ⁻ a)
    idTail p =
        K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ ◁3 K p _ _ _ ⟩ ⟩ ⟩
      ∙ K.⟨⟩⋆₂⟨ pushr K (α⁺natM K p κ⁰ a) _ ⟩
      ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ pushn K (κ⁰collapse p) _ ⟩ ⟩
      ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⋆₂IdL _ ⟩ ⟩
      ∙ K.⟨⟩⋆₂⟨ pushn K (K.triangle _ _ _ p a) _ ⟩
      ∙ pushn K (ρcollapse p) _
      ∙ K.⋆₂IdL _

    private
      ρλid : K.ρ⁻ (K.id₁ {c}) K.⋆₂ K.λ⁺ K.id₁ ≡ K.id₂
      ρλid = K.⟨⟩⋆₂⟨ λ⁺≡ρ⁺ K ⟩ ∙ K.ρU c c .nIso (K.id₁ , tt*) .sec

      -- The first five factors of `unitAx`'s left-hand side.
      unitKey :
          K.α⁻ K.id₁ n a
            K.⋆₂ (M.η .N-hom (K.id₁ {c}) K.▷w a)
            K.⋆₂ K.α⁺ n (T1 K.id₁) a
            K.⋆₂ (n K.◁w idCell)
            K.⋆₂ K.α⁻ n a K.id₁
        ≡ K.λ⁺ (n K.⋆₁ a) K.⋆₂ K.ρ⁻ (n K.⋆₁ a)
      unitKey =
          K.⟨⟩⋆₂⟨ K.⟨ K.⟨ ηhomId ⟩▷ a ∙ ▷3 K _ _ _ a ⟩⋆₂⟨⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ aR3 K _ _ _ _ ⟩
        ∙ pushn K (λ⋆₁ K n a) _
        ∙ K.⟨⟩⋆₂⟨ rw4 K (idTail n) _ ⟩
        ∙ K.⟨⟩⋆₂⟨ sym (ρ⁻⋆₁ K n a) ⟩

    idUnitAx :
        K.α⁻ K.id₁ n a
          K.⋆₂ (M.η .N-hom (K.id₁ {c}) K.▷w a)
          K.⋆₂ K.α⁺ n (T1 K.id₁) a
          K.⋆₂ (n K.◁w idCell)
          K.⋆₂ K.α⁻ n a K.id₁
          K.⋆₂ (u K.▷w K.id₁)
          K.⋆₂ K.λ⁺ K.id₁
      ≡ (K.id₁ K.◁w u) K.⋆₂ K.ρ⁺ K.id₁
    idUnitAx =
        sym (aR5 K _ _ _ _ _ _)
      ∙ K.⟨ unitKey ⟩⋆₂⟨⟩
      ∙ K.⋆₂Assoc _ _ _
      ∙ K.⟨⟩⋆₂⟨ pushr K (sym (ρ⁻-nat K u)) (K.λ⁺ K.id₁) ⟩
      ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ ρλid ⟩ ⟩
      ∙ K.⟨⟩⋆₂⟨ K.⋆₂IdR u ⟩
      ∙ sym (λ-nat K u)
      ∙ K.⟨⟩⋆₂⟨ λ⁺≡ρ⁺ K ⟩

    private
      m = A .actMult
      mu = μ1 c

      W : K.2Cell (K.id₁ {Tob (Tob c)}) (T1 (T1 (K.id₁ {c})))
      W = κ⁰ K.⋆₂ T2 κ⁰

      Wi : K.2Cell (T1 (T1 (K.id₁ {c}))) K.id₁
      Wi = T2 κ⁰i K.⋆₂ κ⁰i

      μlaxId : (W K.▷w mu) K.⋆₂ M.μ .N-hom (K.id₁ {c})
        ≡ K.λ⁺ mu K.⋆₂ K.ρ⁻ mu K.⋆₂ (mu K.◁w κ⁰)
      μlaxId = M.μ .lax-id c

      Wsec : Wi K.⋆₂ W ≡ K.id₂
      Wsec =
          K.⋆₂Assoc _ _ _
        ∙ K.⟨⟩⋆₂⟨ pushn K (T.F-id-isIso tt* .sec) _ ∙ K.⋆₂IdL _ ⟩
        ∙ sym (T₂Seq M κ⁰i κ⁰)
        ∙ cong T2 (T.F-id-isIso tt* .sec)
        ∙ T₂Id M

      Wret : W K.⋆₂ Wi ≡ K.id₂
      Wret =
          K.⋆₂Assoc _ _ _
        ∙ K.⟨⟩⋆₂⟨ pushn K (sym (T₂Seq M κ⁰ κ⁰i)
                          ∙ cong T2 (T.F-id-isIso tt* .ret)
                          ∙ T₂Id M) _
                ∙ K.⋆₂IdL _ ⟩
        ∙ T.F-id-isIso tt* .ret

      Wiso : isIso K.Hom[ Tob (Tob c) , Tob (Tob c) ] W
      Wiso .inv = Wi
      Wiso .sec = Wsec
      Wiso .ret = Wret

      T2ρcollapse : T2 (K.ρ⁺ a) K.⋆₂ T2 (K.ρ⁻ a) ≡ K.id₂
      T2ρcollapse =
          sym (T₂Seq M _ _)
        ∙ cong T2 (K.ρU (Tob c) c .nIso (a , tt*) .ret)
        ∙ T₂Id M

      Θ : K.2Cell (T1 a K.⋆₁ T1 (K.id₁ {c})) (T1 a)
      Θ = (T1 a K.◁w κ⁰i) K.⋆₂ K.ρ⁺ (T1 a)

      Xc : K.2Cell (T1 a) (T1 a K.⋆₁ K.id₁)
      Xc = T2 (K.ρ⁻ a) K.⋆₂ κ²⁻ M.T a (K.id₁ {c}) K.⋆₂ (T1 a K.◁w κ⁰i)

      Xstep : K.ρ⁺ (T1 a) K.⋆₂ Xc ≡ K.id₂
      Xstep =
          K.⟨ sym (T.lax-ρ (Tob c) c a) ⟩⋆₂⟨⟩
        ∙ aR3 K _ _ _ _
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ pushn K T2ρcollapse _ ∙ K.⋆₂IdL _ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ pushn K (T.F-seq-isIso (a , K.id₁ {c}) .ret) _
                ∙ K.⋆₂IdL _ ⟩
        ∙ sym (◁wSeq K (T1 a) _ _)
        ∙ T1 a K.◁⟨ T.F-id-isIso tt* .ret ⟩
        ∙ K.◁wId (T1 a)

      Xcell : Xc ≡ K.ρ⁻ (T1 a)
      Xcell =
          sym (K.⋆₂IdL _)
        ∙ K.⟨ sym (K.ρU (Tob (Tob c)) (Tob c) .nIso (T1 a , tt*) .sec) ⟩⋆₂⟨⟩
        ∙ K.⋆₂Assoc _ _ _
        ∙ K.⟨⟩⋆₂⟨ Xstep ⟩
        ∙ K.⋆₂IdR _

      rhoUnit : T2 (K.ρ⁻ a) K.⋆₂ κ²⁻ M.T a (K.id₁ {c}) K.⋆₂ Θ ≡ K.id₂
      rhoUnit =
          sym (aR3 K _ _ _ _)
        ∙ K.⟨ Xcell ⟩⋆₂⟨⟩
        ∙ K.ρU (Tob (Tob c)) (Tob c) .nIso (T1 a , tt*) .sec

      κ⁰▷collapse : (κ⁰ K.▷w a) K.⋆₂ (κ⁰i K.▷w a) ≡ K.id₂
      κ⁰▷collapse =
          sym (▷wSeq K κ⁰ κ⁰i a)
        ∙ K.⟨ T.F-id-isIso tt* .ret ⟩▷ a
        ∙ K.▷wId a

      T2idCell : T2 (κ⁰ K.▷w a) K.⋆₂ T2 idCell
        ≡ T2 (K.λ⁺ a) K.⋆₂ T2 (K.ρ⁻ a)
      T2idCell =
          sym (T₂Seq M _ _)
        ∙ cong T2 (pushn K κ⁰▷collapse _ ∙ K.⋆₂IdL _)
        ∙ T₂Seq M _ _

      Xi : K.2Cell (T1 (T1 (K.id₁ {c})) K.⋆₁ T1 a) (T1 a)
      Xi = T.F² (T1 (K.id₁ {c})) a
             K.⋆₂ T2 idCell
             K.⋆₂ κ²⁻ M.T a (K.id₁ {c})
             K.⋆₂ Θ

      -- The heart of the multiplication axiom for `idCell`: `T`'s two
      -- unit constraints cancel `Xi` down to a left unitor.
      laxKey : (W K.▷w T1 a) K.⋆₂ Xi ≡ K.λ⁺ (T1 a)
      laxKey =
          K.⟨ ▷wSeq K κ⁰ (T2 κ⁰) (T1 a) ⟩⋆₂⟨⟩
        ∙ K.⋆₂Assoc _ _ _
        ∙ K.⟨⟩⋆₂⟨ pushr K (F²nat▷ M.Tl κ⁰ a) _ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ pushr K T2idCell _ ⟩ ⟩
        ∙ rw3 K (T.lax-λ (Tob c) c a) _
        ∙ K.⟨⟩⋆₂⟨ rhoUnit ⟩
        ∙ K.⋆₂IdR _

      Gc : K.2Cell (K.id₁ K.⋆₁ (T1 a K.⋆₁ a))
                   (T1 (T1 (K.id₁ {c})) K.⋆₁ (T1 a K.⋆₁ a))
      Gc = W K.▷w (T1 a K.⋆₁ a)

      Cval : K.2Cell (K.id₁ K.⋆₁ (T1 a K.⋆₁ a)) (mu K.⋆₁ (a K.⋆₁ K.id₁))
      Cval = K.λ⁺ (T1 a K.⋆₁ a) K.⋆₂ m K.⋆₂ (mu K.◁w K.ρ⁻ a)

      e1 : ((W K.▷w mu) K.▷w a) K.⋆₂ (M.μ .N-hom (K.id₁ {c}) K.▷w a)
         ≡ (K.λ⁺ mu K.▷w a) K.⋆₂ (K.ρ⁻ mu K.▷w a)
             K.⋆₂ ((mu K.◁w κ⁰) K.▷w a)
      e1 = sym (▷wSeq K _ _ a) ∙ K.⟨ μlaxId ⟩▷ a ∙ ▷3 K _ _ _ a

      lhsKey : Gc K.⋆₂ (  (T1 (T1 (K.id₁ {c})) K.◁w m)
                        K.⋆₂ K.α⁻ (T1 (T1 (K.id₁ {c}))) mu a
                        K.⋆₂ (M.μ .N-hom (K.id₁ {c}) K.▷w a)
                        K.⋆₂ K.α⁺ mu (T1 (K.id₁ {c})) a
                        K.⋆₂ (mu K.◁w idCell))
             ≡ Cval
      lhsKey =
          pushr K (▷◁exch K W m) _
        ∙ K.⟨⟩⋆₂⟨ pushr K (α⁻natL K W mu a) _ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ pushr3 K e1 _ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ idTail mu ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ pushn K (λ⋆₁ K mu a) _ ⟩
        ∙ pushr K (λ-nat K m) _

      rhsTail :
            K.α⁺ (T1 a) (T1 (K.id₁ {c})) a
            K.⋆₂ (T1 a K.◁w idCell)
            K.⋆₂ K.α⁻ (T1 a) a (K.id₁ {c})
            K.⋆₂ (m K.▷w K.id₁)
            K.⋆₂ K.α⁺ mu a (K.id₁ {c})
          ≡ (Θ K.▷w a) K.⋆₂ m K.⋆₂ (mu K.◁w K.ρ⁻ a)
      rhsTail =
          K.⟨⟩⋆₂⟨ K.⟨ ◁3 K (T1 a) _ _ _ ⟩⋆₂⟨⟩ ∙ aR3 K _ _ _ _ ⟩
        ∙ pushr K (sym (α⁺natM K (T1 a) κ⁰i a)) _
        ∙ K.⟨⟩⋆₂⟨ pushn K (K.triangle _ _ _ (T1 a) a) _ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ pushn K (sym (ρ⁻⋆₁ K (T1 a) a)) _ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ pushr K (sym (ρ⁻-nat K m)) _ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ ρα K mu a ⟩ ⟩ ⟩
        ∙ pushn K (sym (▷wSeq K _ _ a)) _

      five :
            ((W K.▷w T1 a) K.▷w a)
            K.⋆₂ (T.F² (T1 (K.id₁ {c})) a K.▷w a)
            K.⋆₂ (T2 idCell K.▷w a)
            K.⋆₂ (κ²⁻ M.T a (K.id₁ {c}) K.▷w a)
            K.⋆₂ (Θ K.▷w a)
          ≡ (K.λ⁺ (T1 a) K.▷w a)
      five = sym (▷5 K _ _ _ _ _ a) ∙ K.⟨ laxKey ⟩▷ a

      rhsKey : Gc K.⋆₂ (  K.α⁻ (T1 (T1 (K.id₁ {c}))) (T1 a) a
                        K.⋆₂ (T.F² (T1 (K.id₁ {c})) a K.▷w a)
                        K.⋆₂ (T2 idCell K.▷w a)
                        K.⋆₂ (κ²⁻ M.T a (K.id₁ {c}) K.▷w a)
                        K.⋆₂ K.α⁺ (T1 a) (T1 (K.id₁ {c})) a
                        K.⋆₂ (T1 a K.◁w idCell)
                        K.⋆₂ K.α⁻ (T1 a) a (K.id₁ {c})
                        K.⋆₂ (m K.▷w K.id₁)
                        K.⋆₂ K.α⁺ mu a (K.id₁ {c}))
             ≡ Cval
      rhsKey =
          K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ rhsTail ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ pushr K (α⁻natL K W (T1 a) a) _
        ∙ K.⟨⟩⋆₂⟨ rw5 K five _ ⟩
        ∙ pushn K (λ⋆₁ K (T1 a) a) _

    idMultAx :
        (T1 (T1 (K.id₁ {c})) K.◁w A .actMult)
          K.⋆₂ K.α⁻ (T1 (T1 (K.id₁ {c}))) (μ1 c) a
          K.⋆₂ (M.μ .N-hom (K.id₁ {c}) K.▷w a)
          K.⋆₂ K.α⁺ (μ1 c) (T1 (K.id₁ {c})) a
          K.⋆₂ (μ1 c K.◁w idCell)
      ≡   K.α⁻ (T1 (T1 (K.id₁ {c}))) (T1 a) a
          K.⋆₂ (T.F² (T1 (K.id₁ {c})) a K.▷w a)
          K.⋆₂ (T2 idCell K.▷w a)
          K.⋆₂ (T.F-seq-isIso (a , K.id₁ {c}) .inv K.▷w a)
          K.⋆₂ K.α⁺ (T1 a) (T1 (K.id₁ {c})) a
          K.⋆₂ (T1 a K.◁w idCell)
          K.⋆₂ K.α⁻ (T1 a) a (K.id₁ {c})
          K.⋆₂ (A .actMult K.▷w K.id₁)
          K.⋆₂ K.α⁺ (μ1 c) a (K.id₁ {c})
    idMultAx =
      ⋆CancelL (Gc , ▷wIsIso K (T1 a K.⋆₁ a) Wiso) (lhsKey ∙ sym rhsKey)

    -- The identity morphism of pseudoalgebras.
    idAlgHom : AlgHom M A A
    idAlgHom .mor = K.id₁
    idAlgHom .cell = idCell
    idAlgHom .unitAx = idUnitAx
    idAlgHom .multAx = idMultAx

    -- It is a pseudo (indeed strict) morphism.
    idCellIsIso : isIso K.Hom[ Tob c , c ] idCell
    idCellIsIso =
      ⋆IsIso (▷wIsIso K a (invIso (κ⁰I M.T {c}) .snd))
             (⋆IsIso (K.λU (Tob c) c .nIso (tt* , a))
                     (invIso (_ , K.ρU (Tob c) c .nIso (a , tt*)) .snd))

  -- The composite of two lax morphisms: paste the two comparison
  -- cells, splitting `T` of the composite by `T`'s laxity constraint.
  module _ {A B C : PseudoAlgebra M}
           (h : AlgHom M A B) (k : AlgHom M B C) where
    private
      f = h .mor
      g = k .mor
      a = A .act
      b = B .act
      d = C .act

    seqMor : K.1Cell (A .carrier) (C .carrier)
    seqMor = f K.⋆₁ g

    private
      nA = η1 (A .carrier)
      nB = η1 (B .carrier)
      nC = η1 (C .carrier)
      hc = h .cell
      kc = k .cell
      ηf = M.η .N-hom f
      ηg = M.η .N-hom g
      pfn = f K.⋆₁ nB
      qna = nA K.⋆₁ T1 f
      uA = A .actUnit
      uB = B .actUnit
      uC = C .actUnit

      -- `η`'s lax-composition law, with the identity functor's
      -- trivial `F²` cancelled.
      ηfgExp : M.η .N-hom (f K.⋆₁ g)
        ≡ K.α⁺ f g nC
            K.⋆₂ (f K.◁w ηg)
            K.⋆₂ K.α⁻ f nB (T1 g)
            K.⋆₂ (ηf K.▷w T1 g)
            K.⋆₂ K.α⁺ nA (T1 f) (T1 g)
            K.⋆₂ (nA K.◁w T.F² f g)
      ηfgExp = sym (K.⋆₂IdL _) ∙ K.⟨ sym (K.▷wId nC) ⟩⋆₂⟨⟩
             ∙ M.η .lax-seq f g

      κcol : {x : K.0Cell} (p : K.1Cell x (Tob (A .carrier)))
           → ((p K.◁w (T.F² f g K.▷w d))
               K.⋆₂ (p K.◁w (κ²⁻ M.T f g K.▷w d)))
           ≡ K.id₂
      κcol p =
          sym (◁wSeq K p _ _)
        ∙ p K.◁⟨ sym (▷wSeq K _ _ d)
                ∙ K.⟨ T.F-seq-isIso (f , g) .ret ⟩▷ d
                ∙ K.▷wId d ⟩
        ∙ K.◁wId p

      kappaCancel : {x : K.0Cell} (p : K.1Cell x (Tob (A .carrier)))
          →   ((p K.◁w T.F² f g) K.▷w d)
            K.⋆₂ K.α⁺ p (T1 (f K.⋆₁ g)) d
            K.⋆₂ (p K.◁w (κ²⁻ M.T f g K.▷w d))
          ≡ K.α⁺ p (T1 f K.⋆₁ T1 g) d
      kappaCancel p =
          pushr K (α⁺natM K p (T.F² f g) d) _
        ∙ K.⟨⟩⋆₂⟨ κcol p ⟩
        ∙ K.⋆₂IdR _

      -- `pentP3`/`pentP4` post-composed with an associator.
      pentB : K.α⁺ nA (T1 f) (b K.⋆₁ g) K.⋆₂ (nA K.◁w K.α⁻ (T1 f) b g)
        ≡   K.α⁻ qna b g
            K.⋆₂ (K.α⁺ nA (T1 f) b K.▷w g)
            K.⋆₂ K.α⁺ nA (T1 f K.⋆₁ b) g
      pentB =
          K.⟨⟩⋆₂⟨ sym (K.⋆₂IdR _)
                ∙ K.⟨⟩⋆₂⟨ sym (K.α _ _ _ _ .nIso
                                 (nA , T1 f K.⋆₁ b , g) .sec) ⟩ ⟩
        ∙ sym (aR3 K _ _ _ _)
        ∙ K.⟨ sym (pentP3 K nA (T1 f) b g) ⟩⋆₂⟨⟩
        ∙ aR2 K _ _ _

      pentD : K.α⁺ nA (a K.⋆₁ f) g K.⋆₂ (nA K.◁w K.α⁺ a f g)
        ≡   (K.α⁻ nA a f K.▷w g)
            K.⋆₂ K.α⁺ (nA K.⋆₁ a) f g
            K.⋆₂ K.α⁺ nA a (f K.⋆₁ g)
      pentD =
          K.⟨⟩⋆₂⟨ sym (K.⋆₂IdR _)
                ∙ K.⟨⟩⋆₂⟨ sym (K.α _ _ _ _ .nIso
                                 (nA , a , f K.⋆₁ g) .sec) ⟩ ⟩
        ∙ sym (aR3 K _ _ _ _)
        ∙ K.⟨ pentP4 K nA a f g ⟩⋆₂⟨⟩
        ∙ aR2 K _ _ _

      -- The part of the unit axiom that lives under `nA`, moved out
      -- from under it by five naturality/pentagon steps.
      lemSuffix :
            K.α⁺ nA (T1 f) (T1 g K.⋆₁ d)
            K.⋆₂ (nA K.◁w (T1 f K.◁w kc))
            K.⋆₂ (nA K.◁w K.α⁻ (T1 f) b g)
            K.⋆₂ (nA K.◁w (hc K.▷w g))
            K.⋆₂ (nA K.◁w K.α⁺ a f g)
            K.⋆₂ K.α⁻ nA a (f K.⋆₁ g)
            K.⋆₂ (uA K.▷w (f K.⋆₁ g))
            K.⋆₂ K.λ⁺ (f K.⋆₁ g)
          ≡   (qna K.◁w kc)
            K.⋆₂ K.α⁻ qna b g
            K.⋆₂ (K.α⁺ nA (T1 f) b K.▷w g)
            K.⋆₂ ((nA K.◁w hc) K.▷w g)
            K.⋆₂ (K.α⁻ nA a f K.▷w g)
            K.⋆₂ ((uA K.▷w f) K.▷w g)
            K.⋆₂ (K.λ⁺ f K.▷w g)
      lemSuffix =
          pushr K (sym (α⁺natR K nA (T1 f) kc)) _
        ∙ K.⟨⟩⋆₂⟨ pushr3 K pentB _ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (sym (α⁺natM K nA hc g)) _ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr3 K pentD _ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushn K (K.α _ _ _ _ .nIso (nA , a , f K.⋆₁ g) .ret) _
            ∙ K.⋆₂IdL _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (sym (α⁺natL K uA f g)) _ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              αλ K f g ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

    seqCell : K.2Cell (T1 seqMor K.⋆₁ d) (a K.⋆₁ seqMor)
    seqCell =
        (κ²⁻ M.T f g K.▷w d)
        K.⋆₂ K.α⁺ (T1 f) (T1 g) d
        K.⋆₂ (T1 f K.◁w k .cell)
        K.⋆₂ K.α⁻ (T1 f) b g
        K.⋆₂ (h .cell K.▷w g)
        K.⋆₂ K.α⁺ a f g

    private
      Ψeq :   (ηf K.▷w b)
              K.⋆₂ K.α⁺ nA (T1 f) b
              K.⋆₂ (nA K.◁w hc)
              K.⋆₂ K.α⁻ nA a f
              K.⋆₂ (uA K.▷w f)
              K.⋆₂ K.λ⁺ f
            ≡ K.α⁺ f nB b K.⋆₂ (f K.◁w uB) K.⋆₂ K.ρ⁺ f
      Ψeq =
          sym (K.⋆₂IdL _)
        ∙ K.⟨ sym (K.α _ _ _ _ .nIso (f , nB , b) .ret) ⟩⋆₂⟨⟩
        ∙ K.⋆₂Assoc _ _ _
        ∙ K.⟨⟩⋆₂⟨ h .unitAx ⟩

      αcolF : (K.α⁻ f nB (T1 g) K.▷w d) K.⋆₂ (K.α⁺ f nB (T1 g) K.▷w d)
        ≡ K.id₂
      αcolF =
          sym (▷wSeq K _ _ d)
        ∙ K.⟨ K.α _ _ _ _ .nIso (f , nB , T1 g) .sec ⟩▷ d
        ∙ K.▷wId d

      pentG : (K.α⁺ f g nC K.▷w d) K.⋆₂ K.α⁺ f (g K.⋆₁ nC) d
        ≡   K.α⁺ (f K.⋆₁ g) nC d
            K.⋆₂ K.α⁺ f g (nC K.⋆₁ d)
            K.⋆₂ (f K.◁w K.α⁻ g nC d)
      pentG =
          sym (K.⋆₂IdL _)
        ∙ K.⟨ sym (K.α _ _ _ _ .nIso (f K.⋆₁ g , nC , d) .ret) ⟩⋆₂⟨⟩
        ∙ K.⋆₂Assoc _ _ _
        ∙ K.⟨⟩⋆₂⟨ pushr3 K (pentP3 K f g nC d) _ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.α _ _ _ _ .nIso (f , g K.⋆₁ nC , d) .sec ⟩
            ∙ K.⋆₂IdR _ ⟩ ⟩

    -- Common normal form of the two sides of the unit axiom.
    private
      Nform : K.2Cell ((f K.⋆₁ g) K.⋆₁ (nC K.⋆₁ d)) (f K.⋆₁ g)
      Nform =
          K.α⁻ (f K.⋆₁ g) nC d
          K.⋆₂ (K.α⁺ f g nC K.▷w d)
          K.⋆₂ ((f K.◁w ηg) K.▷w d)
          K.⋆₂ (K.α⁻ f nB (T1 g) K.▷w d)
          K.⋆₂ K.α⁺ pfn (T1 g) d
          K.⋆₂ (pfn K.◁w kc)
          K.⋆₂ K.α⁻ pfn b g
          K.⋆₂ ((ηf K.▷w b) K.▷w g)
          K.⋆₂ (K.α⁺ nA (T1 f) b K.▷w g)
          K.⋆₂ ((nA K.◁w hc) K.▷w g)
          K.⋆₂ (K.α⁻ nA a f K.▷w g)
          K.⋆₂ ((uA K.▷w f) K.▷w g)
          K.⋆₂ (K.λ⁺ f K.▷w g)

      lemLHS :
            K.α⁻ (f K.⋆₁ g) nC d
            K.⋆₂ (M.η .N-hom (f K.⋆₁ g) K.▷w d)
            K.⋆₂ K.α⁺ nA (T1 (f K.⋆₁ g)) d
            K.⋆₂ (nA K.◁w seqCell)
            K.⋆₂ K.α⁻ nA a (f K.⋆₁ g)
            K.⋆₂ (uA K.▷w (f K.⋆₁ g))
            K.⋆₂ K.λ⁺ (f K.⋆₁ g)
          ≡ Nform
      lemLHS =
          K.⟨⟩⋆₂⟨ K.⟨ K.⟨ ηfgExp ⟩▷ d ∙ ▷6 K _ _ _ _ _ _ d ⟩⋆₂⟨⟩
                ∙ aR6 K _ _ _ _ _ _ _ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨ ◁6 K nA _ _ _ _ _ _ ⟩⋆₂⟨⟩
                    ∙ aR6 K _ _ _ _ _ _ _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ rw3 K (kappaCancel nA) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ rep3 K (K.pentagon _ _ _ _ _ nA (T1 f) (T1 g) d) _
                    ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ pushr K (α⁺natL K ηf (T1 g) d) _ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ lemSuffix ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ pushr K (▷◁exch K ηf kc) _ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ pushr K (α⁻natL K ηf b g) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

      psiRw :
            ((ηf K.▷w b) K.▷w g)
            K.⋆₂ (K.α⁺ nA (T1 f) b K.▷w g)
            K.⋆₂ ((nA K.◁w hc) K.▷w g)
            K.⋆₂ (K.α⁻ nA a f K.▷w g)
            K.⋆₂ ((uA K.▷w f) K.▷w g)
            K.⋆₂ (K.λ⁺ f K.▷w g)
          ≡ (K.α⁺ f nB b K.▷w g)
            K.⋆₂ ((f K.◁w uB) K.▷w g)
            K.⋆₂ (K.ρ⁺ f K.▷w g)
      psiRw = sym (▷6 K _ _ _ _ _ _ g) ∙ K.⟨ Ψeq ⟩▷ g ∙ ▷3 K _ _ _ g

      lemRHS : Nform ≡ ((f K.⋆₁ g) K.◁w uC) K.⋆₂ K.ρ⁺ (f K.⋆₁ g)
      lemRHS =
          K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ psiRw ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ pushr3 K (pentP3 K f nB b g) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ pushr K (α⁺natR K f nB kc) _ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ pushr3 K
                (sym (K.pentagon _ _ _ _ _ f nB (T1 g) d)) _ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ pushn K αcolF _ ∙ K.⋆₂IdL _ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ pushr K (α⁺natM K f ηg d) _ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ pushr3 K pentG _ ⟩
        ∙ pushn K (K.α _ _ _ _ .nIso (f K.⋆₁ g , nC , d) .sec) _
        ∙ K.⋆₂IdL _
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ pushr K (sym (α⁻natM K f uB g)) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ α⁻ρ▷ K f g ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ sym (◁7 K f _ _ _ _ _ _ _)
                ∙ f K.◁⟨ k .unitAx ⟩
                ∙ ◁wSeq K f _ _ ⟩
        ∙ pushr K (sym (α⁺natR K f g uC)) _
        ∙ K.⟨⟩⋆₂⟨ ρ⋆₁ K g f ⟩

    seqUnitAx :
          K.α⁻ (f K.⋆₁ g) nC d
          K.⋆₂ (M.η .N-hom (f K.⋆₁ g) K.▷w d)
          K.⋆₂ K.α⁺ nA (T1 (f K.⋆₁ g)) d
          K.⋆₂ (nA K.◁w seqCell)
          K.⋆₂ K.α⁻ nA a (f K.⋆₁ g)
          K.⋆₂ (uA K.▷w (f K.⋆₁ g))
          K.⋆₂ K.λ⁺ (f K.⋆₁ g)
        ≡ ((f K.⋆₁ g) K.◁w uC) K.⋆₂ K.ρ⁺ (f K.⋆₁ g)
    seqUnitAx = lemLHS ∙ lemRHS

    -- The multiplication axiom for the composite, as a type; proved
    -- as `seqMultAx` below.
    SeqMultAx : Type ℓ''
    SeqMultAx =
        (T1 (T1 seqMor) K.◁w C .actMult)
          K.⋆₂ K.α⁻ (T1 (T1 seqMor)) (μ1 (C .carrier)) d
          K.⋆₂ (M.μ .N-hom seqMor K.▷w d)
          K.⋆₂ K.α⁺ (μ1 (A .carrier)) (T1 seqMor) d
          K.⋆₂ (μ1 (A .carrier) K.◁w seqCell)
      ≡   K.α⁻ (T1 (T1 seqMor)) (T1 d) d
          K.⋆₂ (T.F² (T1 seqMor) d K.▷w d)
          K.⋆₂ (T2 seqCell K.▷w d)
          K.⋆₂ (T.F-seq-isIso (a , seqMor) .inv K.▷w d)
          K.⋆₂ K.α⁺ (T1 a) (T1 seqMor) d
          K.⋆₂ (T1 a K.◁w seqCell)
          K.⋆₂ K.α⁻ (T1 a) a seqMor
          K.⋆₂ (A .actMult K.▷w seqMor)
          K.⋆₂ K.α⁺ (μ1 (A .carrier)) a seqMor


    private
      Tf = T1 f
      Tg = T1 g
      Ta = T1 a
      Tb = T1 b
      Td = T1 d
      TTf = T1 (T1 f)
      TTg = T1 (T1 g)
      muA = μ1 (A .carrier)
      muB = μ1 (B .carrier)
      muC = μ1 (C .carrier)
      mA = A .actMult
      mB = B .actMult
      mC = C .actMult
      μf = M.μ .N-hom f
      μg = M.μ .N-hom g

      -- The composite pseudofunctor's laxity cell at `(f , g)`.
      W : K.2Cell (TTf K.⋆₁ TTg) (T1 (T1 seqMor))
      W = T.F² Tf Tg K.⋆₂ T2 (T.F² f g)

      Wiso : isIso K.Hom[ Tob (Tob (A .carrier))
                        , Tob (Tob (C .carrier)) ] W
      Wiso = ⋆IsIso (T.F-seq-isIso (Tf , Tg))
                    (F-PresIsIso {F = T.F-Hom} (T.F-seq-isIso (f , g)))

      Gc : K.2Cell ((TTf K.⋆₁ TTg) K.⋆₁ (Td K.⋆₁ d))
                   (T1 (T1 seqMor) K.⋆₁ (Td K.⋆₁ d))
      Gc = W K.▷w (Td K.⋆₁ d)

      μlaxSeq : (W K.▷w muC) K.⋆₂ M.μ .N-hom seqMor
        ≡   K.α⁺ TTf TTg muC
          K.⋆₂ (TTf K.◁w μg)
          K.⋆₂ K.α⁻ TTf muB Tg
          K.⋆₂ (μf K.▷w Tg)
          K.⋆₂ K.α⁺ muA Tf Tg
          K.⋆₂ (muA K.◁w T.F² f g)
      μlaxSeq = M.μ .lax-seq f g

      -- `seqCell` with its leading `κ²⁻` split off.
      scRest : K.2Cell ((Tf K.⋆₁ Tg) K.⋆₁ d) (a K.⋆₁ seqMor)
      scRest =
          K.α⁺ Tf Tg d
          K.⋆₂ (Tf K.◁w kc)
          K.⋆₂ K.α⁻ Tf b g
          K.⋆₂ (hc K.▷w g)
          K.⋆₂ K.α⁺ a f g

      mE1 : ((W K.▷w muC) K.▷w d) K.⋆₂ (M.μ .N-hom seqMor K.▷w d)
          ≡ (K.α⁺ TTf TTg muC K.▷w d)
            K.⋆₂ ((TTf K.◁w μg) K.▷w d)
            K.⋆₂ (K.α⁻ TTf muB Tg K.▷w d)
            K.⋆₂ ((μf K.▷w Tg) K.▷w d)
            K.⋆₂ (K.α⁺ muA Tf Tg K.▷w d)
            K.⋆₂ ((muA K.◁w T.F² f g) K.▷w d)
      mE1 = sym (▷wSeq K _ _ d) ∙ K.⟨ μlaxSeq ⟩▷ d ∙ ▷6 K _ _ _ _ _ _ d

      mTail : ((muA K.◁w T.F² f g) K.▷w d)
              K.⋆₂ K.α⁺ muA (T1 seqMor) d
              K.⋆₂ (muA K.◁w seqCell)
            ≡ K.α⁺ muA (Tf K.⋆₁ Tg) d K.⋆₂ (muA K.◁w scRest)
      mTail =
          K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ ◁wSeq K muA _ _ ⟩ ⟩
        ∙ rw3 K (kappaCancel muA) _

      L1 : K.2Cell ((TTf K.⋆₁ TTg) K.⋆₁ (Td K.⋆₁ d))
                   (muA K.⋆₁ (a K.⋆₁ seqMor))
      L1 =
          ((TTf K.⋆₁ TTg) K.◁w mC)
          K.⋆₂ K.α⁻ (TTf K.⋆₁ TTg) muC d
          K.⋆₂ (K.α⁺ TTf TTg muC K.▷w d)
          K.⋆₂ ((TTf K.◁w μg) K.▷w d)
          K.⋆₂ (K.α⁻ TTf muB Tg K.▷w d)
          K.⋆₂ ((μf K.▷w Tg) K.▷w d)
          K.⋆₂ (K.α⁺ muA Tf Tg K.▷w d)
          K.⋆₂ K.α⁺ muA (Tf K.⋆₁ Tg) d
          K.⋆₂ (muA K.◁w scRest)

      mLemL : Gc K.⋆₂ (  (T1 (T1 seqMor) K.◁w mC)
                       K.⋆₂ K.α⁻ (T1 (T1 seqMor)) muC d
                       K.⋆₂ (M.μ .N-hom seqMor K.▷w d)
                       K.⋆₂ K.α⁺ muA (T1 seqMor) d
                       K.⋆₂ (muA K.◁w seqCell))
            ≡ L1
      mLemL =
          pushr K (▷◁exch K W mC) _
        ∙ K.⟨⟩⋆₂⟨ pushr K (α⁻natL K W muC d) _ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ pushr6 K mE1 _ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ mTail ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

      T2αTfbg : T2 (K.α⁺ Tf b g) K.⋆₂ T2 (K.α⁻ Tf b g) ≡ K.id₂
      T2αTfbg =
          sym (T₂Seq M _ _)
        ∙ cong T2 (K.α _ _ _ _ .nIso (Tf , b , g) .ret)
        ∙ T₂Id M

      UcI : CatIso K.Hom[ Tob (Tob (A .carrier)) , Tob (C .carrier) ]
              ((TTf K.⋆₁ Tb) K.⋆₁ Tg) (TTf K.⋆₁ T1 (b K.⋆₁ g))
      UcI = ⋆Iso (αI K TTf Tb Tg)
                 ( TTf K.◁w T.F² b g
                 , ◁wIsIso K TTf (T.F-seq-isIso (b , g)))

      pC : (K.α⁺ TTf Tb Tg K.⋆₂ (TTf K.◁w T.F² b g))
             K.⋆₂ (T.F² Tf (b K.⋆₁ g) K.⋆₂ T2 (K.α⁻ Tf b g))
         ≡ (T.F² Tf b K.▷w Tg) K.⋆₂ T.F² (Tf K.⋆₁ b) g
      pC =
          K.⋆₂Assoc _ _ _
        ∙ K.⟨⟩⋆₂⟨ sym (K.⋆₂Assoc _ _ _) ⟩
        ∙ sym (K.⋆₂Assoc _ _ _)
        ∙ K.⟨ sym (T.lax-α _ _ _ _ Tf b g) ⟩⋆₂⟨⟩
        ∙ K.⋆₂Assoc _ _ _
        ∙ K.⟨⟩⋆₂⟨ K.⋆₂Assoc _ _ _ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ T2αTfbg ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⋆₂IdR _ ⟩

      -- `T`'s associativity constraint, read on `α⁻`.
      mStepC : T.F² Tf (b K.⋆₁ g) K.⋆₂ T2 (K.α⁻ Tf b g)
             ≡ (TTf K.◁w κ²⁻ M.T b g)
               K.⋆₂ K.α⁻ TTf Tb Tg
               K.⋆₂ (T.F² Tf b K.▷w Tg)
               K.⋆₂ T.F² (Tf K.⋆₁ b) g
      mStepC = ⋆InvLMove UcI pC ∙ K.⋆₂Assoc _ _ _

      pE : (T.F² a f K.▷w Tg)
             K.⋆₂ (T.F² (a K.⋆₁ f) g K.⋆₂ T2 (K.α⁺ a f g)
                     K.⋆₂ κ²⁻ M.T a seqMor)
         ≡ (T.F² a f K.▷w Tg)
             K.⋆₂ ((κ²⁻ M.T a f K.▷w Tg)
                     K.⋆₂ K.α⁺ Ta Tf Tg K.⋆₂ (Ta K.◁w T.F² f g))
      pE =
        (  K.⟨⟩⋆₂⟨ sym (K.⋆₂Assoc _ _ _) ⟩
         ∙ sym (K.⋆₂Assoc _ _ _)
         ∙ K.⟨ T.lax-α _ _ _ _ a f g ⟩⋆₂⟨⟩
         ∙ K.⋆₂Assoc _ _ _
         ∙ K.⟨⟩⋆₂⟨ K.⋆₂Assoc _ _ _ ⟩
         ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ T.F-seq-isIso (a , seqMor) .ret ⟩ ⟩
         ∙ K.⟨⟩⋆₂⟨ K.⋆₂IdR _ ⟩)
        ∙ sym
          (  sym (K.⋆₂Assoc _ _ _)
           ∙ K.⟨ sym (▷wSeq K _ _ Tg)
               ∙ K.⟨ T.F-seq-isIso (a , f) .ret ⟩▷ Tg
               ∙ K.▷wId Tg ⟩⋆₂⟨⟩
           ∙ K.⋆₂IdL _)

      mStepE : T.F² (a K.⋆₁ f) g K.⋆₂ T2 (K.α⁺ a f g)
                 K.⋆₂ κ²⁻ M.T a seqMor
             ≡ (κ²⁻ M.T a f K.▷w Tg)
               K.⋆₂ K.α⁺ Ta Tf Tg
               K.⋆₂ (Ta K.◁w T.F² f g)
      mStepE = ▷wCancelL K (T.F-seq-isIso (a , f)) Tg pE

      κ▷collapse : (T.F² f g K.▷w d) K.⋆₂ (κ²⁻ M.T f g K.▷w d) ≡ K.id₂
      κ▷collapse =
          sym (▷wSeq K _ _ d)
        ∙ K.⟨ T.F-seq-isIso (f , g) .ret ⟩▷ d
        ∙ K.▷wId d

      T2F²cancel : T2 (T.F² f g K.▷w d) K.⋆₂ T2 seqCell ≡ T2 scRest
      T2F²cancel =
          sym (T₂Seq M _ _)
        ∙ cong T2 (pushn K κ▷collapse _ ∙ K.⋆₂IdL _)

      T2scRest : T2 scRest
        ≡ T2 (K.α⁺ Tf Tg d)
          K.⋆₂ T2 (Tf K.◁w kc)
          K.⋆₂ T2 (K.α⁻ Tf b g)
          K.⋆₂ T2 (hc K.▷w g)
          K.⋆₂ T2 (K.α⁺ a f g)
      T2scRest =
          T₂Seq M _ _
        ∙ K.⟨⟩⋆₂⟨ T₂Seq M _ _
                ∙ K.⟨⟩⋆₂⟨ T₂Seq M _ _
                        ∙ K.⟨⟩⋆₂⟨ T₂Seq M _ _ ⟩ ⟩ ⟩

      Bk : K.2Cell ((TTf K.⋆₁ TTg) K.⋆₁ Td) (Ta K.⋆₁ T1 seqMor)
      Bk =
          K.α⁺ TTf TTg Td
          K.⋆₂ (TTf K.◁w T.F² Tg d)
          K.⋆₂ (TTf K.◁w T2 kc)
          K.⋆₂ (TTf K.◁w κ²⁻ M.T b g)
          K.⋆₂ K.α⁻ TTf Tb Tg
          K.⋆₂ (T.F² Tf b K.▷w Tg)
          K.⋆₂ (T2 hc K.▷w Tg)
          K.⋆₂ (κ²⁻ M.T a f K.▷w Tg)
          K.⋆₂ K.α⁺ Ta Tf Tg
          K.⋆₂ (Ta K.◁w T.F² f g)

      mBracket : (W K.▷w Td) K.⋆₂ T.F² (T1 seqMor) d
                   K.⋆₂ T2 seqCell K.⋆₂ κ²⁻ M.T a seqMor
               ≡ Bk
      mBracket =
          K.⟨ ▷wSeq K (T.F² Tf Tg) (T2 (T.F² f g)) Td ⟩⋆₂⟨⟩
        ∙ K.⋆₂Assoc _ _ _
        ∙ K.⟨⟩⋆₂⟨ pushr K (F²nat▷ M.Tl (T.F² f g) d) _ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ pushn K T2F²cancel _ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨ T2scRest ⟩⋆₂⟨⟩ ∙ aR5 K _ _ _ _ _ _ ⟩ ⟩
        ∙ rw3 K (T.lax-α _ _ _ _ Tf Tg d) _ ∙ aR3 K _ _ _ _
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (sym (F²nat◁ M.Tl Tf kc)) _ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ pushr4 K mStepC _ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (sym (F²nat▷ M.Tl hc g)) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ mStepE ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

      mE2 : ((W K.▷w Td) K.▷w d)
              K.⋆₂ (T.F² (T1 seqMor) d K.▷w d)
              K.⋆₂ (T2 seqCell K.▷w d)
              K.⋆₂ (κ²⁻ M.T a seqMor K.▷w d)
          ≡ (K.α⁺ TTf TTg Td K.▷w d)
            K.⋆₂ ((TTf K.◁w T.F² Tg d) K.▷w d)
            K.⋆₂ ((TTf K.◁w T2 kc) K.▷w d)
            K.⋆₂ ((TTf K.◁w κ²⁻ M.T b g) K.▷w d)
            K.⋆₂ (K.α⁻ TTf Tb Tg K.▷w d)
            K.⋆₂ ((T.F² Tf b K.▷w Tg) K.▷w d)
            K.⋆₂ ((T2 hc K.▷w Tg) K.▷w d)
            K.⋆₂ ((κ²⁻ M.T a f K.▷w Tg) K.▷w d)
            K.⋆₂ (K.α⁺ Ta Tf Tg K.▷w d)
            K.⋆₂ ((Ta K.◁w T.F² f g) K.▷w d)
      mE2 = sym (▷4 K _ _ _ _ d) ∙ K.⟨ mBracket ⟩▷ d
          ∙ ▷10 K _ _ _ _ _ _ _ _ _ _ d

      mRTail : ((Ta K.◁w T.F² f g) K.▷w d)
               K.⋆₂ K.α⁺ Ta (T1 seqMor) d
               K.⋆₂ (Ta K.◁w seqCell)
             ≡ K.α⁺ Ta (Tf K.⋆₁ Tg) d K.⋆₂ (Ta K.◁w scRest)
      mRTail =
          K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ ◁wSeq K Ta _ _ ⟩ ⟩
        ∙ rw3 K (kappaCancel Ta) _

      R1 : K.2Cell ((TTf K.⋆₁ TTg) K.⋆₁ (Td K.⋆₁ d))
                   (muA K.⋆₁ (a K.⋆₁ seqMor))
      R1 =
          K.α⁻ (TTf K.⋆₁ TTg) Td d
          K.⋆₂ (K.α⁺ TTf TTg Td K.▷w d)
          K.⋆₂ ((TTf K.◁w T.F² Tg d) K.▷w d)
          K.⋆₂ ((TTf K.◁w T2 kc) K.▷w d)
          K.⋆₂ ((TTf K.◁w κ²⁻ M.T b g) K.▷w d)
          K.⋆₂ (K.α⁻ TTf Tb Tg K.▷w d)
          K.⋆₂ ((T.F² Tf b K.▷w Tg) K.▷w d)
          K.⋆₂ ((T2 hc K.▷w Tg) K.▷w d)
          K.⋆₂ ((κ²⁻ M.T a f K.▷w Tg) K.▷w d)
          K.⋆₂ (K.α⁺ Ta Tf Tg K.▷w d)
          K.⋆₂ K.α⁺ Ta (Tf K.⋆₁ Tg) d
          K.⋆₂ (Ta K.◁w scRest)
          K.⋆₂ K.α⁻ Ta a seqMor
          K.⋆₂ (mA K.▷w seqMor)
          K.⋆₂ K.α⁺ muA a seqMor

      mLemR : Gc K.⋆₂ (  K.α⁻ (T1 (T1 seqMor)) Td d
                       K.⋆₂ (T.F² (T1 seqMor) d K.▷w d)
                       K.⋆₂ (T2 seqCell K.▷w d)
                       K.⋆₂ (T.F-seq-isIso (a , seqMor) .inv K.▷w d)
                       K.⋆₂ K.α⁺ Ta (T1 seqMor) d
                       K.⋆₂ (Ta K.◁w seqCell)
                       K.⋆₂ K.α⁻ Ta a seqMor
                       K.⋆₂ (mA K.▷w seqMor)
                       K.⋆₂ K.α⁺ muA a seqMor)
            ≡ R1
      mLemR =
          pushr K (α⁻natL K W Td d) _
        ∙ K.⟨⟩⋆₂⟨ sym (aR4 K _ _ _ _ _) ∙ K.⟨ mE2 ⟩⋆₂⟨⟩
                ∙ aR10 K _ _ _ _ _ _ _ _ _ _ _ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
                  rep3 K mRTail _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

      sA : ((TTf K.⋆₁ TTg) K.◁w mC)
         ≡ K.α⁺ TTf TTg (Td K.⋆₁ d)
           K.⋆₂ (TTf K.◁w (TTg K.◁w mC))
           K.⋆₂ K.α⁻ TTf TTg (muC K.⋆₁ d)
      sA = ⋆InvRMove (αI K TTf TTg (muC K.⋆₁ d))
             (α⁺natR K TTf TTg mC)
         ∙ K.⋆₂Assoc _ _ _

      αcolC : (K.α⁻ TTf TTg muC K.▷w d) K.⋆₂ (K.α⁺ TTf TTg muC K.▷w d)
            ≡ K.id₂
      αcolC = sym (▷wSeq K _ _ d)
            ∙ K.⟨ K.α _ _ _ _ .nIso (TTf , TTg , muC) .sec ⟩▷ d
            ∙ K.▷wId d

      sB : K.α⁻ TTf TTg (muC K.⋆₁ d)
             K.⋆₂ K.α⁻ (TTf K.⋆₁ TTg) muC d
             K.⋆₂ (K.α⁺ TTf TTg muC K.▷w d)
         ≡ (TTf K.◁w K.α⁻ TTg muC d) K.⋆₂ K.α⁻ TTf (TTg K.⋆₁ muC) d
      sB = sym (K.⋆₂Assoc _ _ _)
         ∙ K.⟨ sym (pentP2 K TTf TTg muC d) ⟩⋆₂⟨⟩
         ∙ aR3 K _ _ _ _
         ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ αcolC ⟩ ∙ K.⋆₂IdR _ ⟩

      sC : K.α⁻ TTf (TTg K.⋆₁ muC) d K.⋆₂ ((TTf K.◁w μg) K.▷w d)
         ≡ (TTf K.◁w (μg K.▷w d)) K.⋆₂ K.α⁻ TTf (muB K.⋆₁ Tg) d
      sC = sym (α⁻natM K TTf μg d)

      sD : K.α⁻ TTf (muB K.⋆₁ Tg) d K.⋆₂ (K.α⁻ TTf muB Tg K.▷w d)
         ≡ (TTf K.◁w K.α⁺ muB Tg d)
           K.⋆₂ K.α⁻ TTf muB (Tg K.⋆₁ d)
           K.⋆₂ K.α⁻ (TTf K.⋆₁ muB) Tg d
      sD = ⋆InvRMove (αI K (TTf K.⋆₁ muB) Tg d)
             (K.⋆₂Assoc _ _ _ ∙ pentP1 K TTf muB Tg d)
         ∙ K.⋆₂Assoc _ _ _

      sE : K.α⁻ (TTf K.⋆₁ muB) Tg d K.⋆₂ ((μf K.▷w Tg) K.▷w d)
         ≡ (μf K.▷w (Tg K.⋆₁ d)) K.⋆₂ K.α⁻ (muA K.⋆₁ Tf) Tg d
      sE = sym (α⁻natL K μf Tg d)

      sF : K.α⁻ (muA K.⋆₁ Tf) Tg d
             K.⋆₂ (K.α⁺ muA Tf Tg K.▷w d)
             K.⋆₂ K.α⁺ muA (Tf K.⋆₁ Tg) d
         ≡ K.α⁺ muA Tf (Tg K.⋆₁ d) K.⋆₂ (muA K.◁w K.α⁻ Tf Tg d)
      sF = pushr3 K (pentP3 K muA Tf Tg d) _
         ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.α _ _ _ _ .nIso (muA , Tf K.⋆₁ Tg , d) .sec ⟩
                 ∙ K.⋆₂IdR _ ⟩

      sG : (muA K.◁w K.α⁻ Tf Tg d) K.⋆₂ (muA K.◁w scRest)
         ≡ (muA K.◁w (Tf K.◁w kc))
           K.⋆₂ (muA K.◁w K.α⁻ Tf b g)
           K.⋆₂ (muA K.◁w (hc K.▷w g))
           K.⋆₂ (muA K.◁w K.α⁺ a f g)
      sG = sym (◁wSeq K muA _ _)
         ∙ muA K.◁⟨ pushn K (K.α _ _ _ _ .nIso (Tf , Tg , d) .sec) _
                  ∙ K.⋆₂IdL _ ⟩
         ∙ ◁4 K muA _ _ _ _

      sH : K.α⁻ TTf muB (Tg K.⋆₁ d)
             K.⋆₂ (μf K.▷w (Tg K.⋆₁ d))
             K.⋆₂ K.α⁺ muA Tf (Tg K.⋆₁ d)
             K.⋆₂ (muA K.◁w (Tf K.◁w kc))
         ≡ (TTf K.◁w (muB K.◁w kc))
           K.⋆₂ K.α⁻ TTf muB (b K.⋆₁ g)
           K.⋆₂ (μf K.▷w (b K.⋆₁ g))
           K.⋆₂ K.α⁺ muA Tf (b K.⋆₁ g)
      sH = K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ sym (α⁺natR K muA Tf kc) ⟩ ⟩
         ∙ K.⟨⟩⋆₂⟨ pushr K (▷◁exch K μf kc) _ ⟩
         ∙ pushr K (sym (α⁻natR K TTf muB kc)) _

      sI1 : (TTf K.◁w (mB K.▷w g))
          ≡ K.α⁻ TTf (Tb K.⋆₁ b) g
            K.⋆₂ ((TTf K.◁w mB) K.▷w g)
            K.⋆₂ K.α⁺ TTf (muB K.⋆₁ b) g
      sI1 = ⋆InvRMove (invIso (αI K TTf (muB K.⋆₁ b) g))
              (α⁻natM K TTf mB g)
          ∙ K.⋆₂Assoc _ _ _

      ◁αcol : (muA K.◁w K.α⁺ Tf b g) K.⋆₂ (muA K.◁w K.α⁻ Tf b g)
            ≡ K.id₂
      ◁αcol = sym (◁wSeq K muA _ _)
            ∙ muA K.◁⟨ K.α _ _ _ _ .nIso (Tf , b , g) .ret ⟩
            ∙ K.◁wId muA

      sI4 : K.α⁺ (muA K.⋆₁ Tf) b g
              K.⋆₂ K.α⁺ muA Tf (b K.⋆₁ g)
              K.⋆₂ (muA K.◁w K.α⁻ Tf b g)
          ≡ (K.α⁺ muA Tf b K.▷w g) K.⋆₂ K.α⁺ muA (Tf K.⋆₁ b) g
      sI4 = pushr3 K (sym (K.pentagon _ _ _ _ _ muA Tf b g)) _
          ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ ◁αcol ⟩ ∙ K.⋆₂IdR _ ⟩

      sI : (TTf K.◁w (mB K.▷w g))
             K.⋆₂ (TTf K.◁w K.α⁺ muB b g)
             K.⋆₂ K.α⁻ TTf muB (b K.⋆₁ g)
             K.⋆₂ (μf K.▷w (b K.⋆₁ g))
             K.⋆₂ K.α⁺ muA Tf (b K.⋆₁ g)
             K.⋆₂ (muA K.◁w K.α⁻ Tf b g)
             K.⋆₂ (muA K.◁w (hc K.▷w g))
         ≡ K.α⁻ TTf (Tb K.⋆₁ b) g
           K.⋆₂ ((TTf K.◁w mB) K.▷w g)
           K.⋆₂ (K.α⁻ TTf muB b K.▷w g)
           K.⋆₂ ((μf K.▷w b) K.▷w g)
           K.⋆₂ (K.α⁺ muA Tf b K.▷w g)
           K.⋆₂ ((muA K.◁w hc) K.▷w g)
           K.⋆₂ K.α⁺ muA (a K.⋆₁ f) g
      sI = K.⟨ sI1 ⟩⋆₂⟨⟩ ∙ aR3 K _ _ _ _
         ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ rep3 K (pentP4 K TTf muB b g) _ ⟩ ⟩
         ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
               pushr K (sym (α⁺natL K μf b g)) _ ⟩ ⟩ ⟩
         ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
               rep3 K sI4 _ ⟩ ⟩ ⟩ ⟩
         ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
               sym (α⁺natM K muA hc g) ⟩ ⟩ ⟩ ⟩ ⟩

      LHSh : K.2Cell (TTf K.⋆₁ (Tb K.⋆₁ b)) (muA K.⋆₁ (a K.⋆₁ f))
      LHSh = (TTf K.◁w mB)
           K.⋆₂ K.α⁻ TTf muB b
           K.⋆₂ (μf K.▷w b)
           K.⋆₂ K.α⁺ muA Tf b
           K.⋆₂ (muA K.◁w hc)

      Mid : K.2Cell (TTf K.⋆₁ (Tb K.⋆₁ b)) (muA K.⋆₁ (a K.⋆₁ f))
          → K.2Cell ((TTf K.⋆₁ TTg) K.⋆₁ (Td K.⋆₁ d))
                    (muA K.⋆₁ (a K.⋆₁ seqMor))
      Mid X =
          K.α⁺ TTf TTg (Td K.⋆₁ d)
          K.⋆₂ (TTf K.◁w K.α⁻ TTg Td d)
          K.⋆₂ (TTf K.◁w (T.F² Tg d K.▷w d))
          K.⋆₂ (TTf K.◁w (T2 kc K.▷w d))
          K.⋆₂ (TTf K.◁w (κ²⁻ M.T b g K.▷w d))
          K.⋆₂ (TTf K.◁w K.α⁺ Tb Tg d)
          K.⋆₂ (TTf K.◁w (Tb K.◁w kc))
          K.⋆₂ (TTf K.◁w K.α⁻ Tb b g)
          K.⋆₂ K.α⁻ TTf (Tb K.⋆₁ b) g
          K.⋆₂ (X K.▷w g)
          K.⋆₂ K.α⁺ muA (a K.⋆₁ f) g
          K.⋆₂ (muA K.◁w K.α⁺ a f g)

      kMultW :
            (TTf K.◁w (TTg K.◁w mC))
            K.⋆₂ (TTf K.◁w K.α⁻ TTg muC d)
            K.⋆₂ (TTf K.◁w (μg K.▷w d))
            K.⋆₂ (TTf K.◁w K.α⁺ muB Tg d)
            K.⋆₂ (TTf K.◁w (muB K.◁w kc))
          ≡ (TTf K.◁w K.α⁻ TTg Td d)
            K.⋆₂ (TTf K.◁w (T.F² Tg d K.▷w d))
            K.⋆₂ (TTf K.◁w (T2 kc K.▷w d))
            K.⋆₂ (TTf K.◁w (κ²⁻ M.T b g K.▷w d))
            K.⋆₂ (TTf K.◁w K.α⁺ Tb Tg d)
            K.⋆₂ (TTf K.◁w (Tb K.◁w kc))
            K.⋆₂ (TTf K.◁w K.α⁻ Tb b g)
            K.⋆₂ (TTf K.◁w (mB K.▷w g))
            K.⋆₂ (TTf K.◁w K.α⁺ muB b g)
      kMultW = sym (◁5 K TTf _ _ _ _ _)
             ∙ TTf K.◁⟨ k .multAx ⟩
             ∙ ◁9 K TTf _ _ _ _ _ _ _ _ _

      phaseI : L1 ≡ Mid LHSh
      phaseI =
          K.⟨ sA ⟩⋆₂⟨⟩ ∙ aR3 K _ _ _ _
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              rep3 K sB _ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K sC _ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr3 K sD _ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K sE _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨
              rep3 K sF _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              sG ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              rw4 K sH _ ∙ aR4 K _ _ _ _ _ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨
              rw5 K kMultW _ ∙ aR9 K _ _ _ _ _ _ _ _ _ _ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              rw7 K sI _ ∙ aR7 K _ _ _ _ _ _ _ _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              rw5 K (sym (▷5 K _ _ _ _ _ g)) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

      RHSh : K.2Cell (TTf K.⋆₁ (Tb K.⋆₁ b)) (muA K.⋆₁ (a K.⋆₁ f))
      RHSh = K.α⁻ TTf Tb b
           K.⋆₂ (T.F² Tf b K.▷w b)
           K.⋆₂ (T2 hc K.▷w b)
           K.⋆₂ (κ²⁻ M.T a f K.▷w b)
           K.⋆₂ K.α⁺ Ta Tf b
           K.⋆₂ (Ta K.◁w hc)
           K.⋆₂ K.α⁻ Ta a f
           K.⋆₂ (mA K.▷w f)
           K.⋆₂ K.α⁺ muA a f

      t1 : K.α⁺ TTf TTg (Td K.⋆₁ d) K.⋆₂ (TTf K.◁w K.α⁻ TTg Td d)
         ≡ K.α⁻ (TTf K.⋆₁ TTg) Td d
           K.⋆₂ (K.α⁺ TTf TTg Td K.▷w d)
           K.⋆₂ K.α⁺ TTf (TTg K.⋆₁ Td) d
      t1 = ⋆InvRMove (invIso (αI K TTf (TTg K.⋆₁ Td) d))
             (K.⋆₂Assoc _ _ _ ∙ sym (pentP3 K TTf TTg Td d))
         ∙ K.⋆₂Assoc _ _ _

      t5 : K.α⁺ TTf (Tb K.⋆₁ Tg) d K.⋆₂ (TTf K.◁w K.α⁺ Tb Tg d)
         ≡ (K.α⁻ TTf Tb Tg K.▷w d)
           K.⋆₂ K.α⁺ (TTf K.⋆₁ Tb) Tg d
           K.⋆₂ K.α⁺ TTf Tb (Tg K.⋆₁ d)
      t5 = ⋆InvRMove (invIso (αI K TTf Tb (Tg K.⋆₁ d)))
             (K.⋆₂Assoc _ _ _ ∙ pentP4 K TTf Tb Tg d)
         ∙ K.⋆₂Assoc _ _ _

      αcolTb : (K.α⁺ TTf Tb b K.▷w g) K.⋆₂ (K.α⁻ TTf Tb b K.▷w g)
             ≡ K.id₂
      αcolTb = sym (▷wSeq K _ _ g)
             ∙ K.⟨ K.α _ _ _ _ .nIso (TTf , Tb , b) .ret ⟩▷ g
             ∙ K.▷wId g

      t7 : K.α⁺ TTf Tb (b K.⋆₁ g)
             K.⋆₂ (TTf K.◁w K.α⁻ Tb b g)
             K.⋆₂ K.α⁻ TTf (Tb K.⋆₁ b) g
             K.⋆₂ (K.α⁻ TTf Tb b K.▷w g)
         ≡ K.α⁻ (TTf K.⋆₁ Tb) b g
      t7 = rep3 K (sym (pentP3 K TTf Tb b g)) _
         ∙ K.⟨⟩⋆₂⟨ αcolTb ⟩
         ∙ K.⋆₂IdR _

      t21 : K.α⁻ Ta (a K.⋆₁ f) g K.⋆₂ (K.α⁻ Ta a f K.▷w g)
          ≡ (Ta K.◁w K.α⁺ a f g)
            K.⋆₂ K.α⁻ Ta a (f K.⋆₁ g)
            K.⋆₂ K.α⁻ (Ta K.⋆₁ a) f g
      t21 = ⋆InvLMove
              ( (Ta K.◁w K.α⁻ a f g)
              , ◁wIsIso K Ta (invIso (αI K a f g) .snd))
              (pentP2 K Ta a f g)

      ◁colaf : (muA K.◁w K.α⁻ a f g) K.⋆₂ (muA K.◁w K.α⁺ a f g)
             ≡ K.id₂
      ◁colaf = sym (◁wSeq K muA _ _)
             ∙ muA K.◁⟨ K.α _ _ _ _ .nIso (a , f , g) .sec ⟩
             ∙ K.◁wId muA

      t23 : K.α⁻ (muA K.⋆₁ a) f g
              K.⋆₂ (K.α⁺ muA a f K.▷w g)
              K.⋆₂ K.α⁺ muA (a K.⋆₁ f) g
              K.⋆₂ (muA K.◁w K.α⁺ a f g)
          ≡ K.α⁺ muA a (f K.⋆₁ g)
      t23 = pushr3 K (pentP3 K muA a f g) _
          ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
                pushn K (K.α _ _ _ _ .nIso (muA , a K.⋆₁ f , g) .sec) _
              ∙ K.⋆₂IdL _ ⟩ ⟩
          ∙ K.⟨⟩⋆₂⟨ ◁colaf ⟩
          ∙ K.⋆₂IdR _

      phaseII : Mid RHSh ≡ R1
      phaseII =
          K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨ ▷9 K _ _ _ _ _ _ _ _ _ g ⟩⋆₂⟨⟩
              ∙ aR9 K _ _ _ _ _ _ _ _ _ _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ pushr3 K t1 _
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (sym (α⁺natM K TTf (T.F² Tg d) d)) _ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (sym (α⁺natM K TTf (T2 kc) d)) _ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (sym (α⁺natM K TTf (κ²⁻ M.T b g) d)) _ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr3 K t5 _ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨
              pushr K (sym (α⁺natR K TTf Tb kc)) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              rw4 K t7 _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (sym (α⁻natL K (T.F² Tf b) b g)) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (sym (α⁻natL K (T2 hc) b g)) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (sym (α⁻natL K (κ²⁻ M.T a f) b g)) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr3 K (pentP3 K Ta Tf b g) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨
              pushr K (sym (▷◁exch K (T.F² Tf b) kc)) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (sym (▷◁exch K (T2 hc) kc)) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (sym (▷◁exch K (κ²⁻ M.T a f) kc)) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (α⁺natR K Ta Tf kc) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (sym (α⁺natL K (T.F² Tf b) Tg d)) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨
              pushr K (sym (α⁺natL K (T2 hc) Tg d)) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (sym (α⁺natL K (κ²⁻ M.T a f) Tg d)) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr3 K (sym (K.pentagon _ _ _ _ _ Ta Tf Tg d)) _
                ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (sym (α⁻natM K Ta hc g)) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr3 K t21 _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (sym (α⁻natL K mA f g)) _
                ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              t23 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              rw5 K (sym (◁5 K Ta _ _ _ _ _)) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

    seqMultAx : SeqMultAx
    seqMultAx =
      ▷wCancelL K Wiso (Td K.⋆₁ d)
        (mLemL ∙ phaseI ∙ cong Mid (h .multAx) ∙ phaseII ∙ sym mLemR)

    -- The composite morphism of pseudoalgebras.
    seqAlgHom : AlgHom M A C
    seqAlgHom .mor = seqMor
    seqAlgHom .cell = seqCell
    seqAlgHom .unitAx = seqUnitAx
    seqAlgHom .multAx = seqMultAx

    -- A composite of pseudo morphisms is pseudo.
    seqCellIsIso :
        isIso K.Hom[ Tob (A .carrier) , B .carrier ] hc
      → isIso K.Hom[ Tob (B .carrier) , C .carrier ] kc
      → isIso K.Hom[ Tob (A .carrier) , C .carrier ] seqCell
    seqCellIsIso ih ik =
      ⋆IsIso (▷wIsIso K d (invIso (κ²I M.T f g) .snd))
        (⋆IsIso (K.α _ _ _ _ .nIso (T1 f , T1 g , d))
          (⋆IsIso (◁wIsIso K (T1 f) ik)
            (⋆IsIso (invIso (_ , K.α _ _ _ _ .nIso (T1 f , b , g)) .snd)
              (⋆IsIso (▷wIsIso K g ih)
                      (K.α _ _ _ _ .nIso (a , f , g))))))
