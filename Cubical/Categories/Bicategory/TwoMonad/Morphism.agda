{-# OPTIONS --lossy-unification #-}
{-
  Identity and composition of lax morphisms of pseudoalgebras, the
  data `Bicategory.TwoMonad.Algebra` does not supply.

  `idAlgHom` is complete.  For the composite the underlying 1-cell,
  the comparison 2-cell and the unit axiom are proved; the
  multiplication axiom is stated as `SeqMultAx` and taken as an
  argument to `seqAlgHom`, so the remaining goal is exact and checked.
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
open import Cubical.Categories.Bicategory.TwoMonad
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

    -- Rewriting a right-nested prefix, as `rep3` but collapsing to a
    -- single 2-cell.  (Belongs next to `pushn`/`rep3` in
    -- `Properties.Coherence`.)
    rw3 : {x y : K.0Cell} {f g h m k : K.1Cell x y}
      {p : K.2Cell f g} {q : K.2Cell g h} {r : K.2Cell h m}
      {w : K.2Cell f m}
      → p K.⋆₂ q K.⋆₂ r ≡ w → (t : K.2Cell m k)
      → p K.⋆₂ q K.⋆₂ r K.⋆₂ t ≡ w K.⋆₂ t
    rw3 e t = sym (aR3 K _ _ _ t) ∙ K.⟨ e ⟩⋆₂⟨⟩

    rw4 : {x y : K.0Cell} {f g h m n k : K.1Cell x y}
      {p : K.2Cell f g} {q : K.2Cell g h} {r : K.2Cell h m}
      {s : K.2Cell m n} {w : K.2Cell f n}
      → p K.⋆₂ q K.⋆₂ r K.⋆₂ s ≡ w → (t : K.2Cell n k)
      → p K.⋆₂ q K.⋆₂ r K.⋆₂ s K.⋆₂ t ≡ w K.⋆₂ t
    rw4 e t = sym (aR4 K _ _ _ _ t) ∙ K.⟨ e ⟩⋆₂⟨⟩

    pushr3 : {x y : K.0Cell} {f g h n₁ n₂ k : K.1Cell x y}
      {u : K.2Cell f g} {v : K.2Cell g h}
      {w₁ : K.2Cell f n₁} {w₂ : K.2Cell n₁ n₂} {w₃ : K.2Cell n₂ h}
      → u K.⋆₂ v ≡ w₁ K.⋆₂ w₂ K.⋆₂ w₃ → (t : K.2Cell h k)
      → u K.⋆₂ v K.⋆₂ t ≡ w₁ K.⋆₂ w₂ K.⋆₂ w₃ K.⋆₂ t
    pushr3 e t = pushn K e t ∙ aR3 K _ _ _ t

    rw5 : {x y : K.0Cell} {f₀ f₁ f₂ f₃ f₄ f₅ k : K.1Cell x y}
      {p : K.2Cell f₀ f₁} {q : K.2Cell f₁ f₂} {r : K.2Cell f₂ f₃}
      {s : K.2Cell f₃ f₄} {v : K.2Cell f₄ f₅} {w : K.2Cell f₀ f₅}
      → p K.⋆₂ q K.⋆₂ r K.⋆₂ s K.⋆₂ v ≡ w → (t : K.2Cell f₅ k)
      → p K.⋆₂ q K.⋆₂ r K.⋆₂ s K.⋆₂ v K.⋆₂ t ≡ w K.⋆₂ t
    rw5 e t = sym (aR5 K _ _ _ _ _ t) ∙ K.⟨ e ⟩⋆₂⟨⟩

    ▷6 : {x y z : K.0Cell} {f₀ f₁ f₂ f₃ f₄ f₅ f₆ : K.1Cell x y}
      (p : K.2Cell f₀ f₁) (q : K.2Cell f₁ f₂) (r : K.2Cell f₂ f₃)
      (s : K.2Cell f₃ f₄) (v : K.2Cell f₄ f₅) (w : K.2Cell f₅ f₆)
      (e : K.1Cell y z)
      →   ((p K.⋆₂ q K.⋆₂ r K.⋆₂ s K.⋆₂ v K.⋆₂ w) K.▷w e)
        ≡ (p K.▷w e) K.⋆₂ (q K.▷w e) K.⋆₂ (r K.▷w e)
            K.⋆₂ (s K.▷w e) K.⋆₂ (v K.▷w e) K.⋆₂ (w K.▷w e)
    ▷6 p q r s v w e = ▷wSeq K p _ e ∙ K.⟨⟩⋆₂⟨ ▷5 K q r s v w e ⟩

    ◁6 : {x y z : K.0Cell} (e : K.1Cell x y)
      {f₀ f₁ f₂ f₃ f₄ f₅ f₆ : K.1Cell y z}
      (p : K.2Cell f₀ f₁) (q : K.2Cell f₁ f₂) (r : K.2Cell f₂ f₃)
      (s : K.2Cell f₃ f₄) (v : K.2Cell f₄ f₅) (w : K.2Cell f₅ f₆)
      →   (e K.◁w (p K.⋆₂ q K.⋆₂ r K.⋆₂ s K.⋆₂ v K.⋆₂ w))
        ≡ (e K.◁w p) K.⋆₂ (e K.◁w q) K.⋆₂ (e K.◁w r)
            K.⋆₂ (e K.◁w s) K.⋆₂ (e K.◁w v) K.⋆₂ (e K.◁w w)
    ◁6 e p q r s v w = ◁wSeq K e p _ ∙ K.⟨⟩⋆₂⟨ ◁5 K e q r s v w ⟩

    ◁7 : {x y z : K.0Cell} (e : K.1Cell x y)
      {f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ : K.1Cell y z}
      (o : K.2Cell f₀ f₁) (p : K.2Cell f₁ f₂) (q : K.2Cell f₂ f₃)
      (r : K.2Cell f₃ f₄) (s : K.2Cell f₄ f₅) (v : K.2Cell f₅ f₆)
      (w : K.2Cell f₆ f₇)
      →   (e K.◁w (o K.⋆₂ p K.⋆₂ q K.⋆₂ r K.⋆₂ s K.⋆₂ v K.⋆₂ w))
        ≡ (e K.◁w o) K.⋆₂ (e K.◁w p) K.⋆₂ (e K.◁w q) K.⋆₂ (e K.◁w r)
            K.⋆₂ (e K.◁w s) K.⋆₂ (e K.◁w v) K.⋆₂ (e K.◁w w)
    ◁7 e o p q r s v w = ◁wSeq K e o _ ∙ K.⟨⟩⋆₂⟨ ◁6 e p q r s v w ⟩

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
        ∙ K.⟨⟩⋆₂⟨ rw4 (idTail n) _ ⟩
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
        ∙ rw3 (T.lax-λ (Tob c) c a) _
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
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ pushr3 e1 _ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ idTail mu ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ pushn K (λ⋆₁ K mu a) _ ⟩
        ∙ pushr K (λ-nat K m) _

      ρα : K.ρ⁻ (mu K.⋆₁ a) K.⋆₂ K.α⁺ mu a (K.id₁ {c}) ≡ (mu K.◁w K.ρ⁻ a)
      ρα =
          K.⟨ ρ⁻⋆₁ K mu a ⟩⋆₂⟨⟩
        ∙ K.⋆₂Assoc _ _ _
        ∙ K.⟨⟩⋆₂⟨ K.α _ _ _ _ .nIso (mu , a , K.id₁) .sec ⟩
        ∙ K.⋆₂IdR _

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
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ ρα ⟩ ⟩ ⟩
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
        ∙ K.⟨⟩⋆₂⟨ rw5 five _ ⟩
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

      κcol : ((nA K.◁w (T.F² f g K.▷w d))
               K.⋆₂ (nA K.◁w (κ²⁻ M.T f g K.▷w d)))
           ≡ K.id₂
      κcol =
          sym (◁wSeq K nA _ _)
        ∙ nA K.◁⟨ sym (▷wSeq K _ _ d)
                ∙ K.⟨ T.F-seq-isIso (f , g) .ret ⟩▷ d
                ∙ K.▷wId d ⟩
        ∙ K.◁wId nA

      kappaCancel :
            ((nA K.◁w T.F² f g) K.▷w d)
            K.⋆₂ K.α⁺ nA (T1 (f K.⋆₁ g)) d
            K.⋆₂ (nA K.◁w (κ²⁻ M.T f g K.▷w d))
          ≡ K.α⁺ nA (T1 f K.⋆₁ T1 g) d
      kappaCancel =
          pushr K (α⁺natM K nA (T.F² f g) d) _
        ∙ K.⟨⟩⋆₂⟨ κcol ⟩
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

      λα : K.α⁺ K.id₁ f g K.⋆₂ K.λ⁺ (f K.⋆₁ g) ≡ (K.λ⁺ f K.▷w g)
      λα =
          K.⟨⟩⋆₂⟨ sym (λ⋆₁ K f g) ⟩
        ∙ pushn K (K.α _ _ _ _ .nIso (K.id₁ , f , g) .ret) _
        ∙ K.⋆₂IdL _

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
        ∙ K.⟨⟩⋆₂⟨ pushr3 pentB _ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (sym (α⁺natM K nA hc g)) _ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr3 pentD _ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushn K (K.α _ _ _ _ .nIso (nA , a , f K.⋆₁ g) .ret) _
            ∙ K.⋆₂IdL _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (sym (α⁺natL K uA f g)) _ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              λα ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

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
        ∙ K.⟨⟩⋆₂⟨ pushr3 (pentP3 K f g nC d) _ ⟩
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
          K.⟨⟩⋆₂⟨ K.⟨ K.⟨ ηfgExp ⟩▷ d ∙ ▷6 _ _ _ _ _ _ d ⟩⋆₂⟨⟩
                ∙ aR6 K _ _ _ _ _ _ _ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨ ◁6 nA _ _ _ _ _ _ ⟩⋆₂⟨⟩
                    ∙ aR6 K _ _ _ _ _ _ _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ rw3 kappaCancel _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
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
      psiRw = sym (▷6 _ _ _ _ _ _ g) ∙ K.⟨ Ψeq ⟩▷ g ∙ ▷3 K _ _ _ g

      lemRHS : Nform ≡ ((f K.⋆₁ g) K.◁w uC) K.⋆₂ K.ρ⁺ (f K.⋆₁ g)
      lemRHS =
          K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ psiRw ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ pushr3 (pentP3 K f nB b g) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ pushr K (α⁺natR K f nB kc) _ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ pushr3
                (sym (K.pentagon _ _ _ _ _ f nB (T1 g) d)) _ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ pushn K αcolF _ ∙ K.⋆₂IdL _ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ pushr K (α⁺natM K f ηg d) _ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ pushr3 pentG _ ⟩
        ∙ pushn K (K.α _ _ _ _ .nIso (f K.⋆₁ g , nC , d) .sec) _
        ∙ K.⋆₂IdL _
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ pushr K (sym (α⁻natM K f uB g)) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ α⁻ρ▷ K f g ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ sym (◁7 f _ _ _ _ _ _ _)
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

    -- The one remaining obligation for the composite.  Stated as a
    -- type rather than assumed, so `seqAlgHom` below is a genuine
    -- theorem and the goal is pinned by the typechecker.
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

    seqAlgHom : SeqMultAx → AlgHom M A C
    seqAlgHom mAx .mor = seqMor
    seqAlgHom mAx .cell = seqCell
    seqAlgHom mAx .unitAx = seqUnitAx
    seqAlgHom mAx .multAx = mAx

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
