{-# OPTIONS --lossy-unification #-}
{-
  Algebras for a 2-monad `M` on a bicategory `K`.

  Morphisms come in two variances, `lax` and `colax`, differing in
  the direction of the comparison 2-cell; `isPseudoAlgHom` and
  `isStrictAlgHom` cut out the other two classical notions in either
  variance.  A pseudo morphism is the same data read either way,
  `pseudoLax→colax`/`pseudoColax→lax`.

  Not to be confused with `Bicategory.MonadAlgebra`, which is the
  Eilenberg-Moore construction for a *formal* monad (a 1-cell
  `t : a → a`).  Here the action of the monad on an algebra is a
  1-cell `T a → a`, so the algebra laws compare 1-cells rather than
  2-cells.
-}
module Cubical.Categories.Bicategory.TwoMonad.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
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
open import Cubical.Categories.Bicategory.Functor.Identity
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.TwoMonad.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

-- The variance of an algebra morphism: which way its comparison
-- 2-cell points.  Invertibility is *not* part of the variance: a
-- morphism whose cell is invertible is the same thing read either
-- way (`pseudoLax→colax` below), so bundling it would duplicate the
-- two pseudo cases rather than name a new one.
data Variance : Type where
  lax colax : Variance

open Category
open NatIso
open LaxNatTrans
open Modification
open isIso

-- Two transpositions in a category, used to read a morphism with an
-- invertible comparison cell in the opposite variance.
private
  module _ {ℓC ℓC' : Level} {C : Category ℓC ℓC'} where
    transposeR : {w x y z : C .ob} {A : C [ w , x ]}
      (q : CatIso C x y) (Bi : CatIso C y z) (Ci : CatIso C w z)
      → A ⋆⟨ C ⟩ (q .fst ⋆⟨ C ⟩ Bi .fst) ≡ Ci .fst
      → q .snd .inv ≡ Bi .fst ⋆⟨ C ⟩ (Ci .snd .inv ⋆⟨ C ⟩ A)
    transposeR {A = A} q Bi Ci p =
      sym ( cong (λ z → Bi .fst ⋆⟨ C ⟩ z)
              ( ⋆InvRMove (⋆Iso q Bi)
                  ( C .⋆Assoc _ _ _
                  ∙ cong (λ z → Ci .snd .inv ⋆⟨ C ⟩ z) p
                  ∙ Ci .snd .sec)
              ∙ C .⋆IdL _)
          ∙ sym (C .⋆Assoc _ _ _)
          ∙ cong (λ z → z ⋆⟨ C ⟩ q .snd .inv) (Bi .snd .ret)
          ∙ C .⋆IdL _)

    transposeR⁻ : {w x y z : C .ob} {A : C [ w , x ]}
      (q : CatIso C x y) (Bi : CatIso C y z) (Ci : CatIso C w z)
      → q .snd .inv ≡ Bi .fst ⋆⟨ C ⟩ (Ci .snd .inv ⋆⟨ C ⟩ A)
      → A ⋆⟨ C ⟩ (q .fst ⋆⟨ C ⟩ Bi .fst) ≡ Ci .fst
    transposeR⁻ {A = A} q Bi Ci p =
      ⋆CancelL (invIso Ci)
        ( sym (C .⋆Assoc _ _ _)
        ∙ ⋆InvRMove⁻ (⋆Iso q Bi)
            ( ⋆CancelL Bi
                ( sym p
                ∙ sym ( sym (C .⋆Assoc _ _ _)
                      ∙ cong (λ z → z ⋆⟨ C ⟩ q .snd .inv) (Bi .snd .ret)
                      ∙ C .⋆IdL _))
            ∙ sym (C .⋆IdL _))
        ∙ sym (Ci .snd .sec))

    transposeL : {x y z : C .ob} {L : C [ z , x ]} {Φ : C [ z , y ]}
      {Ψ : C [ y , z ]} (q : CatIso C x y)
      → Ψ ⋆⟨ C ⟩ Φ ≡ C .id
      → L ⋆⟨ C ⟩ q .fst ≡ Φ
      → q .snd .inv ≡ Ψ ⋆⟨ C ⟩ L
    transposeL {Ψ = Ψ} q e p =
      sym ( cong (λ z → Ψ ⋆⟨ C ⟩ z) (⋆InvRMove q p)
          ∙ sym (C .⋆Assoc _ _ _)
          ∙ cong (λ z → z ⋆⟨ C ⟩ q .snd .inv) e
          ∙ C .⋆IdL _)

    transposeL⁻ : {x y z : C .ob} {L : C [ z , x ]} {Φ : C [ z , y ]}
      {Ψ : C [ y , z ]} (q : CatIso C x y)
      → Φ ⋆⟨ C ⟩ Ψ ≡ C .id
      → q .snd .inv ≡ Ψ ⋆⟨ C ⟩ L
      → L ⋆⟨ C ⟩ q .fst ≡ Φ
    transposeL⁻ {Φ = Φ} q e p =
        cong (λ z → z ⋆⟨ C ⟩ q .fst)
          (sym ( cong (λ z → Φ ⋆⟨ C ⟩ z) p
               ∙ sym (C .⋆Assoc _ _ _)
               ∙ cong (λ z → z ⋆⟨ C ⟩ _) e
               ∙ C .⋆IdL _))
      ∙ C .⋆Assoc _ _ _
      ∙ cong (λ z → Φ ⋆⟨ C ⟩ z) (q .snd .sec)
      ∙ C .⋆IdR _


module _ {K : Bicategory ℓ ℓ' ℓ''} (M : TwoMonad K) where
  private
    module K = Bicategory K
    module M = TwoMonad M
    module T = Pseudofunctor M.T

  T₀ : K.0Cell → K.0Cell
  T₀ = T.F-ob

  T₁ : {x y : K.0Cell} → K.1Cell x y → K.1Cell (T₀ x) (T₀ y)
  T₁ = T.F-1cell

  T₂ : {x y : K.0Cell}{f g : K.1Cell x y}
    → K.2Cell f g → K.2Cell (T₁ f) (T₁ g)
  T₂ = T.F-2cell

  T₂Id : {x y : K.0Cell}{f : K.1Cell x y} → T₂ (K.id₂ {f = f}) ≡ K.id₂
  T₂Id = Functor.F-id T.F-Hom

  T₂Seq : {x y : K.0Cell}{f g h : K.1Cell x y}
    (α : K.2Cell f g) (β : K.2Cell g h)
    → T₂ (α K.⋆₂ β) ≡ T₂ α K.⋆₂ T₂ β
  T₂Seq α β = Functor.F-seq T.F-Hom α β

  ηc : (x : K.0Cell) → K.1Cell x (T₀ x)
  ηc x = M.η .N-1cell x

  μc : (x : K.0Cell) → K.1Cell (T₀ (T₀ x)) (T₀ x)
  μc x = M.μ .N-1cell x

  -- A strict algebra: the two laws are equations of 1-cells.
  record StrictAlgebra : Type (ℓ-max ℓ ℓ') where
    no-eta-equality
    field
      carrier : K.0Cell
      act     : K.1Cell (T₀ carrier) carrier
      actUnit : ηc carrier K.⋆₁ act ≡ K.id₁
      actMult : T₁ act K.⋆₁ act ≡ μc carrier K.⋆₁ act

  -- A pseudoalgebra: the same two laws, up to invertible 2-cells.
  record PseudoAlgebra : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
    no-eta-equality
    field
      carrier    : K.0Cell
      act        : K.1Cell (T₀ carrier) carrier
      actUnit    : K.2Cell (ηc carrier K.⋆₁ act) K.id₁
      actMult    : K.2Cell (T₁ act K.⋆₁ act) (μc carrier K.⋆₁ act)
      actUnitIso : isIso K.Hom[ carrier , carrier ] actUnit
      actMultIso : isIso K.Hom[ T₀ (T₀ carrier) , carrier ] actMult

  open StrictAlgebra
  open PseudoAlgebra

  strictAlgebra→pseudoAlgebra : StrictAlgebra → PseudoAlgebra
  strictAlgebra→pseudoAlgebra A .carrier = A .carrier
  strictAlgebra→pseudoAlgebra A .act = A .act
  strictAlgebra→pseudoAlgebra A .actUnit =
    pathToIso {C = K.Hom[ _ , _ ]} (A .actUnit) .fst
  strictAlgebra→pseudoAlgebra A .actMult =
    pathToIso {C = K.Hom[ _ , _ ]} (A .actMult) .fst
  strictAlgebra→pseudoAlgebra A .actUnitIso =
    pathToIso {C = K.Hom[ _ , _ ]} (A .actUnit) .snd
  strictAlgebra→pseudoAlgebra A .actMultIso =
    pathToIso {C = K.Hom[ _ , _ ]} (A .actMult) .snd

  private
    -- Components of the 2-monad's own unit and associativity laws.
    unitLc : (x : K.0Cell) → K.2Cell (T₁ (ηc x) K.⋆₁ μc x) K.id₁
    unitLc x = M.unitL .fst .M-ob x

    assocc : (x : K.0Cell)
      → K.2Cell (μc (T₀ x) K.⋆₁ μc x) (K.id₁ K.⋆₁ (T₁ (μc x) K.⋆₁ μc x))
    assocc x = M.assoc .fst .M-ob x

    F⁰⁻ = κ⁰⁻ M.T
    F²⁻ = κ²⁻ M.T
  -- The two coherence axioms of a pseudoalgebra, as predicates rather
  -- than fields: `unitCoherence` compares the multiplication
  -- constraint whiskered by `T η` with `T` of the unit constraint;
  -- `multCoherence` is the corresponding pentagon over `T³`.
  module _ (A : PseudoAlgebra) where
    private
      c = A .carrier
      a = A .act
      u = A .actUnit
      m = A .actMult

    unitCoherence : Type ℓ''
    unitCoherence =
        (T₁ (ηc c) K.◁w m)
          K.⋆₂ K.α⁻ (T₁ (ηc c)) (μc c) a
          K.⋆₂ (unitLc c K.▷w a)
      ≡   K.α⁻ (T₁ (ηc c)) (T₁ a) a
          K.⋆₂ (T.F² (ηc c) a K.▷w a)
          K.⋆₂ (T₂ u K.▷w a)
          K.⋆₂ (F⁰⁻ K.▷w a)

    multCoherence : Type ℓ''
    multCoherence =
        (T₁ (T₁ a) K.◁w m)
          K.⋆₂ K.α⁻ (T₁ (T₁ a)) (μc c) a
          K.⋆₂ (M.μ .N-hom a K.▷w a)
          K.⋆₂ K.α⁺ (μc (T₀ c)) (T₁ a) a
          K.⋆₂ (μc (T₀ c) K.◁w m)
          K.⋆₂ K.α⁻ (μc (T₀ c)) (μc c) a
          K.⋆₂ (assocc c K.▷w a)
          K.⋆₂ (K.λ⁺ (T₁ (μc c) K.⋆₁ μc c) K.▷w a)
      ≡   K.α⁻ (T₁ (T₁ a)) (T₁ a) a
          K.⋆₂ (T.F² (T₁ a) a K.▷w a)
          K.⋆₂ (T₂ m K.▷w a)
          K.⋆₂ (F²⁻ (μc c) a K.▷w a)
          K.⋆₂ K.α⁺ (T₁ (μc c)) (T₁ a) a
          K.⋆₂ (T₁ (μc c) K.◁w m)
          K.⋆₂ K.α⁻ (T₁ (μc c)) (μc c) a

  isCoherentPseudoAlgebra : PseudoAlgebra → Type ℓ''
  isCoherentPseudoAlgebra A = unitCoherence A × multCoherence A

  CoherentPseudoAlgebra : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  CoherentPseudoAlgebra = Σ PseudoAlgebra isCoherentPseudoAlgebra

  -- Morphisms of pseudoalgebras: a 1-cell together with a
  -- (not necessarily invertible) comparison 2-cell, coherent with the
  -- unit and multiplication constraints of the two algebras.  The
  -- variance says which way the comparison 2-cell points.
  module _ (A B : PseudoAlgebra) where
    private
      Ac = A .carrier
      Bc = B .carrier
      a  = A .act
      b  = B .act
      uB⁻ = B .actUnitIso .inv
      mA⁻ = A .actMultIso .inv

    -- The comparison 2-cell.  In the `lax` variance it points the way
    -- a lax monoidal functor's constraint does.
    AlgCell : Variance → K.1Cell Ac Bc → Type ℓ''
    AlgCell lax   f = K.2Cell (T₁ f K.⋆₁ b) (a K.⋆₁ f)
    AlgCell colax f = K.2Cell (a K.⋆₁ f) (T₁ f K.⋆₁ b)

    -- The unit axiom.  Reversing the comparison cell forces the
    -- algebra's own unit constraint to be used backwards, which is
    -- why `PseudoAlgebra` and not `LaxAlgebra` is the right domain.
    UnitAx : (v : Variance) (f : K.1Cell Ac Bc) → AlgCell v f → Type ℓ''
    UnitAx lax f c =
        K.α⁻ f (ηc Bc) b
          K.⋆₂ (M.η .N-hom f K.▷w b)
          K.⋆₂ K.α⁺ (ηc Ac) (T₁ f) b
          K.⋆₂ (ηc Ac K.◁w c)
          K.⋆₂ K.α⁻ (ηc Ac) a f
          K.⋆₂ (A .actUnit K.▷w f)
          K.⋆₂ K.λ⁺ f
      ≡ (f K.◁w B .actUnit) K.⋆₂ K.ρ⁺ f
    UnitAx colax f c =
        (ηc Ac K.◁w c)
      ≡   K.α⁻ (ηc Ac) a f
          K.⋆₂ (A .actUnit K.▷w f)
          K.⋆₂ K.λ⁺ f
          K.⋆₂ K.ρ⁻ f
          K.⋆₂ (f K.◁w uB⁻)
          K.⋆₂ K.α⁻ f (ηc Bc) b
          K.⋆₂ (M.η .N-hom f K.▷w b)
          K.⋆₂ K.α⁺ (ηc Ac) (T₁ f) b

    -- The multiplication axiom.
    MultAx : (v : Variance) (f : K.1Cell Ac Bc) → AlgCell v f → Type ℓ''
    MultAx lax f c =
        (T₁ (T₁ f) K.◁w B .actMult)
          K.⋆₂ K.α⁻ (T₁ (T₁ f)) (μc Bc) b
          K.⋆₂ (M.μ .N-hom f K.▷w b)
          K.⋆₂ K.α⁺ (μc Ac) (T₁ f) b
          K.⋆₂ (μc Ac K.◁w c)
      ≡   K.α⁻ (T₁ (T₁ f)) (T₁ b) b
          K.⋆₂ (T.F² (T₁ f) b K.▷w b)
          K.⋆₂ (T₂ c K.▷w b)
          K.⋆₂ (T.F-seq-isIso (a , f) .inv K.▷w b)
          K.⋆₂ K.α⁺ (T₁ a) (T₁ f) b
          K.⋆₂ (T₁ a K.◁w c)
          K.⋆₂ K.α⁻ (T₁ a) a f
          K.⋆₂ (A .actMult K.▷w f)
          K.⋆₂ K.α⁺ (μc Ac) a f
    MultAx colax f c =
        (μc Ac K.◁w c)
      ≡   K.α⁻ (μc Ac) a f
          K.⋆₂ (mA⁻ K.▷w f)
          K.⋆₂ K.α⁺ (T₁ a) a f
          K.⋆₂ (T₁ a K.◁w c)
          K.⋆₂ K.α⁻ (T₁ a) (T₁ f) b
          K.⋆₂ (T.F² a f K.▷w b)
          K.⋆₂ (T₂ c K.▷w b)
          K.⋆₂ (T.F-seq-isIso (T₁ f , b) .inv K.▷w b)
          K.⋆₂ K.α⁺ (T₁ (T₁ f)) (T₁ b) b
          K.⋆₂ (T₁ (T₁ f) K.◁w B .actMult)
          K.⋆₂ K.α⁻ (T₁ (T₁ f)) (μc Bc) b
          K.⋆₂ (M.μ .N-hom f K.▷w b)
          K.⋆₂ K.α⁺ (μc Ac) (T₁ f) b

    record AlgHom (v : Variance) : Type (ℓ-max ℓ' ℓ'') where
      no-eta-equality
      field
        mor    : K.1Cell Ac Bc
        cell   : AlgCell v mor
        unitAx : UnitAx v mor cell
        multAx : MultAx v mor cell

    open AlgHom

    -- Pseudo morphisms: those whose comparison cell is invertible.
    -- The condition does not mention the variance.
    isPseudoAlgHom : {v : Variance} → AlgHom v → Type ℓ''
    isPseudoAlgHom {lax} h = isIso K.Hom[ T₀ Ac , Bc ] (h .cell)
    isPseudoAlgHom {colax} h = isIso K.Hom[ T₀ Ac , Bc ] (h .cell)

    -- Strict morphisms: the comparison cell is the one induced by an
    -- equality of 1-cells.
    isStrictAlgHom : {v : Variance} → AlgHom v → Type (ℓ-max ℓ' ℓ'')
    isStrictAlgHom {lax} h =
      Σ[ p ∈ T₁ (h .mor) K.⋆₁ b ≡ a K.⋆₁ h .mor ]
        pathToIso {C = K.Hom[ T₀ Ac , Bc ]} p .fst ≡ h .cell
    isStrictAlgHom {colax} h =
      Σ[ p ∈ a K.⋆₁ h .mor ≡ T₁ (h .mor) K.⋆₁ b ]
        pathToIso {C = K.Hom[ T₀ Ac , Bc ]} p .fst ≡ h .cell

    isStrictAlgHom→isPseudoAlgHom : {v : Variance} (h : AlgHom v)
      → isStrictAlgHom h → isPseudoAlgHom h
    isStrictAlgHom→isPseudoAlgHom {lax} h (p , q) =
      subst (isIso K.Hom[ T₀ Ac , Bc ]) q
        (pathToIso {C = K.Hom[ T₀ Ac , Bc ]} p .snd)
    isStrictAlgHom→isPseudoAlgHom {colax} h (p , q) =
      subst (isIso K.Hom[ T₀ Ac , Bc ]) q
        (pathToIso {C = K.Hom[ T₀ Ac , Bc ]} p .snd)

    -- Algebra 2-cells: a 2-cell of the underlying 1-cells commuting
    -- with the two comparison cells.
    Compat : (v : Variance) (h k : AlgHom v)
      → K.2Cell (h .mor) (k .mor) → Type ℓ''
    Compat lax h k σ =
      (T₂ σ K.▷w b) K.⋆₂ k .cell ≡ h .cell K.⋆₂ (a K.◁w σ)
    Compat colax h k σ =
      (a K.◁w σ) K.⋆₂ k .cell ≡ h .cell K.⋆₂ (T₂ σ K.▷w b)

    isPropCompat : (v : Variance) (h k : AlgHom v)
      (σ : K.2Cell (h .mor) (k .mor)) → isProp (Compat v h k σ)
    isPropCompat lax h k σ = K.isSet2Cell _ _
    isPropCompat colax h k σ = K.isSet2Cell _ _

    AlgHom2 : {v : Variance} → AlgHom v → AlgHom v → Type ℓ''
    AlgHom2 {v} h k =
      Σ[ σ ∈ K.2Cell (h .mor) (k .mor) ] Compat v h k σ

    idCompat : (v : Variance) (h : AlgHom v) → Compat v h h K.id₂
    idCompat lax h =
        K.⟨ K.⟨ T₂Id ⟩▷ b ∙ K.▷wId b ⟩⋆₂⟨⟩
      ∙ K.⋆₂IdL _
      ∙ sym (K.⟨⟩⋆₂⟨ K.◁wId a ⟩ ∙ K.⋆₂IdR _)
    idCompat colax h =
        K.⟨ K.◁wId a ⟩⋆₂⟨⟩
      ∙ K.⋆₂IdL _
      ∙ sym (K.⟨⟩⋆₂⟨ K.⟨ T₂Id ⟩▷ b ∙ K.▷wId b ⟩ ∙ K.⋆₂IdR _)

    idAlgHom2 : {v : Variance} (h : AlgHom v) → AlgHom2 h h
    idAlgHom2 h .fst = K.id₂
    idAlgHom2 {v} h .snd = idCompat v h

    seqCompat : (v : Variance) (h k l : AlgHom v)
      (σ : AlgHom2 h k) (τ : AlgHom2 k l)
      → Compat v h l (σ .fst K.⋆₂ τ .fst)
    seqCompat lax h k l σ τ =
        K.⟨ K.⟨ T₂Seq (σ .fst) (τ .fst) ⟩▷ b
          ∙ ▷wSeq K (T₂ (σ .fst)) (T₂ (τ .fst)) b ⟩⋆₂⟨⟩
      ∙ K.⋆₂Assoc _ _ _
      ∙ K.⟨⟩⋆₂⟨ τ .snd ⟩
      ∙ sym (K.⋆₂Assoc _ _ _)
      ∙ K.⟨ σ .snd ⟩⋆₂⟨⟩
      ∙ K.⋆₂Assoc _ _ _
      ∙ K.⟨⟩⋆₂⟨ sym (◁wSeq K a (σ .fst) (τ .fst)) ⟩
    seqCompat colax h k l σ τ =
        K.⟨ ◁wSeq K a (σ .fst) (τ .fst) ⟩⋆₂⟨⟩
      ∙ K.⋆₂Assoc _ _ _
      ∙ K.⟨⟩⋆₂⟨ τ .snd ⟩
      ∙ sym (K.⋆₂Assoc _ _ _)
      ∙ K.⟨ σ .snd ⟩⋆₂⟨⟩
      ∙ K.⋆₂Assoc _ _ _
      ∙ K.⟨⟩⋆₂⟨ sym ( K.⟨ T₂Seq (σ .fst) (τ .fst) ⟩▷ b
                    ∙ ▷wSeq K (T₂ (σ .fst)) (T₂ (τ .fst)) b) ⟩

    seqAlgHom2 : {v : Variance} {h k l : AlgHom v}
      → AlgHom2 h k → AlgHom2 k l → AlgHom2 h l
    seqAlgHom2 σ τ .fst = σ .fst K.⋆₂ τ .fst
    seqAlgHom2 {v} {h} {k} {l} σ τ .snd = seqCompat v h k l σ τ

    AlgHom2≡ : {v : Variance} {h k : AlgHom v} {σ τ : AlgHom2 h k}
      → σ .fst ≡ τ .fst → σ ≡ τ
    AlgHom2≡ {v} {h} {k} = Σ≡Prop (isPropCompat v h k)

    -- The hom-category of algebra morphisms and algebra 2-cells.
    AlgHomCat : Variance → Category (ℓ-max ℓ' ℓ'') ℓ''
    AlgHomCat v .ob = AlgHom v
    AlgHomCat v .Hom[_,_] = AlgHom2
    AlgHomCat v .id {h} = idAlgHom2 h
    AlgHomCat v ._⋆_ {h} {k} {l} = seqAlgHom2 {v} {h} {k} {l}
    AlgHomCat v .⋆IdL {h} {k} σ = AlgHom2≡ {v} {h} {k} (K.⋆₂IdL _)
    AlgHomCat v .⋆IdR {h} {k} σ = AlgHom2≡ {v} {h} {k} (K.⋆₂IdR _)
    AlgHomCat v .⋆Assoc {h} {k} {l} {m} σ τ ν =
      AlgHom2≡ {v} {h} {m} (K.⋆₂Assoc _ _ _)
    AlgHomCat v .isSetHom =
      isSetΣ K.isSet2Cell λ _ →
        isProp→isSet (isPropCompat v _ _ _)

    -- A comparison cell that is invertible satisfies the lax axioms
    -- iff its inverse satisfies the colax ones: the two are
    -- transposes along that cell.  This is why invertibility is not
    -- part of the variance.
    module _ (f : K.1Cell Ac Bc) (c : AlgCell lax f)
             (ci : isIso K.Hom[ T₀ Ac , Bc ] c) where
      private
        c⁻ = ci .inv
        Tf = T₁ f
        Ta = T₁ a
        Tb = T₁ b
        TTf = T₁ (T₁ f)
        nA = ηc Ac
        muA = μc Ac

        Bη : CatIso K.Hom[ Ac , Bc ] (nA K.⋆₁ (a K.⋆₁ f)) f
        Bη = ⋆Iso (invIso (αI K nA a f))
               (⋆Iso (_ , ▷wIsIso K f (A .actUnitIso))
                     (K.λ⁺ f , K.λU Ac Bc .nIso (tt* , f)))

        Cη : CatIso K.Hom[ Ac , Bc ] (f K.⋆₁ (ηc Bc K.⋆₁ b)) f
        Cη = ⋆Iso (_ , ◁wIsIso K f (B .actUnitIso)) (ρI K f)

        qη : CatIso K.Hom[ Ac , Bc ]
               (nA K.⋆₁ (Tf K.⋆₁ b)) (nA K.⋆₁ (a K.⋆₁ f))
        qη = _ , ◁wIsIso K nA ci

        qμ : CatIso K.Hom[ T₀ (T₀ Ac) , Bc ]
               (muA K.⋆₁ (Tf K.⋆₁ b)) (muA K.⋆₁ (a K.⋆₁ f))
        qμ = _ , ◁wIsIso K muA ci

        Φi : CatIso K.Hom[ T₀ (T₀ Ac) , Bc ]
               (TTf K.⋆₁ (Tb K.⋆₁ b)) (muA K.⋆₁ (a K.⋆₁ f))
        Φi = ⋆Iso (invIso (αI K TTf Tb b))
             (⋆Iso (_ , ▷wIsIso K b (T.F-seq-isIso (Tf , b)))
             (⋆Iso (_ , ▷wIsIso K b (F-PresIsIso {F = T.F-Hom} ci))
             (⋆Iso (_ , ▷wIsIso K b (invIso (κ²I M.T a f) .snd))
             (⋆Iso (αI K Ta Tf b)
             (⋆Iso (_ , ◁wIsIso K Ta ci)
             (⋆Iso (invIso (αI K Ta a f))
             (⋆Iso (_ , ▷wIsIso K f (A .actMultIso))
                   (αI K muA a f))))))))

        Ψ : K.2Cell (muA K.⋆₁ (a K.⋆₁ f)) (TTf K.⋆₁ (Tb K.⋆₁ b))
        Ψ =   K.α⁻ muA a f
          K.⋆₂ (mA⁻ K.▷w f)
          K.⋆₂ K.α⁺ Ta a f
          K.⋆₂ (Ta K.◁w c⁻)
          K.⋆₂ K.α⁻ Ta Tf b
          K.⋆₂ (T.F² a f K.▷w b)
          K.⋆₂ (T₂ c⁻ K.▷w b)
          K.⋆₂ (T.F-seq-isIso (Tf , b) .inv K.▷w b)
          K.⋆₂ K.α⁺ TTf Tb b

        flat : Φi .snd .inv ≡ Ψ
        flat = K.⟨ K.⟨ K.⟨ K.⟨ K.⟨ K.⟨ aR2 K _ _ _
                                     ⟩⋆₂⟨⟩ ∙ aR3 K _ _ _ _
                                 ⟩⋆₂⟨⟩ ∙ aR4 K _ _ _ _ _
                             ⟩⋆₂⟨⟩ ∙ aR5 K _ _ _ _ _ _
                         ⟩⋆₂⟨⟩ ∙ aR6 K _ _ _ _ _ _ _
                     ⟩⋆₂⟨⟩ ∙ aR7 K _ _ _ _ _ _ _ _
                 ⟩⋆₂⟨⟩ ∙ aR8 K _ _ _ _ _ _ _ _ _

      laxUnit→colaxUnit : UnitAx lax f c → UnitAx colax f c⁻
      laxUnit→colaxUnit e =
          transposeR qη Bη Cη (aR3 K _ _ _ _ ∙ e)
        ∙ K.⟨⟩⋆₂⟨ aR2 K _ _ _ ⟩
        ∙ aR3 K _ _ _ _

      colaxUnit→laxUnit : UnitAx colax f c⁻ → UnitAx lax f c
      colaxUnit→laxUnit e =
          sym (aR3 K _ _ _ _)
        ∙ transposeR⁻ qη Bη Cη
            (e ∙ sym (K.⟨⟩⋆₂⟨ aR2 K _ _ _ ⟩ ∙ aR3 K _ _ _ _))

      laxMult→colaxMult : MultAx lax f c → MultAx colax f c⁻
      laxMult→colaxMult e =
          transposeL qμ (K.⟨ sym flat ⟩⋆₂⟨⟩ ∙ Φi .snd .sec)
            (aR4 K _ _ _ _ _ ∙ e)
        ∙ aR9 K _ _ _ _ _ _ _ _ _ _

      colaxMult→laxMult : MultAx colax f c⁻ → MultAx lax f c
      colaxMult→laxMult e =
          sym (aR4 K _ _ _ _ _)
        ∙ transposeL⁻ qμ (K.⟨⟩⋆₂⟨ sym flat ⟩ ∙ Φi .snd .ret)
            (e ∙ sym (aR9 K _ _ _ _ _ _ _ _ _ _))

    -- A pseudo morphism, read in the other variance.
    pseudoLax→colax : (h : AlgHom lax) → isPseudoAlgHom h → AlgHom colax
    pseudoLax→colax h hi .mor = h .mor
    pseudoLax→colax h hi .cell = hi .inv
    pseudoLax→colax h hi .unitAx =
      laxUnit→colaxUnit (h .mor) (h .cell) hi (h .unitAx)
    pseudoLax→colax h hi .multAx =
      laxMult→colaxMult (h .mor) (h .cell) hi (h .multAx)

    pseudoColax→lax : (k : AlgHom colax) → isPseudoAlgHom k → AlgHom lax
    pseudoColax→lax k ki .mor = k .mor
    pseudoColax→lax k ki .cell = ki .inv
    pseudoColax→lax k ki .unitAx =
      colaxUnit→laxUnit (k .mor) (ki .inv)
        (invIso (k .cell , ki) .snd) (k .unitAx)
    pseudoColax→lax k ki .multAx =
      colaxMult→laxMult (k .mor) (ki .inv)
        (invIso (k .cell , ki) .snd) (k .multAx)

{-
  Sanity check: for the identity 2-monad both `η` and `μ` are identity
  1-cells, so a pseudoalgebra is a 0-cell whose action is isomorphic to
  `id₁`, and every 0-cell carries one.
-}
module _ (K : Bicategory ℓ ℓ' ℓ'') where
  private
    module K = Bicategory K

  open PseudoAlgebra

  idAlgebra : K.0Cell → PseudoAlgebra (idTwoMonad K)
  idAlgebra x .carrier = x
  idAlgebra x .act = K.id₁
  idAlgebra x .actUnit = K.λ⁺ K.id₁
  idAlgebra x .actMult = K.id₂
  idAlgebra x .actUnitIso = K.λU x x .nIso (tt* , K.id₁)
  idAlgebra x .actMultIso = idCatIso .snd

  -- The data really is trivial: identity action, identity constraint.
  idAlgebraTrivial : (x : K.0Cell)
    → (idAlgebra x .act ≡ K.id₁) × (idAlgebra x .actMult ≡ K.id₂)
  idAlgebraTrivial x = refl , refl

  -- Conversely the action of any such algebra is invertible.
  idAlgebraActIso : (A : PseudoAlgebra (idTwoMonad K))
    → CatIso K.Hom[ A .carrier , A .carrier ] (A .act) K.id₁
  idAlgebraActIso A .fst = K.λ⁻ (A .act) K.⋆₂ A .actUnit
  idAlgebraActIso A .snd =
    ⋆IsIso (invIso (K.λ⁺ (A .act) , K.λU _ _ .nIso (tt* , A .act)) .snd)
           (A .actUnitIso)

  idAlgebraUnitCoh : (x : K.0Cell)
    → unitCoherence (idTwoMonad K) (idAlgebra x)
  idAlgebraUnitCoh x =
      K.⟨ K.◁wId K.id₁ ⟩⋆₂⟨⟩ ∙ K.⋆₂IdL _
    ∙ sym ( K.⟨⟩⋆₂⟨ K.⟨ K.▷wId K.id₁ ⟩⋆₂⟨⟩
                  ∙ K.⋆₂IdL _
                  ∙ K.⟨⟩⋆₂⟨ K.▷wId K.id₁ ⟩
                  ∙ K.⋆₂IdR _ ⟩ )

  idAlgebraMultCoh : (x : K.0Cell)
    → multCoherence (idTwoMonad K) (idAlgebra x)
  idAlgebraMultCoh x =
      (  K.⟨ K.◁wId e ⟩⋆₂⟨⟩ ∙ K.⋆₂IdL _
       ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨ K.◁wId e ⟩⋆₂⟨⟩ ∙ K.⋆₂IdL _ ⟩ ⟩ ⟩
       ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ sym (K.⋆₂Assoc _ _ _)
                       ∙ K.⟨ αret ⟩⋆₂⟨⟩ ∙ K.⋆₂IdL _ ⟩ ⟩
       ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ sym (▷wSeq K _ _ e) ⟩
               ∙ sym (▷wSeq K _ _ e) ∙ K.⟨ key ⟩▷ e ∙ K.▷wId e ⟩
       ∙ K.⋆₂IdR _)
    ∙ sym
      (  K.⟨⟩⋆₂⟨ K.⟨ K.▷wId e ⟩⋆₂⟨⟩ ∙ K.⋆₂IdL _ ⟩
       ∙ K.⟨⟩⋆₂⟨ K.⟨ K.▷wId e ⟩⋆₂⟨⟩ ∙ K.⋆₂IdL _ ⟩
       ∙ K.⟨⟩⋆₂⟨ K.⟨ K.▷wId e ⟩⋆₂⟨⟩ ∙ K.⋆₂IdL _ ⟩
       ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨ K.◁wId e ⟩⋆₂⟨⟩ ∙ K.⋆₂IdL _ ⟩ ⟩
       ∙ K.⟨⟩⋆₂⟨ αret ⟩
       ∙ K.⋆₂IdR _)
    where
    e : K.1Cell x x
    e = K.id₁

    αret : K.α⁺ e e e K.⋆₂ K.α⁻ e e e ≡ K.id₂
    αret = K.α x x x x .nIso (e , e , e) .ret

    key : (K.ρ⁺ e K.⋆₂ K.λ⁻ e)
            K.⋆₂ (((K.λ⁻ e K.▷w e) K.⋆₂ K.α⁺ e e e) K.⋆₂ K.λ⁺ (e K.⋆₁ e))
        ≡ K.id₂
    key =
        K.⟨⟩⋆₂⟨ K.⟨ λ⁻⋆₁ K e e ⟩⋆₂⟨⟩
              ∙ K.λU x x .nIso (tt* , e K.⋆₁ e) .sec ⟩
      ∙ K.⋆₂IdR _
      ∙ K.⟨ sym (λ⁺≡ρ⁺ K) ⟩⋆₂⟨⟩
      ∙ K.λU x x .nIso (tt* , e) .ret

  idCoherentAlgebra : K.0Cell → CoherentPseudoAlgebra (idTwoMonad K)
  idCoherentAlgebra x =
    idAlgebra x , idAlgebraUnitCoh x , idAlgebraMultCoh x
