{-# OPTIONS --lossy-unification #-}
{-
  Algebras for a 2-monad `M` on a bicategory `K`.

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
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Functor.Properties
open import Cubical.Categories.Bicategory.Functor.Identity
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.TwoMonad.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

open Category
open NatIso
open LaxNatTrans
open Modification
open isIso

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

  -- Lax morphisms of pseudoalgebras: a 1-cell together with a
  -- (not necessarily invertible) comparison 2-cell, coherent with the
  -- unit and multiplication constraints of the two algebras.
  module _ (A B : PseudoAlgebra) where
    private
      Ac = A .carrier
      Bc = B .carrier
      a  = A .act
      b  = B .act

    record AlgHom : Type (ℓ-max ℓ' ℓ'') where
      no-eta-equality
      field
        mor  : K.1Cell Ac Bc
        cell : K.2Cell (T₁ mor K.⋆₁ b) (a K.⋆₁ mor)

        unitAx :
            K.α⁻ mor (ηc Bc) b
              K.⋆₂ (M.η .N-hom mor K.▷w b)
              K.⋆₂ K.α⁺ (ηc Ac) (T₁ mor) b
              K.⋆₂ (ηc Ac K.◁w cell)
              K.⋆₂ K.α⁻ (ηc Ac) a mor
              K.⋆₂ (A .actUnit K.▷w mor)
              K.⋆₂ K.λ⁺ mor
          ≡ (mor K.◁w B .actUnit) K.⋆₂ K.ρ⁺ mor

        multAx :
            (T₁ (T₁ mor) K.◁w B .actMult)
              K.⋆₂ K.α⁻ (T₁ (T₁ mor)) (μc Bc) b
              K.⋆₂ (M.μ .N-hom mor K.▷w b)
              K.⋆₂ K.α⁺ (μc Ac) (T₁ mor) b
              K.⋆₂ (μc Ac K.◁w cell)
          ≡   K.α⁻ (T₁ (T₁ mor)) (T₁ b) b
              K.⋆₂ (T.F² (T₁ mor) b K.▷w b)
              K.⋆₂ (T₂ cell K.▷w b)
              K.⋆₂ (T.F-seq-isIso (a , mor) .inv K.▷w b)
              K.⋆₂ K.α⁺ (T₁ a) (T₁ mor) b
              K.⋆₂ (T₁ a K.◁w cell)
              K.⋆₂ K.α⁻ (T₁ a) a mor
              K.⋆₂ (A .actMult K.▷w mor)
              K.⋆₂ K.α⁺ (μc Ac) a mor

    open AlgHom

    -- Pseudo morphisms: those whose comparison cell is invertible.
    isPseudoAlgHom : AlgHom → Type ℓ''
    isPseudoAlgHom h = isIso K.Hom[ T₀ Ac , Bc ] (h .cell)

    -- Strict morphisms: the comparison cell is the one induced by an
    -- equality of 1-cells.
    isStrictAlgHom : AlgHom → Type (ℓ-max ℓ' ℓ'')
    isStrictAlgHom h =
      Σ[ p ∈ T₁ (h .mor) K.⋆₁ b ≡ a K.⋆₁ h .mor ]
        pathToIso {C = K.Hom[ T₀ Ac , Bc ]} p .fst ≡ h .cell

    isStrictAlgHom→isPseudoAlgHom :
      (h : AlgHom) → isStrictAlgHom h → isPseudoAlgHom h
    isStrictAlgHom→isPseudoAlgHom h (p , q) =
      subst (isIso K.Hom[ T₀ Ac , Bc ]) q
        (pathToIso {C = K.Hom[ T₀ Ac , Bc ]} p .snd)

    -- Algebra 2-cells: a 2-cell of the underlying 1-cells commuting
    -- with the two comparison cells.
    AlgHom2 : AlgHom → AlgHom → Type ℓ''
    AlgHom2 h k =
      Σ[ σ ∈ K.2Cell (h .mor) (k .mor) ]
        (T₂ σ K.▷w b) K.⋆₂ k .cell ≡ h .cell K.⋆₂ (a K.◁w σ)

    idAlgHom2 : (h : AlgHom) → AlgHom2 h h
    idAlgHom2 h .fst = K.id₂
    idAlgHom2 h .snd =
        K.⟨ K.⟨ T₂Id ⟩▷ b ∙ K.▷wId b ⟩⋆₂⟨⟩
      ∙ K.⋆₂IdL _
      ∙ sym (K.⟨⟩⋆₂⟨ K.◁wId a ⟩ ∙ K.⋆₂IdR _)

    seqAlgHom2 : {h k l : AlgHom}
      → AlgHom2 h k → AlgHom2 k l → AlgHom2 h l
    seqAlgHom2 σ τ .fst = σ .fst K.⋆₂ τ .fst
    seqAlgHom2 σ τ .snd =
        K.⟨ K.⟨ T₂Seq (σ .fst) (τ .fst) ⟩▷ b
          ∙ ▷wSeq K (T₂ (σ .fst)) (T₂ (τ .fst)) b ⟩⋆₂⟨⟩
      ∙ K.⋆₂Assoc _ _ _
      ∙ K.⟨⟩⋆₂⟨ τ .snd ⟩
      ∙ sym (K.⋆₂Assoc _ _ _)
      ∙ K.⟨ σ .snd ⟩⋆₂⟨⟩
      ∙ K.⋆₂Assoc _ _ _
      ∙ K.⟨⟩⋆₂⟨ sym (◁wSeq K a (σ .fst) (τ .fst)) ⟩

    AlgHom2≡ : {h k : AlgHom} {σ τ : AlgHom2 h k}
      → σ .fst ≡ τ .fst → σ ≡ τ
    AlgHom2≡ = Σ≡Prop λ _ → K.isSet2Cell _ _

    -- The hom-category of lax algebra morphisms and algebra 2-cells.
    AlgHomCat : Category (ℓ-max ℓ' ℓ'') ℓ''
    AlgHomCat .ob = AlgHom
    AlgHomCat .Hom[_,_] = AlgHom2
    AlgHomCat .id {h} = idAlgHom2 h
    AlgHomCat ._⋆_ {h} {k} {l} = seqAlgHom2 {h} {k} {l}
    AlgHomCat .⋆IdL {h} {k} σ = AlgHom2≡ {h} {k} (K.⋆₂IdL _)
    AlgHomCat .⋆IdR {h} {k} σ = AlgHom2≡ {h} {k} (K.⋆₂IdR _)
    AlgHomCat .⋆Assoc {h} {k} {l} {m} σ τ ν =
      AlgHom2≡ {h} {m} (K.⋆₂Assoc _ _ _)
    AlgHomCat .isSetHom =
      isSetΣ K.isSet2Cell λ _ → isProp→isSet (K.isSet2Cell _ _)

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
