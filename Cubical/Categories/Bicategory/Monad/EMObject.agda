{-# OPTIONS --lossy-unification #-}
{-
  Eilenberg-Moore objects for a formal monad in a bicategory.

  An EM object of `M : MonadOn B a` IS a biuniversal element of the
  algebra prestack, whose fibre at a probe `b` is `EM B a M b` on the
  nose: the vertex is the EM 0-cell and the ELEMENT is the generic
  algebra, so `⟨ element ⟩ b` sends `h` to `h ⋆₁ u` carrying the
  reindexed action.
-}
module Cubical.Categories.Bicategory.Monad.EMObject where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More hiding (α)
open import Cubical.Categories.Instances.Functors

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Properties.Coherence
open import Cubical.Categories.Bicategory.Constructions.Op
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Hom
open import Cubical.Categories.Bicategory.Universal.Base
open import Cubical.Categories.Bicategory.Monad.Base
open import Cubical.Categories.Bicategory.Monad.Morphism
open import Cubical.Categories.Bicategory.Monad.Algebra

private
  variable
    ℓ ℓ' ℓ'' : Level

open Category
open Functor
open NatTrans
open NatIso
open isIso
open LaxFunctor
open Pseudofunctor

module EMPre {B : Bicategory ℓ ℓ' ℓ''} {a : Bicategory.0Cell B}
  (M : MonadOn B a) where
  private
    module B = Bicategory B
    module M = MonadOn M

  open Algebra
  open AlgebraMor

  Alg : B.0Cell → Type (ℓ-max ℓ' ℓ'')
  Alg b = Algebra B a M b

  EMCat : B.0Cell → Category (ℓ-max ℓ' ℓ'') ℓ''
  EMCat b = EM B a M b

  -- The action of an algebra, reindexed along a 1-cell of probes.
  reindξ : {b b' : B.0Cell} (k : B.1Cell b' b) {h : B.1Cell b a}
    → B.2Cell (h B.⋆₁ M.t) h → B.2Cell ((k B.⋆₁ h) B.⋆₁ M.t) (k B.⋆₁ h)
  reindξ k {h} ξ = B.α⁺ k h M.t B.⋆₂ (k B.◁w ξ)

  reindUnit : {b b' : B.0Cell} (k : B.1Cell b' b) (P : Alg b)
    → (((k B.⋆₁ P .x) B.◁w M.η) B.⋆₂ reindξ k (P .ξ))
      ≡ B.ρ⁺ (k B.⋆₁ P .x)
  reindUnit k P =
      pushr B (α⁺natR B k (P .x) M.η) _
    ∙ B.⟨⟩⋆₂⟨ sym (◁wSeq B k _ _) ∙ k B.◁⟨ P .α-unit ⟩ ⟩
    ∙ ρ⋆₁ B (P .x) k

  reindMult : {b b' : B.0Cell} (k : B.1Cell b' b) (P : Alg b)
    →   (B.α⁺ (k B.⋆₁ P .x) M.t M.t
          B.⋆₂ (((k B.⋆₁ P .x) B.◁w M.μ) B.⋆₂ reindξ k (P .ξ)))
      ≡ ((reindξ k (P .ξ) B.▷w M.t) B.⋆₂ reindξ k (P .ξ))
  reindMult k P = lhs ∙ sym rhs
    where
    h : B.1Cell _ a
    h = P .x
    act : B.2Cell (h B.⋆₁ M.t) h
    act = P .ξ
    Ak = B.α⁺ k h M.t
    Kξ = k B.◁w act
    Qa = B.α⁺ k (h B.⋆₁ M.t) M.t
    Kξt = k B.◁w (act B.▷w M.t)
    Pw = Ak B.▷w M.t

    N : B.2Cell (((k B.⋆₁ h) B.⋆₁ M.t) B.⋆₁ M.t) (k B.⋆₁ h)
    N = Pw B.⋆₂ (Qa B.⋆₂ (Kξt B.⋆₂ Kξ))

    lhs :   (B.α⁺ (k B.⋆₁ h) M.t M.t
              B.⋆₂ (((k B.⋆₁ h) B.◁w M.μ) B.⋆₂ reindξ k act))
          ≡ N
    lhs =
        B.⟨⟩⋆₂⟨ pushr B (α⁺natR B k h M.μ) Kξ ⟩
      ∙ sym (B.⋆₂Assoc _ _ _)
      ∙ B.⟨ sym (B.pentagon _ _ _ _ _ k h M.t M.t) ⟩⋆₂⟨⟩
      ∙ aR3 B Pw Qa (k B.◁w B.α⁺ h M.t M.t) _
      ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨
            sym (◁3 B k (B.α⁺ h M.t M.t) (h B.◁w M.μ) act)
          ∙ k B.◁⟨ P .α-mult ⟩
          ∙ ◁wSeq B k (act B.▷w M.t) act ⟩ ⟩

    rhs : ((reindξ k act B.▷w M.t) B.⋆₂ reindξ k act) ≡ N
    rhs =
        B.⟨ ▷wSeq B Ak Kξ M.t ⟩⋆₂⟨⟩
      ∙ B.⋆₂Assoc _ _ _
      ∙ B.⟨⟩⋆₂⟨ pushr B (α⁺natM B k act M.t) Kξ ⟩

  reindAlg : {b b' : B.0Cell} (k : B.1Cell b' b) → Alg b → Alg b'
  reindAlg k P .x = k B.⋆₁ P .x
  reindAlg k P .ξ = reindξ k (P .ξ)
  reindAlg k P .α-unit = reindUnit k P
  reindAlg k P .α-mult = reindMult k P

  -- The equation making a 2-cell an algebra morphism.
  AlgCond : {b : B.0Cell} (P Q : Alg b) → B.2Cell (P .x) (Q .x) → Type ℓ''
  AlgCond P Q φ = (P .ξ B.⋆₂ φ) ≡ ((φ B.▷w M.t) B.⋆₂ Q .ξ)

  algCondInv : {b : B.0Cell} (P Q : Alg b) (φ : B.2Cell (P .x) (Q .x))
    (isI : isIso B.Hom[ b , a ] φ)
    → AlgCond P Q φ → AlgCond Q P (isI .inv)
  algCondInv P Q φ isI p =
    ⋆InvsFlipSq (φ B.▷w M.t , ▷wIsIso B M.t isI) (φ , isI) (sym p)

  algIso : {b : B.0Cell} {P Q : Alg b} (φ : B.2Cell (P .x) (Q .x))
    (isI : isIso B.Hom[ b , a ] φ)
    → AlgCond P Q φ → CatIso (EMCat b) P Q
  algIso φ isI c .fst .f = φ
  algIso φ isI c .fst .f-comm = c
  algIso φ isI c .snd .inv .f = isI .inv
  algIso {P = P} {Q} φ isI c .snd .inv .f-comm = algCondInv P Q φ isI c
  algIso φ isI c .snd .sec = AlgebraMor≡ B a M _ (isI .sec)
  algIso φ isI c .snd .ret = AlgebraMor≡ B a M _ (isI .ret)

  reindCond : {b b' : B.0Cell} (k : B.1Cell b' b) {P Q : Alg b}
    (u : AlgebraMor B a M b P Q)
    → AlgCond (reindAlg k P) (reindAlg k Q) (k B.◁w u .f)
  reindCond k u =
      B.⋆₂Assoc _ _ _
    ∙ B.⟨⟩⋆₂⟨ sym (◁wSeq B k _ _) ∙ k B.◁⟨ u .f-comm ⟩ ∙ ◁wSeq B k _ _ ⟩
    ∙ sym (B.⋆₂Assoc _ _ _)
    ∙ B.⟨ sym (α⁺natM B k (u .f) M.t) ⟩⋆₂⟨⟩
    ∙ B.⋆₂Assoc _ _ _

  emReind : {b b' : B.0Cell} (k : B.1Cell b' b)
    → Functor (EMCat b) (EMCat b')
  emReind k .F-ob = reindAlg k
  emReind k .F-hom u .f = k B.◁w u .f
  emReind k .F-hom u .f-comm = reindCond k u
  emReind k .F-id = AlgebraMor≡ B a M _ (B.◁wId k)
  emReind k .F-seq _ _ = AlgebraMor≡ B a M _ (◁wSeq B k _ _)

  reind₂Cond : {b b' : B.0Cell} {k k' : B.1Cell b' b}
    (σ : B.2Cell k k') (P : Alg b)
    → AlgCond (reindAlg k P) (reindAlg k' P) (σ B.▷w P .x)
  reind₂Cond σ P =
      B.⋆₂Assoc _ _ _
    ∙ B.⟨⟩⋆₂⟨ sym (▷◁exch B σ (P .ξ)) ⟩
    ∙ sym (B.⋆₂Assoc _ _ _)
    ∙ B.⟨ sym (α⁺natL B σ (P .x) M.t) ⟩⋆₂⟨⟩
    ∙ B.⋆₂Assoc _ _ _

  emReind₂ : {b b' : B.0Cell} {k k' : B.1Cell b' b} (σ : B.2Cell k k')
    → NatTrans (emReind k) (emReind k')
  emReind₂ σ .N-ob P .f = σ B.▷w P .x
  emReind₂ σ .N-ob P .f-comm = reind₂Cond σ P
  emReind₂ σ .N-hom u = AlgebraMor≡ B a M _ (sym (▷◁exch B σ (u .f)))

  -- The unitor and associator, as algebra isomorphisms.
  ιCond : {b : B.0Cell} (P : Alg b)
    → AlgCond P (reindAlg B.id₁ P) (B.λ⁻ (P .x))
  ιCond P =
      λ⁻-nat B (P .ξ)
    ∙ sym (pushn B (λ⁻⋆₁ B (P .x) M.t) _)

  ι⁻Cond : {b : B.0Cell} (P : Alg b)
    → AlgCond (reindAlg B.id₁ P) P (B.λ⁺ (P .x))
  ι⁻Cond {b} P =
    algCondInv P (reindAlg B.id₁ P) (B.λ⁻ (P .x))
      (invIso (NatIsoAt (B.λU b a) (tt* , P .x)) .snd) (ιCond P)

  νCond : {b b' b'' : B.0Cell} (k : B.1Cell b' b) (l : B.1Cell b'' b')
    (P : Alg b)
    → AlgCond (reindAlg l (reindAlg k P)) (reindAlg (l B.⋆₁ k) P)
              (B.α⁻ l k (P .x))
  νCond k l P =
      B.⟨ B.⟨⟩⋆₂⟨ ◁wSeq B l _ _ ⟩ ⟩⋆₂⟨⟩
    ∙ aR3 B (B.α⁺ l (k B.⋆₁ P .x) M.t) (l B.◁w B.α⁺ k (P .x) M.t)
           (l B.◁w (k B.◁w P .ξ)) (B.α⁻ l k (P .x))
    ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ α⁻natR B l k (P .ξ) ⟩ ⟩
    ∙ rep3 B (pentP4 B l k (P .x) M.t) _

  ν⁻Cond : {b b' b'' : B.0Cell} (k : B.1Cell b' b) (l : B.1Cell b'' b')
    (P : Alg b)
    → AlgCond (reindAlg (l B.⋆₁ k) P) (reindAlg l (reindAlg k P))
              (B.α⁺ l k (P .x))
  ν⁻Cond k l P =
    algCondInv (reindAlg l (reindAlg k P)) (reindAlg (l B.⋆₁ k) P)
      (B.α⁻ l k (P .x)) (invIso (αI B l k (P .x)) .snd) (νCond k l P)

  private
    module HA = Pseudofunctor (Hom B a)

    EMPrecomp : {b b' : B.0Cell}
      → Functor B.Hom[ b' , b ] (FUNCTOR (EMCat b) (EMCat b'))
    EMPrecomp .F-ob k = emReind k
    EMPrecomp .F-hom σ = emReind₂ σ
    EMPrecomp .F-id =
      makeNatTransPath (funExt λ P → AlgebraMor≡ B a M _ (B.▷wId (P .x)))
    EMPrecomp .F-seq σ τ =
      makeNatTransPath (funExt λ P →
        AlgebraMor≡ B a M _ (▷wSeq B σ τ (P .x)))

    ιNT : (b : B.0Cell) → NatTrans (Id {C = EMCat b}) (emReind B.id₁)
    ιNT b .N-ob P .f = B.λ⁻ (P .x)
    ιNT b .N-ob P .f-comm = ιCond P
    ιNT b .N-hom u = AlgebraMor≡ B a M _ (λ⁻-nat B (u .f))

    ι⁻NT : (b : B.0Cell) → NatTrans (emReind B.id₁) (Id {C = EMCat b})
    ι⁻NT b .N-ob P .f = B.λ⁺ (P .x)
    ι⁻NT b .N-ob P .f-comm = ι⁻Cond P
    ι⁻NT b .N-hom u = AlgebraMor≡ B a M _ (λ-nat B (u .f))

    νNT : {b b' b'' : B.0Cell} (k : B.1Cell b' b) (l : B.1Cell b'' b')
      → NatTrans (seqCAT (EMCat b) (EMCat b') (EMCat b'')
                    .F-ob (emReind k , emReind l))
                 (emReind (l B.⋆₁ k))
    νNT k l .N-ob P .f = B.α⁻ l k (P .x)
    νNT k l .N-ob P .f-comm = νCond k l P
    νNT k l .N-hom u = AlgebraMor≡ B a M _ (α⁻natR B l k (u .f))

    ν⁻NT : {b b' b'' : B.0Cell} (k : B.1Cell b' b) (l : B.1Cell b'' b')
      → NatTrans (emReind (l B.⋆₁ k))
                 (seqCAT (EMCat b) (EMCat b') (EMCat b'')
                    .F-ob (emReind k , emReind l))
    ν⁻NT k l .N-ob P .f = B.α⁺ l k (P .x)
    ν⁻NT k l .N-ob P .f-comm = ν⁻Cond k l P
    ν⁻NT k l .N-hom u = AlgebraMor≡ B a M _ (α⁺natR B l k (u .f))

  -- The coherences are equations between 2-cells, and the underlying
  -- data is `Hom B a`'s, so they are inherited from it verbatim.
  EMLax : LaxFunctor (B ^opᴮ) (CAT {ℓ-max ℓ' ℓ''} {ℓ''})
  EMLax .F-ob = EMCat
  EMLax .F-Hom {b} {b'} = EMPrecomp {b} {b'}
  EMLax .F-id {b} .N-ob _ = ιNT b
  EMLax .F-id {b} .N-hom σ = makeNatTransPath (funExt λ P →
    AlgebraMor≡ B a M _ (N-obPath (HA.F-id .N-hom σ) (P .x)))
  EMLax .F-seq .N-ob (k , l) = νNT k l
  EMLax .F-seq .N-hom στ = makeNatTransPath (funExt λ P →
    AlgebraMor≡ B a M _ (N-obPath (HA.F-seq .N-hom στ) (P .x)))
  EMLax .lax-λ b b' k = makeNatTransPath (funExt λ P →
    AlgebraMor≡ B a M _ (N-obPath (HA.lax-λ b b' k) (P .x)))
  EMLax .lax-ρ b b' k = makeNatTransPath (funExt λ P →
    AlgebraMor≡ B a M _ (N-obPath (HA.lax-ρ b b' k) (P .x)))
  EMLax .lax-α b b' b'' b''' k l m = makeNatTransPath (funExt λ P →
    AlgebraMor≡ B a M _ (N-obPath (HA.lax-α b b' b'' b''' k l m) (P .x)))

  Prestk : Prestack B (ℓ-max ℓ' ℓ'') ℓ''
  Prestk .laxFunctor = EMLax
  Prestk .F-id-isIso {b} _ .inv = ι⁻NT b
  Prestk .F-id-isIso {b} _ .sec = makeNatTransPath (funExt λ P →
    AlgebraMor≡ B a M _ (B.λU b a .nIso (tt* , P .x) .ret))
  Prestk .F-id-isIso {b} _ .ret = makeNatTransPath (funExt λ P →
    AlgebraMor≡ B a M _ (B.λU b a .nIso (tt* , P .x) .sec))
  Prestk .F-seq-isIso (k , l) .inv = ν⁻NT k l
  Prestk .F-seq-isIso {b} {b'} {b''} (k , l) .sec =
    makeNatTransPath (funExt λ P →
      AlgebraMor≡ B a M _ (B.α b'' b' b a .nIso (l , k , P .x) .ret))
  Prestk .F-seq-isIso {b} {b'} {b''} (k , l) .ret =
    makeNatTransPath (funExt λ P →
      AlgebraMor≡ B a M _ (B.α b'' b' b a .nIso (l , k , P .x) .sec))

  -- The forgetful functor to `Hom B a`; faithful, so isos and
  -- equations upstairs are decided by their carriers.
  emForget : (b : B.0Cell) → Functor (EMCat b) B.Hom[ b , a ]
  emForget b .F-ob = x
  emForget b .F-hom = f
  emForget b .F-id = refl
  emForget b .F-seq _ _ = refl

module _ (B : Bicategory ℓ ℓ' ℓ'') (a : Bicategory.0Cell B)
  (M : MonadOn B a) where

  EMPrestack : Prestack B (ℓ-max ℓ' ℓ'') ℓ''
  EMPrestack = EMPre.Prestk {B = B} {a = a} M

  -- The fibre is the Eilenberg-Moore category of `Monad/Algebra.agda`
  -- on the nose, not merely up to isomorphism.
  EMPrestack-fibre : (b : Bicategory.0Cell B)
    → Pseudofunctor.F-ob EMPrestack b ≡ EM B a M b
  EMPrestack-fibre b = refl

  EMObjectᴮ : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  EMObjectᴮ = BiuniversalElement EMPrestack

module _ (B : Bicategory ℓ ℓ' ℓ'') where
  hasEMObjectsᴮ : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  hasEMObjectsᴮ =
    {a : Bicategory.0Cell B} (M : MonadOn B a) → EMObjectᴮ B a M

  EMObjectOfMonadᴮ : Monad B → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  EMObjectOfMonadᴮ M = EMObjectᴮ B (Monad.a M) (fromMonad B M)

module EMObjectᴮNotation {B : Bicategory ℓ ℓ' ℓ''}
  {a : Bicategory.0Cell B} {M : MonadOn B a} (E : EMObjectᴮ B a M) where
  private
    module B = Bicategory B
    module M = MonadOn M
  module Alg = EMPre {B = B} {a = a} M
  open BiuniversalElementNotation E public
  open Algebra
  open AlgebraMor

  -- The generic algebra: the forgetful 1-cell and its action.
  uᴮ : B.1Cell vertex a
  uᴮ = element .x

  ξᴮ : B.2Cell (uᴮ B.⋆₁ M.t) uᴮ
  ξᴮ = element .ξ

  introᴱ : {b : B.0Cell} → Alg.Alg b → B.1Cell b vertex
  introᴱ P = intro P

  introᴱβ : {b : B.0Cell} (P : Alg.Alg b)
    → (introᴱ P B.⋆₁ uᴮ) B.≅₂ P .x
  introᴱβ {b} P = F-Iso {F = Alg.emForget b} (β P)

  -- `β` is an algebra morphism: it carries the reindexed action.
  introᴱβ-cond : {b : B.0Cell} (P : Alg.Alg b)
    → Alg.AlgCond (Alg.reindAlg (introᴱ P) element) P (introᴱβ P .fst)
  introᴱβ-cond P = β P .fst .f-comm

  introᴱη : {b : B.0Cell} {h : B.1Cell b vertex} {P : Alg.Alg b}
    (φ : (h B.⋆₁ uᴮ) B.≅₂ P .x)
    → Alg.AlgCond (Alg.reindAlg h element) P (φ .fst)
    → h B.≅₂ introᴱ P
  introᴱη φ c = intro≡ (Alg.algIso (φ .fst) (φ .snd) c)

  uᴮ-ext : {b : B.0Cell} {h k : B.1Cell b vertex} (α γ : B.2Cell h k)
    → (α B.▷w uᴮ) ≡ (γ B.▷w uᴮ) → α ≡ γ
  uᴮ-ext α γ p = extensionality α γ (AlgebraMor≡ B a M _ p)

  -- naturality in the probe, from the generic `intro-natural`
  introᴱ-nat : {b' b : B.0Cell} (k : B.1Cell b' b) (P : Alg.Alg b)
    → (k B.⋆₁ introᴱ P) B.≅₂ introᴱ (Alg.reindAlg k P)
  introᴱ-nat k P = intro-natural k P
