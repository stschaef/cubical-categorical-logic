{-# OPTIONS --lossy-unification #-}
{-
  The bicategory `Alg` of pseudoalgebras for a 2-monad: 0-cells are
  pseudoalgebras (coherence is not needed), 1-cells are lax morphisms
  and 2-cells are algebra 2-cells.  Unitors and associator are those
  of the ambient bicategory, so triangle and pentagon are inherited.
-}
module Cubical.Categories.Bicategory.TwoMonad.Bicategory where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Properties.Coherence
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Functor.Properties
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.TwoMonad.Base
open import Cubical.Categories.Bicategory.TwoMonad.Algebra
open import Cubical.Categories.Bicategory.TwoMonad.Morphism

private
  variable
    ℓ ℓ' ℓ'' : Level

open Category
open Functor
open NatIso
open NatTrans
open isIso
open PseudoAlgebra
open AlgHom

module _ {K : Bicategory ℓ ℓ' ℓ''} (M : TwoMonad K) where
  private
    module K = Bicategory K
    module M = TwoMonad M
    module T = Pseudofunctor M.T
    T1 = T₁ M
    T2 = T₂ M

  -- Horizontal composition of algebra 2-cells.
  module _ {A B C : PseudoAlgebra M}
           {h h' : AlgHom M A B} {k k' : AlgHom M B C}
           (σ : AlgHom2 M A B h h') (τ : AlgHom2 M B C k k') where
    private
      a = A .act
      b = B .act
      d = C .act
      f = h .mor
      f' = h' .mor
      g = k .mor
      g' = k' .mor
      hc = h .cell
      hc' = h' .cell
      kc = k .cell
      kc' = k' .cell
      σ₀ = σ .fst
      τ₀ = τ .fst

      e0 : T2 (σ₀ K.⋆ₕ τ₀) K.⋆₂ κ²⁻ M.T f' g'
         ≡ κ²⁻ M.T f g K.⋆₂ (T2 σ₀ K.⋆ₕ T2 τ₀)
      e0 = ⋆InvsFlipSq (κ²I M.T f g) (κ²I M.T f' g')
             (sym (NatTrans.N-hom T.F-seq (σ₀ , τ₀)))

      e1 : (T2 (σ₀ K.⋆ₕ τ₀) K.▷w d) K.⋆₂ (κ²⁻ M.T f' g' K.▷w d)
         ≡ (κ²⁻ M.T f g K.▷w d) K.⋆₂ ((T2 σ₀ K.⋆ₕ T2 τ₀) K.▷w d)
      e1 = sym (▷wSeq K _ _ d) ∙ K.⟨ e0 ⟩▷ d ∙ ▷wSeq K _ _ d

      e2 : (T2 σ₀ K.⋆ₕ (T2 τ₀ K.▷w d)) K.⋆₂ (T1 f' K.◁w kc')
         ≡ (T1 f K.◁w kc) K.⋆₂ (T2 σ₀ K.⋆ₕ (b K.◁w τ₀))
      e2 = sym (K.⋆ₕSeq (T2 σ₀) K.id₂ (T2 τ₀ K.▷w d) kc')
         ∙ K.⟨ K.⋆₂IdR _ ⟩⋆ₕ⟨ τ .snd ⟩
         ∙ K.⟨ sym (K.⋆₂IdL _) ⟩⋆ₕ⟨⟩
         ∙ K.⋆ₕSeq K.id₂ (T2 σ₀) kc (b K.◁w τ₀)

      e4 : ((T2 σ₀ K.▷w b) K.⋆ₕ τ₀) K.⋆₂ (hc' K.▷w g')
         ≡ (hc K.▷w g) K.⋆₂ ((a K.◁w σ₀) K.⋆ₕ τ₀)
      e4 = sym (K.⋆ₕSeq (T2 σ₀ K.▷w b) hc' τ₀ K.id₂)
         ∙ K.⟨ σ .snd ⟩⋆ₕ⟨ K.⋆₂IdR _ ⟩
         ∙ K.⟨⟩⋆ₕ⟨ sym (K.⋆₂IdL _) ⟩
         ∙ K.⋆ₕSeq hc (a K.◁w σ₀) K.id₂ τ₀

      key : ((T2 σ₀ K.⋆ₕ T2 τ₀) K.▷w d)
              K.⋆₂ K.α⁺ (T1 f') (T1 g') d
              K.⋆₂ (T1 f' K.◁w kc')
              K.⋆₂ K.α⁻ (T1 f') b g'
              K.⋆₂ (hc' K.▷w g')
              K.⋆₂ K.α⁺ a f' g'
          ≡   K.α⁺ (T1 f) (T1 g) d
              K.⋆₂ (T1 f K.◁w kc)
              K.⋆₂ K.α⁻ (T1 f) b g
              K.⋆₂ (hc K.▷w g)
              K.⋆₂ K.α⁺ a f g
              K.⋆₂ (a K.◁w (σ₀ K.⋆ₕ τ₀))
      key = pushr K (α⁺nat K (T2 σ₀) (T2 τ₀) K.id₂) _
          ∙ K.⟨⟩⋆₂⟨ pushr K e2 _ ⟩
          ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
                pushr K (α⁻nat K (T2 σ₀) K.id₂ τ₀) _ ⟩ ⟩
          ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ pushr K e4 _ ⟩ ⟩ ⟩
          ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
                α⁺nat K K.id₂ σ₀ τ₀ ⟩ ⟩ ⟩ ⟩

    seqAlgHom2ₕ : AlgHom2 M A C (seqAlgHom M h k) (seqAlgHom M h' k')
    seqAlgHom2ₕ .fst = σ₀ K.⋆ₕ τ₀
    seqAlgHom2ₕ .snd =
        pushr K e1 _
      ∙ K.⟨⟩⋆₂⟨ key ⟩
      ∙ sym (aR6 K _ _ _ _ _ _ _)

  -- The identity 1-cell, as a functor from the terminal category.
  idAlgFunctor : (A : PseudoAlgebra M) → Functor 𝟙C (AlgHomCat M A A)
  idAlgFunctor A .F-ob _ = idAlgHom M A
  idAlgFunctor A .F-hom _ = idAlgHom2 M A A (idAlgHom M A)
  idAlgFunctor A .F-id = refl
  idAlgFunctor A .F-seq _ _ =
    AlgHom2≡ M A A {h = idAlgHom M A} {k = idAlgHom M A}
      (sym (K.⋆₂IdL _))

  -- Horizontal composition, as a bifunctor of hom-categories.
  seqAlgFunctor : (A B C : PseudoAlgebra M)
    → Functor (AlgHomCat M A B ×C AlgHomCat M B C) (AlgHomCat M A C)
  seqAlgFunctor A B C .F-ob (h , k) = seqAlgHom M h k
  seqAlgFunctor A B C .F-hom {x} {y} (σ , τ) =
    seqAlgHom2ₕ {h = x .fst} {h' = y .fst} {k = x .snd} {k' = y .snd}
      σ τ
  seqAlgFunctor A B C .F-id {x} =
    AlgHom2≡ M A C {h = seqAlgHom M (x .fst) (x .snd)}
                   {k = seqAlgHom M (x .fst) (x .snd)} K.⋆ₕId
  seqAlgFunctor A B C .F-seq {x} {_} {z} (σ , τ) (σ' , τ') =
    AlgHom2≡ M A C {h = seqAlgHom M (x .fst) (x .snd)}
                   {k = seqAlgHom M (z .fst) (z .snd)}
      (K.⋆ₕSeq (σ .fst) (σ' .fst) (τ .fst) (τ' .fst))

  -- An algebra 2-cell is invertible as soon as its underlying 2-cell
  -- is.
  module _ {A B : PseudoAlgebra M} {h k : AlgHom M A B}
           (σ : AlgHom2 M A B h k)
           (iso : isIso K.Hom[ A .carrier , B .carrier ] (σ .fst)) where
    private
      a = A .act
      b = B .act

      T2col : T2 (iso .inv) K.⋆₂ T2 (σ .fst) ≡ K.id₂
      T2col = sym (T₂Seq M _ _) ∙ cong T2 (iso .sec) ∙ T₂Id M

    invAlgHom2 : AlgHom2 M A B k h
    invAlgHom2 .fst = iso .inv
    invAlgHom2 .snd =
      ⋆InvRMove (a K.◁w σ .fst , ◁wIsIso K a iso)
        ( K.⋆₂Assoc _ _ _
        ∙ K.⟨⟩⋆₂⟨ sym (σ .snd) ⟩
        ∙ pushn K (sym (▷wSeq K _ _ b) ∙ K.⟨ T2col ⟩▷ b ∙ K.▷wId b) _
        ∙ K.⋆₂IdL _)

    algHom2IsIso : isIso (AlgHomCat M A B) {x = h} {y = k} σ
    algHom2IsIso .inv = invAlgHom2
    algHom2IsIso .sec = AlgHom2≡ M A B {h = k} {k = k} (iso .sec)
    algHom2IsIso .ret = AlgHom2≡ M A B {h = h} {k = h} (iso .ret)

  -- The left unitor.
  module _ {A B : PseudoAlgebra M} (h : AlgHom M A B) where
    private
      a = A .act
      b = B .act
      f = h .mor
      hc = h .cell
      e₀ = T1 (K.id₁ {A .carrier})

      κ0i : K.2Cell e₀ K.id₁
      κ0i = κ⁰⁻ M.T

      UI : CatIso K.Hom[ T₀ M (A .carrier) , T₀ M (B .carrier) ]
             (K.id₁ K.⋆₁ T1 f) (T1 (K.id₁ K.⋆₁ f))
      UI = ⋆Iso (T.F⁰ K.▷w T1 f , ▷wIsIso K (T1 f) (T.F-id-isIso tt*))
                (κ²I M.T K.id₁ f)

      T2λ : T2 (K.λ⁺ f)
          ≡ κ²⁻ M.T K.id₁ f K.⋆₂ (κ0i K.▷w T1 f) K.⋆₂ K.λ⁺ (T1 f)
      T2λ = ⋆InvLMove UI (K.⋆₂Assoc _ _ _ ∙ T.lax-λ _ _ f)
          ∙ K.⋆₂Assoc _ _ _

      trico : (K.ρ⁻ a K.▷w f) K.⋆₂ K.α⁺ a K.id₁ f K.⋆₂ (a K.◁w K.λ⁺ f)
            ≡ K.id₂
      trico = K.⟨⟩⋆₂⟨ K.triangle _ _ _ a f ⟩
            ∙ sym (▷wSeq K _ _ f)
            ∙ K.⟨ K.ρU _ _ .nIso (a , tt*) .sec ⟩▷ f
            ∙ K.▷wId f

      core : ((κ0i K.▷w T1 f) K.▷w b)
               K.⋆₂ (K.λ⁺ (T1 f) K.▷w b)
               K.⋆₂ hc
           ≡ K.α⁺ e₀ (T1 f) b
             K.⋆₂ (e₀ K.◁w hc)
             K.⋆₂ K.α⁻ e₀ a f
             K.⋆₂ (idCell M A K.▷w f)
             K.⋆₂ K.α⁺ a K.id₁ f
             K.⋆₂ (a K.◁w K.λ⁺ f)
      core = sym
        (  K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
               K.⟨ ▷3 K _ _ _ f ⟩⋆₂⟨⟩ ∙ aR3 K _ _ _ _ ⟩ ⟩ ⟩
         ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
               K.⟨⟩⋆₂⟨ trico ⟩ ∙ K.⋆₂IdR _ ⟩ ⟩ ⟩ ⟩
         ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ pushr K (sym (α⁻natL K κ0i a f)) _ ⟩ ⟩
         ∙ K.⟨⟩⋆₂⟨ pushr K (sym (▷◁exch K κ0i hc)) _ ⟩
         ∙ pushr K (sym (α⁺natL K κ0i (T1 f) b)) _
         ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ λ⋆₁ K a f ⟩ ⟩ ⟩
         ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ λ-nat K hc ⟩ ⟩
         ∙ K.⟨⟩⋆₂⟨ pushn K (αλ K (T1 f) b) _ ⟩)

    λAlgCell : AlgHom2 M A B (seqAlgHom M (idAlgHom M A) h) h
    λAlgCell .fst = K.λ⁺ f
    λAlgCell .snd =
        K.⟨ K.⟨ T2λ ⟩▷ b ∙ ▷3 K _ _ _ b ⟩⋆₂⟨⟩ ∙ aR3 K _ _ _ _
      ∙ K.⟨⟩⋆₂⟨ core ⟩
      ∙ sym (aR6 K _ _ _ _ _ _ _)

  -- The right unitor.
  module _ {A B : PseudoAlgebra M} (h : AlgHom M A B) where
    private
      a = A .act
      b = B .act
      f = h .mor
      hc = h .cell
      Tf = T1 f

      κ0i' : K.2Cell (T1 (K.id₁ {B .carrier})) K.id₁
      κ0i' = κ⁰⁻ M.T

      VI : CatIso K.Hom[ T₀ M (A .carrier) , T₀ M (B .carrier) ]
             (Tf K.⋆₁ K.id₁) (T1 (f K.⋆₁ K.id₁))
      VI = ⋆Iso (Tf K.◁w T.F⁰ , ◁wIsIso K Tf (T.F-id-isIso tt*))
                (κ²I M.T f K.id₁)

      T2ρ : T2 (K.ρ⁺ f)
          ≡ κ²⁻ M.T f K.id₁ K.⋆₂ (Tf K.◁w κ0i') K.⋆₂ K.ρ⁺ Tf
      T2ρ = ⋆InvLMove VI (K.⋆₂Assoc _ _ _ ∙ T.lax-ρ _ _ f)
          ∙ K.⋆₂Assoc _ _ _

      col1 : ((Tf K.◁w T.F⁰) K.▷w b) K.⋆₂ ((Tf K.◁w κ0i') K.▷w b)
           ≡ K.id₂
      col1 = sym (▷wSeq K _ _ b)
           ∙ K.⟨ sym (◁wSeq K Tf _ _)
               ∙ Tf K.◁⟨ T.F-id-isIso tt* .ret ⟩
               ∙ K.◁wId Tf ⟩▷ b
           ∙ K.▷wId b

      col2 : (K.ρ⁻ Tf K.▷w b) K.⋆₂ (K.ρ⁺ Tf K.▷w b) ≡ K.id₂
      col2 = sym (▷wSeq K _ _ b)
           ∙ K.⟨ K.ρU _ _ .nIso (Tf , tt*) .sec ⟩▷ b
           ∙ K.▷wId b

      ◁col : (a K.◁w K.ρ⁻ f) K.⋆₂ (a K.◁w K.ρ⁺ f) ≡ K.id₂
      ◁col = sym (◁wSeq K a _ _)
           ∙ a K.◁⟨ K.ρU _ _ .nIso (f , tt*) .sec ⟩
           ∙ K.◁wId a

      JI : CatIso K.Hom[ T₀ M (A .carrier) , B .carrier ]
             (Tf K.⋆₁ b) ((Tf K.⋆₁ T1 (K.id₁ {B .carrier})) K.⋆₁ b)
      JI = ⋆Iso ( K.ρ⁻ Tf K.▷w b
                , ▷wIsIso K b
                    (invIso (K.ρ⁺ Tf , K.ρU _ _ .nIso (Tf , tt*)) .snd))
                ( (Tf K.◁w T.F⁰) K.▷w b
                , ▷wIsIso K b (◁wIsIso K Tf (T.F-id-isIso tt*)))

      eqL : JI .fst
              K.⋆₂ ( ((Tf K.◁w κ0i') K.▷w b)
                     K.⋆₂ (K.ρ⁺ Tf K.▷w b)
                     K.⋆₂ hc)
          ≡ hc
      eqL = K.⋆₂Assoc _ _ _
          ∙ K.⟨⟩⋆₂⟨ pushn K col1 _ ∙ K.⋆₂IdL _ ⟩
          ∙ pushn K col2 _
          ∙ K.⋆₂IdL _

      eqR : JI .fst
              K.⋆₂ ( K.α⁺ Tf (T1 (K.id₁ {B .carrier})) b
                     K.⋆₂ (Tf K.◁w idCell M B)
                     K.⋆₂ K.α⁻ Tf b K.id₁
                     K.⋆₂ (hc K.▷w K.id₁)
                     K.⋆₂ K.α⁺ a f K.id₁
                     K.⋆₂ (a K.◁w K.ρ⁺ f))
          ≡ hc
      eqR = K.⋆₂Assoc _ _ _
          ∙ rw4 K (idTail M B Tf) _
          ∙ pushn K (sym (ρ⁻⋆₁ K Tf b)) _
          ∙ pushr K (sym (ρ⁻-nat K hc)) _
          ∙ K.⟨⟩⋆₂⟨ pushn K (ρα K a f) _ ∙ ◁col ⟩
          ∙ K.⋆₂IdR _

      core' : ((Tf K.◁w κ0i') K.▷w b)
                K.⋆₂ (K.ρ⁺ Tf K.▷w b)
                K.⋆₂ hc
            ≡ K.α⁺ Tf (T1 (K.id₁ {B .carrier})) b
              K.⋆₂ (Tf K.◁w idCell M B)
              K.⋆₂ K.α⁻ Tf b K.id₁
              K.⋆₂ (hc K.▷w K.id₁)
              K.⋆₂ K.α⁺ a f K.id₁
              K.⋆₂ (a K.◁w K.ρ⁺ f)
      core' = ⋆CancelL JI (eqL ∙ sym eqR)

    ρAlgCell : AlgHom2 M A B (seqAlgHom M h (idAlgHom M B)) h
    ρAlgCell .fst = K.ρ⁺ f
    ρAlgCell .snd =
        K.⟨ K.⟨ T2ρ ⟩▷ b ∙ ▷3 K _ _ _ b ⟩⋆₂⟨⟩ ∙ aR3 K _ _ _ _
      ∙ K.⟨⟩⋆₂⟨ core' ⟩
      ∙ sym (aR6 K _ _ _ _ _ _ _)

  -- The associator.
  module _ {A B C D : PseudoAlgebra M}
           (h : AlgHom M A B) (k : AlgHom M B C)
           (l : AlgHom M C D) where
    private
      a = A .act
      b = B .act
      c = C .act
      e = D .act
      f = h .mor
      g = k .mor
      m = l .mor
      hc = h .cell
      kc = k .cell
      lc = l .cell
      Tf = T1 f
      Tg = T1 g
      Tm = T1 m

      PI : CatIso K.Hom[ T₀ M (A .carrier) , T₀ M (D .carrier) ]
             ((Tf K.⋆₁ Tg) K.⋆₁ Tm) (T1 ((f K.⋆₁ g) K.⋆₁ m))
      PI = ⋆Iso ( T.F² f g K.▷w Tm
                , ▷wIsIso K Tm (T.F-seq-isIso (f , g)))
                (κ²I M.T (f K.⋆₁ g) m)

      pα : PI .fst
             K.⋆₂ (T2 (K.α⁺ f g m) K.⋆₂ κ²⁻ M.T f (g K.⋆₁ m))
         ≡ K.α⁺ Tf Tg Tm K.⋆₂ (Tf K.◁w T.F² g m)
      pα = K.⋆₂Assoc _ _ _
         ∙ K.⟨⟩⋆₂⟨ sym (K.⋆₂Assoc _ _ _) ⟩
         ∙ sym (K.⋆₂Assoc _ _ _)
         ∙ K.⟨ T.lax-α _ _ _ _ f g m ⟩⋆₂⟨⟩
         ∙ K.⋆₂Assoc _ _ _
         ∙ K.⟨⟩⋆₂⟨ K.⋆₂Assoc _ _ _ ⟩
         ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
               T.F-seq-isIso (f , g K.⋆₁ m) .ret ⟩ ⟩
         ∙ K.⟨⟩⋆₂⟨ K.⋆₂IdR _ ⟩

      T2α : T2 (K.α⁺ f g m) K.⋆₂ κ²⁻ M.T f (g K.⋆₁ m)
          ≡ κ²⁻ M.T (f K.⋆₁ g) m
            K.⋆₂ (κ²⁻ M.T f g K.▷w Tm)
            K.⋆₂ K.α⁺ Tf Tg Tm
            K.⋆₂ (Tf K.◁w T.F² g m)
      T2α = ⋆InvLMove PI pα ∙ K.⋆₂Assoc _ _ _

      eA : (T2 (K.α⁺ f g m) K.▷w e)
             K.⋆₂ (κ²⁻ M.T f (g K.⋆₁ m) K.▷w e)
         ≡ (κ²⁻ M.T (f K.⋆₁ g) m K.▷w e)
           K.⋆₂ ((κ²⁻ M.T f g K.▷w Tm) K.▷w e)
           K.⋆₂ (K.α⁺ Tf Tg Tm K.▷w e)
           K.⋆₂ ((Tf K.◁w T.F² g m) K.▷w e)
      eA = sym (▷wSeq K _ _ e) ∙ K.⟨ T2α ⟩▷ e ∙ ▷4 K _ _ _ _ e

      ◁κcol : (Tf K.◁w (T.F² g m K.▷w e))
                K.⋆₂ (Tf K.◁w (κ²⁻ M.T g m K.▷w e))
            ≡ K.id₂
      ◁κcol = sym (◁wSeq K Tf _ _)
            ∙ Tf K.◁⟨ sym (▷wSeq K _ _ e)
                    ∙ K.⟨ T.F-seq-isIso (g , m) .ret ⟩▷ e
                    ∙ K.▷wId e ⟩
            ∙ K.◁wId Tf

      sA : ((Tf K.◁w T.F² g m) K.▷w e)
             K.⋆₂ K.α⁺ Tf (T1 (g K.⋆₁ m)) e
             K.⋆₂ (Tf K.◁w (κ²⁻ M.T g m K.▷w e))
         ≡ K.α⁺ Tf (Tg K.⋆₁ Tm) e
      sA = pushr K (α⁺natM K Tf (T.F² g m) e) _
         ∙ K.⟨⟩⋆₂⟨ ◁κcol ⟩
         ∙ K.⋆₂IdR _

      sF : (Tf K.◁w K.α⁺ b g m) K.⋆₂ K.α⁻ Tf b (g K.⋆₁ m)
         ≡ K.α⁻ Tf (b K.⋆₁ g) m
           K.⋆₂ (K.α⁻ Tf b g K.▷w m)
           K.⋆₂ K.α⁺ (Tf K.⋆₁ b) g m
      sF = ⋆InvLMove (αI K Tf (b K.⋆₁ g) m) (pentP4 K Tf b g m)

      CORE : ((κ²⁻ M.T f g K.▷w Tm) K.▷w e)
               K.⋆₂ (K.α⁺ Tf Tg Tm K.▷w e)
               K.⋆₂ ((Tf K.◁w T.F² g m) K.▷w e)
               K.⋆₂ K.α⁺ Tf (T1 (g K.⋆₁ m)) e
               K.⋆₂ (Tf K.◁w seqCell M k l)
               K.⋆₂ K.α⁻ Tf b (g K.⋆₁ m)
               K.⋆₂ (hc K.▷w (g K.⋆₁ m))
               K.⋆₂ K.α⁺ a f (g K.⋆₁ m)
           ≡ K.α⁺ (T1 (f K.⋆₁ g)) Tm e
             K.⋆₂ (T1 (f K.⋆₁ g) K.◁w lc)
             K.⋆₂ K.α⁻ (T1 (f K.⋆₁ g)) c m
             K.⋆₂ (seqCell M h k K.▷w m)
             K.⋆₂ K.α⁺ a (f K.⋆₁ g) m
             K.⋆₂ (a K.◁w K.α⁺ f g m)
      CORE =
          K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨ ◁6 K Tf _ _ _ _ _ _ ⟩⋆₂⟨⟩
              ∙ aR6 K _ _ _ _ _ _ _ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              rw3 K sA _ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨
              rep3 K (K.pentagon _ _ _ _ _ Tf Tg Tm e) _ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (sym (α⁺natR K Tf Tg lc)) _ ⟩ ⟩
        ∙ pushr K (α⁺natL K (κ²⁻ M.T f g) Tm e) _
        ∙ K.⟨⟩⋆₂⟨
              pushr K (▷◁exch K (κ²⁻ M.T f g) lc) _ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr3 K sF _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (sym (α⁺natL K hc g m)) _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              sym (K.pentagon _ _ _ _ _ a f g m) ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (α⁻natM K Tf kc m) _ ⟩ ⟩ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              rep3 K (sym (pentP3 K Tf Tg c m)) _ ⟩ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              pushr K (α⁻natL K (κ²⁻ M.T f g) c m) _ ⟩ ⟩
        ∙ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨ K.⟨⟩⋆₂⟨
              rw6 K (sym (▷6 K _ _ _ _ _ _ m)) _ ⟩ ⟩ ⟩

    αAlgCell : AlgHom2 M A D (seqAlgHom M (seqAlgHom M h k) l)
                            (seqAlgHom M h (seqAlgHom M k l))
    αAlgCell .fst = K.α⁺ f g m
    αAlgCell .snd =
        pushr4 K eA _
      ∙ K.⟨⟩⋆₂⟨ CORE ⟩
      ∙ sym (aR6 K _ _ _ _ _ _ _)

  -- The bicategory of pseudoalgebras, lax morphisms and algebra
  -- 2-cells.
  Alg : Bicategory (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) (ℓ-max ℓ' ℓ'') ℓ''
  Alg .Bicategory.ob = PseudoAlgebra M
  Alg .Bicategory.Hom[_,_] = AlgHomCat M
  Alg .Bicategory.id {A} = idAlgFunctor A
  Alg .Bicategory.seq = seqAlgFunctor
  Alg .Bicategory.λU A B .trans .N-ob (_ , h) = λAlgCell h
  Alg .Bicategory.λU A B .trans .N-hom {_ , u} {_ , v} (_ , σ) =
    AlgHom2≡ M A B {h = seqAlgHom M (idAlgHom M A) u} {k = v}
      (λ-nat K (σ .fst))
  Alg .Bicategory.λU A B .nIso (_ , h) =
    algHom2IsIso (λAlgCell h) (K.λU _ _ .nIso (tt* , h .mor))
  Alg .Bicategory.ρU A B .trans .N-ob (h , _) = ρAlgCell h
  Alg .Bicategory.ρU A B .trans .N-hom {u , _} {v , _} (σ , _) =
    AlgHom2≡ M A B {h = seqAlgHom M u (idAlgHom M B)} {k = v}
      (ρ-nat K (σ .fst))
  Alg .Bicategory.ρU A B .nIso (h , _) =
    algHom2IsIso (ρAlgCell h) (K.ρU _ _ .nIso (h .mor , tt*))
  Alg .Bicategory.α A B C D .trans .N-ob (h , k , l) = αAlgCell h k l
  Alg .Bicategory.α A B C D .trans
    .N-hom {u , v , w} {u' , v' , w'} (σ , τ , υ) =
    AlgHom2≡ M A D
      {h = seqAlgHom M (seqAlgHom M u v) w}
      {k = seqAlgHom M u' (seqAlgHom M v' w')}
      (α⁺nat K (σ .fst) (τ .fst) (υ .fst))
  Alg .Bicategory.α A B C D .nIso (h , k , l) =
    algHom2IsIso (αAlgCell h k l)
      (K.α _ _ _ _ .nIso (h .mor , k .mor , l .mor))
  Alg .Bicategory.triangle A B C h k =
    AlgHom2≡ M A C
      {h = seqAlgHom M (seqAlgHom M h (idAlgHom M B)) k}
      {k = seqAlgHom M h k}
      (K.triangle _ _ _ (h .mor) (k .mor))
  Alg .Bicategory.pentagon A B C D E h k l n =
    AlgHom2≡ M A E
      {h = seqAlgHom M (seqAlgHom M (seqAlgHom M h k) l) n}
      {k = seqAlgHom M h (seqAlgHom M k (seqAlgHom M l n))}
      (K.pentagon _ _ _ _ _ (h .mor) (k .mor) (l .mor) (n .mor))
