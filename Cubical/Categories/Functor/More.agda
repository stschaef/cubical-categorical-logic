{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Categories.Functor.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Equivalence
open import Cubical.Categories.Equivalence.WeakEquivalence

open import Cubical.Categories.Instances.Functors


-- Composition by functor with special properties

module _ {ℓC ℓC' ℓD ℓD' ℓE ℓE'}
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (E : Category ℓE ℓE')
  (F : Functor C D)
  where

  open Category
  open Functor
  open NatTrans
  open isIso

  isFullyFaithful→isFullPostcomp : isFullyFaithful F → isFull (postcomposeF E F)
  isFullyFaithful→isFullPostcomp isFullyFaithfulF G H η = ∣ ext , ext≡ ∣₁
    where

    faith : isFaithful F
    faith = isFullyFaithful→Faithful {F = F} isFullyFaithfulF

    full : isFull F
    full = isFullyFaithful→Full {F = F} isFullyFaithfulF

    Mor : (e : E .ob) → Type _
    Mor e = Σ[ ϕ ∈ C [ G ⟅ e ⟆ , H ⟅ e ⟆ ] ] F ⟪ ϕ ⟫ ≡ η .N-ob e

    isPropMor : (e : E .ob) → isProp (Mor e)
    isPropMor e x y =
      Σ≡Prop
        (λ ψ → D .isSetHom (F ⟪ ψ ⟫) (η .N-ob e))
        (faith
          (G ⟅ e ⟆) (H ⟅ e ⟆)
          (x .fst) (y .fst) (x .snd ∙ sym (y .snd)))

    isContrMor : (e : E .ob) → isContr (Mor e)
    isContrMor e = inhProp→isContr inhab (isPropMor e)
      where
      inhab : Mor e
      inhab =
        rec
          (isPropMor e)
          (λ (f , Ff≡ηe) → f , Ff≡ηe)
          (full
            (G ⟅ e ⟆) (H ⟅ e ⟆) (η .N-ob e))

    ext : FUNCTOR E C [ G , H ]
    ext .N-ob e = isContrMor e .fst .fst
    ext .N-hom {e}{e'} f =
      faith (G ⟅ e ⟆) (H ⟅ e' ⟆)
        (G ⟪ f ⟫ ⋆⟨ C ⟩ ext .N-ob e') (ext .N-ob e ⋆⟨ C ⟩ H ⟪ f ⟫)
        ((F .F-seq (G .F-hom f) (ext .N-ob e')) ∙
        cong (λ a → F ⟪ G ⟪ f ⟫ ⟫ ⋆⟨ D ⟩ a) (isContrMor e' .fst .snd) ∙
        η .N-hom f ∙
        sym (cong (λ a → a ⋆⟨ D ⟩ F ⟪ H ⟪ f ⟫ ⟫) (isContrMor e .fst .snd)) ∙
        sym (F .F-seq (ext .N-ob e) (H ⟪ f ⟫)))

    ext≡ : F-hom (postcomposeF E F) ext ≡ η
    ext≡ = makeNatTransPath (funExt (λ e → isContrMor e .fst .snd))

  isFaithful→isFaithfulPostcomp : isFaithful F →
                                  isFaithful (postcomposeF E F)
  isFaithful→isFaithfulPostcomp isFaithfulF G H η η' p =
    makeNatTransPath (funExt (λ e →
      isFaithfulF (G ⟅ e ⟆) (H ⟅ e ⟆)
        (η .N-ob e) (η' .N-ob e) (cong (λ a → a .N-ob e) p)))

  isFullyFaithful→isFullyFaithfulPostcomp : isFullyFaithful F →
                                            isFullyFaithful (postcomposeF E F)
  isFullyFaithful→isFullyFaithfulPostcomp isFullFaithF =
    isFull+Faithful→isFullyFaithful {F = postcomposeF E F}
      (isFullyFaithful→isFullPostcomp isFullFaithF)
      (isFaithful→isFaithfulPostcomp
        (isFullyFaithful→Faithful {F = F} isFullFaithF))
