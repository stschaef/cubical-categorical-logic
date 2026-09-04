{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Bicategory.Instances.CAT.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Terminal

private
  variable
    ℓ ℓ' ℓ'' : Level

open Functor
open NatTrans
open Category

module _ {ℓ ℓ' : Level} where

  -- Direct, not point-free through `appF`: that spelling injects a
  -- `⋆ id` per layer, making A-srcCAT/A-tgtCAT disagree on morphisms.
  hSeqCAT : {C D E : Category ℓ ℓ'}
    {F F' : Functor C D} {G G' : Functor D E}
    → NatTrans F F' → NatTrans G G' → NatTrans (G ∘F F) (G' ∘F F')
  hSeqCAT {E = E} {F' = F'} {G = G} β γ .N-ob c =
    G .F-hom (β .N-ob c) ⋆⟨ E ⟩ γ .N-ob (F' .F-ob c)
  hSeqCAT {E = E} {F' = F'} {G = G} {G' = G'} β γ .N-hom {c} {c'} f =
      sym (E .⋆Assoc _ _ _)
    ∙ cong (λ m → m ⋆⟨ E ⟩ γ .N-ob (F' .F-ob c'))
           ( sym (G .F-seq _ _)
           ∙ cong (G .F-hom) (β .N-hom f)
           ∙ G .F-seq _ _)
    ∙ E .⋆Assoc _ _ _
    ∙ cong (λ m → G .F-hom (β .N-ob c) ⋆⟨ E ⟩ m) (γ .N-hom (F' .F-hom f))
    ∙ sym (E .⋆Assoc _ _ _)

  seqCAT : (C D E : Category ℓ ℓ')
    → Functor (FUNCTOR C D ×C FUNCTOR D E) (FUNCTOR C E)
  seqCAT C D E .F-ob (F , G) = G ∘F F
  seqCAT C D E .F-hom (β , γ) = hSeqCAT β γ
  seqCAT C D E .F-id {F , G} = makeNatTransPath (funExt λ c →
      cong (λ m → m ⋆⟨ E ⟩ E .id) (G .F-id)
    ∙ E .⋆IdL _)
  seqCAT C D E .F-seq {F , G} {F' , G'} {F'' , G''} (β , γ) (β' , γ') =
    makeNatTransPath (funExt λ c →
        cong (λ m → m ⋆⟨ E ⟩ (γ .N-ob (F'' .F-ob c)
                              ⋆⟨ E ⟩ γ' .N-ob (F'' .F-ob c)))
             (G .F-seq _ _)
      ∙ E .⋆Assoc _ _ _
      ∙ cong (λ m → G .F-hom (β .N-ob c) ⋆⟨ E ⟩ m)
             ( sym (E .⋆Assoc _ _ _)
             ∙ cong (λ m → m ⋆⟨ E ⟩ γ' .N-ob (F'' .F-ob c))
                    (γ .N-hom (β' .N-ob c))
             ∙ E .⋆Assoc _ _ _)
      ∙ sym (E .⋆Assoc _ _ _))

  module _ (C D : Category ℓ ℓ') where
    LU-srcCAT : Functor (TerminalCategory {ℓ-zero} ×C FUNCTOR C D) (FUNCTOR C D)
    LU-srcCAT = seqCAT C C D ∘F (FunctorFromTerminal Id ×F 𝟙⟨ FUNCTOR C D ⟩)

    LU-tgtCAT : Functor (TerminalCategory {ℓ-zero} ×C FUNCTOR C D) (FUNCTOR C D)
    LU-tgtCAT = Snd TerminalCategory (FUNCTOR C D)

    RU-srcCAT : Functor (FUNCTOR C D ×C TerminalCategory {ℓ-zero}) (FUNCTOR C D)
    RU-srcCAT = seqCAT C D D ∘F (𝟙⟨ FUNCTOR C D ⟩ ×F FunctorFromTerminal Id)

    RU-tgtCAT : Functor (FUNCTOR C D ×C TerminalCategory {ℓ-zero}) (FUNCTOR C D)
    RU-tgtCAT = Fst (FUNCTOR C D) TerminalCategory

  module _ (C D E W : Category ℓ ℓ') where
    A-srcCAT : Functor (FUNCTOR C D ×C (FUNCTOR D E ×C FUNCTOR E W))
                       (FUNCTOR C W)
    A-srcCAT =
        seqCAT C E W
      ∘F (seqCAT C D E ×F 𝟙⟨ FUNCTOR E W ⟩)
      ∘F ×C-assoc (FUNCTOR C D) (FUNCTOR D E) (FUNCTOR E W)

    A-tgtCAT : Functor (FUNCTOR C D ×C (FUNCTOR D E ×C FUNCTOR E W))
                       (FUNCTOR C W)
    A-tgtCAT = seqCAT C D W ∘F (𝟙⟨ FUNCTOR C D ⟩ ×F seqCAT D E W)
