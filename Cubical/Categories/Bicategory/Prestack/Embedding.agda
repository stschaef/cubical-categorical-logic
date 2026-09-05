{-# OPTIONS --lossy-unification #-}
{- The Yoneda pseudofunctor よ : B → PRESTACK B, sending a 0-cell to
   its representable prestack and a 1-cell to postcomposition. -}
module Cubical.Categories.Bicategory.Prestack.Embedding where

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
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.Transformation.Properties
open import Cubical.Categories.Bicategory.Transformation.Identity
open import Cubical.Categories.Bicategory.Transformation.Composition
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Hom
open import Cubical.Categories.Bicategory.Prestack.Morphism
open import Cubical.Categories.Bicategory.Prestack.Bicategory

private
  variable
    ℓ ℓ' ℓ'' : Level

open Functor
open NatTrans
open NatIso
open isIso
open LaxFunctor
open Pseudofunctor
open LaxNatTrans
open Modification

module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  module _ {a b : B.0Cell} (k : B.1Cell a b) where
    private
      module Pa = PrestackNotation (Hom B a)
      module Pb = PrestackNotation (Hom B b)

      nh : {x y : B.0Cell} (f : B.1Cell y x)
        → NatTrans (B.postcomp k ∘F Pa.reind f)
                   (Pb.reind f ∘F B.postcomp k)
      nh {x} {y} f .N-ob g = B.α⁺ f g k
      nh {x} {y} f .N-hom θ = B.α y x a b .trans .N-hom (B.id₂ , θ , B.id₂)

      core : {x y z : B.0Cell} (f : B.1Cell y x) (g : B.1Cell z y)
        (h : B.1Cell x a)
        →   (B.α⁻ g f h B.▷w k) B.⋆₂ B.α⁺ (g B.⋆₁ f) h k
          ≡   B.α⁺ g (f B.⋆₁ h) k
            B.⋆₂ (g B.◁w B.α⁺ f h k)
            B.⋆₂ B.α⁻ g f (h B.⋆₁ k)
      core f g h = sym (pentP4 B g f h k)

    yo1 : PrestackHom (Hom B a) (Hom B b)
    yo1 .N-1cell x = B.postcomp k
    yo1 .N-hom f = nh f
    yo1 .N-natural {x} {y} {f} θ = makeNatTransPath (funExt λ g →
        B.⟨ B.⋆₂IdR _ ⟩⋆₂⟨⟩
      ∙ B.α y x a b .trans .N-hom (θ , B.id₂ , B.id₂)
      ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆ₕ⟨ B.⋆ₕId ⟩
              ∙ sym (B.⋆₂IdL _)
              ∙ B.⟨ sym (B.◁wId f) ⟩⋆₂⟨⟩ ⟩)
    yo1 .lax-id x = makeNatTransPath (funExt λ g →
        B.⟨ B.⋆₂IdR _ ⟩⋆₂⟨⟩
      ∙ λ⁻⋆₁ B g k
      ∙ sym (B.⋆₂IdL _ ∙ B.⋆₂IdL _ ∙ B.⋆₂IdL _))
    yo1 .lax-seq {x} {y} {z} f g = makeNatTransPath (funExt λ h →
        B.⟨ B.⋆₂IdR _ ⟩⋆₂⟨⟩
      ∙ core f g h
      ∙ sym ( B.⋆₂IdL _
            ∙ B.⟨ B.⟨ B.⟨ B.◁wId g ⟩▷ k ∙ B.▷wId k ⟩⋆₂⟨⟩
                  ∙ B.⋆₂IdL _ ⟩⋆₂⟨⟩
            ∙ B.⟨⟩⋆₂⟨ B.⋆₂IdL _
                    ∙ B.⟨ B.⋆₂IdR _ ⟩⋆₂⟨⟩
                    ∙ B.⟨⟩⋆₂⟨ B.⋆₂IdL _
                            ∙ B.⟨ g B.◁⟨ B.◁wId f ⟩ ∙ B.◁wId g ⟩⋆₂⟨⟩
                            ∙ B.⋆₂IdL _ ⟩ ⟩))

    yo1-pseudo : isPseudoNat (Hom B a) (Hom B b) yo1
    yo1-pseudo {x} {y} f =
      FUNCTORIso B.Hom[ x , a ] B.Hom[ y , b ] (nh f)
        (λ g → B.α y x a b .nIso (f , g , k))

    yo1ᵖ : PrestackPseudoHom (Hom B a) (Hom B b)
    yo1ᵖ = yo1 , yo1-pseudo

  module _ {a b : B.0Cell} {k k' : B.1Cell a b} (κ : B.2Cell k k') where
    private
      mo : (x : B.0Cell)
        → NatTrans (B.postcomp {x} k) (B.postcomp {x} k')
      mo x .N-ob g = g B.◁w κ
      mo x .N-hom θ = ▷◁exch B θ κ

    yo2 : Modification (yo1 k) (yo1 k')
    yo2 .M-ob = mo
    yo2 .M-hom {x} {y} f = makeNatTransPath (funExt λ g →
        B.⟨⟩⋆₂⟨ B.⋆₂IdR _ ⟩
      ∙ sym (B.α y x a b .trans .N-hom (B.id₂ , B.id₂ , κ))
      ∙ B.⟨ B.⟨ B.⋆ₕId ⟩⋆ₕ⟨⟩ ⟩⋆₂⟨⟩
      ∙ sym (B.⟨ B.⟨ B.▷wId k ⟩⋆₂⟨⟩ ∙ B.⋆₂IdL _ ⟩⋆₂⟨⟩))

  yoF : {a b : B.0Cell}
    → Functor B.Hom[ a , b ] (PrestackHomCat (Hom B a) (Hom B b))
  yoF .F-ob k = yo1ᵖ k
  yoF .F-hom κ = yo2 κ
  yoF .F-id = makeModificationPath λ x →
    makeNatTransPath (funExt λ g → B.◁wId g)
  yoF .F-seq κ κ' = makeModificationPath λ x →
    makeNatTransPath (funExt λ g → ◁wSeq B g κ κ')

  module _ (x : B.0Cell) where
    private
      io : (u : B.0Cell)
        → NatTrans (Id {C = B.Hom[ u , x ]}) (B.postcomp (B.id₁ {x}))
      io u .N-ob g = B.ρ⁻ g
      io u .N-hom θ = ρ⁻-nat B θ

    yoId : Modification (idLaxNatTrans (Hom B x .laxFunctor))
                        (yo1 (B.id₁ {x}))
    yoId .M-ob = io
    yoId .M-hom {u} {v} f = makeNatTransPath (funExt λ g →
        B.⟨ B.⋆₂IdL _ ⟩⋆₂⟨⟩
      ∙ B.⋆₂IdL _
      ∙ B.⋆₂IdR _
      ∙ ρ⁻◁ B f g
      ∙ sym (B.⟨ B.⋆₂IdL _ ⟩⋆₂⟨⟩))

  module _ {x y z : B.0Cell} (k : B.1Cell x y) (l : B.1Cell y z) where
    private
      so : (u : B.0Cell)
        → NatTrans (B.postcomp {u} l ∘F B.postcomp {u} k)
                   (B.postcomp {u} (k B.⋆₁ l))
      so u .N-ob g = B.α⁺ g k l
      so u .N-hom θ =
          B.α u x y z .trans .N-hom (θ , B.id₂ , B.id₂)
        ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆ₕ⟨ B.⋆ₕId ⟩ ⟩

    yoSeq : Modification (seqLaxNatTrans (yo1 k) (yo1 l)) (yo1 (k B.⋆₁ l))
    yoSeq .M-ob = so
    yoSeq .M-hom {u} {v} f = makeNatTransPath (funExt λ g →
        B.⟨ B.⋆₂IdL _
          ∙ B.⟨ B.⋆₂IdR _ ⟩⋆₂⟨⟩
          ∙ B.⟨⟩⋆₂⟨ B.⋆₂IdL _
                  ∙ B.⋆₂IdR _
                  ∙ B.⟨ B.⟨ B.◁wId f ⟩▷ l ∙ B.▷wId l ⟩⋆₂⟨⟩
                  ∙ B.⋆₂IdL _ ⟩ ⟩⋆₂⟨⟩
      ∙ B.⟨⟩⋆₂⟨ B.⋆₂IdR _ ⟩
      ∙ B.⋆₂Assoc _ _ _
      ∙ B.pentagon v u x y z f g k l
      ∙ sym (B.⟨ B.⟨ B.⟨ B.▷wId k ⟩▷ l ∙ B.▷wId l ⟩⋆₂⟨⟩
                 ∙ B.⋆₂IdL _ ⟩⋆₂⟨⟩))

  よLax : LaxFunctor B (PRESTACK B ℓ' ℓ'')
  よLax .F-ob x = Hom B x
  よLax .F-Hom = yoF
  よLax .F-id {x} .N-ob _ = yoId x
  よLax .F-id {x} .N-hom r = makeModificationPath λ u →
    makeNatTransPath (funExt λ g →
        B.⋆₂IdL _
      ∙ sym ( B.⟨⟩⋆₂⟨ g B.◁⟨ B.id {x} .F-id ⟩ ∙ B.◁wId g ⟩
            ∙ B.⋆₂IdR _))
  よLax .F-seq .N-ob (k , l) = yoSeq k l
  よLax .F-seq {x} {y} {z} .N-hom {k , l} {k' , l'} (κ , μ) =
    makeModificationPath λ u → makeNatTransPath (funExt λ g →
        B.⟨ sym (B.⋆ₕSeq (g B.◁w κ) B.id₂ B.id₂ μ)
          ∙ B.⟨ B.⋆₂IdR _ ⟩⋆ₕ⟨ B.⋆₂IdL _ ⟩ ⟩⋆₂⟨⟩
      ∙ B.α u x y z .trans .N-hom (B.id₂ , κ , μ))
  よLax .lax-λ x y f = makeModificationPath λ u →
    makeNatTransPath (funExt λ g →
        B.⟨ B.⋆₂IdR _ ⟩⋆₂⟨⟩
      ∙ B.⟨⟩⋆₂⟨ B.triangle u x y g f ⟩
      ∙ sym (▷wSeq B (B.ρ⁻ g) (B.ρ⁺ g) f)
      ∙ B.⟨ B.ρU u x .nIso (g , tt*) .sec ⟩▷ f
      ∙ B.▷wId f)
  よLax .lax-ρ x y f = makeModificationPath λ u →
    makeNatTransPath (funExt λ g →
        B.⟨ B.⋆₂IdL _ ⟩⋆₂⟨⟩
      ∙ B.⟨⟩⋆₂⟨ ρ⋆₁ B f g ⟩
      ∙ B.ρU u y .nIso (g B.⋆₁ f , tt*) .sec)
  よLax .lax-α x y z w f g h = makeModificationPath λ u →
    makeNatTransPath (funExt λ p →
        B.⟨ B.⋆₂IdR _ ⟩⋆₂⟨⟩
      ∙ B.pentagon u x y z w p f g h
      ∙ sym ( B.⋆₂IdL _
            ∙ B.⟨ B.⟨ B.⟨ B.▷wId g ⟩▷ h ∙ B.▷wId h ⟩⋆₂⟨⟩
                  ∙ B.⋆₂IdL _ ⟩⋆₂⟨⟩))

  private
    yoIdIsIso : (x u : B.0Cell)
      → isIso (FUNCTOR B.Hom[ u , x ] B.Hom[ u , x ]) (yoId x .M-ob u)
    yoIdIsIso x u = FUNCTORIso B.Hom[ u , x ] B.Hom[ u , x ] (yoId x .M-ob u)
      (λ g → invIso (_ , B.ρU u x .nIso (g , tt*)) .snd)

    yoSeqIsIso : {x y z : B.0Cell} (k : B.1Cell x y) (l : B.1Cell y z)
      (u : B.0Cell)
      → isIso (FUNCTOR B.Hom[ u , x ] B.Hom[ u , z ]) (yoSeq k l .M-ob u)
    yoSeqIsIso {x} {y} {z} k l u =
      FUNCTORIso B.Hom[ u , x ] B.Hom[ u , z ] (yoSeq k l .M-ob u)
        (λ g → B.α u x y z .nIso (g , k , l))

  -- The Yoneda pseudofunctor: a 0-cell goes to its representable
  -- prestack, a 1-cell to postcomposition, a 2-cell to whiskering.
  よ : Pseudofunctor B (PRESTACK B ℓ' ℓ'')
  よ .laxFunctor = よLax
  よ .F-id-isIso {x} _ =
    isiso (invMod (yoId x) (yoIdIsIso x))
          (makeModificationPath λ u → yoIdIsIso x u .sec)
          (makeModificationPath λ u → yoIdIsIso x u .ret)
  よ .F-seq-isIso (k , l) =
    isiso (invMod (yoSeq k l) (yoSeqIsIso k l))
          (makeModificationPath λ u → yoSeqIsIso k l u .sec)
          (makeModificationPath λ u → yoSeqIsIso k l u .ret)
