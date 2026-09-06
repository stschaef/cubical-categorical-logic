{-# OPTIONS --lossy-unification #-}
{-
  The free monoidal category 2-monad `T C = FreeMonoidalOn C` on CAT.

  Every laxity, coherence and modification cell is `rec₂` of the
  identity: the functors being compared agree on `↑` definitionally,
  and differ only in how they act on `unit` and `_⊗_`.  Every
  equation between such cells is `uniq₂`, so it is checked only at
  `↑`, where all the components are identities.
-}
module Cubical.Categories.Bicategory.Instances.CAT.TwoMonad.Instances.FreeMonoidal
  where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Category.More
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Functor hiding (_∘Lax_)
open import Cubical.Categories.Instances.Free.Monoidal.OnCategory
open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Functor.Identity
open import Cubical.Categories.Bicategory.Functor.Composition
open import Cubical.Categories.Bicategory.Transformation
open import Cubical.Categories.Bicategory.Transformation.Properties
open import Cubical.Categories.Bicategory.Transformation.Composition
open import Cubical.Categories.Bicategory.Transformation.Whisker
open import Cubical.Categories.Bicategory.Transformation.Coherence
open import Cubical.Categories.Bicategory.TwoMonad.Base
open import Cubical.Categories.Bicategory.TwoMonad.Algebra
  hiding (T₁; T₂)
open import Cubical.Categories.Instances.BinProduct

private
  variable
    ℓ : Level

open Category
open Functor
open NatTrans
open isIso
open StrongMonoidalFunctor
open PseudoAlgebra

module _ {ℓ : Level} where
  -- The comparison cells all have identity components on ↑, so their
  -- generating data is the transformation with identity components
  -- between two functors that agree definitionally.
  ι⁰ : {C : Category ℓ ℓ}
    → NatTrans (Id {C = |FreeMonoidalOn| C}) (T₁ (Id {C = C}))
  ι⁰ {C} = rec₂ C (FreeMonoidalOn C) IdStr (T₁Str Id)
    (natTrans (λ _ → K .id) (λ f → K .⋆IdR _ ∙ sym (K .⋆IdL _)))
    where K = |FreeMonoidalOn| C

  ι⁰⁻ : {C : Category ℓ ℓ}
    → NatTrans (T₁ (Id {C = C})) (Id {C = |FreeMonoidalOn| C})
  ι⁰⁻ {C} = rec₂ C (FreeMonoidalOn C) (T₁Str Id) IdStr
    (natTrans (λ _ → K .id) (λ f → K .⋆IdR _ ∙ sym (K .⋆IdL _)))
    where K = |FreeMonoidalOn| C

  ι² : {C D E : Category ℓ ℓ} (F : Functor C D) (G : Functor D E)
    → NatTrans (T₁ G ∘F T₁ F) (T₁ (G ∘F F))
  ι² {C} {D} {E} F G = rec₂ C (FreeMonoidalOn E)
    (T₁Str G ∘Str T₁Str F) (T₁Str (G ∘F F))
    (natTrans (λ _ → K .id) (λ f → K .⋆IdR _ ∙ sym (K .⋆IdL _)))
    where K = |FreeMonoidalOn| E

  ι²⁻ : {C D E : Category ℓ ℓ} (F : Functor C D) (G : Functor D E)
    → NatTrans (T₁ (G ∘F F)) (T₁ G ∘F T₁ F)
  ι²⁻ {C} {D} {E} F G = rec₂ C (FreeMonoidalOn E)
    (T₁Str (G ∘F F)) (T₁Str G ∘Str T₁Str F)
    (natTrans (λ _ → K .id) (λ f → K .⋆IdR _ ∙ sym (K .⋆IdL _)))
    where K = |FreeMonoidalOn| E

  private
    mι⁰ : {C : Category ℓ ℓ}
      → isMonoidalNat IdStr (T₁Str (Id {C = C})) (ι⁰ {C})
    mι⁰ {C} = rec₂-isMonoidal C (FreeMonoidalOn C) IdStr (T₁Str Id) _

    mι⁰⁻ : {C : Category ℓ ℓ}
      → isMonoidalNat (T₁Str (Id {C = C})) IdStr (ι⁰⁻ {C})
    mι⁰⁻ {C} = rec₂-isMonoidal C (FreeMonoidalOn C) (T₁Str Id) IdStr _

    mι² : {C D E : Category ℓ ℓ} (F : Functor C D) (G : Functor D E)
      → isMonoidalNat (T₁Str G ∘Str T₁Str F) (T₁Str (G ∘F F)) (ι² F G)
    mι² {C} {D} {E} F G = rec₂-isMonoidal C (FreeMonoidalOn E)
      (T₁Str G ∘Str T₁Str F) (T₁Str (G ∘F F)) _

    mι²⁻ : {C D E : Category ℓ ℓ} (F : Functor C D) (G : Functor D E)
      → isMonoidalNat (T₁Str (G ∘F F)) (T₁Str G ∘Str T₁Str F) (ι²⁻ F G)
    mι²⁻ {C} {D} {E} F G = rec₂-isMonoidal C (FreeMonoidalOn E)
      (T₁Str (G ∘F F)) (T₁Str G ∘Str T₁Str F) _

  ι⁰-sec : {C : Category ℓ ℓ}
    → seqTrans (ι⁰⁻ {C}) (ι⁰ {C}) ≡ idTrans (T₁ (Id {C = C}))
  ι⁰-sec {C} = uniq₂ C (FreeMonoidalOn C) (T₁Str Id) (T₁Str Id)
    (isMonoidalNat-seq (T₁Str Id) IdStr (T₁Str Id) ι⁰⁻ ι⁰ mι⁰⁻ mι⁰)
    (isMonoidalNat-id (T₁Str Id))
    (λ c → (|FreeMonoidalOn| C) .⋆IdL _)

  ι⁰-ret : {C : Category ℓ ℓ}
    → seqTrans (ι⁰ {C}) (ι⁰⁻ {C}) ≡ idTrans (Id {C = |FreeMonoidalOn| C})
  ι⁰-ret {C} = uniq₂ C (FreeMonoidalOn C) IdStr IdStr
    (isMonoidalNat-seq IdStr (T₁Str Id) IdStr ι⁰ ι⁰⁻ mι⁰ mι⁰⁻)
    (isMonoidalNat-id IdStr)
    (λ c → (|FreeMonoidalOn| C) .⋆IdL _)

  ι²-sec : {C D E : Category ℓ ℓ} (F : Functor C D) (G : Functor D E)
    → seqTrans (ι²⁻ F G) (ι² F G) ≡ idTrans (T₁ (G ∘F F))
  ι²-sec {C} {D} {E} F G =
    uniq₂ C (FreeMonoidalOn E) (T₁Str (G ∘F F)) (T₁Str (G ∘F F))
      (isMonoidalNat-seq (T₁Str (G ∘F F)) (T₁Str G ∘Str T₁Str F)
        (T₁Str (G ∘F F)) (ι²⁻ F G) (ι² F G) (mι²⁻ F G) (mι² F G))
      (isMonoidalNat-id (T₁Str (G ∘F F)))
      (λ c → (|FreeMonoidalOn| E) .⋆IdL _)

  ι²-ret : {C D E : Category ℓ ℓ} (F : Functor C D) (G : Functor D E)
    → seqTrans (ι² F G) (ι²⁻ F G) ≡ idTrans (T₁ G ∘F T₁ F)
  ι²-ret {C} {D} {E} F G =
    uniq₂ C (FreeMonoidalOn E)
      (T₁Str G ∘Str T₁Str F) (T₁Str G ∘Str T₁Str F)
      (isMonoidalNat-seq (T₁Str G ∘Str T₁Str F) (T₁Str (G ∘F F))
        (T₁Str G ∘Str T₁Str F) (ι² F G) (ι²⁻ F G) (mι² F G) (mι²⁻ F G))
      (isMonoidalNat-id (T₁Str G ∘Str T₁Str F))
      (λ c → (|FreeMonoidalOn| E) .⋆IdL _)

  private
    -- The unitors and associator of CAT have identity components, so
    -- their monoidality is just the functoriality of the ε and μ of
    -- an `∘Str` composite.
    mλ⁺ : {a b : Category ℓ ℓ}
      (P : StrongMonoidalFunctor (FreeMonoidalOn a) (FreeMonoidalOn b))
      → isMonoidalNat (P ∘Str IdStr) P
                      (Bicategory.λ⁺ (CAT {ℓ} {ℓ}) (P .F))
    mλ⁺ {a} {b} P .fst =
      K .⋆IdR _ ∙ cong₂ (seq' K) refl (P .F-id) ∙ K .⋆IdR _
      where K = |FreeMonoidalOn| b
    mλ⁺ {a} {b} P .snd u v =
        K .⋆IdR _ ∙ cong₂ (seq' K) refl (P .F-id)
      ∙ K .⋆IdR _ ∙ sym (collapseL K ⊗id)
      where K = |FreeMonoidalOn| b

    mρ⁺ : {a b : Category ℓ ℓ}
      (P : StrongMonoidalFunctor (FreeMonoidalOn a) (FreeMonoidalOn b))
      → isMonoidalNat (IdStr ∘Str P) P
                      (Bicategory.ρ⁺ (CAT {ℓ} {ℓ}) (P .F))
    mρ⁺ {a} {b} P .fst = K .⋆IdR _ ∙ K .⋆IdL _
      where K = |FreeMonoidalOn| b
    mρ⁺ {a} {b} P .snd u v =
      K .⋆IdR _ ∙ K .⋆IdL _ ∙ sym (collapseL K ⊗id)
      where K = |FreeMonoidalOn| b

    mρ⁻ : {a b : Category ℓ ℓ}
      (P : StrongMonoidalFunctor (FreeMonoidalOn a) (FreeMonoidalOn b))
      → isMonoidalNat P (IdStr ∘Str P)
                      (Bicategory.ρ⁻ (CAT {ℓ} {ℓ}) (P .F))
    mρ⁻ {a} {b} P .fst = K .⋆IdR _ ∙ sym (K .⋆IdL _)
      where K = |FreeMonoidalOn| b
    mρ⁻ {a} {b} P .snd u v =
      K .⋆IdR _ ∙ sym (collapseL K ⊗id ∙ K .⋆IdL _)
      where K = |FreeMonoidalOn| b

    mα⁺ : {a b c d : Category ℓ ℓ}
      (P : StrongMonoidalFunctor (FreeMonoidalOn a) (FreeMonoidalOn b))
      (Q : StrongMonoidalFunctor (FreeMonoidalOn b) (FreeMonoidalOn c))
      (R : StrongMonoidalFunctor (FreeMonoidalOn c) (FreeMonoidalOn d))
      → isMonoidalNat (R ∘Str (Q ∘Str P)) ((R ∘Str Q) ∘Str P)
          (Bicategory.α⁺ (CAT {ℓ} {ℓ}) (P .F) (Q .F) (R .F))
    mα⁺ {a} {b} {c} {d} P Q R .fst =
        K .⋆IdR _ ∙ cong₂ (seq' K) refl (R .F-seq _ _)
      ∙ sym (K .⋆Assoc _ _ _)
      where K = |FreeMonoidalOn| d
    mα⁺ {a} {b} {c} {d} P Q R .snd u v =
        K .⋆IdR _
      ∙ cong₂ (seq' K) refl (R .F-seq _ _)
      ∙ sym (K .⋆Assoc _ _ _)
      ∙ sym (collapseL K ⊗id)
      where K = |FreeMonoidalOn| d

    mα⁻ : {a b c d : Category ℓ ℓ}
      (P : StrongMonoidalFunctor (FreeMonoidalOn a) (FreeMonoidalOn b))
      (Q : StrongMonoidalFunctor (FreeMonoidalOn b) (FreeMonoidalOn c))
      (R : StrongMonoidalFunctor (FreeMonoidalOn c) (FreeMonoidalOn d))
      → isMonoidalNat ((R ∘Str Q) ∘Str P) (R ∘Str (Q ∘Str P))
          (Bicategory.α⁻ (CAT {ℓ} {ℓ}) (P .F) (Q .F) (R .F))
    mα⁻ {a} {b} {c} {d} P Q R .fst =
        K .⋆IdR _ ∙ K .⋆Assoc _ _ _
      ∙ cong₂ (seq' K) refl (sym (R .F-seq _ _))
      where K = |FreeMonoidalOn| d
    mα⁻ {a} {b} {c} {d} P Q R .snd u v =
        K .⋆IdR _ ∙ K .⋆Assoc _ _ _
      ∙ cong₂ (seq' K) refl (sym (R .F-seq _ _))
      ∙ sym (collapseL K ⊗id)
      where K = |FreeMonoidalOn| d

  FMLax : LaxFunctor (CAT {ℓ} {ℓ}) (CAT {ℓ} {ℓ})
  FMLax .LaxFunctor.F-ob C = |FreeMonoidalOn| C
  FMLax .LaxFunctor.F-Hom = TFun
  FMLax .LaxFunctor.F-id .N-ob _ = ι⁰
  FMLax .LaxFunctor.F-id {x} .N-hom _ =
    uniq₂ x (FreeMonoidalOn x) IdStr (T₁Str Id)
      (isMonoidalNat-seq IdStr IdStr (T₁Str Id)
        (idTrans Id) ι⁰ (isMonoidalNat-id IdStr) mι⁰)
      (isMonoidalNat-seq IdStr (T₁Str Id) (T₁Str Id)
        ι⁰ (T₂ Id Id (idTrans Id)) mι⁰ (T₂-isMonoidal Id Id (idTrans Id)))
      (λ c → cong (λ m → K .id ⋆⟨ K ⟩ m) (sym ↑ₘId))
    where K = |FreeMonoidalOn| x
  FMLax .LaxFunctor.F-seq .N-ob (F , G) = ι² F G
  FMLax .LaxFunctor.F-seq {x} {y} {z} .N-hom {F , G} {F' , G'} (u , v) =
    uniq₂ x (FreeMonoidalOn z)
      (T₁Str G ∘Str T₁Str F) (T₁Str (G' ∘F F'))
      (isMonoidalNat-seq (T₁Str G ∘Str T₁Str F) (T₁Str G' ∘Str T₁Str F')
        (T₁Str (G' ∘F F')) (hSeqCAT (T₂ F F' u) (T₂ G G' v)) (ι² F' G')
        (isMonoidalNat-seq (T₁Str G ∘Str T₁Str F) (T₁Str G ∘Str T₁Str F')
          (T₁Str G' ∘Str T₁Str F')
          (T₁ G ∘ʳ T₂ F F' u) (T₂ G G' v ∘ˡ T₁ F')
          (isMonoidalNat-∘ʳ (T₁Str G) (T₁Str F) (T₁Str F')
            (T₂ F F' u) (T₂-isMonoidal F F' u))
          (isMonoidalNat-∘ˡ (T₁Str F') (T₁Str G) (T₁Str G')
            (T₂ G G' v) (T₂-isMonoidal G G' v)))
        (mι² F' G'))
      (isMonoidalNat-seq (T₁Str G ∘Str T₁Str F) (T₁Str (G ∘F F))
        (T₁Str (G' ∘F F')) (ι² F G)
        (T₂ (G ∘F F) (G' ∘F F') (hSeqCAT u v)) (mι² F G)
        (T₂-isMonoidal (G ∘F F) (G' ∘F F') (hSeqCAT u v)))
      (λ c → K .⋆IdR _ ∙ sym (↑ₘSeq _ _) ∙ sym (K .⋆IdL _))
    where K = |FreeMonoidalOn| z
  FMLax .LaxFunctor.lax-λ x y f =
    uniq₂ x (FreeMonoidalOn y) (T₁Str f ∘Str IdStr) (T₁Str f)
      (isMonoidalNat-seq (T₁Str f ∘Str IdStr) (T₁Str f ∘Str T₁Str Id)
        (T₁Str f) wh rest
        (isMonoidalNat-seq (T₁Str f ∘Str IdStr) (T₁Str f ∘Str T₁Str Id)
          (T₁Str f ∘Str T₁Str Id) (T₁ f ∘ʳ ι⁰) (idTrans (T₁ f) ∘ˡ T₁ Id)
          (isMonoidalNat-∘ʳ (T₁Str f) IdStr (T₁Str Id) ι⁰ mι⁰)
          (isMonoidalNat-∘ˡ (T₁Str Id) (T₁Str f) (T₁Str f)
            (idTrans (T₁ f)) (isMonoidalNat-id (T₁Str f))))
        (isMonoidalNat-seq (T₁Str f ∘Str T₁Str Id) (T₁Str (f ∘F Id))
          (T₁Str f) (ι² Id f) (T₂ (f ∘F Id) f uf) (mι² Id f)
          (T₂-isMonoidal (f ∘F Id) f uf)))
      (mλ⁺ (T₁Str f))
      (λ c → collapse K (K .⋆IdL _) (K .⋆IdL _ ∙ ↑ₘId))
    where
      K = |FreeMonoidalOn| y
      uf = Bicategory.λ⁺ (CAT {ℓ} {ℓ}) f
      wh = hSeqCAT ι⁰ (idTrans (T₁ f))
      rest = seqTrans (ι² Id f) (T₂ (f ∘F Id) f uf)
  FMLax .LaxFunctor.lax-ρ x y f =
    uniq₂ x (FreeMonoidalOn y) (IdStr ∘Str T₁Str f) (T₁Str f)
      (isMonoidalNat-seq (IdStr ∘Str T₁Str f) (T₁Str Id ∘Str T₁Str f)
        (T₁Str f) wh rest
        (isMonoidalNat-seq (IdStr ∘Str T₁Str f) (IdStr ∘Str T₁Str f)
          (T₁Str Id ∘Str T₁Str f)
          (Id ∘ʳ idTrans (T₁ f)) (ι⁰ ∘ˡ T₁ f)
          (isMonoidalNat-∘ʳ IdStr (T₁Str f) (T₁Str f)
            (idTrans (T₁ f)) (isMonoidalNat-id (T₁Str f)))
          (isMonoidalNat-∘ˡ (T₁Str f) IdStr (T₁Str Id) ι⁰ mι⁰))
        (isMonoidalNat-seq (T₁Str Id ∘Str T₁Str f) (T₁Str (Id ∘F f))
          (T₁Str f) (ι² f Id) (T₂ (Id ∘F f) f uf) (mι² f Id)
          (T₂-isMonoidal (Id ∘F f) f uf)))
      (mρ⁺ (T₁Str f))
      (λ c → collapse K (K .⋆IdL _) (K .⋆IdL _ ∙ ↑ₘId))
    where
      K = |FreeMonoidalOn| y
      uf = Bicategory.ρ⁺ (CAT {ℓ} {ℓ}) f
      wh = hSeqCAT (idTrans (T₁ f)) ι⁰
      rest = seqTrans (ι² f Id) (T₂ (Id ∘F f) f uf)
  FMLax .LaxFunctor.lax-α x y z w f g h =
    uniq₂ x (FreeMonoidalOn w)
      (T₁Str h ∘Str (T₁Str g ∘Str T₁Str f)) (T₁Str ((h ∘F g) ∘F f))
      (isMonoidalNat-seq (T₁Str h ∘Str (T₁Str g ∘Str T₁Str f))
        (T₁Str h ∘Str T₁Str (g ∘F f)) (T₁Str ((h ∘F g) ∘F f)) whL restL
        (isMonoidalNat-seq (T₁Str h ∘Str (T₁Str g ∘Str T₁Str f))
          (T₁Str h ∘Str T₁Str (g ∘F f)) (T₁Str h ∘Str T₁Str (g ∘F f))
          (T₁ h ∘ʳ ι² f g) (idTrans (T₁ h) ∘ˡ T₁ (g ∘F f))
          (isMonoidalNat-∘ʳ (T₁Str h) (T₁Str g ∘Str T₁Str f)
            (T₁Str (g ∘F f)) (ι² f g) (mι² f g))
          (isMonoidalNat-∘ˡ (T₁Str (g ∘F f)) (T₁Str h) (T₁Str h)
            (idTrans (T₁ h)) (isMonoidalNat-id (T₁Str h))))
        (isMonoidalNat-seq (T₁Str h ∘Str T₁Str (g ∘F f))
          (T₁Str (h ∘F (g ∘F f))) (T₁Str ((h ∘F g) ∘F f))
          (ι² (g ∘F f) h) (T₂ (h ∘F (g ∘F f)) ((h ∘F g) ∘F f) af)
          (mι² (g ∘F f) h)
          (T₂-isMonoidal (h ∘F (g ∘F f)) ((h ∘F g) ∘F f) af)))
      (isMonoidalNat-seq (T₁Str h ∘Str (T₁Str g ∘Str T₁Str f))
        ((T₁Str h ∘Str T₁Str g) ∘Str T₁Str f) (T₁Str ((h ∘F g) ∘F f))
        af' (seqTrans whR (ι² f (h ∘F g))) (mα⁺ (T₁Str f) (T₁Str g) (T₁Str h))
        (isMonoidalNat-seq ((T₁Str h ∘Str T₁Str g) ∘Str T₁Str f)
          (T₁Str (h ∘F g) ∘Str T₁Str f) (T₁Str ((h ∘F g) ∘F f))
          whR (ι² f (h ∘F g))
          (isMonoidalNat-seq ((T₁Str h ∘Str T₁Str g) ∘Str T₁Str f)
            ((T₁Str h ∘Str T₁Str g) ∘Str T₁Str f)
            (T₁Str (h ∘F g) ∘Str T₁Str f)
            ((T₁ h ∘F T₁ g) ∘ʳ idTrans (T₁ f)) (ι² g h ∘ˡ T₁ f)
            (isMonoidalNat-∘ʳ (T₁Str h ∘Str T₁Str g) (T₁Str f) (T₁Str f)
              (idTrans (T₁ f)) (isMonoidalNat-id (T₁Str f)))
            (isMonoidalNat-∘ˡ (T₁Str f) (T₁Str h ∘Str T₁Str g)
              (T₁Str (h ∘F g)) (ι² g h) (mι² g h)))
          (mι² f (h ∘F g))))
      (λ c → collapse K (K .⋆IdL _) (K .⋆IdL _ ∙ ↑ₘId) ∙ sym (four' K))
    where
      K = |FreeMonoidalOn| w
      af = Bicategory.α⁺ (CAT {ℓ} {ℓ}) f g h
      af' = Bicategory.α⁺ (CAT {ℓ} {ℓ}) (T₁ f) (T₁ g) (T₁ h)
      whL = hSeqCAT (ι² f g) (idTrans (T₁ h))
      whR = hSeqCAT (idTrans (T₁ f)) (ι² g h)
      restL = seqTrans (ι² (g ∘F f) h)
        (T₂ (h ∘F (g ∘F f)) ((h ∘F g) ∘F f) af)

  FMPs : Pseudofunctor (CAT {ℓ} {ℓ}) (CAT {ℓ} {ℓ})
  FMPs .Pseudofunctor.laxFunctor = FMLax
  FMPs .Pseudofunctor.F-id-isIso _ .inv = ι⁰⁻
  FMPs .Pseudofunctor.F-id-isIso _ .sec = ι⁰-sec
  FMPs .Pseudofunctor.F-id-isIso _ .ret = ι⁰-ret
  FMPs .Pseudofunctor.F-seq-isIso (F , G) .inv = ι²⁻ F G
  FMPs .Pseudofunctor.F-seq-isIso (F , G) .sec = ι²-sec F G
  FMPs .Pseudofunctor.F-seq-isIso (F , G) .ret = ι²-ret F G

  -- `T₁ F ∘F ηFree` and `ηFree ∘F F` agree definitionally, so the
  -- unit is 2-natural with identity components.
  private
    ηnat : {x y : Category ℓ ℓ} (F : Functor x y)
      → NatTrans (ηFree y ∘F F) (T₁ F ∘F ηFree x)
    ηnat {x} {y} F = natTrans (λ _ → K .id)
      (λ f → K .⋆IdR _ ∙ sym (K .⋆IdL _))
      where K = |FreeMonoidalOn| y

  FMUnit : LaxNatTrans (LaxId (CAT {ℓ} {ℓ})) FMLax
  FMUnit .LaxNatTrans.N-1cell = ηFree
  FMUnit .LaxNatTrans.N-hom F = ηnat F
  FMUnit .LaxNatTrans.N-natural {y = y} {f} θ =
    makeNatTransPath (funExt λ c →
        cong (λ m → m ⋆⟨ K ⟩ K .id) (K .⋆IdR _) ∙ K .⋆IdR _
      ∙ sym (K .⋆IdL _ ∙ collapseL K (T₁ f .F-id {x = ↑ c})))
    where K = |FreeMonoidalOn| y
  FMUnit .LaxNatTrans.lax-id C =
    makeNatTransPath (funExt λ c →
        collapse K (collapse K ↑ₘId refl) refl
      ∙ sym (collapse K refl (collapse K refl (K .⋆IdL _))))
    where K = |FreeMonoidalOn| C
  FMUnit .LaxNatTrans.lax-seq {z = z} f g =
    makeNatTransPath (funExt λ c →
      let pb = K .⋆IdR _ ∙ cong (ηFree z .F-hom) (g .F-id) ∙ ↑ₘId
          pd = K .⋆IdR _ ∙ T₁ g .F-id {x = ↑ (f ⟅ c ⟆)}
          pe = K .⋆IdR _
             ∙ cong (T₁ g .F-hom) (T₁ f .F-id {x = ↑ c})
             ∙ T₁ g .F-id
      in  collapse K (collapse K ↑ₘId refl) refl
        ∙ sym (collapse K refl (collapse K pb
                (collapse K refl (collapse K pd
                  (collapse K refl pe))))))
    where K = |FreeMonoidalOn| z

  -- `μFree ∘F T₁ (T₁ F)` and `T₁ F ∘F μFree` agree on ↑, so the
  -- multiplication is 2-natural by `rec₂`.
  μnat : {x y : Category ℓ ℓ} (F : Functor x y)
    → NatTrans (μFree y ∘F T₁ (T₁ F)) (T₁ F ∘F μFree x)
  μnat {x} {y} F = rec₂ (|FreeMonoidalOn| x) (FreeMonoidalOn y)
    (μFreeStr y ∘Str T₁Str (T₁ F)) (T₁Str F ∘Str μFreeStr x)
    (natTrans (λ _ → K .id) (λ f → K .⋆IdR _ ∙ sym (K .⋆IdL _)))
    where K = |FreeMonoidalOn| y

  private
    mμnat : {x y : Category ℓ ℓ} (F : Functor x y)
      → isMonoidalNat (μFreeStr y ∘Str T₁Str (T₁ F))
                      (T₁Str F ∘Str μFreeStr x) (μnat F)
    mμnat {x} {y} F =
      rec₂-isMonoidal (|FreeMonoidalOn| x) (FreeMonoidalOn y)
        (μFreeStr y ∘Str T₁Str (T₁ F)) (T₁Str F ∘Str μFreeStr x) _

    -- the laxity cell of `FMLax ∘Lax FMLax`
    ι²² : {x y z : Category ℓ ℓ} (f : Functor x y) (g : Functor y z)
      → NatTrans (T₁ (T₁ g) ∘F T₁ (T₁ f)) (T₁ (T₁ (g ∘F f)))
    ι²² f g = seqTrans (ι² (T₁ f) (T₁ g))
      (T₂ (T₁ g ∘F T₁ f) (T₁ (g ∘F f)) (ι² f g))

    mι²² : {x y z : Category ℓ ℓ} (f : Functor x y) (g : Functor y z)
      → isMonoidalNat (T₁Str (T₁ g) ∘Str T₁Str (T₁ f))
                      (T₁Str (T₁ (g ∘F f))) (ι²² f g)
    mι²² f g = isMonoidalNat-seq
      (T₁Str (T₁ g) ∘Str T₁Str (T₁ f)) (T₁Str (T₁ g ∘F T₁ f))
      (T₁Str (T₁ (g ∘F f))) (ι² (T₁ f) (T₁ g))
      (T₂ (T₁ g ∘F T₁ f) (T₁ (g ∘F f)) (ι² f g))
      (mι² (T₁ f) (T₁ g))
      (T₂-isMonoidal (T₁ g ∘F T₁ f) (T₁ (g ∘F f)) (ι² f g))

    ι⁰⁰ : {x : Category ℓ ℓ}
      → NatTrans (Id {C = |FreeMonoidalOn| (|FreeMonoidalOn| x)})
                 (T₁ (T₁ (Id {C = x})))
    ι⁰⁰ = seqTrans ι⁰ (T₂ Id (T₁ Id) ι⁰)

    mι⁰⁰ : {x : Category ℓ ℓ}
      → isMonoidalNat IdStr (T₁Str (T₁ (Id {C = x}))) (ι⁰⁰ {x})
    mι⁰⁰ = isMonoidalNat-seq IdStr (T₁Str Id) (T₁Str (T₁ Id))
      ι⁰ (T₂ Id (T₁ Id) ι⁰) mι⁰ (T₂-isMonoidal Id (T₁ Id) ι⁰)

  FMMult : LaxNatTrans (FMLax ∘Lax FMLax) FMLax
  FMMult .LaxNatTrans.N-1cell = μFree
  FMMult .LaxNatTrans.N-hom F = μnat F
  FMMult .LaxNatTrans.N-natural {x} {y} {f} {g} θ =
    uniq₂ (|FreeMonoidalOn| x) (FreeMonoidalOn y)
      (μFreeStr y ∘Str T₁Str (T₁ f)) (T₁Str g ∘Str μFreeStr x)
      (isMonoidalNat-seq (μFreeStr y ∘Str T₁Str (T₁ f))
        (μFreeStr y ∘Str T₁Str (T₁ g)) (T₁Str g ∘Str μFreeStr x)
        wh (μnat g)
        (isMonoidalNat-seq (μFreeStr y ∘Str T₁Str (T₁ f))
          (μFreeStr y ∘Str T₁Str (T₁ g)) (μFreeStr y ∘Str T₁Str (T₁ g))
          (μFree y ∘ʳ T₂ (T₁ f) (T₁ g) (T₂ f g θ))
          (idTrans (μFree y) ∘ˡ T₁ (T₁ g))
          (isMonoidalNat-∘ʳ (μFreeStr y) (T₁Str (T₁ f)) (T₁Str (T₁ g))
            (T₂ (T₁ f) (T₁ g) (T₂ f g θ))
            (T₂-isMonoidal (T₁ f) (T₁ g) (T₂ f g θ)))
          (isMonoidalNat-∘ˡ (T₁Str (T₁ g)) (μFreeStr y) (μFreeStr y)
            (idTrans (μFree y)) (isMonoidalNat-id (μFreeStr y))))
        (mμnat g))
      (isMonoidalNat-seq (μFreeStr y ∘Str T₁Str (T₁ f))
        (T₁Str f ∘Str μFreeStr x) (T₁Str g ∘Str μFreeStr x)
        (μnat f) wh' (mμnat f)
        (isMonoidalNat-seq (T₁Str f ∘Str μFreeStr x)
          (T₁Str f ∘Str μFreeStr x) (T₁Str g ∘Str μFreeStr x)
          (T₁ f ∘ʳ idTrans (μFree x)) (T₂ f g θ ∘ˡ μFree x)
          (isMonoidalNat-∘ʳ (T₁Str f) (μFreeStr x) (μFreeStr x)
            (idTrans (μFree x)) (isMonoidalNat-id (μFreeStr x)))
          (isMonoidalNat-∘ˡ (μFreeStr x) (T₁Str f) (T₁Str g)
            (T₂ f g θ) (T₂-isMonoidal f g θ))))
      (λ c → cong (λ m → m ⋆⟨ K ⟩ K .id) (K .⋆IdR _) ∙ K .⋆IdR _
           ∙ sym (K .⋆IdL _ ∙ collapseL K (T₁ f .F-id {x = c})))
    where
      K = |FreeMonoidalOn| y
      wh = hSeqCAT (T₂ (T₁ f) (T₁ g) (T₂ f g θ)) (idTrans (μFree y))
      wh' = hSeqCAT (idTrans (μFree x)) (T₂ f g θ)
  FMMult .LaxNatTrans.lax-id C =
    uniq₂ (|FreeMonoidalOn| C) (FreeMonoidalOn C)
      (μFreeStr C ∘Str IdStr) (T₁Str Id ∘Str μFreeStr C)
      (isMonoidalNat-seq (μFreeStr C ∘Str IdStr)
        (μFreeStr C ∘Str T₁Str (T₁ Id)) (T₁Str Id ∘Str μFreeStr C)
        wh (μnat Id)
        (isMonoidalNat-seq (μFreeStr C ∘Str IdStr)
          (μFreeStr C ∘Str T₁Str (T₁ Id)) (μFreeStr C ∘Str T₁Str (T₁ Id))
          (μFree C ∘ʳ ι⁰⁰) (idTrans (μFree C) ∘ˡ T₁ (T₁ Id))
          (isMonoidalNat-∘ʳ (μFreeStr C) IdStr (T₁Str (T₁ Id)) ι⁰⁰ mι⁰⁰)
          (isMonoidalNat-∘ˡ (T₁Str (T₁ Id)) (μFreeStr C) (μFreeStr C)
            (idTrans (μFree C)) (isMonoidalNat-id (μFreeStr C))))
        (mμnat Id))
      (isMonoidalNat-seq (μFreeStr C ∘Str IdStr) (μFreeStr C)
        (T₁Str Id ∘Str μFreeStr C) lu (seqTrans ru wh')
        (mλ⁺ (μFreeStr C))
        (isMonoidalNat-seq (μFreeStr C) (IdStr ∘Str μFreeStr C)
          (T₁Str Id ∘Str μFreeStr C) ru wh' (mρ⁻ (μFreeStr C))
          (isMonoidalNat-seq (IdStr ∘Str μFreeStr C)
            (IdStr ∘Str μFreeStr C) (T₁Str Id ∘Str μFreeStr C)
            (Id ∘ʳ idTrans (μFree C)) (ι⁰ ∘ˡ μFree C)
            (isMonoidalNat-∘ʳ IdStr (μFreeStr C) (μFreeStr C)
              (idTrans (μFree C)) (isMonoidalNat-id (μFreeStr C)))
            (isMonoidalNat-∘ˡ (μFreeStr C) IdStr (T₁Str Id) ι⁰ mι⁰))))
      (λ c → K .⋆IdR _ ∙ K .⋆IdR _ ∙ sym (K .⋆IdL _ ∙ K .⋆IdL _))
    where
      K = |FreeMonoidalOn| C
      wh = hSeqCAT ι⁰⁰ (idTrans (μFree C))
      wh' = hSeqCAT (idTrans (μFree C)) ι⁰
      lu = Bicategory.λ⁺ (CAT {ℓ} {ℓ}) (μFree C)
      ru = Bicategory.ρ⁻ (CAT {ℓ} {ℓ}) (μFree C)
  FMMult .LaxNatTrans.lax-seq {x} {y} {z} f g =
    uniq₂ (|FreeMonoidalOn| x) (FreeMonoidalOn z)
      S0 (T₁Str (g ∘F f) ∘Str μFreeStr x)
      (isMonoidalNat-seq S0 (μFreeStr z ∘Str T₁Str (T₁ (g ∘F f)))
        (T₁Str (g ∘F f) ∘Str μFreeStr x) whL (μnat (g ∘F f))
        (isMonoidalNat-seq S0 (μFreeStr z ∘Str T₁Str (T₁ (g ∘F f)))
          (μFreeStr z ∘Str T₁Str (T₁ (g ∘F f)))
          (μFree z ∘ʳ ι²² f g) (idTrans (μFree z) ∘ˡ T₁ (T₁ (g ∘F f)))
          (isMonoidalNat-∘ʳ (μFreeStr z) (T₁Str (T₁ g) ∘Str T₁Str (T₁ f))
            (T₁Str (T₁ (g ∘F f))) (ι²² f g) (mι²² f g))
          (isMonoidalNat-∘ˡ (T₁Str (T₁ (g ∘F f))) (μFreeStr z)
            (μFreeStr z) (idTrans (μFree z))
            (isMonoidalNat-id (μFreeStr z))))
        (mμnat (g ∘F f)))
      (isMonoidalNat-seq S0 S1 (T₁Str (g ∘F f) ∘Str μFreeStr x) A1
        (seqTrans A2 (seqTrans A3 (seqTrans A4 (seqTrans A5 A6))))
        (mα⁺ (T₁Str (T₁ f)) (T₁Str (T₁ g)) (μFreeStr z))
        (isMonoidalNat-seq S1 S2 (T₁Str (g ∘F f) ∘Str μFreeStr x) A2
          (seqTrans A3 (seqTrans A4 (seqTrans A5 A6)))
          (isMonoidalNat-seq S1 S1 S2
            ((μFree z ∘F T₁ (T₁ g)) ∘ʳ idTrans (T₁ (T₁ f)))
            (μnat g ∘ˡ T₁ (T₁ f))
            (isMonoidalNat-∘ʳ (μFreeStr z ∘Str T₁Str (T₁ g))
              (T₁Str (T₁ f)) (T₁Str (T₁ f)) (idTrans (T₁ (T₁ f)))
              (isMonoidalNat-id (T₁Str (T₁ f))))
            (isMonoidalNat-∘ˡ (T₁Str (T₁ f))
              (μFreeStr z ∘Str T₁Str (T₁ g)) (T₁Str g ∘Str μFreeStr y)
              (μnat g) (mμnat g)))
          (isMonoidalNat-seq S2 S3 (T₁Str (g ∘F f) ∘Str μFreeStr x) A3
            (seqTrans A4 (seqTrans A5 A6))
            (mα⁻ (T₁Str (T₁ f)) (μFreeStr y) (T₁Str g))
            (isMonoidalNat-seq S3 S4 (T₁Str (g ∘F f) ∘Str μFreeStr x)
              A4 (seqTrans A5 A6)
              (isMonoidalNat-seq S3 S4 S4
                (T₁ g ∘ʳ μnat f) (idTrans (T₁ g) ∘ˡ (T₁ f ∘F μFree x))
                (isMonoidalNat-∘ʳ (T₁Str g)
                  (μFreeStr y ∘Str T₁Str (T₁ f))
                  (T₁Str f ∘Str μFreeStr x) (μnat f) (mμnat f))
                (isMonoidalNat-∘ˡ (T₁Str f ∘Str μFreeStr x) (T₁Str g)
                  (T₁Str g) (idTrans (T₁ g))
                  (isMonoidalNat-id (T₁Str g))))
              (isMonoidalNat-seq S4 S5
                (T₁Str (g ∘F f) ∘Str μFreeStr x) A5 A6
                (mα⁺ (μFreeStr x) (T₁Str f) (T₁Str g))
                (isMonoidalNat-seq S5 S5
                  (T₁Str (g ∘F f) ∘Str μFreeStr x)
                  ((T₁ g ∘F T₁ f) ∘ʳ idTrans (μFree x))
                  (ι² f g ∘ˡ μFree x)
                  (isMonoidalNat-∘ʳ (T₁Str g ∘Str T₁Str f) (μFreeStr x)
                    (μFreeStr x) (idTrans (μFree x))
                    (isMonoidalNat-id (μFreeStr x)))
                  (isMonoidalNat-∘ˡ (μFreeStr x)
                    (T₁Str g ∘Str T₁Str f) (T₁Str (g ∘F f)) (ι² f g)
                    (mι² f g))))))))
      (λ c → K .⋆IdR _ ∙ K .⋆IdR _
           ∙ sym (K .⋆IdL _ ∙ collapseL K (K .⋆IdL _) ∙ K .⋆IdL _
                 ∙ collapseL K (K .⋆IdL _) ∙ K .⋆IdL _))
    where
      K = |FreeMonoidalOn| z
      S0 = μFreeStr z ∘Str (T₁Str (T₁ g) ∘Str T₁Str (T₁ f))
      S1 = (μFreeStr z ∘Str T₁Str (T₁ g)) ∘Str T₁Str (T₁ f)
      S2 = (T₁Str g ∘Str μFreeStr y) ∘Str T₁Str (T₁ f)
      S3 = T₁Str g ∘Str (μFreeStr y ∘Str T₁Str (T₁ f))
      S4 = T₁Str g ∘Str (T₁Str f ∘Str μFreeStr x)
      S5 = (T₁Str g ∘Str T₁Str f) ∘Str μFreeStr x
      whL = hSeqCAT (ι²² f g) (idTrans (μFree z))
      A1 = Bicategory.α⁺ (CAT {ℓ} {ℓ}) (T₁ (T₁ f)) (T₁ (T₁ g)) (μFree z)
      A2 = hSeqCAT (idTrans (T₁ (T₁ f))) (μnat g)
      A3 = Bicategory.α⁻ (CAT {ℓ} {ℓ}) (T₁ (T₁ f)) (μFree y) (T₁ g)
      A4 = hSeqCAT (μnat f) (idTrans (T₁ g))
      A5 = Bicategory.α⁺ (CAT {ℓ} {ℓ}) (μFree x) (T₁ f) (T₁ g)
      A6 = hSeqCAT (idTrans (μFree x)) (ι² f g)

  private
    mλ⁻ : {a b : Category ℓ ℓ}
      (P : StrongMonoidalFunctor (FreeMonoidalOn a) (FreeMonoidalOn b))
      → isMonoidalNat P (P ∘Str IdStr)
                      (Bicategory.λ⁻ (CAT {ℓ} {ℓ}) (P .F))
    mλ⁻ {a} {b} P .fst =
      K .⋆IdR _ ∙ sym (cong₂ (seq' K) refl (P .F-id) ∙ K .⋆IdR _)
      where K = |FreeMonoidalOn| b
    mλ⁻ {a} {b} P .snd u v =
        K .⋆IdR _
      ∙ sym (collapseL K ⊗id ∙ cong₂ (seq' K) refl (P .F-id)
            ∙ K .⋆IdR _)
      where K = |FreeMonoidalOn| b

  -- The left unit law: `μFree ∘F T₁ ηFree ≅ Id`.
  uL : (C : Category ℓ ℓ)
    → NatTrans (μFree C ∘F T₁ (ηFree C)) (Id {C = |FreeMonoidalOn| C})
  uL C = rec₂ C (FreeMonoidalOn C)
    (μFreeStr C ∘Str T₁Str (ηFree C)) IdStr
    (natTrans (λ _ → K .id) (λ f → K .⋆IdR _ ∙ sym (K .⋆IdL _)))
    where K = |FreeMonoidalOn| C

  uL⁻ : (C : Category ℓ ℓ)
    → NatTrans (Id {C = |FreeMonoidalOn| C}) (μFree C ∘F T₁ (ηFree C))
  uL⁻ C = rec₂ C (FreeMonoidalOn C) IdStr
    (μFreeStr C ∘Str T₁Str (ηFree C))
    (natTrans (λ _ → K .id) (λ f → K .⋆IdR _ ∙ sym (K .⋆IdL _)))
    where K = |FreeMonoidalOn| C

  private
    muL : (C : Category ℓ ℓ)
      → isMonoidalNat (μFreeStr C ∘Str T₁Str (ηFree C)) IdStr (uL C)
    muL C = rec₂-isMonoidal C (FreeMonoidalOn C)
      (μFreeStr C ∘Str T₁Str (ηFree C)) IdStr _

    muL⁻ : (C : Category ℓ ℓ)
      → isMonoidalNat IdStr (μFreeStr C ∘Str T₁Str (ηFree C)) (uL⁻ C)
    muL⁻ C = rec₂-isMonoidal C (FreeMonoidalOn C)
      IdStr (μFreeStr C ∘Str T₁Str (ηFree C)) _

    uL-isIso : (C : Category ℓ ℓ)
      → isIso (FUNCTOR (|FreeMonoidalOn| C) (|FreeMonoidalOn| C)) (uL C)
    uL-isIso C .inv = uL⁻ C
    uL-isIso C .sec = uniq₂ C (FreeMonoidalOn C) IdStr IdStr
      (isMonoidalNat-seq IdStr (μFreeStr C ∘Str T₁Str (ηFree C)) IdStr
        (uL⁻ C) (uL C) (muL⁻ C) (muL C))
      (isMonoidalNat-id IdStr)
      (λ c → (|FreeMonoidalOn| C) .⋆IdL _)
    uL-isIso C .ret = uniq₂ C (FreeMonoidalOn C)
      (μFreeStr C ∘Str T₁Str (ηFree C))
      (μFreeStr C ∘Str T₁Str (ηFree C))
      (isMonoidalNat-seq (μFreeStr C ∘Str T₁Str (ηFree C)) IdStr
        (μFreeStr C ∘Str T₁Str (ηFree C)) (uL C) (uL⁻ C) (muL C) (muL⁻ C))
      (isMonoidalNat-id (μFreeStr C ∘Str T₁Str (ηFree C)))
      (λ c → (|FreeMonoidalOn| C) .⋆IdL _)

  unitLMod : Modification
    (seqLaxNatTrans (whiskerL FMPs FMUnit) FMMult) (ridLax FMLax)
  unitLMod .Modification.M-ob C = uL C
  unitLMod .Modification.M-hom {x} {y} f =
    uniq₂ x (FreeMonoidalOn y) M0 M6
      (isMonoidalNat-seq M0 M5 M6
        (seqTrans A1 (seqTrans A2 (seqTrans A3 (seqTrans A4 A5)))) A6
        (isMonoidalNat-seq M0 M1 M5 A1
          (seqTrans A2 (seqTrans A3 (seqTrans A4 A5)))
          (mα⁻ (T₁Str f) (T₁Str (ηFree y)) (μFreeStr y))
          (isMonoidalNat-seq M1 M2 M5 A2
            (seqTrans A3 (seqTrans A4 A5))
            (isMonoidalNat-seq M1 M2 M2
              (μFree y ∘ʳ WH) (idTrans (μFree y) ∘ˡ TT)
              (isMonoidalNat-∘ʳ (μFreeStr y)
                (T₁Str (ηFree y) ∘Str T₁Str f)
                (T₁Str (T₁ f) ∘Str T₁Str (ηFree x)) WH mWH)
              (isMonoidalNat-∘ˡ (T₁Str (T₁ f) ∘Str T₁Str (ηFree x))
                (μFreeStr y) (μFreeStr y) (idTrans (μFree y))
                (isMonoidalNat-id (μFreeStr y))))
            (isMonoidalNat-seq M2 M3 M5 A3 (seqTrans A4 A5)
              (mα⁺ (T₁Str (ηFree x)) (T₁Str (T₁ f)) (μFreeStr y))
              (isMonoidalNat-seq M3 M4 M5 A4 A5
                (isMonoidalNat-seq M3 M3 M4
                  ((μFree y ∘F T₁ (T₁ f)) ∘ʳ idTrans (T₁ (ηFree x)))
                  (μnat f ∘ˡ T₁ (ηFree x))
                  (isMonoidalNat-∘ʳ (μFreeStr y ∘Str T₁Str (T₁ f))
                    (T₁Str (ηFree x)) (T₁Str (ηFree x))
                    (idTrans (T₁ (ηFree x)))
                    (isMonoidalNat-id (T₁Str (ηFree x))))
                  (isMonoidalNat-∘ˡ (T₁Str (ηFree x))
                    (μFreeStr y ∘Str T₁Str (T₁ f))
                    (T₁Str f ∘Str μFreeStr x) (μnat f) (mμnat f)))
                (mα⁻ (T₁Str (ηFree x)) (μFreeStr x) (T₁Str f))))))
        (isMonoidalNat-seq M5 M6 M6
          (T₁ f ∘ʳ uL x) (idTrans (T₁ f) ∘ˡ Id)
          (isMonoidalNat-∘ʳ (T₁Str f)
            (μFreeStr x ∘Str T₁Str (ηFree x)) IdStr (uL x) (muL x))
          (isMonoidalNat-∘ˡ IdStr (T₁Str f) (T₁Str f) (idTrans (T₁ f))
            (isMonoidalNat-id (T₁Str f)))))
      (isMonoidalNat-seq M0 R1 M6 B1 (seqTrans B2 B3)
        (isMonoidalNat-seq M0 M0 R1
          ((μFree y ∘F T₁ (ηFree y)) ∘ʳ idTrans (T₁ f)) (uL y ∘ˡ T₁ f)
          (isMonoidalNat-∘ʳ (μFreeStr y ∘Str T₁Str (ηFree y))
            (T₁Str f) (T₁Str f) (idTrans (T₁ f))
            (isMonoidalNat-id (T₁Str f)))
          (isMonoidalNat-∘ˡ (T₁Str f)
            (μFreeStr y ∘Str T₁Str (ηFree y)) IdStr (uL y) (muL y)))
        (isMonoidalNat-seq R1 (T₁Str f) M6 B2 B3
          (mρ⁺ (T₁Str f)) (mλ⁻ (T₁Str f))))
      (λ c → collapse K
               (collapse K refl
                 (collapse K
                   (collapse K (collapse K refl (K .⋆IdL _)) refl)
                   (collapse K refl (collapse K (K .⋆IdL _) refl))))
               (K .⋆IdL _)
           ∙ sym (four K))
    where
      K = |FreeMonoidalOn| y
      TT = T₁ (T₁ f) ∘F T₁ (ηFree x)
      WH = seqTrans (ι² f (ηFree y))
        (seqTrans (T₂ (ηFree y ∘F f) (T₁ f ∘F ηFree x) (ηnat f))
          (ι²⁻ (ηFree x) (T₁ f)))
      mWH = isMonoidalNat-seq (T₁Str (ηFree y) ∘Str T₁Str f)
        (T₁Str (ηFree y ∘F f)) (T₁Str (T₁ f) ∘Str T₁Str (ηFree x))
        (ι² f (ηFree y))
        (seqTrans (T₂ (ηFree y ∘F f) (T₁ f ∘F ηFree x) (ηnat f))
          (ι²⁻ (ηFree x) (T₁ f)))
        (mι² f (ηFree y))
        (isMonoidalNat-seq (T₁Str (ηFree y ∘F f))
          (T₁Str (T₁ f ∘F ηFree x))
          (T₁Str (T₁ f) ∘Str T₁Str (ηFree x))
          (T₂ (ηFree y ∘F f) (T₁ f ∘F ηFree x) (ηnat f))
          (ι²⁻ (ηFree x) (T₁ f))
          (T₂-isMonoidal (ηFree y ∘F f) (T₁ f ∘F ηFree x) (ηnat f))
          (mι²⁻ (ηFree x) (T₁ f)))
      M0 = (μFreeStr y ∘Str T₁Str (ηFree y)) ∘Str T₁Str f
      M1 = μFreeStr y ∘Str (T₁Str (ηFree y) ∘Str T₁Str f)
      M2 = μFreeStr y ∘Str (T₁Str (T₁ f) ∘Str T₁Str (ηFree x))
      M3 = (μFreeStr y ∘Str T₁Str (T₁ f)) ∘Str T₁Str (ηFree x)
      M4 = (T₁Str f ∘Str μFreeStr x) ∘Str T₁Str (ηFree x)
      M5 = T₁Str f ∘Str (μFreeStr x ∘Str T₁Str (ηFree x))
      M6 = T₁Str f ∘Str IdStr
      R1 = IdStr ∘Str T₁Str f
      A1 = Bicategory.α⁻ (CAT {ℓ} {ℓ}) (T₁ f) (T₁ (ηFree y)) (μFree y)
      A2 = hSeqCAT WH (idTrans (μFree y))
      A3 = Bicategory.α⁺ (CAT {ℓ} {ℓ})
        (T₁ (ηFree x)) (T₁ (T₁ f)) (μFree y)
      A4 = hSeqCAT (idTrans (T₁ (ηFree x))) (μnat f)
      A5 = Bicategory.α⁻ (CAT {ℓ} {ℓ}) (T₁ (ηFree x)) (μFree x) (T₁ f)
      A6 = hSeqCAT (uL x) (idTrans (T₁ f))
      B1 = hSeqCAT (idTrans (T₁ f)) (uL y)
      B2 = Bicategory.ρ⁺ (CAT {ℓ} {ℓ}) (T₁ f)
      B3 = Bicategory.λ⁻ (CAT {ℓ} {ℓ}) (T₁ f)

  -- The right unit law is strict on objects and morphisms, so unlike
  -- the other two it needs no induction: identity components suffice.
  uR : (C : Category ℓ ℓ)
    → NatTrans (μFree C ∘F ηFree (|FreeMonoidalOn| C))
               (Id {C = |FreeMonoidalOn| C})
  uR C = natTrans (λ _ → K .id) (λ f → K .⋆IdR _ ∙ sym (K .⋆IdL _))
    where K = |FreeMonoidalOn| C

  uR⁻ : (C : Category ℓ ℓ)
    → NatTrans (Id {C = |FreeMonoidalOn| C})
               (μFree C ∘F ηFree (|FreeMonoidalOn| C))
  uR⁻ C = natTrans (λ _ → K .id) (λ f → K .⋆IdR _ ∙ sym (K .⋆IdL _))
    where K = |FreeMonoidalOn| C

  unitRMod : Modification
    (seqLaxNatTrans (whiskerR FMLax FMUnit) FMMult) (lidLax FMLax)
  unitRMod .Modification.M-ob C = uR C
  unitRMod .Modification.M-hom {x} {y} f =
    makeNatTransPath (funExt λ u →
        collapse K
          (collapse K refl
            (collapse K (K .⋆IdL _)
              (collapse K refl (collapse K (K .⋆IdL _) refl))))
          (K .⋆IdL _)
      ∙ sym (four K))
    where K = |FreeMonoidalOn| y

  private
    uR-isIso : (C : Category ℓ ℓ)
      → isIso (FUNCTOR (|FreeMonoidalOn| C) (|FreeMonoidalOn| C)) (uR C)
    uR-isIso C .inv = uR⁻ C
    uR-isIso C .sec =
      makeNatTransPath (funExt λ u → (|FreeMonoidalOn| C) .⋆IdL _)
    uR-isIso C .ret =
      makeNatTransPath (funExt λ u → (|FreeMonoidalOn| C) .⋆IdL _)

  -- The associativity law.
  aM : (C : Category ℓ ℓ)
    → NatTrans (μFree C ∘F μFree (|FreeMonoidalOn| C))
               ((μFree C ∘F T₁ (μFree C)) ∘F Id)
  aM C = rec₂ (|FreeMonoidalOn| (|FreeMonoidalOn| C)) (FreeMonoidalOn C)
    (μFreeStr C ∘Str μFreeStr (|FreeMonoidalOn| C))
    ((μFreeStr C ∘Str T₁Str (μFree C)) ∘Str IdStr)
    (natTrans (λ _ → K .id) (λ f → K .⋆IdR _ ∙ sym (K .⋆IdL _)))
    where K = |FreeMonoidalOn| C

  aM⁻ : (C : Category ℓ ℓ)
    → NatTrans ((μFree C ∘F T₁ (μFree C)) ∘F Id)
               (μFree C ∘F μFree (|FreeMonoidalOn| C))
  aM⁻ C = rec₂ (|FreeMonoidalOn| (|FreeMonoidalOn| C)) (FreeMonoidalOn C)
    ((μFreeStr C ∘Str T₁Str (μFree C)) ∘Str IdStr)
    (μFreeStr C ∘Str μFreeStr (|FreeMonoidalOn| C))
    (natTrans (λ _ → K .id) (λ f → K .⋆IdR _ ∙ sym (K .⋆IdL _)))
    where K = |FreeMonoidalOn| C

  private
    maM : (C : Category ℓ ℓ)
      → isMonoidalNat (μFreeStr C ∘Str μFreeStr (|FreeMonoidalOn| C))
          ((μFreeStr C ∘Str T₁Str (μFree C)) ∘Str IdStr) (aM C)
    maM C = rec₂-isMonoidal (|FreeMonoidalOn| (|FreeMonoidalOn| C))
      (FreeMonoidalOn C)
      (μFreeStr C ∘Str μFreeStr (|FreeMonoidalOn| C))
      ((μFreeStr C ∘Str T₁Str (μFree C)) ∘Str IdStr) _

    maM⁻ : (C : Category ℓ ℓ)
      → isMonoidalNat ((μFreeStr C ∘Str T₁Str (μFree C)) ∘Str IdStr)
          (μFreeStr C ∘Str μFreeStr (|FreeMonoidalOn| C)) (aM⁻ C)
    maM⁻ C = rec₂-isMonoidal (|FreeMonoidalOn| (|FreeMonoidalOn| C))
      (FreeMonoidalOn C)
      ((μFreeStr C ∘Str T₁Str (μFree C)) ∘Str IdStr)
      (μFreeStr C ∘Str μFreeStr (|FreeMonoidalOn| C)) _

    aM-isIso : (C : Category ℓ ℓ)
      → isIso (FUNCTOR (|FreeMonoidalOn| (|FreeMonoidalOn|
                (|FreeMonoidalOn| C))) (|FreeMonoidalOn| C)) (aM C)
    aM-isIso C .inv = aM⁻ C
    aM-isIso C .sec = uniq₂ (|FreeMonoidalOn| (|FreeMonoidalOn| C))
      (FreeMonoidalOn C)
      ((μFreeStr C ∘Str T₁Str (μFree C)) ∘Str IdStr)
      ((μFreeStr C ∘Str T₁Str (μFree C)) ∘Str IdStr)
      (isMonoidalNat-seq
        ((μFreeStr C ∘Str T₁Str (μFree C)) ∘Str IdStr)
        (μFreeStr C ∘Str μFreeStr (|FreeMonoidalOn| C))
        ((μFreeStr C ∘Str T₁Str (μFree C)) ∘Str IdStr)
        (aM⁻ C) (aM C) (maM⁻ C) (maM C))
      (isMonoidalNat-id ((μFreeStr C ∘Str T₁Str (μFree C)) ∘Str IdStr))
      (λ c → (|FreeMonoidalOn| C) .⋆IdL _)
    aM-isIso C .ret = uniq₂ (|FreeMonoidalOn| (|FreeMonoidalOn| C))
      (FreeMonoidalOn C)
      (μFreeStr C ∘Str μFreeStr (|FreeMonoidalOn| C))
      (μFreeStr C ∘Str μFreeStr (|FreeMonoidalOn| C))
      (isMonoidalNat-seq
        (μFreeStr C ∘Str μFreeStr (|FreeMonoidalOn| C))
        ((μFreeStr C ∘Str T₁Str (μFree C)) ∘Str IdStr)
        (μFreeStr C ∘Str μFreeStr (|FreeMonoidalOn| C))
        (aM C) (aM⁻ C) (maM C) (maM⁻ C))
      (isMonoidalNat-id
        (μFreeStr C ∘Str μFreeStr (|FreeMonoidalOn| C)))
      (λ c → (|FreeMonoidalOn| C) .⋆IdL _)

  assocMod' : Modification
    (seqLaxNatTrans (whiskerR FMLax FMMult) FMMult)
    (seqLaxNatTrans (assocLax FMLax FMLax FMLax)
      (seqLaxNatTrans (whiskerL FMPs FMMult) FMMult))
  assocMod' .Modification.M-ob C = aM C
  assocMod' .Modification.M-hom {x} {y} f =
    uniq₂ (|FreeMonoidalOn| (|FreeMonoidalOn| x)) (FreeMonoidalOn y)
      P0 P6 mlhs mrhs pgen
    where
      K = |FreeMonoidalOn| y
      TX = |FreeMonoidalOn| x
      TY = |FreeMonoidalOn| y
      TTTf = T₁ (T₁ (T₁ f))
      TTf = T₁Str (T₁ (T₁ f))
      TTf1 = T₁Str (T₁ f)
      Tf = T₁Str f
      μy = μFreeStr y
      μx = μFreeStr x
      μTy = μFreeStr (|FreeMonoidalOn| y)
      μTx = μFreeStr (|FreeMonoidalOn| x)
      Tμy = T₁Str (μFree y)
      Tμx = T₁Str (μFree x)
      P0 = (μy ∘Str μTy) ∘Str TTf
      P1 = μy ∘Str (μTy ∘Str TTf)
      P2 = μy ∘Str (TTf1 ∘Str μTx)
      P3 = (μy ∘Str TTf1) ∘Str μTx
      P4 = (Tf ∘Str μx) ∘Str μTx
      P5 = Tf ∘Str (μx ∘Str μTx)
      P6 = Tf ∘Str ((μx ∘Str Tμx) ∘Str IdStr)
      Q1 = ((μy ∘Str Tμy) ∘Str IdStr) ∘Str TTf
      Q2 = (μy ∘Str Tμy) ∘Str (IdStr ∘Str TTf)
      Q3 = (μy ∘Str Tμy) ∘Str (TTf ∘Str IdStr)
      Q4 = ((μy ∘Str Tμy) ∘Str TTf) ∘Str IdStr
      Q5 = (Tf ∘Str (μx ∘Str Tμx)) ∘Str IdStr
      R0 = (μy ∘Str Tμy) ∘Str TTf
      R1 = μy ∘Str (Tμy ∘Str TTf)
      R2 = μy ∘Str (TTf1 ∘Str Tμx)
      R3 = (μy ∘Str TTf1) ∘Str Tμx
      R4 = (Tf ∘Str μx) ∘Str Tμx
      R5 = Tf ∘Str (μx ∘Str Tμx)
      a1 = Bicategory.α⁻ (CAT {ℓ} {ℓ}) TTTf (μFree TY) (μFree y)
      a2 = hSeqCAT (μnat (T₁ f)) (idTrans (μFree y))
      a3 = Bicategory.α⁺ (CAT {ℓ} {ℓ}) (μFree TX) (T₁ (T₁ f)) (μFree y)
      a4 = hSeqCAT (idTrans (μFree TX)) (μnat f)
      a5 = Bicategory.α⁻ (CAT {ℓ} {ℓ}) (μFree TX) (μFree x) (T₁ f)
      a6 = hSeqCAT (aM x) (idTrans (T₁ f))
      AH = seqTrans (Bicategory.ρ⁺ (CAT {ℓ} {ℓ}) TTTf)
                    (Bicategory.λ⁻ (CAT {ℓ} {ℓ}) TTTf)
      mAH = isMonoidalNat-seq (IdStr ∘Str TTf) TTf (TTf ∘Str IdStr)
        (Bicategory.ρ⁺ (CAT {ℓ} {ℓ}) TTTf)
        (Bicategory.λ⁻ (CAT {ℓ} {ℓ}) TTTf) (mρ⁺ TTf) (mλ⁻ TTf)
      TH = seqTrans (ι² (T₁ (T₁ f)) (μFree y))
        (seqTrans (T₂ (μFree y ∘F T₁ (T₁ f)) (T₁ f ∘F μFree x) (μnat f))
          (ι²⁻ (μFree x) (T₁ f)))
      mTH = isMonoidalNat-seq (Tμy ∘Str TTf)
        (T₁Str (μFree y ∘F T₁ (T₁ f))) (TTf1 ∘Str Tμx)
        (ι² (T₁ (T₁ f)) (μFree y))
        (seqTrans (T₂ (μFree y ∘F T₁ (T₁ f)) (T₁ f ∘F μFree x) (μnat f))
          (ι²⁻ (μFree x) (T₁ f)))
        (mι² (T₁ (T₁ f)) (μFree y))
        (isMonoidalNat-seq (T₁Str (μFree y ∘F T₁ (T₁ f)))
          (T₁Str (T₁ f ∘F μFree x)) (TTf1 ∘Str Tμx)
          (T₂ (μFree y ∘F T₁ (T₁ f)) (T₁ f ∘F μFree x) (μnat f))
          (ι²⁻ (μFree x) (T₁ f))
          (T₂-isMonoidal (μFree y ∘F T₁ (T₁ f)) (T₁ f ∘F μFree x)
            (μnat f))
          (mι²⁻ (μFree x) (T₁ f)))
      s1 = Bicategory.α⁻ (CAT {ℓ} {ℓ}) TTTf (T₁ (μFree y)) (μFree y)
      s2 = hSeqCAT TH (idTrans (μFree y))
      s3 = Bicategory.α⁺ (CAT {ℓ} {ℓ})
        (T₁ (μFree x)) (T₁ (T₁ f)) (μFree y)
      s4 = hSeqCAT (idTrans (T₁ (μFree x))) (μnat f)
      s5 = Bicategory.α⁻ (CAT {ℓ} {ℓ}) (T₁ (μFree x)) (μFree x) (T₁ f)
      SH = seqTrans s1 (seqTrans s2 (seqTrans s3 (seqTrans s4 s5)))
      mSH = isMonoidalNat-seq R0 R1 R5 s1
        (seqTrans s2 (seqTrans s3 (seqTrans s4 s5))) (mα⁻ TTf Tμy μy)
        (isMonoidalNat-seq R1 R2 R5 s2 (seqTrans s3 (seqTrans s4 s5))
          (isMonoidalNat-seq R1 R2 R2
            (μFree y ∘ʳ TH)
            (idTrans (μFree y) ∘ˡ (T₁ (T₁ f) ∘F T₁ (μFree x)))
            (isMonoidalNat-∘ʳ μy (Tμy ∘Str TTf) (TTf1 ∘Str Tμx) TH mTH)
            (isMonoidalNat-∘ˡ (TTf1 ∘Str Tμx) μy μy
              (idTrans (μFree y)) (isMonoidalNat-id μy)))
          (isMonoidalNat-seq R2 R3 R5 s3 (seqTrans s4 s5)
            (mα⁺ Tμx TTf1 μy)
            (isMonoidalNat-seq R3 R4 R5 s4 s5
              (isMonoidalNat-seq R3 R3 R4
                ((μFree y ∘F T₁ (T₁ f)) ∘ʳ idTrans (T₁ (μFree x)))
                (μnat f ∘ˡ T₁ (μFree x))
                (isMonoidalNat-∘ʳ (μy ∘Str TTf1) Tμx Tμx
                  (idTrans (T₁ (μFree x))) (isMonoidalNat-id Tμx))
                (isMonoidalNat-∘ˡ Tμx (μy ∘Str TTf1) (Tf ∘Str μx)
                  (μnat f) (mμnat f)))
              (mα⁻ Tμx μx Tf))))
      b1 = hSeqCAT (idTrans TTTf) (aM y)
      b2 = Bicategory.α⁻ (CAT {ℓ} {ℓ}) TTTf Id
        (μFree y ∘F T₁ (μFree y))
      b3 = hSeqCAT AH (idTrans (μFree y ∘F T₁ (μFree y)))
      b4 = Bicategory.α⁺ (CAT {ℓ} {ℓ}) Id TTTf
        (μFree y ∘F T₁ (μFree y))
      b5 = hSeqCAT (idTrans Id) SH
      b6 = Bicategory.α⁻ (CAT {ℓ} {ℓ}) Id
        (μFree x ∘F T₁ (μFree x)) (T₁ f)

      lhs : NatTrans (P0 .F) (P6 .F)
      lhs =
        seqTrans (seqTrans a1 (seqTrans a2 (seqTrans a3
          (seqTrans a4 a5)))) a6

      rhs : NatTrans (P0 .F) (P6 .F)
      rhs =
        seqTrans b1 (seqTrans b2 (seqTrans b3 (seqTrans b4
          (seqTrans b5 b6))))

      mlhs : isMonoidalNat P0 P6 lhs
      mlhs =
        isMonoidalNat-seq P0 P5 P6
          (seqTrans a1 (seqTrans a2 (seqTrans a3 (seqTrans a4 a5)))) a6
          (isMonoidalNat-seq P0 P1 P5 a1
            (seqTrans a2 (seqTrans a3 (seqTrans a4 a5)))
            (mα⁻ TTf μTy μy)
            (isMonoidalNat-seq P1 P2 P5 a2
              (seqTrans a3 (seqTrans a4 a5))
              (isMonoidalNat-seq P1 P2 P2
                (μFree y ∘ʳ μnat (T₁ f))
                (idTrans (μFree y) ∘ˡ (T₁ (T₁ f) ∘F μFree TX))
                (isMonoidalNat-∘ʳ μy (μTy ∘Str TTf) (TTf1 ∘Str μTx)
                  (μnat (T₁ f)) (mμnat (T₁ f)))
                (isMonoidalNat-∘ˡ (TTf1 ∘Str μTx) μy μy
                  (idTrans (μFree y)) (isMonoidalNat-id μy)))
              (isMonoidalNat-seq P2 P3 P5 a3 (seqTrans a4 a5)
                (mα⁺ μTx TTf1 μy)
                (isMonoidalNat-seq P3 P4 P5 a4 a5
                  (isMonoidalNat-seq P3 P3 P4
                    ((μFree y ∘F T₁ (T₁ f)) ∘ʳ idTrans (μFree TX))
                    (μnat f ∘ˡ μFree TX)
                    (isMonoidalNat-∘ʳ (μy ∘Str TTf1) μTx μTx
                      (idTrans (μFree TX)) (isMonoidalNat-id μTx))
                    (isMonoidalNat-∘ˡ μTx (μy ∘Str TTf1) (Tf ∘Str μx)
                      (μnat f) (mμnat f)))
                  (mα⁻ μTx μx Tf)))))
          (isMonoidalNat-seq P5 P6 P6
            (T₁ f ∘ʳ aM x)
            (idTrans (T₁ f) ∘ˡ ((μFree x ∘F T₁ (μFree x)) ∘F Id))
            (isMonoidalNat-∘ʳ Tf (μx ∘Str μTx)
              ((μx ∘Str Tμx) ∘Str IdStr) (aM x) (maM x))
            (isMonoidalNat-∘ˡ ((μx ∘Str Tμx) ∘Str IdStr) Tf Tf
              (idTrans (T₁ f)) (isMonoidalNat-id Tf)))

      mrhs : isMonoidalNat P0 P6 rhs
      mrhs =
        isMonoidalNat-seq P0 Q1 P6 b1
          (seqTrans b2 (seqTrans b3 (seqTrans b4 (seqTrans b5 b6))))
          (isMonoidalNat-seq P0 P0 Q1
            ((μFree y ∘F μFree TY) ∘ʳ idTrans TTTf) (aM y ∘ˡ TTTf)
            (isMonoidalNat-∘ʳ (μy ∘Str μTy) TTf TTf (idTrans TTTf)
              (isMonoidalNat-id TTf))
            (isMonoidalNat-∘ˡ TTf (μy ∘Str μTy)
              ((μy ∘Str Tμy) ∘Str IdStr) (aM y) (maM y)))
          (isMonoidalNat-seq Q1 Q2 P6 b2
            (seqTrans b3 (seqTrans b4 (seqTrans b5 b6)))
            (mα⁻ TTf IdStr (μy ∘Str Tμy))
            (isMonoidalNat-seq Q2 Q3 P6 b3
              (seqTrans b4 (seqTrans b5 b6))
              (isMonoidalNat-seq Q2 Q3 Q3
                ((μFree y ∘F T₁ (μFree y)) ∘ʳ AH)
                (idTrans (μFree y ∘F T₁ (μFree y)) ∘ˡ (TTTf ∘F Id))
                (isMonoidalNat-∘ʳ (μy ∘Str Tμy) (IdStr ∘Str TTf)
                  (TTf ∘Str IdStr) AH mAH)
                (isMonoidalNat-∘ˡ (TTf ∘Str IdStr) (μy ∘Str Tμy)
                  (μy ∘Str Tμy) (idTrans (μFree y ∘F T₁ (μFree y)))
                  (isMonoidalNat-id (μy ∘Str Tμy))))
              (isMonoidalNat-seq Q3 Q4 P6 b4 (seqTrans b5 b6)
                (mα⁺ IdStr TTf (μy ∘Str Tμy))
                (isMonoidalNat-seq Q4 Q5 P6 b5 b6
                  (isMonoidalNat-seq Q4 Q4 Q5
                    (((μFree y ∘F T₁ (μFree y)) ∘F TTTf) ∘ʳ idTrans Id)
                    (SH ∘ˡ Id)
                    (isMonoidalNat-∘ʳ ((μy ∘Str Tμy) ∘Str TTf) IdStr
                      IdStr (idTrans Id) (isMonoidalNat-id IdStr))
                    (isMonoidalNat-∘ˡ IdStr ((μy ∘Str Tμy) ∘Str TTf)
                      (Tf ∘Str (μx ∘Str Tμx)) SH mSH))
                  (mα⁻ IdStr (μx ∘Str Tμx) Tf)))))

      pgen : (w : (|FreeMonoidalOn| TX) .ob)
        → lhs .N-ob (↑ w) ≡ rhs .N-ob (↑ w)
      pgen w =
        let ps2 = K .⋆IdR _ ∙ K .⋆IdL _ ∙ K .⋆IdR _
            pF = collapse K refl (collapse K (K .⋆IdL _) refl)
            pSH = K .⋆IdL _ ∙ cong₂ (seq' K) ps2 pF ∙ K .⋆IdR _
            pA = K .⋆IdL _ ∙ collapseL K (K .⋆IdL _)
               ∙ K .⋆IdL _ ∙ K .⋆IdR _ ∙ K .⋆IdL _
        in  cong₂ (seq' K) pA (K .⋆IdL _) ∙ K .⋆IdR _
          ∙ sym (collapseL K (K .⋆IdL _) ∙ K .⋆IdL _
                ∙ collapseL K (collapse K (K .⋆IdL _) refl)
                ∙ K .⋆IdL _ ∙ K .⋆IdR _ ∙ K .⋆IdL _ ∙ pSH)

  FreeMonoidalTwoMonad : TwoMonad (CAT {ℓ} {ℓ})
  FreeMonoidalTwoMonad .TwoMonad.T = FMPs
  FreeMonoidalTwoMonad .TwoMonad.η = FMUnit
  FreeMonoidalTwoMonad .TwoMonad.μ = FMMult
  FreeMonoidalTwoMonad .TwoMonad.unitL =
    unitLMod , modIsIso unitLMod uL-isIso
  FreeMonoidalTwoMonad .TwoMonad.unitR =
    unitRMod , modIsIso unitRMod uR-isIso
  FreeMonoidalTwoMonad .TwoMonad.assoc =
    assocMod' , modIsIso assocMod' aM-isIso

module _ {ℓ : Level} (M : MonoidalCategory ℓ ℓ) where
  private
    module M = MonoidalCategory M
    actStr : StrongMonoidalFunctor (FreeMonoidalOn (M .MonoidalCategory.C)) M
    actStr = rec (M .MonoidalCategory.C) M Id
    A = M .MonoidalCategory.C
    ev = actStr .F
    G = actStr ∘Str T₁Str ev
    H = actStr ∘Str μFreeStr A

  -- The multiplication law: `ev ∘F T₁ ev` and `act ∘F μFree` agree
  -- on ↑, so they are compared by `rec₂` of the identity.
  actMultCell : NatTrans (ev ∘F T₁ ev) (ev ∘F μFree A)
  actMultCell = rec₂ (|FreeMonoidalOn| A) M G H
    (natTrans (λ _ → A .id) (λ f → A .⋆IdR _ ∙ sym (A .⋆IdL _)))

  actMultCell⁻ : NatTrans (ev ∘F μFree A) (ev ∘F T₁ ev)
  actMultCell⁻ = rec₂ (|FreeMonoidalOn| A) M H G
    (natTrans (λ _ → A .id) (λ f → A .⋆IdR _ ∙ sym (A .⋆IdL _)))

  private
    mMult : isMonoidalNat G H actMultCell
    mMult = rec₂-isMonoidal (|FreeMonoidalOn| A) M G H _

    mMult⁻ : isMonoidalNat H G actMultCell⁻
    mMult⁻ = rec₂-isMonoidal (|FreeMonoidalOn| A) M H G _

  actMultIsIso : isIso (FUNCTOR (|FreeMonoidalOn| (|FreeMonoidalOn| A)) A)
    actMultCell
  actMultIsIso .inv = actMultCell⁻
  actMultIsIso .sec = uniq₂ (|FreeMonoidalOn| A) M H H
    (isMonoidalNat-seq H G H actMultCell⁻ actMultCell mMult⁻ mMult)
    (isMonoidalNat-id H)
    (λ c → A .⋆IdL _)
  actMultIsIso .ret = uniq₂ (|FreeMonoidalOn| A) M G G
    (isMonoidalNat-seq G H G actMultCell actMultCell⁻ mMult mMult⁻)
    (isMonoidalNat-id G)
    (λ c → A .⋆IdL _)

  -- `act ∘F ηFree ≡ Id` holds on the nose, so the unit law is a path.
  monoidalPseudoAlgebra : PseudoAlgebra (FreeMonoidalTwoMonad {ℓ})
  monoidalPseudoAlgebra .carrier = A
  monoidalPseudoAlgebra .act = ev
  monoidalPseudoAlgebra .actUnit =
    pathToIso {C = FUNCTOR A A} (rec-β A M Id) .fst
  monoidalPseudoAlgebra .actUnitIso =
    pathToIso {C = FUNCTOR A A} (rec-β A M Id) .snd
  monoidalPseudoAlgebra .actMult = actMultCell
  monoidalPseudoAlgebra .actMultIso = actMultIsIso

{-
  The converse.  The tensor and unit of the monoidal structure on a
  pseudoalgebra come straight from the free structure, with no use of
  `actUnit`/`actMult`.  The associator and unitors do need them: e.g.
  `(x ⊗ y) ⊗ z` is `ev (↑ (ev (↑ x ⊗ ↑ y)) ⊗ ↑ z)`, which `actMult`
  relates to `ev ((↑ x ⊗ ↑ y) ⊗ ↑ z)`, and only there does the free
  associator become available.  That half is not done here.
-}
module _ {ℓ : Level} (P : PseudoAlgebra (FreeMonoidalTwoMonad {ℓ})) where
  private
    C = P .carrier
    ev = P .act

  algebraTensor : Functor (C ×C C) C
  algebraTensor .F-ob (x , y) = ev ⟅ ↑ x ⊗ ↑ y ⟆
  algebraTensor .F-hom (f , g) = ev ⟪ ↑ₘ f ⊗ ↑ₘ g ⟫
  algebraTensor .F-id {x = x , y} =
      cong (ev .F-hom)
        ((λ i → ↑ₘId {x = x} i ⊗ ↑ₘId {x = y} i) ∙ ⊗id)
    ∙ ev .F-id
  algebraTensor .F-seq (f , g) (f' , g') =
      cong (ev .F-hom)
        ((λ i → ↑ₘSeq f f' i ⊗ ↑ₘSeq g g' i) ∙ ⊗⋆ _ _ _ _)
    ∙ ev .F-seq _ _

  algebraTensorStr : TensorStr C
  algebraTensorStr .TensorStr.─⊗─ = algebraTensor
  algebraTensorStr .TensorStr.unit = ev ⟅ unit ⟆

  -- REIVEW
  -- Build the rest of the monoidal structure by showing coherences
