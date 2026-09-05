{-# OPTIONS --lossy-unification #-}
{- The inserter prestack of `f g : B.1Cell a b`: a probe `x` is sent to
   the category of pairs `(h : x → a , θ : h ⋆₁ f ⇒ h ⋆₁ g)`. -}
module Cubical.Categories.Bicategory.Prestack.Inserter where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More hiding (α)
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.BinProduct

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Constructions.Op
open import Cubical.Categories.Bicategory.Instances.CAT
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo
open import Cubical.Categories.Bicategory.Prestack.Base
open import Cubical.Categories.Bicategory.Prestack.Hom
open import Cubical.Categories.Bicategory.Transformation.Composition

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

module InserterPre {B : Bicategory ℓ ℓ' ℓ''} {a b : Bicategory.0Cell B}
  (f g : Bicategory.1Cell B a b) where
  private
    module B = Bicategory B

  Ins2 : {x : B.0Cell} → B.1Cell x a → Type ℓ''
  Ins2 h = B.2Cell (h B.⋆₁ f) (h B.⋆₁ g)

  InsCond : {x : B.0Cell} {h h' : B.1Cell x a}
    → Ins2 h → Ins2 h' → B.2Cell h h' → Type ℓ''
  InsCond θ θ' α = (α B.▷w f) B.⋆₂ θ' ≡ θ B.⋆₂ (α B.▷w g)

  isPropInsCond : {x : B.0Cell} {h h' : B.1Cell x a}
    (θ : Ins2 h) (θ' : Ins2 h') (α : B.2Cell h h') → isProp (InsCond θ θ' α)
  isPropInsCond {x} θ θ' α = B.Hom[ x , b ] .isSetHom _ _

  InsOb : B.0Cell → Type (ℓ-max ℓ' ℓ'')
  InsOb x = Σ[ h ∈ B.1Cell x a ] Ins2 h

  InsHom : {x : B.0Cell} → InsOb x → InsOb x → Type ℓ''
  InsHom (h , θ) (h' , θ') = Σ[ α ∈ B.2Cell h h' ] InsCond θ θ' α

  InsHom≡ : {x : B.0Cell} {e e' : InsOb x} {u v : InsHom e e'}
    → u .fst ≡ v .fst → u ≡ v
  InsHom≡ {e = _ , θ} {_ , θ'} = Σ≡Prop (isPropInsCond θ θ')

  insId : {x : B.0Cell} {h : B.1Cell x a} (θ : Ins2 h) → InsCond θ θ B.id₂
  insId {x} {h} θ =
      B.⟨ B.▷wId f ⟩⋆₂⟨⟩ ∙ B.⋆₂IdL θ
    ∙ sym (B.⋆₂IdR θ) ∙ B.⟨⟩⋆₂⟨ sym (B.▷wId g) ⟩

  insSeq : {x : B.0Cell} {h h' h'' : B.1Cell x a}
    {θ : Ins2 h} {θ' : Ins2 h'} {θ'' : Ins2 h''}
    {α : B.2Cell h h'} {β : B.2Cell h' h''}
    → InsCond θ θ' α → InsCond θ' θ'' β → InsCond θ θ'' (α B.⋆₂ β)
  insSeq {α = α} {β} p q =
      B.⟨ ▷wSeq B α β f ⟩⋆₂⟨⟩
    ∙ B.⋆₂Assoc _ _ _
    ∙ B.⟨⟩⋆₂⟨ q ⟩
    ∙ sym (B.⋆₂Assoc _ _ _)
    ∙ B.⟨ p ⟩⋆₂⟨⟩
    ∙ B.⋆₂Assoc _ _ _
    ∙ B.⟨⟩⋆₂⟨ sym (▷wSeq B α β g) ⟩

  InsCat : B.0Cell → Category (ℓ-max ℓ' ℓ'') ℓ''
  InsCat x .ob = InsOb x
  InsCat x .Hom[_,_] = InsHom
  InsCat x .id {h , θ} = B.id₂ , insId θ
  InsCat x ._⋆_ (α , p) (β , q) = α B.⋆₂ β , insSeq p q
  InsCat x .⋆IdL _ = InsHom≡ (B.⋆₂IdL _)
  InsCat x .⋆IdR _ = InsHom≡ (B.⋆₂IdR _)
  InsCat x .⋆Assoc _ _ _ = InsHom≡ (B.⋆₂Assoc _ _ _)
  InsCat x .isSetHom {_ , θ} {_ , θ'} =
    isSetΣ (B.Hom[ x , a ] .isSetHom)
           (λ α → isProp→isSet (isPropInsCond θ θ' α))

  -- Interchange, in the form used to move a whiskered 2-cell past
  -- another.  (`Transformation/Composition` has this only privately.)
  ▷◁exch : {x y z : B.0Cell} {k k' : B.1Cell x y} (σ : B.2Cell k k')
    {m n : B.1Cell y z} (θ : B.2Cell m n)
    → (σ B.▷w m) B.⋆₂ (k' B.◁w θ) ≡ (k B.◁w θ) B.⋆₂ (σ B.▷w n)
  ▷◁exch σ θ =
      sym (B.⋆ₕSeq σ B.id₂ B.id₂ θ)
    ∙ B.⟨ B.⋆₂IdR σ ⟩⋆ₕ⟨ B.⋆₂IdL θ ⟩
    ∙ B.⟨ sym (B.⋆₂IdL σ) ⟩⋆ₕ⟨ sym (B.⋆₂IdR θ) ⟩
    ∙ B.⋆ₕSeq B.id₂ σ θ B.id₂

  reindθ : {x y : B.0Cell} (k : B.1Cell y x) {h : B.1Cell x a}
    → Ins2 h → Ins2 (k B.⋆₁ h)
  reindθ k {h} θ = B.α⁺ k h f B.⋆₂ (k B.◁w θ) B.⋆₂ B.α⁻ k h g

  reindCond : {x y : B.0Cell} (k : B.1Cell y x) {h h' : B.1Cell x a}
    {θ : Ins2 h} {θ' : Ins2 h'} {α : B.2Cell h h'}
    → InsCond θ θ' α → InsCond (reindθ k θ) (reindθ k θ') (k B.◁w α)
  reindCond k {θ = θ} {θ'} {α} p =
      pushr B (α⁺natM B k α f) _
    ∙ B.⟨⟩⋆₂⟨ pushr B mid _ ⟩
    ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ α⁻natM B k α g ⟩ ⟩
    ∙ sym (aR3 B _ _ _ _)
    where
    mid : (k B.◁w (α B.▷w f)) B.⋆₂ (k B.◁w θ')
        ≡ (k B.◁w θ) B.⋆₂ (k B.◁w (α B.▷w g))
    mid = sym (◁wSeq B k _ _) ∙ k B.◁⟨ p ⟩ ∙ ◁wSeq B k _ _

  insReind : {x y : B.0Cell} (k : B.1Cell y x)
    → Functor (InsCat x) (InsCat y)
  insReind k .F-ob (h , θ) = k B.⋆₁ h , reindθ k θ
  insReind k .F-hom (α , p) = k B.◁w α , reindCond k p
  insReind k .F-id = InsHom≡ (B.◁wId k)
  insReind k .F-seq _ _ = InsHom≡ (◁wSeq B k _ _)

  insReind₂ : {x y : B.0Cell} {k k' : B.1Cell y x} (σ : B.2Cell k k')
    → NatTrans (insReind k) (insReind k')
  insReind₂ {k = k} {k'} σ .N-ob (h , θ) = σ B.▷w h , cond
    where
    cond : InsCond (reindθ k θ) (reindθ k' θ) (σ B.▷w h)
    cond =
        pushr B (α⁺natL B σ h f) _
      ∙ B.⟨⟩⋆₂⟨ pushr B (▷◁exch σ θ) _ ⟩
      ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ α⁻natL B σ h g ⟩ ⟩
      ∙ sym (aR3 B _ _ _ _)
  insReind₂ σ .N-hom (α , _) = InsHom≡ (sym (▷◁exch σ α))

  insCondInv : {x : B.0Cell} {h h' : B.1Cell x a}
    {θ : Ins2 h} {θ' : Ins2 h'} {α : B.2Cell h h'}
    (isI : isIso B.Hom[ x , a ] α)
    → InsCond θ θ' α → InsCond θ' θ (isI .inv)
  insCondInv isI p =
    sym (⋆InvsFlipSq (_ , ▷wIsIso B f isI) (_ , ▷wIsIso B g isI) p)

  ιCond : {x : B.0Cell} {h : B.1Cell x a} (θ : Ins2 h)
    → InsCond θ (reindθ B.id₁ θ) (B.λ⁻ h)
  ιCond {x} {h} θ =
      pushn B (λ⁻⋆₁ B h f) _
    ∙ pushr B (sym (λ⁻-nat B θ)) _
    ∙ B.⟨⟩⋆₂⟨ B.⟨ sym (λ⁻⋆₁ B h g) ⟩⋆₂⟨⟩
            ∙ B.⋆₂Assoc _ _ _
            ∙ B.⟨⟩⋆₂⟨ αI B B.id₁ h g .snd .ret ⟩
            ∙ B.⋆₂IdR _ ⟩

  ι⁻Cond : {x : B.0Cell} {h : B.1Cell x a} (θ : Ins2 h)
    → InsCond (reindθ B.id₁ θ) θ (B.λ⁺ h)
  ι⁻Cond {x} {h} θ =
    insCondInv (invIso (NatIsoAt (B.λU x a) (tt* , h)) .snd) (ιCond θ)

  νCond : {x y z : B.0Cell} (k : B.1Cell y x) (l : B.1Cell z y)
    {h : B.1Cell x a} (θ : Ins2 h)
    → InsCond (reindθ l (reindθ k θ)) (reindθ (l B.⋆₁ k) θ) (B.α⁻ l k h)
  νCond {x} {y} {z} k l {h} θ = lhs≡ ∙ sym rhs≡
    where
    D  = B.α⁻ l k h
    Pf = B.α⁺ (l B.⋆₁ k) h f
    Ag = B.α⁻ (l B.⋆₁ k) h g
    K  = (l B.⋆₁ k) B.◁w θ
    X  = l B.◁w (k B.◁w θ)
    P' = B.α⁺ l (k B.⋆₁ h) f
    Q' = l B.◁w B.α⁺ k h f
    Cg = B.α⁻ l k (h B.⋆₁ g)
    Ck = l B.◁w B.α⁻ k h g
    Eg = B.α⁻ l (k B.⋆₁ h) g

    N : B.2Cell ((l B.⋆₁ (k B.⋆₁ h)) B.⋆₁ f) (((l B.⋆₁ k) B.⋆₁ h) B.⋆₁ g)
    N = P' B.⋆₂ Q' B.⋆₂ X B.⋆₂ Cg B.⋆₂ Ag

    lhs≡ : (D B.▷w f) B.⋆₂ reindθ (l B.⋆₁ k) θ ≡ N
    lhs≡ =
        pushr B (sym (pentP4 B l k h f)) _
      ∙ B.⟨⟩⋆₂⟨ aR2 B Q' _ (K B.⋆₂ Ag) ⟩
      ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ pushr B (sym (α⁻natR B l k θ)) Ag ⟩ ⟩

    rhs≡ : reindθ l (reindθ k θ) B.⋆₂ (D B.▷w g) ≡ N
    rhs≡ =
        B.⟨ B.⟨⟩⋆₂⟨ B.⟨ ◁3 B l _ _ _ ⟩⋆₂⟨⟩ ⟩ ⟩⋆₂⟨⟩
      ∙ B.⟨ B.⟨⟩⋆₂⟨ aR3 B Q' X Ck Eg ⟩ ⟩⋆₂⟨⟩
      ∙ aR4 B P' Q' X (Ck B.⋆₂ Eg) (D B.▷w g)
      ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨
          aR2 B Ck Eg (D B.▷w g) ∙ pentP2 B l k h g ⟩ ⟩ ⟩

  ν⁻Cond : {x y z : B.0Cell} (k : B.1Cell y x) (l : B.1Cell z y)
    {h : B.1Cell x a} (θ : Ins2 h)
    → InsCond (reindθ (l B.⋆₁ k) θ) (reindθ l (reindθ k θ)) (B.α⁺ l k h)
  ν⁻Cond k l {h} θ = insCondInv (invIso (αI B l k h) .snd) (νCond k l θ)

  private
    module HA = Pseudofunctor (Hom B a)

    InsPrecomp : {x y : B.0Cell}
      → Functor B.Hom[ y , x ] (FUNCTOR (InsCat x) (InsCat y))
    InsPrecomp .F-ob k = insReind k
    InsPrecomp .F-hom σ = insReind₂ σ
    InsPrecomp .F-id =
      makeNatTransPath (funExt λ e → InsHom≡ (B.▷wId (e .fst)))
    InsPrecomp .F-seq σ τ =
      makeNatTransPath (funExt λ e → InsHom≡ (▷wSeq B σ τ (e .fst)))

    ιNT : (x : B.0Cell) → NatTrans (Id {C = InsCat x}) (insReind B.id₁)
    ιNT x .N-ob (h , θ) = B.λ⁻ h , ιCond θ
    ιNT x .N-hom (α , _) = InsHom≡ (λ⁻-nat B α)

    ι⁻NT : (x : B.0Cell) → NatTrans (insReind B.id₁) (Id {C = InsCat x})
    ι⁻NT x .N-ob (h , θ) = B.λ⁺ h , ι⁻Cond θ
    ι⁻NT x .N-hom (α , _) = InsHom≡ (λ-nat B α)

    νNT : {x y z : B.0Cell} (k : B.1Cell y x) (l : B.1Cell z y)
      → NatTrans (seqCAT (InsCat x) (InsCat y) (InsCat z)
                    .F-ob (insReind k , insReind l))
                 (insReind (l B.⋆₁ k))
    νNT k l .N-ob (h , θ) = B.α⁻ l k h , νCond k l θ
    νNT k l .N-hom (α , _) = InsHom≡ (α⁻natR B l k α)

    ν⁻NT : {x y z : B.0Cell} (k : B.1Cell y x) (l : B.1Cell z y)
      → NatTrans (insReind (l B.⋆₁ k))
                 (seqCAT (InsCat x) (InsCat y) (InsCat z)
                    .F-ob (insReind k , insReind l))
    ν⁻NT k l .N-ob (h , θ) = B.α⁺ l k h , ν⁻Cond k l θ
    ν⁻NT k l .N-hom (α , _) = InsHom≡ (α⁺natR B l k α)

  InserterLax : LaxFunctor (B ^opᴮ) (CAT {ℓ-max ℓ' ℓ''} {ℓ''})
  InserterLax .F-ob = InsCat
  InserterLax .F-Hom {x} {y} = InsPrecomp {x} {y}
  InserterLax .F-id {x} .N-ob _ = ιNT x
  InserterLax .F-id {x} .N-hom σ = makeNatTransPath (funExt λ e →
    InsHom≡ (N-obPath (HA.F-id .N-hom σ) (e .fst)))
  InserterLax .F-seq .N-ob (k , l) = νNT k l
  InserterLax .F-seq .N-hom στ = makeNatTransPath (funExt λ e →
    InsHom≡ (N-obPath (HA.F-seq .N-hom στ) (e .fst)))
  InserterLax .lax-λ x y k = makeNatTransPath (funExt λ e →
    InsHom≡ (N-obPath (HA.lax-λ x y k) (e .fst)))
  InserterLax .lax-ρ x y k = makeNatTransPath (funExt λ e →
    InsHom≡ (N-obPath (HA.lax-ρ x y k) (e .fst)))
  InserterLax .lax-α x y z w k l m = makeNatTransPath (funExt λ e →
    InsHom≡ (N-obPath (HA.lax-α x y z w k l m) (e .fst)))

  Prestk : Prestack B (ℓ-max ℓ' ℓ'') ℓ''
  Prestk .laxFunctor = InserterLax
  Prestk .F-id-isIso {x} _ .inv = ι⁻NT x
  Prestk .F-id-isIso {x} _ .sec = makeNatTransPath (funExt λ e →
    InsHom≡ (B.λU x a .nIso (tt* , e .fst) .ret))
  Prestk .F-id-isIso {x} _ .ret = makeNatTransPath (funExt λ e →
    InsHom≡ (B.λU x a .nIso (tt* , e .fst) .sec))
  Prestk .F-seq-isIso (k , l) .inv = ν⁻NT k l
  Prestk .F-seq-isIso {x} {y} {z} (k , l) .sec =
    makeNatTransPath (funExt λ e →
      InsHom≡ (B.α z y x a .nIso (l , k , e .fst) .ret))
  Prestk .F-seq-isIso {x} {y} {z} (k , l) .ret =
    makeNatTransPath (funExt λ e →
      InsHom≡ (B.α z y x a .nIso (l , k , e .fst) .sec))

  -- The forgetful functor to `Hom B a`; faithful, so isos and
  -- equations upstairs are decided by their first components.
  insForget : (x : B.0Cell) → Functor (InsCat x) B.Hom[ x , a ]
  insForget x .F-ob = fst
  insForget x .F-hom = fst
  insForget x .F-id = refl
  insForget x .F-seq _ _ = refl

  insIso : {x : B.0Cell} {h h' : B.1Cell x a} {θ : Ins2 h} {θ' : Ins2 h'}
    (φ : B.2Cell h h') (isI : isIso B.Hom[ x , a ] φ)
    → InsCond θ θ' φ → CatIso (InsCat x) (h , θ) (h' , θ')
  insIso φ isI c .fst = φ , c
  insIso φ isI c .snd .inv = isI .inv , insCondInv isI c
  insIso φ isI c .snd .sec = InsHom≡ (isI .sec)
  insIso φ isI c .snd .ret = InsHom≡ (isI .ret)

module _ (B : Bicategory ℓ ℓ' ℓ'') {a b : Bicategory.0Cell B} where
  InserterPrestack : (f g : Bicategory.1Cell B a b)
    → Prestack B (ℓ-max ℓ' ℓ'') ℓ''
  InserterPrestack f g = InserterPre.Prestk {a = a} {b = b} f g
