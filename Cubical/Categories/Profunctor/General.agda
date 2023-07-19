{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Profunctor.General where

open import Cubical.Reflection.RecordEquiv

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Functor.More
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functors.More
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Instances.Functors.More

open import Cubical.Tactics.CategorySolver.Reflection

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS ℓR : Level

open Category
open Functor
open UniversalElement
open Bifunctor

-- Convenient notation for function composition in the same order as
-- ⋆⟨ C ⟩ in a category C
-- i.e. for ⋆⟨ SET _ ⟩ without having to prove that everything indeed lives
-- SET _.
_⋆f_ : {ℓ : Level} {A : Type ℓ } → {B : A → Type ℓ} →
       {C : (a : A) → B a → Type ℓ} →
       (f : (a : A) → B a) → (g : {a : A} → (b : B a) → C a b) →
       (a : A) → C a (f a)
f ⋆f g = λ x → (g ∘f f) x

_o-[_]-*_ : (C : Category ℓC ℓC') → ∀ ℓS → (D : Category ℓD ℓD') → Type _
C o-[ ℓS ]-* D = Bifunctor (C ^op) D (SET ℓS)

_*-[_]-o_ : (C : Category ℓC ℓC') → ∀ ℓS → (D : Category ℓD ℓD') → Type _
C *-[ ℓS ]-o D = D o-[ ℓS ]-* C

module _  {C : Category ℓC ℓC'}
          {D : Category ℓD ℓD'}
          (R : C o-[ ℓR ]-* D) (S : C o-[ ℓS ]-* D) where

  private
    ℓmaxCDSR : Level
    ℓmaxCDSR = (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓD (ℓ-max ℓD' (ℓ-max ℓS ℓR)))))

  -- A definition of profunctor homomorphism that avoids Lifts
  record ProfHomo : Type ℓmaxCDSR where
    field
      PH-ob : ∀ {c d} → (r : ⟨ R ⟅ c , d ⟆b ⟩) → ⟨ S ⟅ c , d ⟆b ⟩
      PH-natL : ∀ {c c' d} (f : C [ c , c' ]) (r : ⟨ R ⟅ c' , d ⟆b ⟩)
              → PH-ob ((R ⟪ f ⟫l) r) ≡ (S ⟪ f ⟫l) (PH-ob r)
      PH-natR : ∀ {c d d'} (r : ⟨ R ⟅ c , d ⟆b ⟩) (g : D [ d , d' ])
              → PH-ob ((R ⟪ g ⟫r) r) ≡ (S ⟪ g ⟫r) (PH-ob r)

  open ProfHomo

  -- A definition of profunctor homomorphism without implicit arguments
  -- so that it'll work with the reflection library
  record ProfHomo' : Type ℓmaxCDSR where
    field
      PH-ob : ∀ c d → (r : ⟨ R ⟅ c , d ⟆b ⟩) → ⟨ S ⟅ c , d ⟆b ⟩
      PH-natL : ∀ c c' d (f : C [ c , c' ]) (r : ⟨ R ⟅ c' , d ⟆b ⟩)
              → PH-ob c d ((R ⟪ f ⟫l) r) ≡ (S ⟪ f ⟫l) (PH-ob c' d r)
      PH-natR : ∀ c d d' (r : ⟨ R ⟅ c , d ⟆b ⟩) (g : D [ d , d' ])
              → PH-ob c d' ((R ⟪ g ⟫r) r) ≡ (S ⟪ g ⟫r) (PH-ob c d r)

  isProp-natL : (PH' : ProfHomo') →
              isProp (∀ c c' d (f : C [ c , c' ]) (r : ⟨ R ⟅ c' , d ⟆b ⟩)
              → ProfHomo'.PH-ob PH' c d ((R ⟪ f ⟫l) r) ≡
                (S ⟪ f ⟫l) (ProfHomo'.PH-ob PH' c' d r))
  isProp-natL PH' =
    isPropΠ5
    (λ x y z w v →
      str (S ⟅ x , z ⟆b)
        (ProfHomo'.PH-ob PH' x z ((R ⟪ w ⟫l) v))
        ((S ⟪ w ⟫l) (ProfHomo'.PH-ob PH' y z v))
    )

  isProp-natR : (PH' : ProfHomo') →
                isProp (∀ c d d' (r : ⟨ R ⟅ c , d ⟆b ⟩) (g : D [ d , d' ])
              → ProfHomo'.PH-ob PH' c d' ((R ⟪ g ⟫r) r) ≡
                (S ⟪ g ⟫r) (ProfHomo'.PH-ob PH' c d r))
  isProp-natR PH' =
    isPropΠ5
    (λ x y z w v →
      str (S ⟅ x , z ⟆b)
        (ProfHomo'.PH-ob PH' x z ((R ⟪ v ⟫r) w))
        ((S ⟪ v ⟫r) (ProfHomo'.PH-ob PH' x y w))
    )

  -- Use reflection to reason about equivalence of ProfHomo' and an
  -- iterated Σ type
  -- We can then use this Σ type to define paths between instances of ProfHomo'
  unquoteDecl ProfHomo'IsoΣ =
    declareRecordIsoΣ ProfHomo'IsoΣ (quote (ProfHomo'))

  -- The explicit and implicit versions of ProfHomo are indeed the same
  isoProfHomoProfHomo' : Iso ProfHomo ProfHomo'
  isoProfHomoProfHomo' =
    iso
    (λ x → record {
      PH-ob = λ c d r → x .PH-ob {c = c} {d = d} r ;
      PH-natL = λ c c' d f r → x .PH-natL {c = c} {c' = c'} {d = d} f r ;
      PH-natR = λ c d d' r g → x .PH-natR {c = c} {d = d} {d' = d'} r g
    })
    (λ x → record {
      PH-ob = λ {c} {d} r → ProfHomo'.PH-ob x c d r ;
      PH-natL = λ {c}{c'}{d} f r → ProfHomo'.PH-natL x c c' d f r ;
      PH-natR = λ {c}{d}{d'} r g → ProfHomo'.PH-natR x c d d' r g
    })
    (λ _ → refl)
    (λ _ → refl)

  ProfIso : Type _
  ProfIso = Σ[ ϕ ∈ ProfHomo ] ∀ c d → isIso (ϕ .PH-ob {c}{d})

open ProfHomo
module _  {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} {ℓS : Level} where
  -- Product of a presheaf with a profunctor
  -- This could be done by turning the presheaf into a profunctor
  -- first but at the cost of extra ids.
  _o×_ : (P : 𝓟o C ℓS) → (R : C o-[ ℓS ]-* D) → C o-[ ℓS ]-* D
  (P o× R) = mkBifunctorParAx F where
    open BifunctorParAx
    F : BifunctorParAx (C ^op) D (SET ℓS)
    F .Bif-ob c d = (⟨ P ⟅ c ⟆ ⟩ × ⟨  R ⟅ c , d ⟆b ⟩)
      , (isSet× ((P ⟅ c ⟆) .snd) ((R ⟅ c , d ⟆b) .snd))
    F .Bif-homL f _ (p , r) = (P ⟪ f ⟫) p , (R ⟪ f ⟫l) r
    F .Bif-homR _ g (p , r) = p , ((R ⟪ g ⟫r) r)
    F .Bif-hom× f g (p , r) = ((P ⟪ f ⟫) p) , ((R ⟪ f , g ⟫×) r)
    F .Bif-×-id = funExt (λ (p , r) → ΣPathP ((funExt⁻ (P .F-id) _)
      , funExt⁻ (R .Bif-×-id) _))
    F .Bif-×-seq f f' g g' = funExt (λ (p , r) → ΣPathP (
      ( funExt⁻ (P .F-seq f f') _)
      , funExt⁻ (R .Bif-×-seq f f' g g') _))
    F .Bif-L×-agree f = funExt (λ (p , r) → ΣPathP (refl
      , (funExt⁻ (R .Bif-L×-agree _) _)))
    F .Bif-R×-agree g = funExt (λ (p , r) → ΣPathP ((sym (funExt⁻ (P .F-id) _))
      , funExt⁻ (R .Bif-R×-agree _) _))

Functor→Prof*-o : (C : Category ℓC ℓC')
                  (D : Category ℓD ℓD') (F : Functor C D) → C *-[ ℓD' ]-o D
Functor→Prof*-o C D F = HomBif D ∘Fr F

Functor→Profo-* : (C : Category ℓC ℓC')
                  (D : Category ℓD ℓD') (F : Functor C D) → C o-[ ℓD' ]-* D
Functor→Profo-* C D F = HomBif D ∘Fl (F ^opF)

Prof*-o→Functor : (C : Category ℓC ℓC')
                  (D : Category ℓD ℓD') (R : C *-[ ℓS ]-o D) →
                    Functor C (FUNCTOR (D ^op) (SET ℓS))
Prof*-o→Functor C D R = curryFl (D ^op) (SET _) ⟅ BifunctorToParFunctor R ⟆

Profo-*→Functor : (C : Category ℓC ℓC')
                  (D : Category ℓD ℓD') (R : C o-[ ℓS ]-* D) →
                    Functor (C ^op) (FUNCTOR D (SET ℓS))
Profo-*→Functor C D R = curryF D (SET _) ⟅ BifunctorToParFunctor R ⟆

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') (R : C *-[ ℓS ]-o D) where

  open NatTrans
  open NatIso
  open isIsoC
  open isEquiv

  UniversalElementAt : C .ob → Type _
  UniversalElementAt c = UniversalElement D (appR R c)

  UniversalElements : Type _
  UniversalElements = ((∀ (c : C .ob) → UniversalElement D (appR R c)))

  FunctorComprehension :
    ((∀ (c : C .ob) → UniversalElement D (appR R c)))
    → Σ[ F ∈ Functor C D ] (∀ (c : C .ob)
    → UniversalElementOn D (appR R c) (F ⟅ c ⟆))
  FunctorComprehension ues = F ,
    (λ c → UniversalElementToUniversalElementOn _ _ (ues c)) where
    F : Functor C D
    F .F-ob c = ues c .vertex
    F .F-hom f =
      ues _ .universal _ .equiv-proof ((R ⟪ f ⟫r) (ues _ .element))
      .fst .fst
    F .F-id {x = c} = cong fst (ues c .universal (ues c .vertex) .equiv-proof
      ((R ⟪ C .id ⟫r) (ues _ .element)) .snd (_ ,
      funExt⁻ (R .Bif-L-id) _
      ∙ sym (funExt⁻ (R .Bif-R-id) _)))
    F .F-seq f g = cong fst ((ues _ .universal (ues _ .vertex) .equiv-proof
      ((R ⟪ f ⋆⟨ C ⟩ g ⟫r) (ues _ .element))) .snd (_ ,
      funExt⁻ (R .Bif-L-seq _ _) _
      ∙ cong (R .Bif-homL _ _) (ues _ .universal _ .equiv-proof
          ((R ⟪ g ⟫r) (ues _ .element)) .fst .snd)
      ∙ funExt⁻ ( (Bif-RL-commute R _ _)) _
      ∙ cong (R .Bif-homR _ _) ((ues _ .universal _ .equiv-proof
          ((R ⟪ f ⟫r) (ues _ .element)) .fst .snd))
      ∙ sym (funExt⁻ (R .Bif-R-seq _ _) _) ))

  open isUnivalent
  open UniversalElementNotation

  PshFunctorRepresentation : Type _
  PshFunctorRepresentation =
    Σ[ G ∈ Functor C D ]
    NatIso (Prof*-o→Functor C D ((LiftF {ℓS}{ℓD'}) ∘Fb R ))
           (Prof*-o→Functor C D (LiftF {ℓD'}{ℓS} ∘Fb (Functor→Prof*-o C D G)))

-- ((∀ (c : C .ob) → UniversalElement D (appR R c)))
-- UniversalElementOn D (appR R c) (F ⟅ c ⟆)
--

  UEOToUE : {F : Functor C D } → {c : C .ob} →
            UniversalElementOn D (appR R c) (F ⟅ c ⟆) →
            UniversalElement D (appR R c)
  UEOToUE {F} {c} UEO .vertex = F ⟅ c ⟆
  UEOToUE UEO .element = UEO .fst
  UEOToUE UEO .universal = UEO .snd

  UniversalElementOnToPshFunctorRepresentation :
    (F : Functor C D) →
    ((∀ (c : C .ob) → UniversalElementOn D (appR R c) (F ⟅ c ⟆)))
    → NatIso (Prof*-o→Functor C D ((LiftF {ℓS}{ℓD'}) ∘Fb R ))
           (Prof*-o→Functor C D (LiftF {ℓD'}{ℓS} ∘Fb (Functor→Prof*-o C D F)))
  UniversalElementOnToPshFunctorRepresentation F universalAtF
    .trans .N-ob c .N-ob d =
      λ f → lift {ℓD'}{ℓS} (intro (UEOToUE (universalAtF c)) (lower f))
  UniversalElementOnToPshFunctorRepresentation F universalAtF
    .trans .N-ob c .N-hom {d}{d'} ϕ =
      let coind = intro (UEOToUE (universalAtF c)) in
      funExt (λ x →
          ((λ i → lift (coind (R .Bif-hom× ϕ (C .id) (lower x))))) ∙
          {!!} ∙
          {!!}
        )
  UniversalElementOnToPshFunctorRepresentation F universalAtF
    .trans .N-hom ϕ = {!!}
  UniversalElementOnToPshFunctorRepresentation F universalAtF
    .nIso = {!!}


  open isWeakEquivalence
  UniqueFunctorComprehension : isUnivalent D →
    ((∀ (c : C .ob) → UniversalElement D (appR R c)))
    → ∃![ F ∈ Functor C D ] (∀ (c : C .ob)
    → UniversalElementOn D (appR R c) (F ⟅ c ⟆))
  UniqueFunctorComprehension isUnivD ues =
    (F , universalAtF) ,
    λ (G , universalAtG) →
    ΣPathP (
      {!isFullyFaithful→isFullyFaithfulPostcomp !} ,
      -- UniversalElementOnToPshFunctorRepresentation F universalAtF) ,
      funExt (λ c → {!TODO' G universalAtG .!})
      )
    where
    F = FunctorComprehension ues .fst
    universalAtF = FunctorComprehension ues .snd

    TODO : (G : Functor C D) →
           ((c : C .ob) →
           UniversalElementOn D (appR R c) (G ⟅ c ⟆)) →
           _
    TODO G universalAtG =
      seqNatIso
        (symNatIso
          (UniversalElementOnToPshFunctorRepresentation F universalAtF))
          (UniversalElementOnToPshFunctorRepresentation G universalAtG)

    -- Echoing this from Categories.Yoneda but without levels issues
    yon : {ℓE ℓE' : Level} {E : Category ℓE ℓE'} → (E .ob) → Functor (E ^op) (SET (ℓ-max ℓE' ℓS))
    yon {_}{ℓE'}{E} x .F-ob y .fst = Lift {ℓE'}{ℓS} (E [ y , x ])
    yon {_}{_}{E} x .F-ob y .snd =
      λ x₁ y₁ x₂ y₂ i i₁ →
        lift (E .isSetHom (lower x₁) (lower y₁) (cong lower x₂) (cong lower y₂) i i₁)
    yon {_}{_}{E} x .F-hom f g = lift (f ⋆⟨ E ⟩ (lower g))
    yon {_}{_}{E} x .F-id i f = lift (E .⋆IdL (lower f) i)
    yon {_}{_}{E} x .F-seq f g i h = lift (E. ⋆Assoc g f (lower h) i)

    YON : {ℓE ℓE' : Level} {E : Category ℓE ℓE'} → Functor E (FUNCTOR (E ^op) (SET (ℓ-max ℓE' ℓS)))
    YON {_}{_}{E} .F-ob e = yon {E = E} e
    YON {_}{_}{E} .F-hom f .N-ob z g = lift (lower g ⋆⟨ E ⟩ f)
    YON {_}{_}{E} .F-hom f .N-hom g i h = lift (E .⋆Assoc g (lower h) f i)
    YON {_}{_}{E} .F-id = makeNatTransPath (λ i _ → λ f → lift (E .⋆IdR (lower f) i) )
    YON {_}{_}{E} .F-seq f g = makeNatTransPath λ i _ → λ h → lift (E .⋆Assoc (lower h) f g (~ i))

    the-trans : (H : Functor C D) →
                NatTrans (Prof*-o→Functor C D (compF (LiftF {ℓD'}{ℓS})
                        (Functor→Prof*-o C D H)))
                        (YON ∘F H)

    the-trans H .N-ob c .N-ob d f = f
    the-trans H .N-ob c .N-hom ϕ =
      (SET _) .⋆IdR _ ∙
      funExt (λ z i → lift ((cong (λ a → (D ⋆ seq' D ϕ (lower z)) a) (H .F-id)) i)) ∙
      funExt (λ z i → lift (D .⋆IdR (seq' D ϕ (lower z)) i)) ∙
      funExt (λ z i → lift ((SET _) .⋆IdL
        {Hom[ D , _ ] (H .F-ob c) , D .isSetHom}
        {Hom[ D , _ ] (H .F-ob c) , D .isSetHom} (λ x → ϕ ⋆⟨ D ⟩ x) i (lower z)))
    the-trans H .N-hom {c}{c'} ϕ =
      let
        prop-proof : (c : C .ob) → (d : D .ob) →
                     (x y : Lift {ℓD'}{ℓS} (Hom[ D , d ] (F-ob H c))) →
                     isProp (x ≡ y)
        prop-proof c d x y x₁ y₁ i i₁ =
          lift (D .isSetHom
            (lower x)
            (lower y)
            (cong lower x₁)
            (cong lower y₁) i i₁)
      in
      makeNatTransPath (funExt (λ d →
        (SET _) .⋆IdR
          {Lift (Hom[ D , d ] (F-ob H c)) , prop-proof c d}
          {Lift (Hom[ D , d ] (H ⟅ c' ⟆)) , prop-proof c' d}
          _ ∙
        funExt (λ z → cong lift
          (cong (λ a → a (lower z))
            (sym((Functor→Prof*-o C D H) .Bif-R×-agree ϕ)))) ∙
        sym ((SET _) .⋆IdL
          {Lift (Hom[ D , d ] (F-ob H c)) , prop-proof c d}
          {Lift (Hom[ D , d ] (H ⟅ c' ⟆)) , prop-proof c' d}
          _)
      ))


    TODONatIso : (H : Functor C D) →
                 NatIso (Prof*-o→Functor C D (compF (LiftF {ℓD'}{ℓS})
                                           (Functor→Prof*-o C D H)))
                        (YON ∘F H)
    TODONatIso H .trans = the-trans H
    TODONatIso H .nIso c =
      isiso
        the-inverse the-sec the-ret
      where

      prop-proof : (c : C .ob) → (d : D .ob) →
                   (x y : Lift {ℓD'}{ℓS} (Hom[ D , d ] (F-ob H c))) →
                   isProp (x ≡ y)
      prop-proof c d x y x₁ y₁ i i₁ =
        lift (D .isSetHom
          (lower x)
          (lower y)
          (cong lower x₁)
          (cong lower y₁) i i₁)

      the-inverse :
        NatTrans ((YON ∘F H) .F-ob c)
                 (Prof*-o→Functor C D
                   (compF LiftF (Functor→Prof*-o C D H)) .F-ob c)
      the-inverse .N-ob d f = f
      the-inverse .N-hom {x}{y} ϕ =
        (SET _) .⋆IdR _ ∙
        funExt (λ z → sym (cong lift (((cong (λ a → a (lower z)) (sym ((Functor→Prof*-o C D H) .Bif-L×-agree ϕ))))))) ∙
        sym ((SET _) .⋆IdL
          {Lift (Hom[ D , _ ] (F-ob H c)) , prop-proof c x}
          {Lift (Hom[ D , _ ] (H ⟅ c ⟆)) , prop-proof c y}
        _)

      the-sec : seq' (FUNCTOR (D ^op) (SET (ℓ-max ℓD' ℓS))) the-inverse
               (N-ob (TODONatIso H .trans) c)
               ≡ FUNCTOR (D ^op) (SET (ℓ-max ℓD' ℓS)) .id
      the-sec =
        makeNatTransPath
        (funExt (λ d → (SET _) .⋆IdR
          {Lift (D [ d , H ⟅ c ⟆ ]) , prop-proof c d}
          {Lift (D [ d , H ⟅ c ⟆ ]) , prop-proof c d}
        _))

      the-ret : seq' (FUNCTOR (D ^op) (SET (ℓ-max ℓD' ℓS)))
               (N-ob (TODONatIso H .trans) c) the-inverse
               ≡ FUNCTOR (D ^op) (SET (ℓ-max ℓD' ℓS)) .id
      the-ret =
        makeNatTransPath
        (funExt (λ d → (SET _) .⋆IdR
          {Lift (D [ d , H ⟅ c ⟆ ]) , prop-proof c d}
          {Lift (D [ d , H ⟅ c ⟆ ]) , prop-proof c d}
          _
        ))

    TODOFunc≅R : (G : Functor C D) →
           ((c : C .ob) →
           UniversalElementOn D (appR R c) (G ⟅ c ⟆)) →
           NatIso (Prof*-o→Functor C D (compF (LiftF {ℓD'}{ℓS}) (Functor→Prof*-o C D G)))
                  (Prof*-o→Functor C D (LiftF {ℓS}{ℓD'} ∘Fb R))
    TODOFunc≅R G universalAtG = {!!}


    TODOYonF≅YonG : (G : Functor C D) →
           ((c : C .ob) →
           UniversalElementOn D (appR R c) (G ⟅ c ⟆)) →
           _
    TODOYonF≅YonG G universalAtG =
      seqNatIso
        (symNatIso (TODONatIso F))
        (seqNatIso (TODO G universalAtG) (TODONatIso G))

    yon-yon-yon :
      {ℓE ℓE' : Level} {E : Category ℓE ℓE'}{x : E .ob} →
      (H : Functor (E ^op) (SET _)) →
      NatTrans (yon x) H → H .F-ob x .fst
    yon-yon-yon {_}{_}{E}{x} H α = α .N-ob x (lift (E .id))

    non-non-non : {ℓE ℓE' : Level} {E : Category ℓE ℓE'}{x : E .ob} →
      (H : Functor (E ^op) (SET _)) →
      H .F-ob x .fst → NatTrans (yon x) H
    non-non-non {_} {_} {E} {x} H f .N-ob y ϕ = H .F-hom (lower ϕ) f
    non-non-non {_} {_} {E} {x} H f .N-hom a = funExt (λ g i → H .F-seq (lower g) a i f)

    yonIso : {ℓE ℓE' : Level} {E : Category ℓE ℓE'}{x : E .ob} →
      (H : Functor (E ^op) (SET _)) →
      Iso (NatTrans (yon x) H) (H .F-ob x .fst)
    yonIso {_} {_} {E} {x} H .Iso.fun = yon-yon-yon H
    yonIso {_} {_} {E} {x} H .Iso.inv = non-non-non H
    yonIso {_} {_} {E} {x} H .Iso.rightInv b i = H .F-id i b
    yonIso {_} {_} {E} {x} H .Iso.leftInv a = makeNatTransPath (funExt λ _ → funExt λ x₁ i → rem (lower x₁) i)
      where
        rem : ∀ {z} (x₁ : E [ z , x ]) → H .F-hom x₁ (yon-yon-yon H a) ≡ (a .N-ob z) (lift x₁)
        rem g =
          H .F-hom g (yon-yon-yon H a)
            ≡[ i ]⟨ a .N-hom g (~ i) (lift (E .id)) ⟩
          a .N-hom g i0 (lift (E .id))
            ≡[ i ]⟨ a .N-ob _ (lift(E .⋆IdR g i)) ⟩
          (a .N-ob _) (lift g)
            ∎

    yonEquiv : {ℓE ℓE' : Level} {E : Category ℓE ℓE'}{x : E .ob} →
      (H : Functor (E ^op) (SET _)) →
      NatTrans (yon x) H ≃ H .F-ob x .fst
    yonEquiv H = isoToEquiv (yonIso H)

    isFullYON : {ℓE ℓE' : Level} {E : Category ℓE ℓE'} → isFull (YON {E = E})
    isFullYON {_}{_}{E} x y F[f] = ∣ lower (yon-yon-yon (F-ob (YON {E = E}) y) F[f]) , yonIso {x = x} (yon y) .Iso.leftInv F[f] ∣₁

    isFaithfulYON : {ℓE ℓE' : Level} {E : Category ℓE ℓE'} → isFaithful (YON {E = E})
    isFaithfulYON {_}{_}{E} x y f g p i =
      hcomp
        (λ j → λ{ (i = i0) → E .⋆IdL f j ; (i = i1) → E .⋆IdL g j })
        (lower (yon-yon-yon _ (p i)))

    isFullyFaithfulYON : isFullyFaithful YON
    isFullyFaithfulYON = isFull+Faithful→isFullyFaithful {F = YON} isFullYON isFaithfulYON

    _ :  postcomposeF C YON .F-ob F ≡ YON ∘F F
    _ = refl


    the-yoneda-comp-iso : (G : Functor C D) →
                    ((c : C .ob) →
                    UniversalElementOn D (appR R c) (G ⟅ c ⟆)) →
                    _
    the-yoneda-comp-iso G universalAtG =
      NatIso→FUNCTORIso C (FUNCTOR (D ^op) (SET (ℓ-max ℓD' ℓS)))
        {F = YON ∘F F}{G = YON ∘F G} (TODOYonF≅YonG G universalAtG)

    TODOYonedaIso : (G : Functor C D) →
                    ((c : C .ob) →
                    UniversalElementOn D (appR R c) (G ⟅ c ⟆)) →
                    _
    TODOYonedaIso G universalAtG =
      isFullyFaithful→Conservative {F = postcomposeF C (YON {ℓD}{ℓD'}{D})}
        (isFullyFaithful→isFullyFaithfulPostcomp C (YON {ℓD}{ℓD'}{D}) isFullyFaithfulYON)
      {!the-yoneda-comp-iso G universalAtG .snd!}

    -- ueF : ∀ (c : C .ob) → UniversalElement D (appR R c)
    -- ueF c .vertex = F ⟅ c ⟆
    -- ueF c .element = universalAtF c .fst
    -- ueF c .universal = universalAtF c .snd

    -- ueG : (G : Functor C D) → (c : C .ob) →
    --     UniversalElementOn D (appR R c) (G ⟅ c ⟆) →
    --     UniversalElement D (appR R c)
    -- ueG G c universalAtGc .vertex = G ⟅ c ⟆
    -- ueG G c universalAtGc .element = universalAtGc .fst
    -- ueG G c universalAtGc .universal = universalAtGc .snd

    -- the-nat-trans : (G : Functor C D) → ((c : C .ob) →
    --     UniversalElementOn D (appR R c) (G ⟅ c ⟆)) → FUNCTOR C D [ F , G ]
    -- the-nat-trans G universalAtG .N-ob c =
    --   intro {P = appR R c} (ueG G c (universalAtG c))
    --     (universalAtF c .fst)
    -- the-nat-trans G universalAtG .N-hom {c}{c'} ϕ =
    --   {! !}
      -- {!(intro-natural {P = appR R c} (ueG G c (universalAtG c)) {f = G .F-hom ϕ}) ∙ ?!}
      -- intro-natural {P = appR R c} {!ueG G c (universalAtG c')!}


 -- -- ParamUnivElt → PshFunctorRepresentation
  -- ParamUnivElt→PshFunctorRepresentation : ParamUnivElt →
  --                                         PshFunctorRepresentation
  -- ParamUnivElt→PshFunctorRepresentation ues =
  --   (representing-functor , representing-nat-iso) where
  --   representing-functor : Functor C D
  --   representing-functor = ParamUnivElt→Functor ues

  --   rep-nat-iso-trans : (c : C .ob) →
  --     NatTrans (Prof*-o→Functor C D (LiftF {ℓS}{ℓD'} ∘Fb R) .F-ob c)
  --              (Prof*-o→Functor C D (LiftF {ℓD'}{ℓS} ∘Fb
  --                (Functor→Prof*-o C D representing-functor)) .F-ob c)
  --   rep-nat-iso-trans c .N-ob d  =
  --     let R⟅-,c⟆ = (pAppR R c) in
  --     (λ f → lift {ℓD'}{ℓS} ((ues c) .universal .coinduction {b = d}
  --       (lower {ℓS}{ℓD'} f)))
  --   rep-nat-iso-trans c .N-hom {d}{d'} ϕ =
  --     let R⟅-,c⟆ = (pAppR R c) in
  --     let εc = ues c .element in
  --     let coind = (ues c) .universal .coinduction in
  --     funExt λ x →
  --       lift (coind (((Prof*-o→Functor C D R .F-ob c) ⟪ ϕ ⟫) (lower x)))
  --         ≡⟨ ( λ i → lift (coind ((R .Bif-idR (i)) ((R .Bif-homL ϕ c)
  --           (lower x))))) ⟩
  --       lift (coind (D [ (lower x) ∘ᴾ⟨ R⟅-,c⟆ ⟩ ϕ ] ))
  --         ≡⟨ (λ i → lift ((coinduction-natural ((ues c) .universal)
  --           (lower x) ϕ) (~ i))) ⟩
  --       lift ((coind (lower x)) ∘⟨ D ⟩ ϕ )
  --         ≡⟨ (λ i → lift (((HomBif D) .Bif-idR (~ i))
  --           (((HomBif D) .Bif-homL ϕ _) (coind (lower x)))) ) ⟩
  --       lift (((Bifunctor→Functor (HomBif D)) ⟪ ϕ , D .id ⟫ ) (coind (lower x)))
  --         ≡⟨ (λ i → lift (((Bifunctor→Functor (HomBif D))
  --           ⟪ ϕ , representing-functor .F-id (~ i) ⟫ ) (coind (lower x)))) ⟩
  --       lift (((Bifunctor→Functor (HomBif D))
  --         ⟪ ϕ , representing-functor ⟪ C . id ⟫ ⟫ ) (coind (lower x))) ∎

  --   representing-nat-iso  : NatIso
  --       (Prof*-o→Functor C D (LiftF {ℓS}{ℓD'} ∘Fb R))
  --       (Prof*-o→Functor C D (LiftF {ℓD'}{ℓS} ∘Fb
  --         (Functor→Prof*-o C D representing-functor)))
  --   representing-nat-iso .trans .N-ob c = rep-nat-iso-trans c
  --   representing-nat-iso .trans .N-hom {x}{y} ψ =
  --     let R⟅-,x⟆ = (pAppR R x) in
  --     let R⟅-,y⟆ = (pAppR R y) in
  --     let εy = ues y .element in
  --     let εx = ues x .element in
  --     let coindx = ues x .universal .coinduction in
  --     let coindy = ues y .universal .coinduction in
  --     makeNatTransPath (funExt (λ d → funExt (λ α →
  --         lift (coindy (((Bifunctor→Functor R) ⟪ D .id , ψ ⟫) (lower α)))
  --           ≡⟨ (λ i → lift (coindy
  --             (R .Bif-homR _ ψ ((R .Bif-idL (i)) (lower α))))) ⟩
  --         lift (coindy (R .Bif-homR _ ψ (lower α)))
  --           ≡⟨ ( λ i → lift (ues y .universal .is-uniq
  --                 (R .Bif-homR _ ψ (lower α))
  --                 ((coindx (lower α)) ⋆⟨ D ⟩ (representing-functor ⟪ ψ ⟫))
  --                 (
  --                 (
  --                   D [ εy ∘ᴾ⟨ R⟅-,y⟆ ⟩ (coindy ((R .Bif-homR _ ψ) εx) ∘⟨ D ⟩
  --                     (coindx (lower α))) ]
  --                     ≡⟨ (λ i → D [
  --                       εy ∘ᴾ⟨ R⟅-,y⟆ ⟩ ((coinduction-natural (ues y .universal)
  --                       ((R .Bif-homR _ ψ) εx) (coindx (lower α))) i)]  ) ⟩
  --                   D [ εy ∘ᴾ⟨ R⟅-,y⟆ ⟩
  --                     coindy ( D [ ((R .Bif-homR _ ψ) εx) ∘ᴾ⟨ R⟅-,y⟆ ⟩
  --                       (coindx (lower α)) ]) ]
  --                     ≡⟨ ues y .universal .commutes
  --                       (D [ ((R .Bif-homR _ ψ) εx) ∘ᴾ⟨ R⟅-,y⟆ ⟩
  --                         (coindx (lower α)) ]) ⟩
  --                   D [ ((R .Bif-homR _ ψ) εx) ∘ᴾ⟨ R⟅-,y⟆ ⟩ (coindx (lower α)) ]
  --                    ≡⟨ (λ i → ((R .Bif-assoc (coindx (lower α)) ψ) (~ i)) εx) ⟩
  --                   (R .Bif-homR _ ψ) (D [ εx ∘ᴾ⟨ R⟅-,x⟆ ⟩ (coindx (lower α)) ])
  --                    ≡⟨ (λ i → (R .Bif-homR _ ψ)
  --                      (ues x .universal .commutes (lower α) (i))) ⟩
  --                   (R .Bif-homR _ ψ (lower α)) ∎
  --                 )
  --                 )
  --                 (~ i))) ⟩
  --         lift ((coindx (lower α)) ⋆⟨ D ⟩ (representing-functor ⟪ ψ ⟫))
  --           ≡⟨ (λ i → lift ((HomBif D) .Bif-homR _ (representing-functor ⟪ ψ ⟫)
  --             (((HomBif D) .Bif-idL (~ i)) (coindx (lower α))))) ⟩
  --         lift (((Bifunctor→Functor (HomBif D)) ⟪ D .id ,
  --           representing-functor ⟪ ψ ⟫ ⟫) (coindx (lower α))) ∎

  --     )))
  --   representing-nat-iso .nIso c .inv .N-ob d =
  --     let εc = ues c .element in
  --     let R⟅-,c⟆ = (pAppR R c) in
  --     λ f → lift (D [ εc ∘ᴾ⟨ R⟅-,c⟆ ⟩ (lower f) ])
  --   representing-nat-iso .nIso c .inv .N-hom {d}{d'} ϕ =
  --     let εc = ues c .element in
  --     let R⟅-,c⟆ =(pAppR R c) in
  --     funExt λ x →
  --       lift (D [ εc ∘ᴾ⟨ R⟅-,c⟆ ⟩ ((Bifunctor→Functor (HomBif D))
  --         ⟪ ϕ , representing-functor ⟪ C .id ⟫ ⟫) (lower x) ])
  --         ≡⟨ (λ i → lift (D [ εc ∘ᴾ⟨ R⟅-,c⟆ ⟩ ((Bifunctor→Functor (HomBif D))
  --           ⟪ ϕ , representing-functor .F-id i ⟫) (lower x) ])) ⟩
  --       lift (D [ εc ∘ᴾ⟨ R⟅-,c⟆ ⟩ ((Bifunctor→Functor (HomBif D))
  --         ⟪ ϕ , D .id ⟫ ) (lower x) ])
  --         ≡⟨ (λ i → lift (D [ εc ∘ᴾ⟨ R⟅-,c⟆ ⟩ ((HomBif D) .Bif-idR (i)
  --           (((HomBif D) .Bif-homL ϕ _) (lower x))) ])) ⟩
  --       lift (D [ εc ∘ᴾ⟨ R⟅-,c⟆ ⟩ (ϕ ⋆⟨ D ⟩ (lower x)) ])
  --         ≡⟨ (λ i → lift (((R⟅-,c⟆ .F-seq (lower x) ϕ) i) εc)) ⟩
  --       lift ((R .Bif-homL ϕ _) (D [ εc ∘ᴾ⟨ R⟅-,c⟆ ⟩ (lower x) ]))
  --         ≡⟨ (λ i → lift ((R .Bif-idR (~ i)) ((R .Bif-homL ϕ _)
  --           (D [ εc ∘ᴾ⟨ R⟅-,c⟆ ⟩ (lower x) ])))) ⟩
  --       lift (((Bifunctor→Functor R) ⟪ ϕ , C .id ⟫)
  --         (D [ εc ∘ᴾ⟨ R⟅-,c⟆ ⟩ (lower x) ])) ∎

  --   representing-nat-iso .nIso c .sec =
  --     let R⟅-,c⟆ = (pAppR R c) in
  --     makeNatTransPath (funExt λ d → funExt λ x → (λ i →
  --       lift ((η-expansion ((ues c) .universal) (lower x)) (~ i))) )
  --   representing-nat-iso .nIso c .ret =
  --     let R⟅-,c⟆ = (pAppR R c) in
  --     makeNatTransPath (funExt λ d → funExt λ x → (λ i →
  --       lift (((ues c) .universal .commutes (lower x)) i)))

  -- -- -- ParamUniversalElement → ParamUnivElt
  -- -- ParamUniversalElement→ParamUnivElt : ParamUniversalElement → ParamUnivElt
  -- -- ParamUniversalElement→ParamUnivElt U c =
  -- --   UniversalElement→UnivElt D (pAppR R c) (U c)

  -- -- -- ParamUnivElt → ParamUniversalElement
  -- -- ParamUnivElt→ParamUniversalElement : ParamUnivElt → ParamUniversalElement
  -- -- ParamUnivElt→ParamUniversalElement U c =
  -- --   UnivElt→UniversalElement D (pAppR R c) (U c)

  -- -- {-
  -- --   We have now given maps
  -- --     ProfRepresentation ⇔ PshFunctorRepresentation
  -- --     PshFunctorRepresentation ⇔ ParamUnivElt
  -- --     ParamUnivElt ⇔ ParamUniversalElement

  -- --   For convenience,
  -- --   below we also stitch these together to give all pairwise maps.
  -- -- -}

  -- -- -- ProfRepresentation → ParamUnivElt
  -- -- ProfRepresentation→ParamUnivElt : ProfRepresentation → ParamUnivElt
  -- -- ProfRepresentation→ParamUnivElt R =
  -- --   PshFunctorRepresentation→ParamUnivElt
  -- --     (ProfRepresentation→PshFunctorRepresentation R)

  -- -- -- ProfRepresentation → ParamUniversalElement
  -- -- ProfRepresentation→ParamUniversalElement : ProfRepresentation →
  -- --                                            ParamUniversalElement
  -- -- ProfRepresentation→ParamUniversalElement R =
  -- --   ParamUnivElt→ParamUniversalElement (ProfRepresentation→ParamUnivElt R)

  -- -- -- PshFunctorRepresentation → ParamUniversalElement
  -- -- PshFunctorRepresentation→ParamUniversalElement : PshFunctorRepresentation →
  -- --                                                  ParamUniversalElement
  -- -- PshFunctorRepresentation→ParamUniversalElement R =
  -- --   ParamUnivElt→ParamUniversalElement (PshFunctorRepresentation→ParamUnivElt R)

  -- -- -- ParamUnivElt → ProfRepresentation
  -- -- ParamUnivElt→ProfRepresentation : ParamUnivElt → ProfRepresentation
  -- -- ParamUnivElt→ProfRepresentation U =
  -- --   PshFunctorRepresentation→ProfRepresentation
  -- --     (ParamUnivElt→PshFunctorRepresentation U)

  -- -- -- ParamUniversalElement → ProfRepresentation
  -- -- ParamUniversalElement→ProfRepresentation : ParamUniversalElement →
  -- --                                            ProfRepresentation
  -- -- ParamUniversalElement→ProfRepresentation U =
  -- --   ParamUnivElt→ProfRepresentation (ParamUniversalElement→ParamUnivElt U)

  -- -- -- ParamUniversalElement → PshFunctorRepresentation
  -- -- ParamUniversalElement→PshFunctorRepresentation : ParamUniversalElement →
  -- --                                                  PshFunctorRepresentation
  -- -- ParamUniversalElement→PshFunctorRepresentation U =
  -- --   ParamUnivElt→PshFunctorRepresentation (ParamUniversalElement→ParamUnivElt U)
