{-

  Definition of profunctors (https://ncatlab.org/nlab/show/profunctor)
  and some basic facts about them.

  We define a profunctor C ⊶ D as a functor C^o x D -> Set. We pick
  the universe levels such that the hom sets of C and D match Set,
  which roughly matches the set-theoretic notion of "locally small"
  categories.

  We give some convenient notation for thinking of profunctors as a
  notion of "heteromorphism" between objects of different categories,
  with appropriate composition.

  A main use of profunctors is in defining universal properties as
  profunctors representable as a functor. The first definition is the
  isomorphism Hom[ F - , = ] =~ R[ - , = ] and the second is a
  generalization of the definition of an adjoint by giving "universal
  morphisms". These notions are equivalent, though for now we have
  only shown logical equivalence.

-}

{-# OPTIONS --safe #-}
module Cubical.Categories.Profunctor.General where

open import Cubical.Foundations.Prelude hiding (Path)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)

open import Cubical.Data.Graph.Base
open import Cubical.Data.Graph.Path

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functors.More
open import Cubical.Categories.Functors.HomFunctor

open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.Yoneda.More


open import Cubical.Categories.Equivalence.Base
open import Cubical.Categories.Equivalence.Properties
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.NaturalTransformation.More

open import Cubical.Categories.Presheaf.More
open import Cubical.Tactics.CategorySolver.Reflection
open import Cubical.Categories.Constructions.BinProduct.More


open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Presheaf.More

-- There are possibly 5 different levels to consider: the levels of
-- objects and arrows of the two different categories and the level of
-- the sets in the profunctor.

private
  variable
    ℓC ℓC' ℓD ℓD' : Level
PROFo-* : (C : Category ℓC ℓC') (D : Category ℓD ℓD') → ∀ ℓS → Category _ _
PROFo-* C D ℓS = FUNCTOR (C ^op ×C D) (SET ℓS)

PROF⊶ = PROFo-*

PROF*-o : (D : Category ℓD ℓD')(C : Category ℓC ℓC') → ∀ ℓS → Category _ _
PROF*-o D C = PROFo-* C D

PROF⊷ = PROF*-o

_o-[_]-*_ : (C : Category ℓC ℓC') → ∀ ℓS → (D : Category ℓD ℓD') → Type _
C o-[ ℓS ]-* D = Category.ob (PROF⊶ C D ℓS)

_*-[_]-o_ : (C : Category ℓC ℓC') → ∀ ℓS → (D : Category ℓD ℓD') → Type _
C *-[ ℓS ]-o D = D o-[ ℓS ]-* C

private
  variable
    ℓs : Level

open Functor

Functor→Prof*-o : (C : Category ℓC ℓC') (D : Category ℓD ℓD') (F : Functor C D) → C *-[ ℓD' ]-o D
Functor→Prof*-o C D F = HomFunctor D ∘F (Id {C = D ^op} ×F F)

Functor→Profo-* : (C : Category ℓC ℓC') (D : Category ℓD ℓD') (F : Functor C D) → C o-[ ℓD' ]-* D
Functor→Profo-* C D F = HomFunctor D ∘F ((F ^opF) ×F Id {C = D})

Prof*-o→Functor : (C : Category ℓC ℓC') (D : Category ℓD ℓD') (R : C *-[ ℓs ]-o D) → Functor C (FUNCTOR (D ^op) (SET ℓs))
Prof*-o→Functor C D R = curryFl (D ^op) (SET _) ⟅ R ⟆

Profo-*→Functor : (C : Category ℓC ℓC') (D : Category ℓD ℓD') (R : C o-[ ℓs ]-* D) → Functor (C ^op) (FUNCTOR D (SET ℓs))
Profo-*→Functor C D R = curryF D (SET _) ⟅ R ⟆

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') where
  open Category

  -- | Note that this works for both *-o and o-*, either way, the
  -- | contravariant variable goes on the left, to match Hom.
  _p[_,_] : ∀ {ℓs} → (C *-[ ℓs ]-o D) → D .ob → C .ob → Type ℓs
  R p[ d , c ] = ⟨ R ⟅ d , c ⟆ ⟩

  module _ {ℓs} (R : C *-[ ℓs ]-o D) where
    ProfRepresents : (Functor C D) → Type _
    ProfRepresents G = NatIso (LiftF {ℓs}{ℓD'} ∘F R) (LiftF {ℓD'}{ℓs} ∘F Functor→Prof*-o C D G)

    -- | Definition 1: A profunctor R representation is a functor G
    -- | with a natural isomorphism between R and G viewed as a profunctor
    ProfRepresentation : Type _
    ProfRepresentation = Σ[ G ∈ Functor C D ] ProfRepresents G

    -- | Definition 2: A profunctor R representation is a functor G
    -- | with a natural isomorphism between λF R and Y o G.
    PshFunctorRepresentation : Type _
    PshFunctorRepresentation =
      Σ[ G ∈ Functor C D ]
      NatIso (Prof*-o→Functor C D (LiftF {ℓs}{ℓD'} ∘F R))
             (Prof*-o→Functor C D (LiftF {ℓD'}{ℓs} ∘F Functor→Prof*-o C D G))

    -- | Definition 3: Parameterized Universal Element
    -- | A profunctor R representation is a *function* from objects (c : C) to universal elements for R [-, c ]
    ParamUniversalElement : Type _
    ParamUniversalElement = (c : C .ob) → UniversalElement D (R ∘F (Id {C = D ^op} ,F Constant (D ^op) C c))

    -- | Definition 4: Parameterized UnivElt
    -- | Same but with the unpacked UnivElt definition
    ParamUnivElt : Type _
    ParamUnivElt = (c : C .ob) → UnivElt D (R ∘F (Id {C = D ^op} ,F Constant (D ^op) C c))

    -- Show equivalence of all four definitions.
    -- Here we provide functions between definitions,
    -- we offload the proofs that these are indeed equivalences to Profunctor.Equivalence

    -- Try to replace the snd of the next term with its own function
    -- this hangs, while the original will typecheck. Both with ℓs and with _ after "SET"
    TODOa : {G : Functor C D} → NatIso (LiftF {ℓs}{ℓD'} ∘F R) (LiftF {ℓD'}{ℓs} ∘F Functor→Prof*-o C D G)
      → NatIso (Prof*-o→Functor C D (LiftF {ℓs}{ℓD'} ∘F R)) (Prof*-o→Functor C D (LiftF {ℓD'}{ℓs} ∘F Functor→Prof*-o C D G))
    TODOa η = (preservesNatIsosF (curryFl (D ^op) (SET _) {Γ = C}) η)

    -- | Definition 1 → Definition 2
    ProfRepresentation→PshFunctorRepresentation : ProfRepresentation → PshFunctorRepresentation
    ProfRepresentation→PshFunctorRepresentation (G , η) = (G ,
        -- (preservesNatIsosF (curryFl (D ^op) (SET _) {Γ = C}) η)
        TODOa η
      )

    open isEquivalence
    open NatIso
    open isWeakEquivalence

    TODOb : {G : Functor C D}
      → NatIso (Prof*-o→Functor C D (LiftF {ℓs}{ℓD'} ∘F R)) (Prof*-o→Functor C D (LiftF {ℓD'}{ℓs} ∘F Functor→Prof*-o C D G))
      → NatIso (LiftF {ℓs}{ℓD'} ∘F R) (LiftF {ℓD'}{ℓs} ∘F Functor→Prof*-o C D G)
    TODOb η =
      FUNCTORIso→NatIso (D ^op ×C C) (SET _)
        (liftIso {F = curryFl (D ^op) (SET _) {Γ = C}}
          (isEquiv→isWeakEquiv (curryFl-isEquivalence (D ^op) (SET _) {Γ = C}) .fullfaith)
          (NatIso→FUNCTORIso C _ η)
        -- TODO below hangs but above doesn't. Shouldn't it be cheaper to compute the _ up front?
        -- (NatIso→FUNCTORIso C (FUNCTOR (D ^op) (SET (ℓ-max ℓD' ℓs))) η)
        )

    -- | Definition 2 → Definition 1
    PshFunctorRepresentation→ProfRepresentation : PshFunctorRepresentation → ProfRepresentation
    PshFunctorRepresentation→ProfRepresentation (G , η) = (G ,
      -- FUNCTORIso→NatIso (D ^op ×C C) (SET _)
      --   (liftIso {F = curryFl (D ^op) (SET _) {Γ = C}}
      --     (isEquiv→isWeakEquiv (curryFl-isEquivalence (D ^op) (SET _) {Γ = C}) .fullfaith)
      --     (NatIso→FUNCTORIso C _ η)
      --   -- TODO below hangs but above doesn't. Shouldn't it be cheaper to compute the _ up front?
      --   -- (NatIso→FUNCTORIso C (FUNCTOR (D ^op) (SET (ℓ-max ℓD' ℓs))) η)
      -- )
      TODOb η
      )

    open isIso
    open NatTrans

    -- TODO refactor?
    -- | Definition 2 → Definition 3
    PshFunctorRepresentation→ParamUniversalElement : PshFunctorRepresentation → ParamUniversalElement
    PshFunctorRepresentation→ParamUniversalElement (G , η) = (λ c →
      RepresentationToUniversalElement D ( R ∘F (Id {C = D ^op} ,F Constant (D ^op) C c) )
        (G .F-ob c ,
          NatIso→FUNCTORIso (D ^op) (SET (ℓ-max ℓD' ℓs))
          (seqNatIso
            (LiftF {ℓD'} {ℓs} ∘ʳi
              (pathToNatIso (
                (D [-, G .F-ob c ])
                  ≡⟨ sym (HomFunctorPath (G .F-ob c)) ⟩
                HomFunctor D ∘F (Id ,F Constant (D ^op) D (G .F-ob c))
                  ≡⟨ ((λ i → ( HomFunctor D ∘F (Id ,F ConstantComposeFunctor C D c G i)  ))) ⟩
                HomFunctor D ∘F (Id ,F (G ∘F (Constant (D ^op) C c)))
                  ≡⟨ Functor≡ (λ c → refl) (λ f → refl) ⟩
                HomFunctor D ∘F (Id {C = D ^op} ×F G) ∘F (Id {C = D ^op} ,F Constant (D ^op) C c)
                  ≡⟨ F-assoc ⟩
                Functor→Prof*-o C D G ∘F (Id {C = D ^op} ,F Constant (D ^op) C c) ∎
              ))
            )
        (seqNatIso
        (seqNatIso
        (CAT⋆Assoc (Id {C = D ^op} ,F Constant (D ^op) C c) (Functor→Prof*-o C D G) (LiftF {ℓD'} {ℓs}))
        (
        (Id {C = D ^op} ,F Constant (D ^op) C c) ∘ˡi
          (FUNCTORIso→NatIso (D ^op ×C C) (SET _)
            (liftIso {F = curryFl (D ^op) (SET _) {Γ = C}}
            (isEquiv→isWeakEquiv (curryFl-isEquivalence (D ^op) (SET _) {Γ = C}) .fullfaith)
            (NatIso→FUNCTORIso C _ (symNatIso η)))
          )
        ))
        (symNatIso
        (CAT⋆Assoc (Id {C = D ^op} ,F Constant (D ^op) C c) (R) (LiftF {ℓs} {ℓD'}))))) ))
        where
        HomFunctorPath : (d : D .ob) → HomFunctor D ∘F (Id {C = D ^op} ,F Constant (D ^op) D d ) ≡ D [-, d ]
        HomFunctorPath d = Functor≡
          ((λ c → ( refl )))
          (λ f → (
            HomFunctor D .F-hom (f , id (D ^op))
              ≡⟨ funExt (λ θ → ( (D ∘ id D) ((D ∘ θ) f) ≡⟨ solveCat! D ⟩ seq' D f θ ∎ )) ⟩
            (D [-, d ]) .F-hom f ∎
          ))

    open UnivElt
    open isUniversal
    -- | Definition 3 → Definition 2
    ParamUniversalElement→PshFunctorRepresentation : ParamUniversalElement → PshFunctorRepresentation
    ParamUniversalElement→PshFunctorRepresentation U =
      ( representing-functor U ,
        preservesNatIsosF (curryFl (D ^op) (SET _))
        (binaryNatIso{C = D ^op} {D = C} {E = SET _}
          (LiftF {ℓs} {ℓD'} ∘F R)
          (LiftF {ℓD'} {ℓs} ∘F (Functor→Prof*-o C D (representing-functor U)))
            (λ (d : D .ob) → 
              seqNatIso
                (CurryInD d)
                (seqNatIso
                  (symNatIso (DFixed U d))
                  (CurryOutD U d)
                )
            )
            (λ (c : C .ob) →
              (seqNatIso
                (CurryInC c)
                (seqNatIso
                  (CFixed U c)
                  (CurryOutC U c)
                )
              )
            )
          (λ (c , d) → refl)
        )
      ) where
      Prof*-o→FunctorR : (C : Category ℓC ℓC') (D : Category ℓD ℓD') (R : C *-[ ℓs ]-o D) → Functor (D ^op) (FUNCTOR C (SET ℓs))
      Prof*-o→FunctorR C D R = curryF C (SET _) ⟅ R ⟆

      -- | For Definition 3 → Definition 2, we need to construct a functor
      representing-functor : ParamUniversalElement → Functor C D
      representing-functor U .F-ob c = fst (fst (U c))
      representing-functor U .F-hom {x} {y} ϕ =
        (UniversalElement→UnivElt D (R ∘F (Id {C = D ^op} ,F Constant (D ^op) C y)) (U y))
          .universal .coinduction
          ((((Prof*-o→FunctorR C D R)  ⟅ (fst (fst (U x))) ⟆) ⟪ ϕ ⟫) (snd (fst (U x))))
      representing-functor U .F-id {x} =
        let R⟅-,x⟆ = R ∘F (Id {C = D ^op} ,F Constant (D ^op) C x) in
        let (dₓ , θₓ) = (fst (U x)) in
          (UniversalElement→UnivElt D R⟅-,x⟆ (U x))
              .universal .coinduction
            ((((Prof*-o→FunctorR C D R)  ⟅ dₓ ⟆) ⟪ C .id ⟫) θₓ)
          -- Use the fact that curryF is a functor to simplify coinduction target (F-id)
          ≡⟨ (λ i →
              (UniversalElement→UnivElt D R⟅-,x⟆ (U x))
                .universal .coinduction
                ((((Prof*-o→FunctorR C D R)  ⟅ dₓ ⟆) .F-id (i)) θₓ)) ⟩
          (UniversalElement→UnivElt D R⟅-,x⟆ (U x)) .universal .coinduction θₓ
          -- use uniqueness of universal element.
          ≡⟨ sym ((UniversalElement→UnivElt D R⟅-,x⟆ (U x)) .universal .is-uniq θₓ (D .id)
                -- Nested proof that identity also works.
                ( (R⟅-,x⟆ ⟪ D .id ⟫) ((UniversalElement→UnivElt D R⟅-,x⟆ (U x)) .element)
                  ≡⟨ (λ i → (R⟅-,x⟆ .F-id (i)) ((UniversalElement→UnivElt D R⟅-,x⟆ (U x)) .element)) ⟩
                θₓ ∎
                )
          )⟩
        D .id ∎
      representing-functor U .F-seq {x} {y} {z} ϕ ψ =
        let Gϕ⋆ψ = (representing-functor U) .F-hom (ϕ ⋆⟨ C ⟩ ψ) in
        let Gϕ = (representing-functor U) .F-hom ϕ in
        let Gψ = (representing-functor U) .F-hom ψ in
        let (dx , εx) = (fst (U x)) in
        let (dy , εy) = (fst (U y)) in
        let (dz , εz) = (fst (U z)) in
        let R⟅-,y⟆ = R ∘F (Id {C = D ^op} ,F Constant (D ^op) C y) in
        let R⟅-,z⟆ = R ∘F (Id {C = D ^op} ,F Constant (D ^op) C z) in
        let R⟅dx,-⟆ = ((Prof*-o→FunctorR C D R) ⟅ dx ⟆) in
        let R⟅dy,-⟆ = ((Prof*-o→FunctorR C D R) ⟅ dy ⟆) in
          ( Gϕ⋆ψ )
          ≡⟨ (λ i → (UniversalElement→UnivElt D R⟅-,z⟆ (U z))
            .universal .coinduction
            (((R⟅dx,-⟆ .F-seq ϕ ψ) (i)) εx)
          ) ⟩
          ((UniversalElement→UnivElt D R⟅-,z⟆ (U z))
            .universal .coinduction
            ((R⟅dx,-⟆ ⟪ ψ ⟫)
              ((R⟅dx,-⟆ ⟪ ϕ ⟫) εx)
            )
          )
          ≡⟨ sym ((UniversalElement→UnivElt D R⟅-,z⟆ (U z)) .universal .is-uniq
            ((R⟅dx,-⟆ ⟪ ψ ⟫)((R⟅dx,-⟆ ⟪ ϕ ⟫) εx))
            -- enough to show that this function also yields above result
            (Gϕ ⋆⟨ D ⟩ Gψ)
            (
              (D [ εz ∘ᴾ⟨ R⟅-,z⟆ ⟩ (Gϕ ⋆⟨ D ⟩ Gψ) ])
                ≡⟨ (λ i → ((R⟅-,z⟆ .F-seq Gψ Gϕ) (i)) εz) ⟩
              (D [ (D [ εz ∘ᴾ⟨ R⟅-,z⟆ ⟩ (Gψ) ]) ∘ᴾ⟨ R⟅-,z⟆ ⟩ Gϕ ])
                ≡⟨ (λ i →
                  (D [
                    (((UniversalElement→UnivElt D R⟅-,z⟆ (U z)) .universal .commutes ((R⟅dy,-⟆ ⟪ ψ ⟫) εy)) (i))
                    ∘ᴾ⟨ R⟅-,z⟆ ⟩ Gϕ ]
                  )
                ) ⟩
              (D [ ((R⟅dy,-⟆ ⟪ ψ ⟫) εy) ∘ᴾ⟨ R⟅-,z⟆ ⟩ Gϕ ])
                ≡⟨ refl ⟩
              ((R ⟪ Gϕ , C .id ⟫) ((R ⟪ D .id , ψ ⟫) (εy)))
                ≡⟨ (λ i → (
                  ((BinMorphDecompR {C = (D ^op)} {D = C} {E = (SET _)}
                    (Gϕ , ψ) R) (~ i)
                  ) (εy)
                )) ⟩
              ((R ⟪ Gϕ , ψ ⟫) (εy))
                ≡⟨ (λ i → (
                  ((BinMorphDecompL {C = (D ^op)} {D = C} {E = (SET _)}
                    (Gϕ , ψ) R) (i)
                  ) (εy)
                )) ⟩
              ((R ⟪ D .id , ψ ⟫) ((R ⟪ Gϕ , C .id ⟫) (εy)))
                ≡⟨ refl ⟩
              ((R⟅dx,-⟆ ⟪ ψ ⟫) (D [ εy ∘ᴾ⟨ R⟅-,y⟆ ⟩ Gϕ ]))
                ≡⟨ (λ i →
                  ((R⟅dx,-⟆ ⟪ ψ ⟫)
                    (((UniversalElement→UnivElt D R⟅-,y⟆ (U y)) .universal .commutes ((R⟅dx,-⟆ ⟪ ϕ ⟫) εx)) (i))
                  )
                ) ⟩
              ((R⟅dx,-⟆ ⟪ ψ ⟫)((R⟅dx,-⟆ ⟪ ϕ ⟫) εx))
            ∎)
          )⟩
          (Gϕ ⋆⟨ D ⟩ Gψ) ∎

      -- | Fixing the C component of R gives a natural isomorphism
      CFixed : (U : ParamUniversalElement) →
        (∀ (c : C .ob)
          → NatIso
            (LiftF {ℓs} {ℓD'} ∘F (R ∘F (Id {C = D ^op} ,F Constant (D ^op) C c)))
            (LiftF {ℓD'} {ℓs} ∘F ( D [-, (fst (fst (U c))) ]))
        )
      CFixed U c = let R' = (R ∘F (Id {C = D ^op} ,F Constant (D ^op) C c)) in
        symNatIso (
          FUNCTORIso→NatIso (D ^op) (SET _)
            (catiso
              (Iso.inv
                (yonedaᴾ* R' (fst (fst (U c))))
                (snd (fst (U c)))
              )
              (isTerminalElement→YoIso D R' (U c) .inv)
              (isTerminalElement→YoIso D R' (U c) .sec)
              (isTerminalElement→YoIso D R' (U c) .ret)
            )
        )

      -- | Likewise, fixing the D ^op component of R gives a natural isomorphism
      DFixed : (U : ParamUniversalElement) →
        (∀ (d : D .ob) → NatIso
          (LiftF {ℓD'} {ℓs} ∘F ( (D [ d ,-]) ∘F (representing-functor U)))
            (LiftF {ℓs} {ℓD'} ∘F (R ∘F (Constant C (D ^op) d ,F Id)))
        )
      DFixed U d .trans .N-ob c f =
        let R' = (LiftF {ℓs} {ℓD'} ∘F (R ∘F (Id ,F Constant (D ^op) C c))) in
        D [ lift (U c .fst .snd) ∘ᴾ⟨ R' ⟩ lower f ]
      DFixed U d .trans .N-hom {c₁} {c₂} g =
        let R' = LiftF {ℓs} {ℓD'} ∘F R in
        let R'₂ = (LiftF {ℓs} {ℓD'} ∘F (R ∘F (Id ,F Constant (D ^op) C c₂))) in
        let R''₂ = (R ∘F (Id ,F Constant (D ^op) C c₂)) in
        let R'd = (LiftF {ℓs} {ℓD'} ∘F (R ∘F (Constant C (D ^op) d ,F Id))) in
        let G = representing-functor U in
        let R'Gc₁ = (LiftF {ℓs} {ℓD'} ∘F (R ∘F (Constant C (D ^op) (G .F-ob c₁) ,F Id))) in
        let UE₂ = UniversalElement→UnivElt D R''₂ (U c₂) in
        let ε₂ = U c₂ .fst .snd in
        let ε₁ = U c₁ .fst .snd in
        let coind₂ = UE₂ .universal .coinduction in
        let g⋆ε = (C ^op) [ lift ε₁ ∘ᴾ⟨ R'Gc₁ ⟩ g ] in
        funExt (λ h →
          D [ lift (ε₂) ∘ᴾ⟨ R'₂ ⟩ (coind₂ (lower g⋆ε)) ∘⟨ D ⟩ (lower h) ]
            ≡⟨ ∘ᴾAssoc D R'₂ (lift ε₂) (coind₂ (lower g⋆ε)) (lower h) ⟩
          D [ D [ lift (ε₂) ∘ᴾ⟨ R'₂ ⟩ (coind₂ (lower g⋆ε)) ] ∘ᴾ⟨ R'₂ ⟩ (lower h) ]
            ≡⟨ ((λ i → D [ lift ((UE₂ .universal .commutes (lower g⋆ε)) i) ∘ᴾ⟨ R'₂ ⟩ (lower h) ] )) ⟩
          D [ g⋆ε ∘ᴾ⟨ R'₂ ⟩ (lower h) ]
            ≡⟨ (λ i → (BinMorphDecompR {C = D ^op} {D = C} {E = SET _} (lower h , g) R') (~ i) (lift ε₁)) ⟩
          (R' ⟪ lower h , g ⟫) (lift ε₁)
            ≡⟨ (λ i → (BinMorphDecompL {C = D ^op} {D = C} {E = SET _} (lower h , g) R') i (lift ε₁)) ⟩
          (R' ⟪ D .id , g ⟫) ((R' ⟪ lower h , C .id ⟫) (lift ε₁)) ∎
        )
      DFixed U d .nIso c =
        let univ = UniversalElement→UnivElt D (R ∘F (Id ,F Constant (D ^op) C c)) (U c) .universal in
        isiso
          (λ f  → lift (univ .coinduction (lower f)))
          (funExt (λ f → λ i → lift (univ .commutes (lower f) i)))
          (funExt (λ f → λ i → lift (η-expansion univ (lower f) (~ i))))

      CurryInC : ∀ (c : C .ob) → NatIso
        ((curryFl (D ^op) (SET _) {Γ = C} ⟅ (LiftF {ℓs} {ℓD'} ∘F R) ⟆) ⟅ c ⟆)
        (LiftF {ℓs} {ℓD'} ∘F (R ∘F (Id ,F Constant (D ^op) C c)))
      CurryInC _ .trans .N-ob _ = (λ h → h)
      CurryInC _ .trans .N-hom _ = refl
      CurryInC _ .nIso _ .inv = (λ h → h)
      CurryInC _ .nIso _ .sec = refl
      CurryInC _ .nIso _ .ret = refl

      CurryInD : ∀ (d : D .ob) → NatIso
        ((curryF C (SET _) {Γ = D ^op} ⟅ LiftF {ℓs} {ℓD'} ∘F R ⟆) ⟅ d ⟆)
        (LiftF {ℓs} {ℓD'} ∘F (R ∘F (Constant C (D ^op) d ,F Id)))
      CurryInD _ .trans .N-ob _ = (λ h → h)
      CurryInD _ .trans .N-hom _ = refl
      CurryInD _ .nIso _ .inv = (λ h → h)
      CurryInD _ .nIso _ .sec = refl
      CurryInD _ .nIso _ .ret = refl

      CurryOutC : (U : ParamUniversalElement) →
        (∀ (c : C .ob) → NatIso
          (LiftF {ℓD'} {ℓs} ∘F ( D [-, (fst (fst (U c))) ]))
          ((curryFl (D ^op) (SET _) {Γ = C} ⟅ (LiftF {ℓD'} {ℓs} ∘F (Functor→Prof*-o C D (representing-functor U))) ⟆) ⟅ c ⟆)
        )
      CurryOutC U c .trans .N-ob d = (λ h → h)
      CurryOutC U c .trans .N-hom {x} {y} f =
        let G = representing-functor U in
          ((LiftF {ℓD'} {ℓs} ∘F ( D [-, (fst (fst (U c))) ])) ⟪ f ⟫)
            ≡⟨ (λ i →
              (λ z → lift ((λ (h : (D [ x , (fst (fst (U c))) ])) → (D .⋆IdR (f ⋆⟨ D ⟩ h)) (~ i)) (z .lower)))
            ) ⟩
          (λ z → lift (((HomFunctor D) ⟪ f , D .id ⟫) (z .lower)))
            ≡⟨ (λ i → (λ z → lift (((HomFunctor D) ⟪ f , (G .F-id (~ i)) ⟫) (z .lower)))) ⟩
          ((curryFl (D ^op) (SET _) {Γ = C} ⟅ (LiftF {ℓD'} {ℓs} ∘F (Functor→Prof*-o C D G)) ⟆) ⟅ c ⟆) ⟪ f ⟫ ∎
      CurryOutC U c .nIso d .inv = (λ h → h)
      CurryOutC U c .nIso d .sec = refl
      CurryOutC U c .nIso d .ret = refl

      CurryOutD : (U : ParamUniversalElement) →
        (∀ (d : D .ob) → NatIso
          (LiftF {ℓD'} {ℓs} ∘F ( (D [ d ,-]) ∘F (representing-functor U) ))
          ((curryF C (SET _) {Γ = (D ^op)} ⟅ LiftF {ℓD'} {ℓs} ∘F (Functor→Prof*-o C D (representing-functor U)) ⟆) ⟅ d ⟆)
        )
      CurryOutD U d .trans .N-ob c = (λ h → h)
      CurryOutD U d .trans .N-hom {x} {y} f =
        let G = representing-functor U in
        ((LiftF {ℓD'} {ℓs} ∘F ( (D [ d ,-]) ∘F  G)) ⟪ f ⟫)
          ≡⟨ (λ i →
            (λ z → lift ((λ (h : D [ d ,  (G ⟅ x ⟆) ]) → ((D .⋆IdL h) (~ i)) ⋆⟨ D ⟩ (G ⟪ f ⟫)) (z .lower)))
          ) ⟩
        (((curryF C (SET _) {Γ = (D ^op)} ⟅ LiftF {ℓD'} {ℓs} ∘F (Functor→Prof*-o C D G) ⟆) ⟅ d ⟆) ⟪ f ⟫) ∎
      CurryOutD U d .nIso c .inv = (λ h → h)
      CurryOutD U d .nIso c .sec = refl
      CurryOutD U d .nIso c .ret = refl

    -- | Definition 3 → Definition 4
    ParamUniversalElement→ParamUnivElt : ParamUniversalElement → ParamUnivElt
    ParamUniversalElement→ParamUnivElt U c = UniversalElement→UnivElt D (R ∘F (Id {C = D ^op} ,F Constant (D ^op) C c)) (U c)

    -- | Definition 4 → Definition 3
    ParamUnivElt→ParamUniversalElement : ParamUnivElt → ParamUniversalElement
    ParamUnivElt→ParamUniversalElement U c = UnivElt→UniversalElement D (R ∘F (Id {C = D ^op} ,F Constant (D ^op) C c)) (U c)
