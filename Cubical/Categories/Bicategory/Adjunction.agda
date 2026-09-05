{- Adjunctions in a bicategory (Street's formal adjunctions). -}
module Cubical.Categories.Bicategory.Adjunction where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Properties.Coherence
open import Cubical.Categories.Bicategory.Constructions.Co
open import Cubical.Categories.Bicategory.Constructions.Op

private
  variable
    ℓ ℓ' ℓ'' : Level

open NatIso
open isIso

module _ (C : Bicategory ℓ ℓ' ℓ'') where
  private
    module C = Bicategory C

  record Adjunction : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
    field
      c d : C.0Cell
      f : C.1Cell c d
      u : C.1Cell d c
      η : C.2Cell C.id₁ (f C.⋆₁ u)
      ε : C.2Cell (u C.⋆₁ f) C.id₁

    field
      zigzagL :
          C.λ⁻ f
            C.⋆₂ ((η C.▷w f)
            C.⋆₂ (C.α⁺ f u f
            C.⋆₂ ((f C.◁w ε) C.⋆₂ C.ρ⁺ f)))
        ≡ C.id₂

      zigzagR :
          C.ρ⁻ u
            C.⋆₂ ((u C.◁w η)
            C.⋆₂ (C.α⁻ u f u
            C.⋆₂ ((ε C.▷w u) C.⋆₂ C.λ⁺ u)))
        ≡ C.id₂

{- Coherence for a 2-cell `σ : q ⇒ id₁` sitting in the middle of a
   composite: everything below is about whiskering such a `σ`, and
   needs no adjunction. -}
module _ (C : Bicategory ℓ ℓ' ℓ'') where
  private
    module C = Bicategory C

  -- The two ways of absorbing the unit `σ` creates agree.
  unitMid : {x y w : C.0Cell} (p : C.1Cell x y) {q : C.1Cell y y}
    (r : C.1Cell y w) (σ : C.2Cell q C.id₁)
    →   C.α⁺ p q r C.⋆₂ (p C.◁w ((σ C.▷w r) C.⋆₂ C.λ⁺ r))
      ≡ ((p C.◁w σ) C.⋆₂ C.ρ⁺ p) C.▷w r
  unitMid p r σ =
      C.⟨⟩⋆₂⟨ ◁wSeq C p _ _ ⟩
    ∙ sym (C.⋆₂Assoc _ _ _)
    ∙ C.⟨ sym (α⁺natM C p σ r) ⟩⋆₂⟨⟩
    ∙ C.⋆₂Assoc _ _ _
    ∙ C.⟨⟩⋆₂⟨ C.triangle _ _ _ p r ⟩
    ∙ sym (▷wSeq C _ _ r)

  module _ {c d : C.0Cell} {f : C.1Cell c d} {u : C.1Cell d c}
    (ε : C.2Cell (u C.⋆₁ f) C.id₁) where

    -- `ε` acting on the right of `u`, at an arbitrary 1-cell.
    εAct : {e : C.0Cell} (m : C.1Cell d e) → C.2Cell (u C.⋆₁ f C.⋆₁ m) m
    εAct m = C.α⁻ u f m C.⋆₂ (ε C.▷w m) C.⋆₂ C.λ⁺ m

    -- The action is natural in its 1-cell argument.
    εActNat : {e : C.0Cell} {m n : C.1Cell d e} (θ : C.2Cell m n)
      → (u C.◁w (f C.◁w θ)) C.⋆₂ εAct n ≡ εAct m C.⋆₂ θ
    εActNat θ =
        sym (C.⋆₂Assoc _ _ _)
      ∙ C.⟨ α⁻natR C u f θ ⟩⋆₂⟨⟩
      ∙ C.⋆₂Assoc _ _ _
      ∙ C.⟨⟩⋆₂⟨ sym (C.⋆₂Assoc _ _ _) ⟩
      ∙ C.⟨⟩⋆₂⟨ C.⟨ sym (▷◁exch C ε θ) ⟩⋆₂⟨⟩ ⟩
      ∙ C.⟨⟩⋆₂⟨ C.⋆₂Assoc _ _ _ ⟩
      ∙ C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ λ-nat C θ ⟩ ⟩
      ∙ sym (C.⋆₂Assoc _ _ _ ∙ C.⟨⟩⋆₂⟨ C.⋆₂Assoc _ _ _ ⟩)

    -- Whiskering the action is the action at the composite.
    εAct▷ : {e e' : C.0Cell} (m : C.1Cell d e) (n : C.1Cell e e')
      →   C.α⁺ u (f C.⋆₁ m) n C.⋆₂ (u C.◁w C.α⁺ f m n) C.⋆₂ εAct (m C.⋆₁ n)
        ≡ εAct m C.▷w n
    εAct▷ m n =
        C.⟨⟩⋆₂⟨ sym (C.⋆₂Assoc _ _ _) ⟩
      ∙ sym (C.⋆₂Assoc _ _ _)
      ∙ C.⟨ pentP4 C u f m n ⟩⋆₂⟨⟩
      ∙ C.⋆₂Assoc _ _ _
      ∙ C.⟨⟩⋆₂⟨ sym εsplit ⟩
      ∙ C.⟨⟩⋆₂⟨ sym (▷wSeq C _ _ n) ⟩
      ∙ sym (▷wSeq C _ _ n)
      where
      εsplit :   ((ε C.▷w m) C.▷w n) C.⋆₂ (C.λ⁺ m C.▷w n)
               ≡ C.α⁺ (u C.⋆₁ f) m n
                   C.⋆₂ (ε C.▷w (m C.⋆₁ n)) C.⋆₂ C.λ⁺ (m C.⋆₁ n)
      εsplit =
          C.⟨ ▷⋆₁ C ε m n ⟩⋆₂⟨⟩
        ∙ C.⋆₂Assoc _ _ _
        ∙ C.⟨⟩⋆₂⟨ C.⋆₂Assoc _ _ _ ∙ C.⟨⟩⋆₂⟨ λ⋆₁ C m n ⟩ ⟩

{- Notation for a formal adjunction: the composites and whiskered
   cells the zigzag identities are stated in. -}
module AdjunctionNotation {C : Bicategory ℓ ℓ' ℓ''}
  (A : Adjunction C) where
  private
    module C = Bicategory C
  open Adjunction A public

  fu : C.1Cell c c
  fu = f C.⋆₁ u

  uf : C.1Cell d d
  uf = u C.⋆₁ f

  ηf : C.2Cell (C.id₁ C.⋆₁ f) (fu C.⋆₁ f)
  ηf = η C.▷w f

  fε : C.2Cell (f C.⋆₁ uf) (f C.⋆₁ C.id₁)
  fε = f C.◁w ε

  uη : C.2Cell (u C.⋆₁ C.id₁) (u C.⋆₁ fu)
  uη = u C.◁w η

  εu : C.2Cell (uf C.⋆₁ u) (C.id₁ C.⋆₁ u)
  εu = ε C.▷w u

  -- `ε` acting on the left of `f`, and on the right of `u`.
  Gf : C.2Cell (fu C.⋆₁ f) f
  Gf = C.α⁺ f u f C.⋆₂ fε C.⋆₂ C.ρ⁺ f

  Eu : C.2Cell (u C.⋆₁ fu) u
  Eu = C.α⁻ u f u C.⋆₂ εu C.⋆₂ C.λ⁺ u

  -- The zigzags, in that notation.
  zigzagL' : C.λ⁻ f C.⋆₂ ηf C.⋆₂ Gf ≡ C.id₂
  zigzagL' = zigzagL

  zigzagR' : C.ρ⁻ u C.⋆₂ uη C.⋆₂ Eu ≡ C.id₂
  zigzagR' = zigzagR

  {- An adjoint equivalence: an adjunction whose unit and counit are
     invertible.  There is no bicategorical `Equivalence` yet to
     connect this to, so it is stated as a bare predicate. -}
  isAdjointEquivalence : Type ℓ''
  isAdjointEquivalence =
      Cubical.Categories.Category.isIso C.Hom[ c , c ] η
    × Cubical.Categories.Category.isIso C.Hom[ d , d ] ε

  -- The same, with the leading unitor moved to the other side.
  zigzagL⁺ : ηf C.⋆₂ Gf ≡ C.λ⁺ f
  zigzagL⁺ =
      ⋆InvLMove (invIso (C.λ⁺ f , C.λU c d .nIso (tt* , f))) zigzagL'
    ∙ C.⋆₂IdR _

  zigzagR⁺ : uη C.⋆₂ Eu ≡ C.ρ⁺ u
  zigzagR⁺ =
      ⋆InvLMove (invIso (C.ρ⁺ u , C.ρU d c .nIso (u , tt*))) zigzagR'
    ∙ C.⋆₂IdR _

{- `_^opᴮ` reverses the 1-cells and keeps the 2-cells, so it exchanges
   the two legs and the two zigzags on the nose. -}
opAdjunction : {C : Bicategory ℓ ℓ' ℓ''}
  → Adjunction C → Adjunction (C ^opᴮ)
opAdjunction A = A' where
  module A = Adjunction A
  A' : Adjunction _
  A' .Adjunction.c = A.c
  A' .Adjunction.d = A.d
  A' .Adjunction.f = A.u
  A' .Adjunction.u = A.f
  A' .Adjunction.η = A.η
  A' .Adjunction.ε = A.ε
  A' .Adjunction.zigzagL = A.zigzagR
  A' .Adjunction.zigzagR = A.zigzagL

{- `_^coᴮ` reverses the 2-cells, so the unit becomes a counit and the
   two legs swap.  Reversing also reverses the zigzag composites, so
   the laws only match after reassociating. -}
coAdjunction : {C : Bicategory ℓ ℓ' ℓ''}
  → Adjunction C → Adjunction (C ^coᴮ)
coAdjunction {C = C} A = A' where
  module C = Bicategory C
  module A = Adjunction A

  -- Reversing `a ⋆₂ b ⋆₂ c ⋆₂ d ⋆₂ e` nests it to the left.
  reassoc : {x y : C.0Cell} {g₀ g₁ g₂ g₃ g₄ g₅ : C.1Cell x y}
    (a : C.2Cell g₀ g₁) (b : C.2Cell g₁ g₂) (cc : C.2Cell g₂ g₃)
    (e : C.2Cell g₃ g₄) (h : C.2Cell g₄ g₅)
    → (((a C.⋆₂ b) C.⋆₂ cc) C.⋆₂ e) C.⋆₂ h
      ≡ a C.⋆₂ b C.⋆₂ cc C.⋆₂ e C.⋆₂ h
  reassoc a b cc e h =
      C.⟨ C.⟨ C.⋆₂Assoc a b cc ⟩⋆₂⟨⟩ ⟩⋆₂⟨⟩
    ∙ C.⟨ C.⋆₂Assoc a (b C.⋆₂ cc) e ⟩⋆₂⟨⟩
    ∙ C.⋆₂Assoc a ((b C.⋆₂ cc) C.⋆₂ e) h
    ∙ C.⟨⟩⋆₂⟨ C.⋆₂Assoc (b C.⋆₂ cc) e h ⟩
    ∙ C.⟨⟩⋆₂⟨ C.⋆₂Assoc b cc (e C.⋆₂ h) ⟩

  A' : Adjunction _
  A' .Adjunction.c = A.d
  A' .Adjunction.d = A.c
  A' .Adjunction.f = A.u
  A' .Adjunction.u = A.f
  A' .Adjunction.η = A.ε
  A' .Adjunction.ε = A.η
  A' .Adjunction.zigzagL =
    reassoc (C.ρ⁻ A.u) (A.u C.◁w A.η) (C.α⁻ A.u A.f A.u)
            (A.ε C.▷w A.u) (C.λ⁺ A.u)
    ∙ A.zigzagR
  A' .Adjunction.zigzagR =
    reassoc (C.λ⁻ A.f) (A.η C.▷w A.f) (C.α⁺ A.f A.u A.f)
            (A.f C.◁w A.ε) (C.ρ⁺ A.f)
    ∙ A.zigzagL

{- The identity adjunction at a 0-cell: `id₁ ⊣ id₁`, with the unitors
   as unit and counit.  Both zigzags come down to Kelly's `λ⁺≡ρ⁺`. -}
idAdjunction : {C : Bicategory ℓ ℓ' ℓ''} (x : Bicategory.0Cell C)
  → Adjunction C
idAdjunction {C = C} x = A where
  module C = Bicategory C

  λsec : C.λ⁻ C.id₁ C.⋆₂ C.λ⁺ C.id₁ ≡ C.id₂
  λsec = C.λU x x .nIso (tt* , C.id₁) .sec

  A : Adjunction C
  A .Adjunction.c = x
  A .Adjunction.d = x
  A .Adjunction.f = C.id₁
  A .Adjunction.u = C.id₁
  A .Adjunction.η = C.λ⁻ C.id₁
  A .Adjunction.ε = C.λ⁺ C.id₁
  A .Adjunction.zigzagL =
      C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ sym (C.⋆₂Assoc _ _ _)
                    ∙ C.⟨ C.triangle x x x C.id₁ C.id₁ ⟩⋆₂⟨⟩ ⟩ ⟩
    ∙ C.⟨⟩⋆₂⟨ sym (C.⋆₂Assoc _ _ _) ⟩
    ∙ C.⟨⟩⋆₂⟨ C.⟨ sym (▷wSeq C _ _ C.id₁)
                ∙ C.⟨ C.⟨⟩⋆₂⟨ sym (λ⁺≡ρ⁺ C) ⟩ ∙ λsec ⟩▷ C.id₁
                ∙ C.▷wId C.id₁ ⟩⋆₂⟨⟩ ⟩
    ∙ C.⟨⟩⋆₂⟨ C.⋆₂IdL _ ⟩
    ∙ C.⟨⟩⋆₂⟨ sym (λ⁺≡ρ⁺ C) ⟩
    ∙ λsec
  A .Adjunction.zigzagR =
      C.⟨⟩⋆₂⟨ C.⟨⟩⋆₂⟨ sym (C.⋆₂Assoc _ _ _)
                    ∙ C.⟨ C.⟨⟩⋆₂⟨ C.⟨ λ⁺≡ρ⁺ C ⟩▷ C.id₁ ⟩
                        ∙ α⁻ρ▷ C C.id₁ C.id₁ ⟩⋆₂⟨⟩ ⟩ ⟩
    ∙ C.⟨⟩⋆₂⟨ sym (C.⋆₂Assoc _ _ _) ⟩
    ∙ C.⟨⟩⋆₂⟨ C.⟨ sym (◁wSeq C C.id₁ _ _)
                ∙ C.id₁ C.◁⟨ λsec ⟩
                ∙ C.◁wId C.id₁ ⟩⋆₂⟨⟩ ⟩
    ∙ C.⟨⟩⋆₂⟨ C.⋆₂IdL _ ⟩
    ∙ C.⟨⟩⋆₂⟨ λ⁺≡ρ⁺ C ⟩
    ∙ C.ρU x x .nIso (C.id₁ , tt*) .sec
