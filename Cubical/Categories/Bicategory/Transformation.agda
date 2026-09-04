{-
  Lax natural transformations between lax functors of bicategories.

  Given lax functors F, G : B → C, a lax natural transformation
  α : F ⇒ G consists of:
    • a 1-cell  N-1cell x : F(x) → G(x)  for each 0-cell x of B;
    • for each 1-cell f : x → y of B, a 2-cell
         N-hom f :  F(f) ⋆₁ N-1cell y  ⇒  N-1cell x ⋆₁ G(f)
      natural in f;
    • coherence with the unit laxity cells (F⁰, G⁰) and the
      composition laxity cells (F², G²) of F and G.
-}
module Cubical.Categories.Bicategory.Transformation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Terminal

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Functor.Lax

private
  variable
    ℓb ℓb' ℓb'' ℓc ℓc' ℓc'' : Level

record LaxNatTrans
  {B : Bicategory ℓb ℓb' ℓb''}
  {C : Bicategory ℓc ℓc' ℓc''}
  (F G : LaxFunctor B C) :
  Type (ℓ-max (ℓ-max ℓb (ℓ-max ℓb' ℓb''))
              (ℓ-max ℓc (ℓ-max ℓc' ℓc''))) where
  no-eta-equality

  private
    module B = Bicategory B
    module C = Bicategory C
    module F = LaxFunctor F
    module G = LaxFunctor G

  field
    -- Component 1-cell at each 0-cell x of B.
    N-1cell : (x : B.ob) → C.1Cell (F.F-ob x) (G.F-ob x)

    -- Naturality 2-cell:  F(f) ⋆₁ N-1cell y  ⇒  N-1cell x ⋆₁ G(f).
    N-hom : ∀ {x y : B.ob} (f : B.1Cell x y)
      → C.2Cell (F.F-1cell f C.⋆₁ N-1cell y)
                (N-1cell x C.⋆₁ G.F-1cell f)

    -- Naturality in 2-cells: for any 2-cell θ : f ⇒ g of B,
    --
    --     F(f) ⋆₁ α y  ──N-hom f──→  α x ⋆₁ G(f)
    --        │                            │
    --     F(θ) ▷w α y                     │ α x ◁w G(θ)
    --        ↓                            ↓
    --     F(g) ⋆₁ α y  ──N-hom g──→  α x ⋆₁ G(g)
    N-natural : ∀ {x y : B.ob} {f g : B.1Cell x y}
      (θ : B.2Cell f g)
      →   (F.F-2cell θ C.▷w N-1cell y) C.⋆₂ N-hom g
        ≡ N-hom f C.⋆₂ (N-1cell x C.◁w G.F-2cell θ)

    -- Unit coherence: two parallel 2-cells from id ⋆₁ α x to α x ⋆₁ G(id)
    -- agree.
    --
    --   id ⋆ α  ──[F⁰ ▷w α]──→  F(id) ⋆ α  ──[N-hom id]──→  α ⋆ G(id)
    --
    -- equals
    --
    --   id ⋆ α  ──[C.λ⁺]──→  α  ──[C.ρ⁻]──→  α ⋆ id  ──[α ◁w G⁰]──→  α ⋆ G(id)
    lax-id : (x : B.ob)
      →   (F.F⁰ C.▷w N-1cell x) C.⋆₂ N-hom B.id₁
        ≡ C.λ⁺ (N-1cell x) C.⋆₂ C.ρ⁻ (N-1cell x) C.⋆₂ (N-1cell x C.◁w G.F⁰)

    -- Composition coherence:
    --
    --   LHS: F²(f,g) ▷w α z ; N-hom (f ⋆ g)
    --     ((F f ⋆ F g) ⋆ α z)  ──F²▷wα z──→  F(f⋆g) ⋆ α z
    --                                              │
    --                                              │  N-hom (f⋆g)
    --                                              ↓
    --                                          α x ⋆ G(f⋆g)
    --
    --   RHS: associate, whisker by N-hom g, reassociate (α⁻),
    --        whisker by N-hom f, associate again, then apply G²(f,g)
    --        on the right.
    lax-seq : ∀ {x y z : B.ob}
      (f : B.1Cell x y) (g : B.1Cell y z)
      →   (F.F² f g C.▷w N-1cell z) C.⋆₂ N-hom (f B.⋆₁ g)
        ≡   C.α⁺ (F.F-1cell f) (F.F-1cell g) (N-1cell z)
          C.⋆₂ (F.F-1cell f C.◁w N-hom g)
          C.⋆₂ C.α⁻ (F.F-1cell f) (N-1cell y) (G.F-1cell g)
          C.⋆₂ (N-hom f C.▷w G.F-1cell g)
          C.⋆₂ C.α⁺ (N-1cell x) (G.F-1cell f) (G.F-1cell g)
          C.⋆₂ (N-1cell x C.◁w G.F² f g)
{-
  Modifications between lax natural transformations.

  Given lax functors F, G : B → C and two lax natural transformations
  α, β : F ⇒ G, a modification Γ : α ⇛ β is:
    • for each 0-cell x of B, a 2-cell  Γ x : α x ⇒ β x  in C;
    • cylinder coherence with the naturality 2-cells: for each 1-cell
      f : x → y of B,
         α.N-hom f ⋆₂ (Γ x ▷w G f)  ≡  (F f ◁w Γ y) ⋆₂ β.N-hom f.
-}
record Modification
  {B : Bicategory ℓb ℓb' ℓb''}
  {C : Bicategory ℓc ℓc' ℓc''}
  {F G : LaxFunctor B C}
  (α β : LaxNatTrans F G) :
  Type (ℓ-max (ℓ-max ℓb (ℓ-max ℓb' ℓb''))
              (ℓ-max ℓc (ℓ-max ℓc' ℓc''))) where
  no-eta-equality

  private
    module B = Bicategory B
    module C = Bicategory C
    module F = LaxFunctor F
    module G = LaxFunctor G
    module α = LaxNatTrans α
    module β = LaxNatTrans β

  field
    -- Component 2-cells:  Γ x : α x ⇒ β x  in C.
    M-ob : (x : B.ob) → C.2Cell (α.N-1cell x) (β.N-1cell x)

    -- Cylinder coherence with N-hom:
    --
    --   F f ⋆₁ α y  ──α.N-hom f──→  α x ⋆₁ G f
    --      │                            │
    --   F f ◁w Γ y                      │ Γ x ▷w G f
    --      ↓                            ↓
    --   F f ⋆₁ β y  ──β.N-hom f──→  β x ⋆₁ G f
    M-hom : ∀ {x y : B.ob} (f : B.1Cell x y)
      →   α.N-hom f C.⋆₂ (M-ob x C.▷w G.F-1cell f)
        ≡ (F.F-1cell f C.◁w M-ob y) C.⋆₂ β.N-hom f
