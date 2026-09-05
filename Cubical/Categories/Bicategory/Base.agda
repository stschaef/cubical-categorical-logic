module Cubical.Categories.Bicategory.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Terminal

private
  variable
    ℓ ℓ' ℓ'' : Level

open Functor
open NatTrans
open NatIso
open isIso

𝟙C : Category ℓ-zero ℓ-zero
𝟙C = TerminalCategory {ℓ-zero}

module _ (ℓ ℓ' ℓ'' : Level) where

  record Bicategory : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc (ℓ-max ℓ' ℓ''))) where
    no-eta-equality
    field
      ob       : Type ℓ
      Hom[_,_] : ob → ob → Category ℓ' ℓ''

      id  : ∀ {x : ob} → Functor 𝟙C Hom[ x , x ]
      seq : (x y z : ob)
        → Functor (Hom[ x , y ] ×C Hom[ y , z ]) Hom[ x , z ]

    0Cell : Type ℓ
    0Cell = ob

    1Cell : 0Cell → 0Cell → Type ℓ'
    1Cell x y = Hom[ x , y ] .Category.ob

    2Cell : ∀ {x y} → 1Cell x y → 1Cell x y → Type ℓ''
    2Cell {x}{y} f g = Hom[ x , y ] .Category.Hom[_,_] f g

    -- Horizontal composition of 1-cells
    _⋆₁_ : ∀ {x y z} → 1Cell x y → 1Cell y z → 1Cell x z
    _⋆₁_ {x}{y}{z} f g = seq x y z .F-ob (f , g)
    infixr 9 _⋆₁_

    -- Identity 1-cell at an object
    id₁ : ∀ {x} → 1Cell x x
    id₁ {x} = id {x} .F-ob tt*

    -- Identity 2-cell at a 1-cell
    id₂ : ∀ {x y}{f : 1Cell x y} → 2Cell f f
    id₂ {x}{y} = Hom[ x , y ] .Category.id

    -- Vertical composition of 2-cells
    _⋆₂_ : ∀ {x y}{f g h : 1Cell x y}
      → 2Cell f g → 2Cell g h → 2Cell f h
    _⋆₂_ {x}{y} α β = α ⋆⟨ Hom[ x , y ] ⟩ β
    infixr 9 _⋆₂_

    postcomp : ∀ {x y z} (g : 1Cell y z)
      → Functor Hom[ x , y ] Hom[ x , z ]
    postcomp {x}{y}{z} g =
      seq x y z ∘F (𝟙⟨ Hom[ x , y ] ⟩ ,F Constant _ _ g)

    precomp : ∀ {x y z} (f : 1Cell x y)
      → Functor Hom[ y , z ] Hom[ x , z ]
    precomp {x}{y}{z} f =
      seq x y z ∘F (Constant _ _ f ,F 𝟙⟨ Hom[ y , z ] ⟩)

    isSet2Cell : ∀ {x y} {f g : 1Cell x y} → isSet (2Cell f g)
    isSet2Cell {x}{y} = Hom[ x , y ] .Category.isSetHom

    -- isomorphism of 1-cells: an invertible 2-cell
    _≅₂_ : ∀ {x y} → 1Cell x y → 1Cell x y → Type ℓ''
    _≅₂_ {x}{y} f g = CatIso Hom[ x , y ] f g

    ⋆₂Assoc : ∀ {x y}{f g h k : 1Cell x y}
      (α : 2Cell f g) (β : 2Cell g h) (γ : 2Cell h k)
      → (α ⋆₂ β) ⋆₂ γ ≡ α ⋆₂ (β ⋆₂ γ)
    ⋆₂Assoc {x}{y} = Hom[ x , y ] .Category.⋆Assoc

    ⋆₂IdL : ∀ {x y}{f g : 1Cell x y} (α : 2Cell f g) → id₂ ⋆₂ α ≡ α
    ⋆₂IdL {x}{y} = Hom[ x , y ] .Category.⋆IdL

    ⋆₂IdR : ∀ {x y}{f g : 1Cell x y} (α : 2Cell f g) → α ⋆₂ id₂ ≡ α
    ⋆₂IdR {x}{y} = Hom[ x , y ] .Category.⋆IdR

    -- Congruence for vertical composition, after `⟨_⟩⋆⟨_⟩` in
    -- `Categories.Category.Base`.
    ⟨_⟩⋆₂⟨_⟩ : ∀ {x y}{f g h : 1Cell x y}{α α' : 2Cell f g}{β β' : 2Cell g h}
      → α ≡ α' → β ≡ β' → α ⋆₂ β ≡ α' ⋆₂ β'
    ⟨ p ⟩⋆₂⟨ q ⟩ = cong₂ _⋆₂_ p q

    ⟨_⟩⋆₂⟨⟩ : ∀ {x y}{f g h : 1Cell x y}{α α' : 2Cell f g}{β : 2Cell g h}
      → α ≡ α' → α ⋆₂ β ≡ α' ⋆₂ β
    ⟨ p ⟩⋆₂⟨⟩ = cong (_⋆₂ _) p

    ⟨⟩⋆₂⟨_⟩ : ∀ {x y}{f g h : 1Cell x y}{α : 2Cell f g}{β β' : 2Cell g h}
      → β ≡ β' → α ⋆₂ β ≡ α ⋆₂ β'
    ⟨⟩⋆₂⟨ q ⟩ = cong (_ ⋆₂_) q

    -- Horizontal composition of 2-cells, and its congruence.
    _⋆ₕ_ : ∀ {x y z}{f f' : 1Cell x y}{g g' : 1Cell y z}
      → 2Cell f f' → 2Cell g g' → 2Cell (f ⋆₁ g) (f' ⋆₁ g')
    _⋆ₕ_ {x}{y}{z} α β = seq x y z .F-hom (α , β)
    infixr 9 _⋆ₕ_

    ⟨_⟩⋆ₕ⟨_⟩ : ∀ {x y z}{f f' : 1Cell x y}{g g' : 1Cell y z}
      {α α' : 2Cell f f'}{β β' : 2Cell g g'}
      → α ≡ α' → β ≡ β' → α ⋆ₕ β ≡ α' ⋆ₕ β'
    ⟨_⟩⋆ₕ⟨_⟩ {x}{y}{z} p q =
      cong₂ (λ α β → seq x y z .F-hom (α , β)) p q

    ⟨_⟩⋆ₕ⟨⟩ : ∀ {x y z}{f f' : 1Cell x y}{g g' : 1Cell y z}
      {α α' : 2Cell f f'}{β : 2Cell g g'}
      → α ≡ α' → α ⋆ₕ β ≡ α' ⋆ₕ β
    ⟨ p ⟩⋆ₕ⟨⟩ = ⟨ p ⟩⋆ₕ⟨ refl ⟩

    ⟨⟩⋆ₕ⟨_⟩ : ∀ {x y z}{f f' : 1Cell x y}{g g' : 1Cell y z}
      {α : 2Cell f f'}{β β' : 2Cell g g'}
      → β ≡ β' → α ⋆ₕ β ≡ α ⋆ₕ β'
    ⟨⟩⋆ₕ⟨ q ⟩ = ⟨ refl ⟩⋆ₕ⟨ q ⟩

    -- Left whiskering
    _◁w_ : ∀ {x y z} (f : 1Cell x y) {g h : 1Cell y z}
      → 2Cell g h → 2Cell (f ⋆₁ g) (f ⋆₁ h)
    _◁w_ {x}{y}{z} f α = seq x y z .F-hom (id₂ , α)

    -- Right whiskering
    _▷w_ : ∀ {x y z} {f g : 1Cell x y}
      → 2Cell f g → (h : 1Cell y z) → 2Cell (f ⋆₁ h) (g ⋆₁ h)
    _▷w_ {x}{y}{z} α h = seq x y z .F-hom (α , id₂)

    -- Congruence for whiskering.
    _◁⟨_⟩ : ∀ {x y z} (f : 1Cell x y){g h : 1Cell y z}{α β : 2Cell g h}
      → α ≡ β → f ◁w α ≡ f ◁w β
    f ◁⟨ p ⟩ = cong (λ m → f ◁w m) p
    infixl 35 _◁⟨_⟩

    ⟨_⟩▷_ : ∀ {x y z}{f g : 1Cell x y}{α β : 2Cell f g}
      → α ≡ β → (h : 1Cell y z) → α ▷w h ≡ β ▷w h
    ⟨ p ⟩▷ h = cong (λ m → m ▷w h) p
    infixl 35 ⟨_⟩▷_

    -- `seq`'s functoriality, in bicategorical notation.
    ⋆ₕId : ∀ {x y z}{f : 1Cell x y}{g : 1Cell y z}
      → id₂ {f = f} ⋆ₕ id₂ {f = g} ≡ id₂
    ⋆ₕId {x}{y}{z} = seq x y z .F-id

    -- interchange: horizontal composition is functorial in both slots
    ⋆ₕSeq : ∀ {x y z}{f f' f'' : 1Cell x y}{g g' g'' : 1Cell y z}
      (α : 2Cell f f') (α' : 2Cell f' f'')
      (β : 2Cell g g') (β' : 2Cell g' g'')
      → (α ⋆₂ α') ⋆ₕ (β ⋆₂ β') ≡ (α ⋆ₕ β) ⋆₂ (α' ⋆ₕ β')
    ⋆ₕSeq {x}{y}{z} α α' β β' = seq x y z .F-seq (α , β) (α' , β')

    ◁wId : ∀ {x y z} (f : 1Cell x y){g : 1Cell y z}
      → f ◁w id₂ {f = g} ≡ id₂
    ◁wId {x}{y}{z} f = seq x y z .F-id

    ▷wId : ∀ {x y z}{f : 1Cell x y} (g : 1Cell y z)
      → id₂ {f = f} ▷w g ≡ id₂
    ▷wId {x}{y}{z} g = seq x y z .F-id

    private
      LU-src : (x y : ob) → Functor (𝟙C ×C Hom[ x , y ]) Hom[ x , y ]
      LU-src x y = seq x x y ∘F (id {x} ×F 𝟙⟨ Hom[ x , y ] ⟩)

      LU-tgt : (x y : ob) → Functor (𝟙C ×C Hom[ x , y ]) Hom[ x , y ]
      LU-tgt x y = Snd 𝟙C Hom[ x , y ]

      RU-src : (x y : ob) → Functor (Hom[ x , y ] ×C 𝟙C) Hom[ x , y ]
      RU-src x y = seq x y y ∘F (𝟙⟨ Hom[ x , y ] ⟩ ×F id {y})

      RU-tgt : (x y : ob) → Functor (Hom[ x , y ] ×C 𝟙C) Hom[ x , y ]
      RU-tgt x y = Fst Hom[ x , y ] 𝟙C

      A-src : (x y z w : ob)
        → Functor (Hom[ x , y ] ×C (Hom[ y , z ] ×C Hom[ z , w ]))
                  Hom[ x , w ]
      A-src x y z w =
          seq x z w
          ∘F (seq x y z ×F 𝟙⟨ Hom[ z , w ] ⟩)
          ∘F ×C-assoc Hom[ x , y ] Hom[ y , z ] Hom[ z , w ]

      A-tgt : (x y z w : ob)
        → Functor (Hom[ x , y ] ×C (Hom[ y , z ] ×C Hom[ z , w ]))
                  Hom[ x , w ]
      A-tgt x y z w =
          seq x y w ∘F (𝟙⟨ Hom[ x , y ] ⟩ ×F seq y z w)

    field
      λU : (x y : ob)     → NatIso (LU-src x y)    (LU-tgt x y)
      ρU : (x y : ob)     → NatIso (RU-src x y)    (RU-tgt x y)
      α  : (x y z w : ob) → NatIso (A-src x y z w) (A-tgt x y z w)

    -- Component 2-cells of the unitors and associator
    λ⁺ : ∀ {x y} (f : 1Cell x y) → 2Cell (id₁ ⋆₁ f) f
    λ⁺ {x}{y} f = λU x y .trans .N-ob (tt* , f)

    λ⁻ : ∀ {x y} (f : 1Cell x y) → 2Cell f (id₁ ⋆₁ f)
    λ⁻ {x}{y} f = λU x y .nIso (tt* , f) .inv

    ρ⁺ : ∀ {x y} (f : 1Cell x y) → 2Cell (f ⋆₁ id₁) f
    ρ⁺ {x}{y} f = ρU x y .trans .N-ob (f , tt*)

    ρ⁻ : ∀ {x y} (f : 1Cell x y) → 2Cell f (f ⋆₁ id₁)
    ρ⁻ {x}{y} f = ρU x y .nIso (f , tt*) .inv

    α⁺ : ∀ {x y z w}
      (f : 1Cell x y) (g : 1Cell y z) (h : 1Cell z w)
      → 2Cell ((f ⋆₁ g) ⋆₁ h) (f ⋆₁ (g ⋆₁ h))
    α⁺ {x}{y}{z}{w} f g h = α x y z w .trans .N-ob (f , g , h)

    α⁻ : ∀ {x y z w}
      (f : 1Cell x y) (g : 1Cell y z) (h : 1Cell z w)
      → 2Cell (f ⋆₁ (g ⋆₁ h)) ((f ⋆₁ g) ⋆₁ h)
    α⁻ {x}{y}{z}{w} f g h = α x y z w .nIso (f , g , h) .inv

    field
      triangle : (x y z : ob)
        (f : 1Cell x y) (g : 1Cell y z)
        → α⁺ f id₁ g ⋆₂ (f ◁w λ⁺ g) ≡ (ρ⁺ f ▷w g)

      pentagon : (x y z w v : ob)
        (f : 1Cell x y) (g : 1Cell y z)
        (h : 1Cell z w) (k : 1Cell w v)
        →    (α⁺ f g h ▷w k) ⋆₂ α⁺ f (g ⋆₁ h) k ⋆₂ (f ◁w α⁺ g h k)
          ≡  α⁺ (f ⋆₁ g) h k ⋆₂ α⁺ f g (h ⋆₁ k)
