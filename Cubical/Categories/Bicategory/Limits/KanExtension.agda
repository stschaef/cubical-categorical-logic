{-# OPTIONS --lossy-unification #-}
{-
  Kan extensions in a bicategory.

  A Kan extension's vertex is a 1-cell, not a 0-cell, so -- unlike
  terminal objects, products, inserters and commas -- it is not a
  `BiuniversalElement`: it is a `UniversalElement` one dimension down,
  of a presheaf on the hom-category `B [ b , c ]`.  `RanPsh j f` sends
  `g : b → c` to the set of 2-cells `j ⋆₁ g ⇒ f`; its universal
  element is `(Ran j f , ε)`.  That presheaf and its notation come
  from `Limits/Extension.agda`: a Ran is a right adjoint to `precomp
  j`.  Left Kan extensions are right Kan extensions in `B ^coᴮ`.
-}
module Cubical.Categories.Bicategory.Limits.KanExtension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Limits.Extension
open import Cubical.Categories.Bicategory.Properties
open import Cubical.Categories.Bicategory.Properties.Coherence
open import Cubical.Categories.Bicategory.Constructions.Co
open import Cubical.Categories.Bicategory.Limits.Product
open import Cubical.Categories.Bicategory.Limits.Inserter
open import Cubical.Categories.Bicategory.Limits.Comma

private
  variable
    ℓ ℓ' ℓ'' : Level

open Functor
open NatIso

module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  module _ {a b c : B.0Cell} (j : B.1Cell a b) (f : B.1Cell a c) where
    -- g ↦ 2-cells j ⋆₁ g ⇒ f, contravariant by whiskering with j
    RanPsh : Presheaf B.Hom[ b , c ] ℓ''
    RanPsh = RanPshᴮ B j f

    Ranᴮ : Type (ℓ-max ℓ' ℓ'')
    Ranᴮ = RightExtensionᴮ B j f

  -- all right Kan extensions along a fixed j, and along everything
  hasRansAlongᴮ : {a b : B.0Cell} (j : B.1Cell a b) → Type _
  hasRansAlongᴮ {a} j = {c : B.0Cell} (f : B.1Cell a c) → Ranᴮ j f

  hasRansᴮ : Type _
  hasRansᴮ = {a b : B.0Cell} (j : B.1Cell a b) → hasRansAlongᴮ j

module RanᴮNotation {B : Bicategory ℓ ℓ' ℓ''}
  {a b c : Bicategory.0Cell B} {j : Bicategory.1Cell B a b}
  {f : Bicategory.1Cell B a c} (R : Ranᴮ B j f) where
  private
    module B = Bicategory B
  open RightExtensionᴮNotation R public

  ran : B.1Cell b c
  ran = vertex

  -- the counit
  ranε : B.2Cell (j B.⋆₁ ran) f
  ranε = element

  -- the comparison map, of which `universal` says it is an equivalence
  ranCompare : {g : B.1Cell b c} → B.2Cell g ran → B.2Cell (j B.⋆₁ g) f
  ranCompare = compare

  ranIntro : {g : B.1Cell b c} → B.2Cell (j B.⋆₁ g) f → B.2Cell g ran
  ranIntro = intro

  ranβ : {g : B.1Cell b c} (θ : B.2Cell (j B.⋆₁ g) f)
    → ranCompare (ranIntro θ) ≡ θ
  ranβ θ = β

  ranη : {g : B.1Cell b c} (α : B.2Cell g ran)
    → α ≡ ranIntro (ranCompare α)
  ranη α = η

  ranExt : {g : B.1Cell b c} {α γ : B.2Cell g ran}
    → ranCompare α ≡ ranCompare γ → α ≡ γ
  ranExt = extensionality

  -- the analogue of `ff`: the comparison is an equivalence at every
  -- probe 1-cell, and everything above is derived from it
  ffRan : (g : B.1Cell b c) → isEquiv (ranCompare {g})
  ffRan = ff

  ranIso : (g : B.1Cell b c) → Iso (B.2Cell g ran) (B.2Cell (j B.⋆₁ g) f)
  ranIso = compareIso

  -- the counit whiskered by a 1-cell out of c, i.e. the candidate
  -- counit exhibiting `ran ⋆₁ m` as a Ran of `f ⋆₁ m`
  ranεPost : {d : B.0Cell} (m : B.1Cell c d)
    → B.2Cell (j B.⋆₁ (ran B.⋆₁ m)) (f B.⋆₁ m)
  ranεPost m = B.α⁻ j ran m B.⋆₂ (ranε B.▷w m)

module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  -- Absolute: every postcomposite `ran ⋆₁ m` is again a right Kan
  -- extension, with the whiskered counit.
  isAbsoluteRanᴮ : {a b c : B.0Cell} {j : B.1Cell a b} {f : B.1Cell a c}
    → Ranᴮ B j f → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  isAbsoluteRanᴮ {b = b} {c} {j} {f} R = {d : B.0Cell} (m : B.1Cell c d)
    → isRightExtensionᴮ B j (RanᴮNotation.ran R B.⋆₁ m)
        (RanᴮNotation.ranεPost R m)

  -- Ran along the identity is the 1-cell itself, with counit λ⁺.
  ranId : {a c : B.0Cell} (f : B.1Cell a c) → Ranᴮ B B.id₁ f
  ranId {a} {c} f .UniversalElement.vertex = f
  ranId {a} {c} f .UniversalElement.element = B.λ⁺ f
  ranId {a} {c} f .UniversalElement.universal g = isoToIsEquiv theIso
    where
    unit : B.λ⁻ g B.⋆₂ B.λ⁺ g ≡ B.id₂
    unit = B.λU a c .nIso (tt* , g) .Cubical.Categories.Category.isIso.sec

    cancel : (B.id₁ B.◁w B.λ⁻ g) B.⋆₂ B.λ⁺ (B.id₁ B.⋆₁ g) ≡ B.id₂
    cancel =
        cong ((B.id₁ B.◁w B.λ⁻ g) B.⋆₂_) (sym (◁λ⁺ B g))
      ∙ sym (◁wSeq B B.id₁ (B.λ⁻ g) (B.λ⁺ g))
      ∙ cong (B.id₁ B.◁w_) unit
      ∙ B.◁wId B.id₁

    theIso : Iso (B.2Cell g f) (B.2Cell (B.id₁ B.⋆₁ g) f)
    theIso .Iso.fun α = (B.id₁ B.◁w α) B.⋆₂ B.λ⁺ f
    theIso .Iso.inv θ = B.λ⁻ g B.⋆₂ θ
    theIso .Iso.sec θ =
        cong (B._⋆₂ B.λ⁺ f) (◁wSeq B B.id₁ (B.λ⁻ g) θ)
      ∙ B.⋆₂Assoc _ _ _
      ∙ cong ((B.id₁ B.◁w B.λ⁻ g) B.⋆₂_) (λ-nat B θ)
      ∙ sym (B.⋆₂Assoc _ _ _)
      ∙ cong (B._⋆₂ θ) cancel
      ∙ B.⋆₂IdL θ
    theIso .Iso.ret α =
        cong (B.λ⁻ g B.⋆₂_) (λ-nat B α)
      ∙ sym (B.⋆₂Assoc _ _ _)
      ∙ cong (B._⋆₂ α) unit
      ∙ B.⋆₂IdL α

  -- … and it is absolute: whiskering λ⁺ is λ⁺ at the composite.
  ranIdAbsolute : {a c : B.0Cell} (f : B.1Cell a c)
    → isAbsoluteRanᴮ (ranId f)
  ranIdAbsolute {a} {c} f {d} m =
    subst (isUniversal B.Hom[ a , d ] (RanPsh B B.id₁ (f B.⋆₁ m))
            (f B.⋆₁ m))
      (sym (λ⋆₁ B f m))
      (UniversalElement.universal (ranId (f B.⋆₁ m)))

  -- Lan in B is Ran in B ^coᴮ: reversing 2-cells turns the presheaf
  -- g ↦ (j ⋆₁ g ⇒ f) into g ↦ (f ⇒ j ⋆₁ g), and a universal element
  -- of the latter in Hom[ b , c ] ^op is exactly a left extension.
  Lanᴮ : {a b c : B.0Cell} (j : B.1Cell a b) (f : B.1Cell a c)
    → Type (ℓ-max ℓ' ℓ'')
  Lanᴮ j f = Ranᴮ (B ^coᴮ) j f

  hasLansAlongᴮ : {a b : B.0Cell} (j : B.1Cell a b) → Type _
  hasLansAlongᴮ j = hasRansAlongᴮ (B ^coᴮ) j

  hasLansᴮ : Type _
  hasLansᴮ = hasRansᴮ (B ^coᴮ)

module LanᴮNotation {B : Bicategory ℓ ℓ' ℓ''}
  {a b c : Bicategory.0Cell B} {j : Bicategory.1Cell B a b}
  {f : Bicategory.1Cell B a c} (L : Lanᴮ B j f) where
  private
    module B = Bicategory B
  open RanᴮNotation L public
    using (universal; universalIso)
    renaming (ran to lan; ranε to lanη; ranIntro to lanIntro)

  -- the unit, with B's own 2-cell direction restored
  lanηᴮ : B.2Cell f (j B.⋆₁ lan)
  lanηᴮ = lanη

  lanCompare : {g : B.1Cell b c} → B.2Cell lan g → B.2Cell f (j B.⋆₁ g)
  lanCompare α = lanηᴮ B.⋆₂ (j B.◁w α)

  lanIntroᴮ : {g : B.1Cell b c} → B.2Cell f (j B.⋆₁ g) → B.2Cell lan g
  lanIntroᴮ = lanIntro

  lanβ : {g : B.1Cell b c} (θ : B.2Cell f (j B.⋆₁ g))
    → lanCompare (lanIntroᴮ θ) ≡ θ
  lanβ θ = RanᴮNotation.ranβ L θ

  lanη-rule : {g : B.1Cell b c} (α : B.2Cell lan g)
    → α ≡ lanIntroᴮ (lanCompare α)
  lanη-rule α = RanᴮNotation.ranη L α

  lanExt : {g : B.1Cell b c} {α γ : B.2Cell lan g}
    → lanCompare α ≡ lanCompare γ → α ≡ γ
  lanExt = RanᴮNotation.ranExt L

  ffLan : (g : B.1Cell b c) → isEquiv (lanCompare {g})
  ffLan g = universal g

  lanIso : (g : B.1Cell b c) → Iso (B.2Cell lan g) (B.2Cell f (j B.⋆₁ g))
  lanIso g = universalIso g

-- Pointwise right Kan extensions.  `Commaᴮ` is stated relative to a
-- chosen binary product, so the comma object is carried explicitly as
-- an argument here rather than assumed: a bicategory with no products
-- simply has no `CommaOverᴮ` to feed these definitions.
module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  CommaOverᴮ : {x a b : B.0Cell} (k : B.1Cell x b) (j : B.1Cell a b)
    → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  CommaOverᴮ {x} {a} k j =
    Σ[ P ∈ BinProductᴮ B x a ] Commaᴮ B P k j

  module _ {a b c : B.0Cell} {j : B.1Cell a b} {f : B.1Cell a c}
    (R : Ranᴮ B j f) {x : B.0Cell} (k : B.1Cell x b)
    (Kom : CommaOverᴮ k j) where
    private
      module R = RanᴮNotation R
      module K = CommaᴮNotation {P = Kom .fst} {f = k} {g = j} (Kom .snd)

    -- p ⋆₁ (k ⋆₁ ran) ⇒ (p ⋆₁ k) ⋆₁ ran ⇒ (q ⋆₁ j) ⋆₁ ran
    --              ⇒ q ⋆₁ (j ⋆₁ ran) ⇒ q ⋆₁ f
    ranCommaCounit
      : B.2Cell (K.commaπ₁ᴮ B.⋆₁ (k B.⋆₁ R.ran)) (K.commaπ₂ᴮ B.⋆₁ f)
    ranCommaCounit =
        B.α⁻ K.commaπ₁ᴮ k R.ran
      B.⋆₂ (K.commaθᴮ B.▷w R.ran)
      B.⋆₂ B.α⁺ K.commaπ₂ᴮ j R.ran
      B.⋆₂ (K.commaπ₂ᴮ B.◁w R.ranε)

    -- `k ⋆₁ ran` is the right Kan extension of `q ⋆₁ f` along `p`
    isPointwiseAtᴮ : Type (ℓ-max ℓ' ℓ'')
    isPointwiseAtᴮ =
      isRightExtensionᴮ B K.commaπ₁ᴮ (k B.⋆₁ R.ran) ranCommaCounit

  isPointwiseRanᴮ : {a b c : B.0Cell} {j : B.1Cell a b} {f : B.1Cell a c}
    (R : Ranᴮ B j f)
    (K : {x : B.0Cell} (k : B.1Cell x b) → CommaOverᴮ k j)
    → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  isPointwiseRanᴮ {b = b} R K =
    {x : B.0Cell} (k : B.1Cell x b) → isPointwiseAtᴮ R k (K k)

  -- The hypothesis is satisfiable: products and inserters give commas.
  commaOverᴮ : (P : (x a : B.0Cell) → BinProductᴮ B x a)
    (ins : hasInsertersᴮ B) {x a b : B.0Cell}
    (k : B.1Cell x b) (j : B.1Cell a b) → CommaOverᴮ k j
  commaOverᴮ P ins {x} {a} k j =
    P x a , commaFromInsertersᴮ B ins (P x a) k j

-- Duals, by instantiating the right-extension notions at B ^coᴮ.
module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  isAbsoluteLanᴮ : {a b c : B.0Cell} {j : B.1Cell a b} {f : B.1Cell a c}
    → Lanᴮ B j f → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  isAbsoluteLanᴮ = isAbsoluteRanᴮ (B ^coᴮ)

  -- Lan along the identity is the 1-cell itself, and is absolute.
  lanId : {a c : B.0Cell} (f : B.1Cell a c) → Lanᴮ B B.id₁ f
  lanId = ranId (B ^coᴮ)

  lanIdAbsolute : {a c : B.0Cell} (f : B.1Cell a c)
    → isAbsoluteLanᴮ (lanId f)
  lanIdAbsolute = ranIdAbsolute (B ^coᴮ)

  -- Pointwiseness for Lan uses comma objects formed in B ^coᴮ:
  -- reversing 2-cells reverses the comma square, so a `CommaOverᴮ
  -- (B ^coᴮ) k j` is the comma object of j and k in B.
  isPointwiseLanᴮ : {a b c : B.0Cell} {j : B.1Cell a b} {f : B.1Cell a c}
    (L : Lanᴮ B j f)
    (K : {x : B.0Cell} (k : B.1Cell x b) → CommaOverᴮ (B ^coᴮ) k j)
    → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  isPointwiseLanᴮ = isPointwiseRanᴮ (B ^coᴮ)

-- An adjunction f ⊣ u exhibits u as a left Kan extension of id₁ along
-- f.  The adjunction data is taken as explicit arguments so that this
-- file does not depend on `Bicategory/Adjunction.agda`.
module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  module AdjunctionLan {a b : B.0Cell}
    (f : B.1Cell a b) (u : B.1Cell b a)
    (η : B.2Cell B.id₁ (f B.⋆₁ u)) (ε : B.2Cell (u B.⋆₁ f) B.id₁)
    (triᶠ : B.λ⁻ f B.⋆₂ (η B.▷w f) B.⋆₂ B.α⁺ f u f B.⋆₂ (f B.◁w ε)
              B.⋆₂ B.ρ⁺ f ≡ B.id₂)
    (triᵘ : B.ρ⁻ u B.⋆₂ (u B.◁w η) B.⋆₂ B.α⁻ u f u B.⋆₂ (ε B.▷w u)
              B.⋆₂ B.λ⁺ u ≡ B.id₂)
    where

    -- the transpose and its candidate inverse
    Ψ : (g : B.1Cell b a) → B.2Cell u g → B.2Cell B.id₁ (f B.⋆₁ g)
    Ψ g α = η B.⋆₂ (f B.◁w α)

    Φ : (g : B.1Cell b a) → B.2Cell B.id₁ (f B.⋆₁ g) → B.2Cell u g
    Φ g θ = B.ρ⁻ u B.⋆₂ (u B.◁w θ) B.⋆₂ B.α⁻ u f g
              B.⋆₂ (ε B.▷w g) B.⋆₂ B.λ⁺ g

    private
      tailA : {g : B.1Cell b a} (α : B.2Cell u g)
        →   (u B.◁w (η B.⋆₂ (f B.◁w α))) B.⋆₂ B.α⁻ u f g
              B.⋆₂ (ε B.▷w g) B.⋆₂ B.λ⁺ g
          ≡ (u B.◁w η) B.⋆₂ B.α⁻ u f u B.⋆₂ (ε B.▷w u)
              B.⋆₂ B.λ⁺ u B.⋆₂ α
      tailA {g} α =
          B.⟨ ◁wSeq B u η (f B.◁w α) ⟩⋆₂⟨⟩
        ∙ B.⋆₂Assoc _ _ _
        ∙ B.⟨⟩⋆₂⟨ pushr B (α⁻natR B u f α) ((ε B.▷w g) B.⋆₂ B.λ⁺ g) ⟩
        ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ pushr B (sym (▷◁exch B ε α)) (B.λ⁺ g) ⟩ ⟩
        ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ λ-nat B α ⟩ ⟩ ⟩

    ΦΨ : {g : B.1Cell b a} (α : B.2Cell u g) → Φ g (Ψ g α) ≡ α
    ΦΨ {g} α = B.⟨⟩⋆₂⟨ tailA α ⟩ ∙ rw5 B triᵘ α ∙ B.⋆₂IdL α

    private
      -- the counit-side composite that the triangle for f collapses
      core : (g : B.1Cell b a)
        → B.2Cell (B.id₁ B.⋆₁ (f B.⋆₁ g)) (f B.⋆₁ g)
      core g = (η B.▷w (f B.⋆₁ g)) B.⋆₂ B.α⁺ f u (f B.⋆₁ g)
                 B.⋆₂ (f B.◁w B.α⁻ u f g) B.⋆₂ (f B.◁w (ε B.▷w g))
                 B.⋆₂ (f B.◁w B.λ⁺ g)

      whiskerTri : (g : B.1Cell b a)
        →   ((B.λ⁻ f B.⋆₂ (η B.▷w f) B.⋆₂ B.α⁺ f u f B.⋆₂ (f B.◁w ε)
                B.⋆₂ B.ρ⁺ f) B.▷w g)
          ≡ B.λ⁻ (f B.⋆₁ g) B.⋆₂ core g
      whiskerTri g =
          ▷5 B (B.λ⁻ f) (η B.▷w f) (B.α⁺ f u f) (f B.◁w ε) (B.ρ⁺ f) g
        ∙ B.⟨⟩⋆₂⟨ B.⟨ ▷⋆₁ B η f g ⟩⋆₂⟨⟩ ⟩
        ∙ B.⟨⟩⋆₂⟨ aR3 B _ _ _ _ ⟩
        ∙ B.⟨ ⋆InvRMove (αI B B.id₁ f g) (λ⁻⋆₁ B f g) ⟩⋆₂⟨⟩
        ∙ B.⋆₂Assoc _ _ _
        ∙ B.⟨⟩⋆₂⟨ pushn B
            (αI B B.id₁ f g .snd .Cubical.Categories.Category.isIso.sec) _
          ∙ B.⋆₂IdL _ ⟩
        ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ pushn B (pentP3 B f u f g) _
                          ∙ aR3 B _ _ _ _ ⟩ ⟩
        ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨
            pushr B (sym (α⁻natM B f ε g)) (B.ρ⁺ f B.▷w g) ⟩ ⟩ ⟩ ⟩
        ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨
            α⁻ρ▷ B f g ⟩ ⟩ ⟩ ⟩ ⟩

      coreEq : (g : B.1Cell b a) → core g ≡ B.λ⁺ (f B.⋆₁ g)
      coreEq g =
          sym (B.⋆₂IdL _)
        ∙ B.⟨ sym (B.λU a a .nIso (tt* , f B.⋆₁ g)
                     .Cubical.Categories.Category.isIso.ret) ⟩⋆₂⟨⟩
        ∙ B.⋆₂Assoc _ _ _
        ∙ B.⟨⟩⋆₂⟨ sym (whiskerTri g)
                ∙ cong (B._▷w g) triᶠ
                ∙ B.▷wId g ⟩
        ∙ B.⋆₂IdR _

    ΨΦ : {g : B.1Cell b a} (θ : B.2Cell B.id₁ (f B.⋆₁ g))
      → Ψ g (Φ g θ) ≡ θ
    ΨΦ {g} θ =
        B.⟨⟩⋆₂⟨ ◁5 B f (B.ρ⁻ u) (u B.◁w θ) (B.α⁻ u f g) (ε B.▷w g)
                     (B.λ⁺ g) ⟩
      ∙ B.⟨⟩⋆₂⟨ B.⟨ ρ⁻◁ B f u ⟩⋆₂⟨⟩ ⟩
      ∙ B.⟨⟩⋆₂⟨ B.⋆₂Assoc _ _ _ ⟩
      ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ B.⟨ ◁⋆₁ B θ u f ⟩⋆₂⟨⟩ ⟩ ⟩ ⟩
      ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ aR3 B _ _ _ _ ⟩ ⟩ ⟩
      ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ pushn B
          (αI B f u B.id₁ .snd .Cubical.Categories.Category.isIso.ret) _
        ∙ B.⋆₂IdL _ ⟩ ⟩
      ∙ pushr B (ρ⁻-nat B η) _
      ∙ B.⟨⟩⋆₂⟨ pushr B (▷◁exch B η θ) _ ⟩
      ∙ B.⟨⟩⋆₂⟨ B.⟨⟩⋆₂⟨ coreEq g ⟩ ⟩
      ∙ B.⟨⟩⋆₂⟨ λ-nat B θ ⟩
      ∙ pushn B (B.⟨⟩⋆₂⟨ λ⁺≡ρ⁺ B ⟩
                ∙ B.ρU a a .nIso (B.id₁ , tt*)
                    .Cubical.Categories.Category.isIso.sec) θ
      ∙ B.⋆₂IdL θ

    -- f ⊣ u exhibits u as the left Kan extension of id₁ along f, with
    -- the unit as its unit.  (Absoluteness is not proved here.)
    adjunctionLanᴮ : Lanᴮ B f (B.id₁ {a})
    adjunctionLanᴮ .UniversalElement.vertex = u
    adjunctionLanᴮ .UniversalElement.element = η
    adjunctionLanᴮ .UniversalElement.universal g = isoToIsEquiv transpose
      where
      transpose : Iso (B.2Cell u g) (B.2Cell B.id₁ (f B.⋆₁ g))
      transpose .Iso.fun = Ψ g
      transpose .Iso.inv = Φ g
      transpose .Iso.sec = ΨΦ
      transpose .Iso.ret = ΦΨ

-- Right Kan extensions compose: extending along j and then along j'
-- is extending along j ⋆₁ j'.
module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  module _ {a b b' c : B.0Cell} {j : B.1Cell a b} {j' : B.1Cell b b'}
    {f : B.1Cell a c} (R : Ranᴮ B j f)
    (R' : Ranᴮ B j' (RanᴮNotation.ran R)) where
    private
      module R = RanᴮNotation R
      module R' = RanᴮNotation R'

      elt : B.2Cell ((j B.⋆₁ j') B.⋆₁ R'.ran) f
      elt = B.α⁺ j j' R'.ran B.⋆₂ (j B.◁w R'.ranε) B.⋆₂ R.ranε

      αIso : (g : B.1Cell b' c)
        → Iso (B.2Cell (j B.⋆₁ (j' B.⋆₁ g)) f)
              (B.2Cell ((j B.⋆₁ j') B.⋆₁ g) f)
      αIso g .Iso.fun θ = B.α⁺ j j' g B.⋆₂ θ
      αIso g .Iso.inv θ = B.α⁻ j j' g B.⋆₂ θ
      αIso g .Iso.sec θ =
          sym (B.⋆₂Assoc _ _ _)
        ∙ B.⟨ αI B j j' g .snd .Cubical.Categories.Category.isIso.ret ⟩⋆₂⟨⟩
        ∙ B.⋆₂IdL θ
      αIso g .Iso.ret θ =
          sym (B.⋆₂Assoc _ _ _)
        ∙ B.⟨ αI B j j' g .snd .Cubical.Categories.Category.isIso.sec ⟩⋆₂⟨⟩
        ∙ B.⋆₂IdL θ

      cmp : (g : B.1Cell b' c)
        → Iso (B.2Cell g R'.ran) (B.2Cell ((j B.⋆₁ j') B.⋆₁ g) f)
      cmp g = Cubical.Foundations.Isomorphism.compIso (R'.ranIso g)
        (Cubical.Foundations.Isomorphism.compIso
          (R.ranIso (j' B.⋆₁ g)) (αIso g))

      cmpEq : (g : B.1Cell b' c) (α : B.2Cell g R'.ran)
        → cmp g .Iso.fun α ≡ ((j B.⋆₁ j') B.◁w α) B.⋆₂ elt
      cmpEq g α =
          B.⟨⟩⋆₂⟨ B.⟨ ◁wSeq B j (j' B.◁w α) R'.ranε ⟩⋆₂⟨⟩ ⟩
        ∙ B.⟨⟩⋆₂⟨ B.⋆₂Assoc _ _ _ ⟩
        ∙ sym (B.⋆₂Assoc _ _ _)
        ∙ B.⟨ sym (α⁺natR B j j' α) ⟩⋆₂⟨⟩
        ∙ B.⋆₂Assoc _ _ _

    ranSeqᴮ : Ranᴮ B (j B.⋆₁ j') f
    ranSeqᴮ .UniversalElement.vertex = R'.ran
    ranSeqᴮ .UniversalElement.element = elt
    ranSeqᴮ .UniversalElement.universal g =
      subst isEquiv (funExt (cmpEq g)) (isoToIsEquiv (cmp g))

-- The dual, by instantiating at B ^coᴮ.
module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  lanSeqᴮ : {a b b' c : B.0Cell} {j : B.1Cell a b} {j' : B.1Cell b b'}
    {f : B.1Cell a c} (L : Lanᴮ B j f)
    (L' : Lanᴮ B j' (RanᴮNotation.ran L)) → Lanᴮ B (j B.⋆₁ j') f
  lanSeqᴮ = ranSeqᴮ (B ^coᴮ)
