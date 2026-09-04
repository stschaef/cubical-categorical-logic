{- Bᵒᵖ: 1-cells reversed, 2-cells not. -}
module Cubical.Categories.Bicategory.Constructions.Op where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More hiding (α)
open import Cubical.Categories.Instances.BinProduct

open import Cubical.Categories.Bicategory.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

open Functor
open NatTrans
open NatIso
open isIso
open Bicategory

module _ (B : Bicategory ℓ ℓ' ℓ'') where
  private
    module B = Bicategory B

  Opᴮ : Bicategory ℓ ℓ' ℓ''
  Opᴮ .ob = B.ob
  Opᴮ .Hom[_,_] x y = B.Hom[ y , x ]
  Opᴮ .id {x} = B.id {x}
  Opᴮ .seq x y z = B.seq z y x ∘F Sym

  Opᴮ .λU x y .trans .N-ob (_ , f) = B.ρ⁺ f
  Opᴮ .λU x y .trans .N-hom (_ , α) = B.ρU y x .trans .N-hom (α , _)
  Opᴮ .λU x y .nIso (_ , f) = B.ρU y x .nIso (f , _)

  Opᴮ .ρU x y .trans .N-ob (f , _) = B.λ⁺ f
  Opᴮ .ρU x y .trans .N-hom (α , _) = B.λU y x .trans .N-hom (_ , α)
  Opᴮ .ρU x y .nIso (f , _) = B.λU y x .nIso (_ , f)

  Opᴮ .α x y z w .trans .N-ob (f , g , h) = B.α⁻ h g f
  Opᴮ .α x y z w .trans .N-hom (φ , γ , ψ) =
    symNatIso (B.α w z y x) .trans .N-hom (ψ , γ , φ)
  Opᴮ .α x y z w .nIso (f , g , h) = symNatIso (B.α w z y x) .nIso (h , g , f)

  Opᴮ .triangle x y z f g =
    sym (⋆InvLMove (NatIsoAt (B.α z y y x) (g , B.id₁ , f))
                   (B.triangle z y x g f))

  Opᴮ .pentagon x y z w v f g h k =
      sym (B.⋆₂Assoc _ _ _)
    ∙ cong (λ i → i .snd .inv)
        (CatIso≡ (⋆Iso cI (⋆Iso bI aI)) (⋆Iso eI dI)
                 (B.pentagon v w z y x k h g f))
    where
    aI = F-Iso {F = B.seq v w x}
           (CatIso× B.Hom[ v , w ] B.Hom[ w , x ]
             idCatIso (NatIsoAt (B.α w z y x) (h , g , f)))
    bI = NatIsoAt (B.α v w y x) (k , h B.⋆₁ g , f)
    cI = F-Iso {F = B.seq v y x}
           (CatIso× B.Hom[ v , y ] B.Hom[ y , x ]
             (NatIsoAt (B.α v w z y) (k , h , g)) idCatIso)
    dI = NatIsoAt (B.α v w z x) (k , h , g B.⋆₁ f)
    eI = NatIsoAt (B.α v z y x) (k B.⋆₁ h , g , f)

infix 30 _^opᴮ

_^opᴮ : Bicategory ℓ ℓ' ℓ'' → Bicategory ℓ ℓ' ℓ''
B ^opᴮ = Opᴮ B
