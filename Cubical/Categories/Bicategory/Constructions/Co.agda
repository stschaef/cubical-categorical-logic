{-# OPTIONS --lossy-unification #-}
{- Bᶜᵒ: 2-cells reversed, 1-cells not. -}
module Cubical.Categories.Bicategory.Constructions.Co where

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

  Coᴮ : Bicategory ℓ ℓ' ℓ''
  Coᴮ .ob = B.ob
  Coᴮ .Hom[_,_] x y = B.Hom[ x , y ] ^op

  Coᴮ .id {x} .F-ob _ = B.id₁
  Coᴮ .id {x} .F-hom p = B.id {x} .F-hom p
  Coᴮ .id {x} .F-id = B.id {x} .F-id
  Coᴮ .id {x} .F-seq p q =
      cong (B.id {x} .F-hom)
        (isProp→isSet isPropUnit* _ _ (p ∙ q) (q ∙ p))
    ∙ B.id {x} .F-seq q p

  Coᴮ .seq x y z .F-ob (f , g) = f B.⋆₁ g
  Coᴮ .seq x y z .F-hom (α , β) = α B.⋆ₕ β
  Coᴮ .seq x y z .F-id = B.seq x y z .F-id
  Coᴮ .seq x y z .F-seq (α , β) (α' , β') =
    B.seq x y z .F-seq (α' , β') (α , β)

  Coᴮ .λU x y .trans .N-ob (_ , f) = B.λ⁻ f
  Coᴮ .λU x y .trans .N-hom (p , α) =
    sym (symNatIso (B.λU x y) .trans .N-hom (p , α))
  Coᴮ .λU x y .nIso (_ , f) .inv = B.λ⁺ f
  Coᴮ .λU x y .nIso (_ , f) .sec = B.λU x y .nIso (tt* , f) .sec
  Coᴮ .λU x y .nIso (_ , f) .ret = B.λU x y .nIso (tt* , f) .ret

  Coᴮ .ρU x y .trans .N-ob (f , _) = B.ρ⁻ f
  Coᴮ .ρU x y .trans .N-hom (α , p) =
    sym (symNatIso (B.ρU x y) .trans .N-hom (α , p))
  Coᴮ .ρU x y .nIso (f , _) .inv = B.ρ⁺ f
  Coᴮ .ρU x y .nIso (f , _) .sec = B.ρU x y .nIso (f , tt*) .sec
  Coᴮ .ρU x y .nIso (f , _) .ret = B.ρU x y .nIso (f , tt*) .ret

  Coᴮ .α x y z w .trans .N-ob (f , g , h) = B.α⁻ f g h
  Coᴮ .α x y z w .trans .N-hom (φ , γ , ψ) =
    sym (symNatIso (B.α x y z w) .trans .N-hom (φ , γ , ψ))
  Coᴮ .α x y z w .nIso (f , g , h) .inv = B.α⁺ f g h
  Coᴮ .α x y z w .nIso (f , g , h) .sec = B.α x y z w .nIso (f , g , h) .sec
  Coᴮ .α x y z w .nIso (f , g , h) .ret = B.α x y z w .nIso (f , g , h) .ret

  Coᴮ .triangle x y z f g =
    cong (λ i → i .snd .inv)
      (CatIso≡ (⋆Iso aI bI) cI (B.triangle x y z f g))
    where
    aI = NatIsoAt (B.α x y y z) (f , B.id₁ , g)
    bI = F-Iso {F = B.seq x y z}
           (CatIso× B.Hom[ x , y ] B.Hom[ y , z ]
             idCatIso (NatIsoAt (B.λU y z) (tt* , g)))
    cI = F-Iso {F = B.seq x y z}
           (CatIso× B.Hom[ x , y ] B.Hom[ y , z ]
             (NatIsoAt (B.ρU x y) (f , tt*)) idCatIso)

  Coᴮ .pentagon x y z w v f g h k =
    cong (λ i → i .snd .inv)
      (CatIso≡ (⋆Iso aI (⋆Iso bI cI)) (⋆Iso dI eI)
               (B.pentagon x y z w v f g h k))
    where
    aI = F-Iso {F = B.seq x w v}
           (CatIso× B.Hom[ x , w ] B.Hom[ w , v ]
             (NatIsoAt (B.α x y z w) (f , g , h)) idCatIso)
    bI = NatIsoAt (B.α x y w v) (f , g B.⋆₁ h , k)
    cI = F-Iso {F = B.seq x y v}
           (CatIso× B.Hom[ x , y ] B.Hom[ y , v ]
             idCatIso (NatIsoAt (B.α y z w v) (g , h , k)))
    dI = NatIsoAt (B.α x z w v) (f B.⋆₁ g , h , k)
    eI = NatIsoAt (B.α x y z v) (f , g , h B.⋆₁ k)

infix 30 _^coᴮ

_^coᴮ : Bicategory ℓ ℓ' ℓ'' → Bicategory ℓ ℓ' ℓ''
B ^coᴮ = Coᴮ B
