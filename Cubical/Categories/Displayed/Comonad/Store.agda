{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Comonad.Store where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More

private
  variable
    ℓ ℓ' : Level

open BinProduct
open NatTrans

module _ {C : Category ℓ ℓ'} (bp : BinProducts C) where
  open Category C
  open Notation C bp
  open Functor
  open Categoryᴰ

  -- TODO: This can probably more generally be defined as a kind of
  -- indexed Kleisli category.
  Store : Categoryᴰ C ℓ ℓ'
  ob[ Store ] Γ = ob
  Store .Hom[_][_,_] {x = Γ} γ A B = C [ Γ × A , B ]
  Store .idᴰ = π₂
  Store ._⋆ᴰ_ {f = γ} f g = ((π₁ ⋆ γ) ,p f) ⋆ g
  Store .⋆IdLᴰ f =
    cong₂ _⋆_ (cong₂ _,p_ (⋆IdR _) refl ∙ sym ×η') refl
    ∙ ⋆IdL _
  Store .⋆IdRᴰ f = ×β₂
  -- Cartesian category solver would be nice here
  Store .⋆Assocᴰ f g h =
    cong₂ _⋆_
      ( cong₂ _,p_
        ( sym (⋆Assoc _ _ _)
        ∙ cong₂ _⋆_ (sym ×β₁) refl
        ∙ ⋆Assoc _ _ _)
        refl
      ∙ sym ,p-natural)
      refl
    ∙ ⋆Assoc _ _ _
  Store .isSetHomᴰ = isSetHom

  open import Cubical.Categories.Displayed.Fibration
  open import Cubical.Categories.Displayed.Presheaf

  open UniversalElementᴰ
  isFibStore : isFibration Store
  isFibStore {d = Δ} ((Γ , A) , f) .vertexᴰ = A
  isFibStore {d = Δ} ((Γ , A) , f) .elementᴰ .fst .fst = f
  isFibStore {d = Δ} ((Γ , A) , f) .elementᴰ .fst .snd = π₂
  isFibStore {d = Δ} ((Γ , A) , f) .elementᴰ .snd = refl
  isFibStore {d = Δ} ((Γ , A) , f) .universalᴰ Θ {f = δ} = isoToIsEquiv (iso _
    (λ ((γ , f) , commutes) → f)
    (λ b → Σ≡Prop (λ _ → isSetHom _ _)
      (ΣPathP (cong₂ _⋆_ (sym (⋆IdR _)) refl ∙ sym (b .snd) ∙ ⋆IdL _
        , ×β₂)))
    λ a → ×β₂)

  -- Then a strong monad is a displayed monad over the identity that is preserved by the fibration??

  open import Cubical.Categories.Displayed.Limits.BinProduct
  open import Cubical.Categories.Adjoint.UniversalElements
  private
    variable
      ℓᴰ ℓᴰ' : Level

  bp' = BinProductsToRightAdjoint' C bp
  module _ {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'} (bpᴰ : BinProductsᴰ Cᴰ bp') where
    module Cᴰ = Categoryᴰ Cᴰ
    open BinProductsᴰNotation Cᴰ bp' bpᴰ
    Storeᴰ : Categoryᴰ (∫C (weakenᴰ Store Cᴰ)) ℓᴰ ℓᴰ'
    Storeᴰ .ob[_] ((Γ , A) , Γᴰ) = Cᴰ.ob[ A ]
    Storeᴰ .Hom[_][_,_] {x = ((Δ , B) , Δᴰ)} ((γ , f) , γᴰ) Bᴰ Aᴰ = Cᴰ [ f ][ Δᴰ ×ᴰ Bᴰ , Aᴰ ]
    Storeᴰ .idᴰ {x = ((Γ , A), Γᴰ)}= π₂ᴰ
    Storeᴰ ._⋆ᴰ_ {f = ((γ , _) , γᴰ)} fᴰ gᴰ = ((π₁ᴰ Cᴰ.⋆ᴰ γᴰ) ,ᴰ fᴰ) Cᴰ.⋆ᴰ gᴰ
    Storeᴰ .⋆IdLᴰ fᴰ = {! lem!}
      where
      -- (Cᴰ ._⋆ᴰ_
      --  (Cᴰ ._⋆ᴰ_ π₁ᴰ (∫C (weakenᴰ Store Cᴰ) .Category.id .snd) ,ᴰ π₂ᴰ) fᴰ)
      -- fᴰ
        lem =
          compPathP (λ i → (Cᴰ.⋆IdRᴰ π₁ᴰ i ,ᴰ π₂ᴰ) Cᴰ.⋆ᴰ fᴰ)
          (compPathP {!(λ i → (Cᴰ.⋆IdRᴰ π₁ᴰ i ,ᴰ π₂ᴰ) Cᴰ.⋆ᴰ fᴰ)!}
          (Cᴰ.⋆IdLᴰ fᴰ))
    Storeᴰ .⋆IdRᴰ fᴰ = ×β₂ᴰ
    Storeᴰ .⋆Assocᴰ = {!!}
    Storeᴰ .isSetHomᴰ = Cᴰ.isSetHomᴰ
