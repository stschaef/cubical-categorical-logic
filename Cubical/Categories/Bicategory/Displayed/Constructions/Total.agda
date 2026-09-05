{-# OPTIONS --lossy-unification #-}
{- The total bicategory of a displayed bicategory -}
module Cubical.Categories.Bicategory.Displayed.Constructions.Total where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Terminal
open import Cubical.Categories.Instances.TotalCategory
import Cubical.Categories.Instances.TotalCategory.Properties as TC
open import Cubical.Categories.Isomorphism

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More

open import Cubical.Categories.Bicategory.Base
open import Cubical.Categories.Bicategory.Displayed
open import Cubical.Categories.Bicategory.Functor.Lax
open import Cubical.Categories.Bicategory.Functor.Pseudo

private
  variable
    ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' ℓᴰ'' : Level

open Functor
open Functorᴰ
open NatTrans
open NatIso
open isIso
open NatTransᴰ
open NatIsoᴰ
open isIsoᴰ

module _ {B : Bicategory ℓ ℓ' ℓ''} (Bᴰ : Bicategoryᴰ B ℓᴰ ℓᴰ' ℓᴰ'') where
  private
    module B = Bicategory B
    module Bᴰ = Bicategoryᴰ Bᴰ

  open Bicategory

  ∫ᴮ : Bicategory (ℓ-max ℓ ℓᴰ) (ℓ-max ℓ' ℓᴰ') (ℓ-max ℓ'' ℓᴰ'')
  ∫ᴮ .ob = Σ B.ob Bᴰ.ob[_]
  ∫ᴮ .Hom[_,_] (_ , xᴰ) (_ , yᴰ) = ∫C Bᴰ.Homᴰ[ xᴰ , yᴰ ]

  -- identity 1-cell
  ∫ᴮ .id {_ , xᴰ} .F-ob _ = B.id .F-ob _ , Bᴰ.idᴰ .F-obᴰ _
  ∫ᴮ .id {_ , xᴰ} .F-hom _ = B.id .F-hom _ , Bᴰ.idᴰ .F-homᴰ _
  ∫ᴮ .id {_ , xᴰ} .F-id = ΣPathP (B.id .F-id , Bᴰ.idᴰ .F-idᴰ)
  ∫ᴮ .id {_ , xᴰ} .F-seq _ _ = ΣPathP (B.id .F-seq _ _ , Bᴰ.idᴰ .F-seqᴰ _ _)

  -- horizontal composition
  ∫ᴮ .seq _ _ _ .F-ob ((f , fᴰ) , (g , gᴰ)) =
    B.seq _ _ _ .F-ob (f , g) , Bᴰ.seqᴰ _ _ _ .F-obᴰ (fᴰ , gᴰ)
  ∫ᴮ .seq _ _ _ .F-hom ((β , βᴰ) , (γ , γᴰ)) =
    B.seq _ _ _ .F-hom (β , γ) , Bᴰ.seqᴰ _ _ _ .F-homᴰ (βᴰ , γᴰ)
  ∫ᴮ .seq _ _ _ .F-id =
    ΣPathP (B.seq _ _ _ .F-id , Bᴰ.seqᴰ _ _ _ .F-idᴰ)
  ∫ᴮ .seq _ _ _ .F-seq _ _ =
    ΣPathP (B.seq _ _ _ .F-seq _ _ , Bᴰ.seqᴰ _ _ _ .F-seqᴰ _ _)

  -- left unitor
  ∫ᴮ .λU (_ , xᴰ) (_ , yᴰ) .trans .N-ob (o , (f , fᴰ)) =
    B.λU _ _ .trans .N-ob (o , f) , Bᴰ.λUᴰ xᴰ yᴰ .transᴰ .N-obᴰ (_ , fᴰ)
  ∫ᴮ .λU (_ , xᴰ) (_ , yᴰ) .trans .N-hom (o , (β , βᴰ)) =
    ΣPathP ( B.λU _ _ .trans .N-hom (o , β)
           , Bᴰ.λUᴰ xᴰ yᴰ .transᴰ .N-homᴰ (_ , βᴰ) )
  ∫ᴮ .λU (_ , xᴰ) (_ , yᴰ) .nIso (o , (f , fᴰ)) .inv =
    B.λU _ _ .nIso (o , f) .inv , Bᴰ.λUᴰ xᴰ yᴰ .nIsoᴰ (_ , fᴰ) .invᴰ
  ∫ᴮ .λU (_ , xᴰ) (_ , yᴰ) .nIso (o , (f , fᴰ)) .sec =
    ΣPathP ( B.λU _ _ .nIso (o , f) .sec
           , Bᴰ.λUᴰ xᴰ yᴰ .nIsoᴰ (_ , fᴰ) .secᴰ )
  ∫ᴮ .λU (_ , xᴰ) (_ , yᴰ) .nIso (o , (f , fᴰ)) .ret =
    ΣPathP ( B.λU _ _ .nIso (o , f) .ret
           , Bᴰ.λUᴰ xᴰ yᴰ .nIsoᴰ (_ , fᴰ) .retᴰ )

  -- right unitor
  ∫ᴮ .ρU (_ , xᴰ) (_ , yᴰ) .trans .N-ob ((f , fᴰ) , o) =
    B.ρU _ _ .trans .N-ob (f , o) , Bᴰ.ρUᴰ xᴰ yᴰ .transᴰ .N-obᴰ (fᴰ , _)
  ∫ᴮ .ρU (_ , xᴰ) (_ , yᴰ) .trans .N-hom ((β , βᴰ) , o) =
    ΣPathP ( B.ρU _ _ .trans .N-hom (β , o)
           , Bᴰ.ρUᴰ xᴰ yᴰ .transᴰ .N-homᴰ (βᴰ , _) )
  ∫ᴮ .ρU (_ , xᴰ) (_ , yᴰ) .nIso ((f , fᴰ) , o) .inv =
    B.ρU _ _ .nIso (f , o) .inv , Bᴰ.ρUᴰ xᴰ yᴰ .nIsoᴰ (fᴰ , _) .invᴰ
  ∫ᴮ .ρU (_ , xᴰ) (_ , yᴰ) .nIso ((f , fᴰ) , o) .sec =
    ΣPathP ( B.ρU _ _ .nIso (f , o) .sec
           , Bᴰ.ρUᴰ xᴰ yᴰ .nIsoᴰ (fᴰ , _) .secᴰ )
  ∫ᴮ .ρU (_ , xᴰ) (_ , yᴰ) .nIso ((f , fᴰ) , o) .ret =
    ΣPathP ( B.ρU _ _ .nIso (f , o) .ret
           , Bᴰ.ρUᴰ xᴰ yᴰ .nIsoᴰ (fᴰ , _) .retᴰ )

  -- associator
  ∫ᴮ .α (_ , xᴰ) (_ , yᴰ) (_ , zᴰ) (_ , wᴰ) .trans .N-ob
      ((f , fᴰ) , (g , gᴰ) , (h , hᴰ)) =
      B.α _ _ _ _ .trans .N-ob (f , g , h)
    , Bᴰ.αᴰ xᴰ yᴰ zᴰ wᴰ .transᴰ .N-obᴰ (fᴰ , gᴰ , hᴰ)
  ∫ᴮ .α (_ , xᴰ) (_ , yᴰ) (_ , zᴰ) (_ , wᴰ) .trans .N-hom
      ((β , βᴰ) , (γ , γᴰ) , (δ , δᴰ)) =
    ΣPathP ( B.α _ _ _ _ .trans .N-hom (β , γ , δ)
           , Bᴰ.αᴰ xᴰ yᴰ zᴰ wᴰ .transᴰ .N-homᴰ (βᴰ , γᴰ , δᴰ) )
  ∫ᴮ .α (_ , xᴰ) (_ , yᴰ) (_ , zᴰ) (_ , wᴰ) .nIso
      ((f , fᴰ) , (g , gᴰ) , (h , hᴰ)) .inv =
      B.α _ _ _ _ .nIso (f , g , h) .inv
    , Bᴰ.αᴰ xᴰ yᴰ zᴰ wᴰ .nIsoᴰ (fᴰ , gᴰ , hᴰ) .invᴰ
  ∫ᴮ .α (_ , xᴰ) (_ , yᴰ) (_ , zᴰ) (_ , wᴰ) .nIso
      ((f , fᴰ) , (g , gᴰ) , (h , hᴰ)) .sec =
    ΣPathP ( B.α _ _ _ _ .nIso (f , g , h) .sec
           , Bᴰ.αᴰ xᴰ yᴰ zᴰ wᴰ .nIsoᴰ (fᴰ , gᴰ , hᴰ) .secᴰ )
  ∫ᴮ .α (_ , xᴰ) (_ , yᴰ) (_ , zᴰ) (_ , wᴰ) .nIso
      ((f , fᴰ) , (g , gᴰ) , (h , hᴰ)) .ret =
    ΣPathP ( B.α _ _ _ _ .nIso (f , g , h) .ret
           , Bᴰ.αᴰ xᴰ yᴰ zᴰ wᴰ .nIsoᴰ (fᴰ , gᴰ , hᴰ) .retᴰ )

  -- coherences
  ∫ᴮ .triangle (_ , xᴰ) (_ , yᴰ) (_ , zᴰ) (f , fᴰ) (g , gᴰ) =
    ΣPathP ( B.triangle _ _ _ f g , Bᴰ.triangleᴰ fᴰ gᴰ )
  ∫ᴮ .pentagon (_ , xᴰ) (_ , yᴰ) (_ , zᴰ) (_ , wᴰ) (_ , vᴰ)
      (f , fᴰ) (g , gᴰ) (h , hᴰ) (k , kᴰ) =
    ΣPathP ( B.pentagon _ _ _ _ _ f g h k , Bᴰ.pentagonᴰ fᴰ gᴰ hᴰ kᴰ )


-- ------------------------------------------------------------------
-- The projection pseudofunctor
-- ------------------------------------------------------------------

module _ {B : Bicategory ℓ ℓ' ℓ''} (Bᴰ : Bicategoryᴰ B ℓᴰ ℓᴰ' ℓᴰ'') where
  private
    module B = Bicategory B

    -- whiskering an identity 2-cell
    idw : {x y z : B.ob} {f : B.1Cell x y} {g : B.1Cell y z}
      → B.seq x y z .F-hom (B.id₂ {f = f} , B.id₂ {f = g}) ≡ B.id₂
    idw {x} {y} {z} = B.seq x y z .F-id

  open LaxFunctor
  open Pseudofunctor

  Laxπᴮ : LaxFunctor (∫ᴮ Bᴰ) B
  Laxπᴮ .F-ob = fst
  Laxπᴮ .F-Hom = TC.Fst
  Laxπᴮ .F-id .N-ob _ = B.id₂
  Laxπᴮ .F-id .N-hom _ =
    B.⋆₂IdR _
    ∙ sym (B.⋆₂IdL _)
  Laxπᴮ .F-seq .N-ob _ = B.id₂
  Laxπᴮ .F-seq .N-hom _ =
    B.⋆₂IdR _
    ∙ sym (B.⋆₂IdL _)
  Laxπᴮ .lax-λ (x , _) (y , _) (f , _) =
    cong (B._⋆₂_ (B.seq x x y .F-hom (B.id₂ , B.id₂)))
         (B.⋆₂IdL (B.λ⁺ f))
    ∙ cong (λ z → B._⋆₂_ z (B.λ⁺ f)) idw
    ∙ B.⋆₂IdL (B.λ⁺ f)
  Laxπᴮ .lax-ρ (x , _) (y , _) (f , _) =
    cong (B._⋆₂_ (B.seq x y y .F-hom (B.id₂ , B.id₂)))
         (B.⋆₂IdL (B.ρ⁺ f))
    ∙ cong (λ z → B._⋆₂_ z (B.ρ⁺ f)) idw
    ∙ B.⋆₂IdL (B.ρ⁺ f)
  Laxπᴮ .lax-α (x , _) (y , _) (z , _) (w , _) (f , _) (g , _) (h , _) =
    (cong (B._⋆₂_ (B.seq x z w .F-hom (B.id₂ , B.id₂)))
          (B.⋆₂IdL (B.α⁺ f g h))
     ∙ cong (λ k → B._⋆₂_ k (B.α⁺ f g h)) idw
     ∙ B.⋆₂IdL (B.α⁺ f g h))
    ∙ sym (cong (B._⋆₂_ (B.α⁺ f g h))
             (cong (λ k → B._⋆₂_ k B.id₂) idw
              ∙ B.⋆₂IdL B.id₂)
           ∙ B.⋆₂IdR (B.α⁺ f g h))

  πᴮ : Pseudofunctor (∫ᴮ Bᴰ) B
  πᴮ .laxFunctor = Laxπᴮ
  πᴮ .F-id-isIso _ = idCatIso .snd
  πᴮ .F-seq-isIso _ = idCatIso .snd
