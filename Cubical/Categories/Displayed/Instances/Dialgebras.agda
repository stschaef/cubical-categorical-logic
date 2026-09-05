{- (F,G)-dialgebras: `F ⟅ x ⟆ → G ⟅ x ⟆` displayed over `C`. -}
module Cubical.Categories.Displayed.Instances.Dialgebras where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.StructureOver
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Displayed.Instances.FunctorAlgebras
open import Cubical.Categories.Displayed.Instances.FunctorCoalgebras

private
  variable ℓC ℓC' ℓD ℓD' : Level

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F G : Functor C D) where
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G

  DialgStructureOver : StructureOver C ℓD' ℓD'
  StructureOver.ob[_] DialgStructureOver x = D [ F.F-ob x , G.F-ob x ]
  StructureOver.Hom[_][_,_] DialgStructureOver f θ θ' =
    θ D.⋆ G.F-hom f ≡ F.F-hom f D.⋆ θ'
  StructureOver.idᴰ DialgStructureOver {p = θ} =
      cong (θ D.⋆_) G.F-id ∙ D.⋆IdR θ
    ∙ sym (cong (D._⋆ θ) F.F-id ∙ D.⋆IdL θ)
  StructureOver._⋆ᴰ_ DialgStructureOver
    {f = f} {g = g} {xᴰ = θ} {yᴰ = θ'} {zᴰ = θ''} pf pg =
      cong (θ D.⋆_) (G.F-seq f g)
    ∙ sym (D.⋆Assoc _ _ _)
    ∙ cong (D._⋆ G.F-hom g) pf
    ∙ D.⋆Assoc _ _ _
    ∙ cong (F.F-hom f D.⋆_) pg
    ∙ sym (D.⋆Assoc _ _ _)
    ∙ cong (D._⋆ θ'') (sym (F.F-seq f g))
  StructureOver.isPropHomᴰ DialgStructureOver = D.isSetHom _ _

  DIALGᴰ : Categoryᴰ C ℓD' ℓD'
  DIALGᴰ = StructureOver→Catᴰ DialgStructureOver

  DIALG : Category (ℓ-max ℓC ℓD') (ℓ-max ℓC' ℓD')
  DIALG = ∫C DIALGᴰ

  Dialgebra : Type (ℓ-max ℓC ℓD')
  Dialgebra = Category.ob DIALG

-- Algebras and coalgebras are the two unit cases.
module _ {C : Category ℓC ℓC'} (F : Functor C C) where
  F-ALG : Category (ℓ-max ℓC ℓC') (ℓ-max ℓC' ℓC')
  F-ALG = DIALG F Id

  F-COALG : Category (ℓ-max ℓC ℓC') (ℓ-max ℓC' ℓC')
  F-COALG = DIALG Id F

  private
    module C = Category C

  -- objects and morphisms unfold as expected
  F-ALG-ob : Category.ob F-ALG ≡ (Σ[ c ∈ C.ob ] C [ Functor.F-ob F c , c ])
  F-ALG-ob = refl

  F-COALG-ob : Category.ob F-COALG ≡ (Σ[ c ∈ C.ob ] C [ c , Functor.F-ob F c ])
  F-COALG-ob = refl

  F-ALG-hom : (x y : Category.ob F-ALG) → F-ALG [ x , y ]
    ≡ (Σ[ f ∈ C [ x .fst , y .fst ] ]
        x .snd C.⋆ f ≡ Functor.F-hom F f C.⋆ y .snd)
  F-ALG-hom x y = refl

  F-COALG-hom : (x y : Category.ob F-COALG) → F-COALG [ x , y ]
    ≡ (Σ[ f ∈ C [ x .fst , y .fst ] ]
        x .snd C.⋆ Functor.F-hom F f ≡ f C.⋆ y .snd)
  F-COALG-hom x y = refl

  -- `ALG` of `Displayed.Instances.FunctorAlgebras` is this unit case
  -- on the nose.
  ALG≡ob : Category.ob (ALG F) ≡ Category.ob F-ALG
  ALG≡ob = refl

  ALG≡hom : (x y : Category.ob (ALG F)) → ALG F [ x , y ] ≡ F-ALG [ x , y ]
  ALG≡hom x y = refl

  -- `COALG` is the same objects, but states its condition reversed.
  COALG≡ob : Category.ob (COALG F) ≡ Category.ob F-COALG
  COALG≡ob = refl

  COALG→F-COALG : Functor (COALG F) F-COALG
  COALG→F-COALG .Functor.F-ob c = c
  COALG→F-COALG .Functor.F-hom (f , p) = f , sym p
  COALG→F-COALG .Functor.F-id =
    ΣPathP (refl , C.isSetHom _ _ _ _)
  COALG→F-COALG .Functor.F-seq _ _ =
    ΣPathP (refl , C.isSetHom _ _ _ _)

  F-COALG→COALG : Functor F-COALG (COALG F)
  F-COALG→COALG .Functor.F-ob c = c
  F-COALG→COALG .Functor.F-hom (f , p) = f , sym p
  F-COALG→COALG .Functor.F-id =
    ΣPathP (refl , C.isSetHom _ _ _ _)
  F-COALG→COALG .Functor.F-seq _ _ =
    ΣPathP (refl , C.isSetHom _ _ _ _)
