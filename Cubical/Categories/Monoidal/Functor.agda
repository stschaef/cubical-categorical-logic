{- Lax and Strong Monoidal Functors -}

module Cubical.Categories.Monoidal.Functor where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.Category.More
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Monoidal.Base

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
open Category
open Functor
open isIso
module _ (M : MonoidalCategory ℓC ℓC') (N : MonoidalCategory ℓD ℓD') where
  private
    module M = MonoidalCategory M
    module N = MonoidalCategory N

  module _ (F : Functor M.C N.C) where
    record LaxMonoidalStr : Type (ℓ-max ℓC (ℓ-max ℓC' ℓD'))
      where
      field
        ε : N.C [ N.unit , F ⟅ M.unit ⟆ ]
        -- N.C [ F x ⊗ F y , F (x ⊗ y) ]
        μ : N.─⊗─ ∘F (F ×F F) ⇒ F ∘F M.─⊗─

      μ⟨_,_⟩ : ∀ x y → N.C [ (F ⟅ x ⟆) N.⊗ (F ⟅ y ⟆) , F ⟅ x M.⊗ y ⟆ ]
      μ⟨ x , y ⟩ = μ ⟦ x , y ⟧

      field
        αμ-law : ∀ (x y z : M.C .ob) →
          (N.α⟨ _ , _ , _ ⟩ ⋆⟨ N.C ⟩ (μ⟨ x , y ⟩ N.⊗ₕ N.id) ⋆⟨ N.C ⟩ μ⟨ _ , z ⟩)
          ≡
          (N.id N.⊗ₕ μ⟨ y , z ⟩ ⋆⟨ N.C ⟩ μ⟨ x , _ ⟩
          ⋆⟨ N.C ⟩ F ⟪ M.α⟨ x , y , z ⟩ ⟫)
        ηε-law : ∀ x →
          Path (N.C [ N.unit N.⊗ (F ⟅ x ⟆) , F ⟅ x ⟆ ])
            (ε N.⊗ₕ N.id ⋆⟨ N.C ⟩ μ⟨ M.unit , x ⟩ ⋆⟨ N.C ⟩ F ⟪ M.η⟨ x ⟩ ⟫)
            N.η⟨ F ⟅ x ⟆ ⟩
        ρε-law : ∀ x →
          N.id N.⊗ₕ ε ⋆⟨ N.C ⟩ μ⟨ x , M.unit ⟩ ⋆⟨ N.C ⟩ F ⟪ M.ρ⟨ x ⟩ ⟫
          ≡ N.ρ⟨ F ⟅ x ⟆ ⟩

      -- α⁻μ-law
      η⁻ε-law : ∀ x →
        N.η⁻¹⟨ F ⟅ x ⟆ ⟩ ⋆⟨ N.C ⟩ (ε N.⊗ₕ N.id) ⋆⟨ N.C ⟩ μ⟨ _ , _ ⟩
        ≡ F ⟪ M.η⁻¹⟨ x ⟩ ⟫
      η⁻ε-law x = ⋆CancelR (F-Iso {F = F} ((NatIsoAt M.η _)))
        (((N.⋆Assoc _ _ _) ∙ N.⋆Assoc _ _ _
        ∙ cong₂ N._⋆_ refl (sym (N.⋆Assoc _ _ _) ∙ ηε-law x)
        ∙ NatIsoAt N.η _ .snd .sec)
        ∙ sym (F .F-id)
        ∙ cong (F .F-hom) (sym (NatIsoAt M.η _ .snd .sec))
        ∙ F .F-seq _ _)

    -- equivalent to LaxMonoidal stuff with op but we'll define it
    -- explicitly for ergonomics
    record OpLaxMonoidalStr : Type (ℓ-max ℓC (ℓ-max ℓC' ℓD')) where
      field
        ε⁻ : N.C [ F ⟅ M.unit ⟆ , N.unit ]
        μ⁻ : F ∘F M.─⊗─ ⇒ N.─⊗─ ∘F (F ×F F)

      μ⁻⟨_,_⟩ : ∀ x y → N.C [ F ⟅ x M.⊗ y ⟆ , (F ⟅ x ⟆) N.⊗ (F ⟅ y ⟆) ]
      μ⁻⟨ x , y ⟩ = μ⁻ ⟦ x , y ⟧

      field
        α⁻μ⁻-law : ∀ (x y z : M.C .ob) →
            (μ⁻⟨ _ , z ⟩ ⋆⟨ N.C ⟩ (μ⁻⟨ x , y ⟩ N.⊗ₕ N.id)
            ⋆⟨ N.C ⟩ N.α⁻¹⟨ _ , _ , _ ⟩)
            ≡
            (F ⟪ M.α⁻¹⟨ x , y , z ⟩ ⟫ ⋆⟨ N.C ⟩ μ⁻⟨ x , _ ⟩
            ⋆⟨ N.C ⟩ N.id N.⊗ₕ μ⁻⟨ y , z ⟩)

        η⁻-law : ∀ x →
            (F ⟪ M.η⁻¹⟨ x ⟩ ⟫ ⋆⟨ N.C ⟩ μ⁻⟨ M.unit , x ⟩ ⋆⟨ N.C ⟩ ε⁻ N.⊗ₕ N.id)
            ≡ N.η⁻¹⟨ F ⟅ x ⟆ ⟩


    -- TODO: α-law⁻ , α⁻¹-law, η⁻¹-law, ρ-law ρ⁻¹-law all derivable

    record StrongMonoidalStr : Type ((ℓ-max ℓC (ℓ-max ℓC' ℓD'))) where
      field
        laxmonstr : LaxMonoidalStr
      open LaxMonoidalStr laxmonstr public
      field
        ε-isIso : isIso N.C ε
        μ-isIso : ∀ x → isIso N.C (μ ⟦ x ⟧)

      ε-Iso : CatIso N.C N.unit (F ⟅ M.unit ⟆)
      ε-Iso = ε , ε-isIso

      μ-Iso :  N.─⊗─ ∘F (F ×F F) ≅ᶜ F ∘F M.─⊗─
      μ-Iso = record { trans = μ ; nIso = μ-isIso }

      -- oplaxmonstr : OpLaxMonoidalStr
      -- oplaxmonstr .OpLaxMonoidalStr.ε⁻ = ε-isIso .isIso.inv
      -- oplaxmonstr .OpLaxMonoidalStr.μ⁻ = symNatIso μ-Iso .NatIso.trans
      -- oplaxmonstr .OpLaxMonoidalStr.α⁻-law x y z = {!α-law x y z!}
      -- oplaxmonstr .OpLaxMonoidalStr.η⁻-law = {!!}

      -- open OpLaxMonoidalStr oplaxmonstr public

  record LaxMonoidalFunctor : Type (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')) where
    field
      F : Functor M.C N.C
      laxmonstr : LaxMonoidalStr F
    open Functor F public
    open LaxMonoidalStr laxmonstr public

  record OplaxMonoidalFunctor : Type (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')) where
    field
      F : Functor M.C N.C
      oplaxmonstr : OpLaxMonoidalStr F
    open Functor F public
    open OpLaxMonoidalStr oplaxmonstr public

  record StrongMonoidalFunctor
    : Type (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')) where
    field
      F : Functor M.C N.C
      strmonstr : StrongMonoidalStr F
    open Functor F public
    open StrongMonoidalStr strmonstr public

module _ {M : MonoidalCategory ℓC ℓC'} where
  open LaxMonoidalStr
  open Functor
  private
    module M = MonoidalCategory M

  IdLaxStr : LaxMonoidalStr M M (Id {C = M.C})
  IdLaxStr .ε = M.id
  IdLaxStr .μ = natTrans (λ _ → M.id) (λ f → M.⋆IdR _ ∙ sym (M.⋆IdL _))
  IdLaxStr .αμ-law x y z =
    M.⋆IdR _
    ∙ (λ i → M.α⟨ _ , _ , _ ⟩ M.⋆ (M.─⊗─ .F-id i))
    ∙ M.⋆IdR _
    ∙ sym (M.⋆IdL _)
    ∙ (λ i → (M.─⊗─ .F-id (~ i)) M.⋆ M.α⟨ _ , _ , _ ⟩)
    ∙ cong₂ M._⋆_ (sym (M.⋆IdR _)) refl
  IdLaxStr .ηε-law x =
    cong₂ M._⋆_ (M.⋆IdR _) refl
    ∙ cong₂ M._⋆_ (M.─⊗─ .F-id) refl
    ∙ M.⋆IdL _
  IdLaxStr .ρε-law x =
    cong₂ M._⋆_ (M.⋆IdR _ ∙ M.─⊗─ .F-id) refl
    ∙ M.⋆IdL _

  IdStrStr : StrongMonoidalStr M M (Id {C = M.C})
  IdStrStr .StrongMonoidalStr.laxmonstr = IdLaxStr
  IdStrStr .StrongMonoidalStr.ε-isIso = idCatIso .snd
  IdStrStr .StrongMonoidalStr.μ-isIso = λ _ → idCatIso .snd

  IdLax : LaxMonoidalFunctor M M
  IdLax .LaxMonoidalFunctor.F = Id
  IdLax .LaxMonoidalFunctor.laxmonstr = IdLaxStr

  IdStr : StrongMonoidalFunctor M M
  IdStr .StrongMonoidalFunctor.F = Id
  IdStr .StrongMonoidalFunctor.strmonstr = IdStrStr
{- Composition: the composite's comparisons are `ε_G ⋆ G(ε_H)` and
   `μ_G ⋆ G(μ_H)`; the coherences follow from `G`'s and `H`'s own,
   plus naturality of `μ_G`. -}
module _ {M : MonoidalCategory ℓC ℓC'}
         {N : MonoidalCategory ℓD ℓD'}
         {O : MonoidalCategory ℓE ℓE'}
         {G : Functor (MonoidalCategory.C N) (MonoidalCategory.C O)}
         {H : Functor (MonoidalCategory.C M) (MonoidalCategory.C N)}
         (Gs : LaxMonoidalStr N O G) (Hs : LaxMonoidalStr M N H) where
  open LaxMonoidalStr
  open NatTrans
  private
    module M = MonoidalCategory M
    module N = MonoidalCategory N
    module O = MonoidalCategory O
    module Gs = LaxMonoidalStr Gs
    module Hs = LaxMonoidalStr Hs

    Gh : {a b : N.C .ob} → N.C [ a , b ] → O.C [ G ⟅ a ⟆ , G ⟅ b ⟆ ]
    Gh = G .F-hom

    cL : {a b c : O.C .ob} {f g : O.C [ a , b ]} {h : O.C [ b , c ]}
      → f ≡ g → f O.⋆ h ≡ g O.⋆ h
    cL p = cong⋆ O.C p refl

    cR : {a b c : O.C .ob} {f : O.C [ a , b ]} {g h : O.C [ b , c ]}
      → g ≡ h → f O.⋆ g ≡ f O.⋆ h
    cR p = cong⋆ O.C refl p

    Gnat : {a b c d : N.C .ob} (f : N.C [ a , b ]) (g : N.C [ c , d ])
      → (Gh f O.⊗ₕ Gh g) O.⋆ Gs.μ⟨ b , d ⟩
        ≡ Gs.μ⟨ a , c ⟩ O.⋆ Gh (f N.⊗ₕ g)
    Gnat f g = Gs.μ .N-hom (f , g)

    GnatL : {a b c : N.C .ob} (f : N.C [ a , b ])
      → (Gh f O.⊗ₕ O.id {G ⟅ c ⟆}) O.⋆ Gs.μ⟨ b , c ⟩
        ≡ Gs.μ⟨ a , c ⟩ O.⋆ Gh (f N.⊗ₕ N.id {c})
    GnatL {c = c} f =
      cL (cong (Gh f O.⊗ₕ_) (sym (G .F-id))) ∙ Gnat f (N.id {c})

    GnatR : {a b c : N.C .ob} (f : N.C [ a , b ])
      → (O.id {G ⟅ c ⟆} O.⊗ₕ Gh f) O.⋆ Gs.μ⟨ c , b ⟩
        ≡ Gs.μ⟨ c , a ⟩ O.⋆ Gh (N.id {c} N.⊗ₕ f)
    GnatR {c = c} f =
      cL (cong (O._⊗ₕ Gh f) (sym (G .F-id))) ∙ Gnat (N.id {c}) f

    ⊗L : {a b c d : O.C .ob} (f : O.C [ a , b ]) (g : O.C [ b , c ])
      → ((f O.⋆ g) O.⊗ₕ O.id {d}) ≡ (f O.⊗ₕ O.id) O.⋆ (g O.⊗ₕ O.id)
    ⊗L f g =
        cong ((f O.⋆ g) O.⊗ₕ_) (sym (O.⋆IdL O.id))
      ∙ O.─⊗─ .F-seq (f , O.id) (g , O.id)

    ⊗R : {a b c d : O.C .ob} (f : O.C [ a , b ]) (g : O.C [ b , c ])
      → (O.id {d} O.⊗ₕ (f O.⋆ g)) ≡ (O.id O.⊗ₕ f) O.⋆ (O.id O.⊗ₕ g)
    ⊗R f g =
        cong (O._⊗ₕ (f O.⋆ g)) (sym (O.⋆IdL O.id))
      ∙ O.─⊗─ .F-seq (O.id , f) (O.id , g)

    Gseq3 : {a b c d : N.C .ob}
      (f : N.C [ a , b ]) (g : N.C [ b , c ]) (h : N.C [ c , d ])
      → Gh ((f N.⋆ g) N.⋆ h) ≡ (Gh f O.⋆ Gh g) O.⋆ Gh h
    Gseq3 f g h = G .F-seq _ _ ∙ cL (G .F-seq f g)

  ∘LaxStr : LaxMonoidalStr M O (G ∘F H)
  ∘LaxStr .ε = Gs.ε O.⋆ Gh Hs.ε
  ∘LaxStr .μ .N-ob (x , y) =
    Gs.μ⟨ H ⟅ x ⟆ , H ⟅ y ⟆ ⟩ O.⋆ Gh Hs.μ⟨ x , y ⟩
  ∘LaxStr .μ .N-hom (f , g) =
      sym (O.⋆Assoc _ _ _)
    ∙ cL (Gnat (H ⟪ f ⟫) (H ⟪ g ⟫))
    ∙ O.⋆Assoc _ _ _
    ∙ cR (sym (G .F-seq _ _)
          ∙ cong Gh (Hs.μ .N-hom (f , g))
          ∙ G .F-seq _ _)
    ∙ sym (O.⋆Assoc _ _ _)
  ∘LaxStr .ηε-law x =
      cL (cL (⊗L Gs.ε (Gh Hs.ε)))
    ∙ cL (O.⋆Assoc _ _ _)
    ∙ cL (cR (sym (O.⋆Assoc _ _ _)))
    ∙ cL (cR (cL (GnatL Hs.ε)))
    ∙ cL (cR (O.⋆Assoc _ _ _))
    ∙ cL (sym (O.⋆Assoc _ _ _))
    ∙ O.⋆Assoc _ _ _
    ∙ cR (sym (Gseq3 (Hs.ε N.⊗ₕ N.id) Hs.μ⟨ M.unit , x ⟩ (H ⟪ M.η⟨ x ⟩ ⟫)))
    ∙ cR (cong Gh (Hs.ηε-law x))
    ∙ Gs.ηε-law (H ⟅ x ⟆)
  ∘LaxStr .ρε-law x =
      cL (cL (⊗R Gs.ε (Gh Hs.ε)))
    ∙ cL (O.⋆Assoc _ _ _)
    ∙ cL (cR (sym (O.⋆Assoc _ _ _)))
    ∙ cL (cR (cL (GnatR Hs.ε)))
    ∙ cL (cR (O.⋆Assoc _ _ _))
    ∙ cL (sym (O.⋆Assoc _ _ _))
    ∙ O.⋆Assoc _ _ _
    ∙ cR (sym (Gseq3 (N.id N.⊗ₕ Hs.ε) Hs.μ⟨ x , M.unit ⟩ (H ⟪ M.ρ⟨ x ⟩ ⟫)))
    ∙ cR (cong Gh (Hs.ρε-law x))
    ∙ Gs.ρε-law (H ⟅ x ⟆)
  ∘LaxStr .αμ-law x y z =
      cL (cR (⊗L Gs.μ⟨ H ⟅ x ⟆ , H ⟅ y ⟆ ⟩ (Gh Hs.μ⟨ x , y ⟩)))
    ∙ cL (sym (O.⋆Assoc _ _ _))
    ∙ sym (O.⋆Assoc _ _ _)
    ∙ cL (O.⋆Assoc _ _ _)
    ∙ cL (cR (GnatL Hs.μ⟨ x , y ⟩))
    ∙ cL (sym (O.⋆Assoc _ _ _))
    ∙ cL (cL (Gs.αμ-law (H ⟅ x ⟆) (H ⟅ y ⟆) (H ⟅ z ⟆)))
    ∙ cL (O.⋆Assoc _ _ _)
    ∙ O.⋆Assoc _ _ _
    ∙ cR (sym (Gseq3 N.α⟨ H ⟅ x ⟆ , H ⟅ y ⟆ , H ⟅ z ⟆ ⟩
                     (Hs.μ⟨ x , y ⟩ N.⊗ₕ N.id) Hs.μ⟨ x M.⊗ y , z ⟩))
    ∙ cR (cong Gh (Hs.αμ-law x y z))
    ∙ cR (Gseq3 (N.id N.⊗ₕ Hs.μ⟨ y , z ⟩) Hs.μ⟨ x , y M.⊗ z ⟩
                (H ⟪ M.α⟨ x , y , z ⟩ ⟫))
    ∙ sym
      ( cL (cL (⊗R Gs.μ⟨ H ⟅ y ⟆ , H ⟅ z ⟆ ⟩ (Gh Hs.μ⟨ y , z ⟩)))
      ∙ cL (O.⋆Assoc _ _ _)
      ∙ cL (cR (sym (O.⋆Assoc _ _ _)))
      ∙ cL (cR (cL (GnatR Hs.μ⟨ y , z ⟩)))
      ∙ cL (cR (O.⋆Assoc _ _ _))
      ∙ cL (sym (O.⋆Assoc _ _ _))
      ∙ O.⋆Assoc _ _ _)

module _ {M : MonoidalCategory ℓC ℓC'}
         {N : MonoidalCategory ℓD ℓD'}
         {O : MonoidalCategory ℓE ℓE'} where
  open LaxMonoidalFunctor
  open StrongMonoidalFunctor

  _∘Lax_ : LaxMonoidalFunctor N O → LaxMonoidalFunctor M N
    → LaxMonoidalFunctor M O
  (G ∘Lax H) .LaxMonoidalFunctor.F = G .F ∘F H .F
  (G ∘Lax H) .LaxMonoidalFunctor.laxmonstr =
    ∘LaxStr (G .laxmonstr) (H .laxmonstr)

  _∘Str_ : StrongMonoidalFunctor N O → StrongMonoidalFunctor M N
    → StrongMonoidalFunctor M O
  (G ∘Str H) .StrongMonoidalFunctor.F =
    G .StrongMonoidalFunctor.F ∘F H .StrongMonoidalFunctor.F
  (G ∘Str H) .StrongMonoidalFunctor.strmonstr .StrongMonoidalStr.laxmonstr =
    ∘LaxStr (G .StrongMonoidalFunctor.laxmonstr)
            (H .StrongMonoidalFunctor.laxmonstr)
  (G ∘Str H) .StrongMonoidalFunctor.strmonstr .StrongMonoidalStr.ε-isIso =
    ⋆IsIso (G .ε-isIso)
           (F-PresIsIso {F = G .StrongMonoidalFunctor.F} (H .ε-isIso))
  (G ∘Str H) .StrongMonoidalFunctor.strmonstr .StrongMonoidalStr.μ-isIso
    (a , b) =
    ⋆IsIso (G .μ-isIso (H .StrongMonoidalFunctor.F ⟅ a ⟆
                       , H .StrongMonoidalFunctor.F ⟅ b ⟆))
           (F-PresIsIso {F = G .StrongMonoidalFunctor.F}
                        (H .μ-isIso (a , b)))

open NatTrans

{- A natural transformation between strong monoidal functors is
   monoidal when it commutes with the ε and μ comparisons. -}
module _ {M : MonoidalCategory ℓC ℓC'} {N : MonoidalCategory ℓD ℓD'}
         (G H : StrongMonoidalFunctor M N) where
  private
    module M = MonoidalCategory M
    module N = MonoidalCategory N
    module G = StrongMonoidalFunctor G
    module H = StrongMonoidalFunctor H

  isMonoidalNat : NatTrans G.F H.F → Type (ℓ-max ℓC ℓD')
  isMonoidalNat σ =
    (G.ε ⋆⟨ N.C ⟩ σ .N-ob M.unit ≡ H.ε)
    × (∀ x y → G.μ⟨ x , y ⟩ ⋆⟨ N.C ⟩ σ .N-ob (x M.⊗ y)
             ≡ (σ .N-ob x N.⊗ₕ σ .N-ob y) ⋆⟨ N.C ⟩ H.μ⟨ x , y ⟩)

module _ {M : MonoidalCategory ℓC ℓC'} {N : MonoidalCategory ℓD ℓD'}
         (G : StrongMonoidalFunctor M N) where
  private
    module N = MonoidalCategory N
    module G = StrongMonoidalFunctor G
  isMonoidalNat-id : isMonoidalNat G G (idTrans G.F)
  isMonoidalNat-id .fst = N.⋆IdR _
  isMonoidalNat-id .snd x y =
    N.⋆IdR _ ∙ sym (N.⋆IdL _) ∙ cong₂ N._⋆_ (sym (N.─⊗─ .F-id)) refl

-- Monoidal natural transformations are closed under composition.
module _ {M : MonoidalCategory ℓC ℓC'} {N : MonoidalCategory ℓD ℓD'}
         (G H K : StrongMonoidalFunctor M N) where
  private
    module N = MonoidalCategory N
    module G = StrongMonoidalFunctor G
    module K = StrongMonoidalFunctor K
  isMonoidalNat-seq : (σ : NatTrans G.F (H .StrongMonoidalFunctor.F))
    (τ : NatTrans (H .StrongMonoidalFunctor.F) K.F)
    → isMonoidalNat G H σ → isMonoidalNat H K τ
    → isMonoidalNat G K (seqTrans σ τ)
  isMonoidalNat-seq σ τ mσ mτ .fst =
    sym (N.⋆Assoc _ _ _) ∙ cong₂ N._⋆_ (mσ .fst) refl ∙ mτ .fst
  isMonoidalNat-seq σ τ mσ mτ .snd x y =
    sym (N.⋆Assoc _ _ _)
    ∙ cong₂ N._⋆_ (mσ .snd x y) refl
    ∙ N.⋆Assoc _ _ _
    ∙ cong₂ N._⋆_ refl (mτ .snd x y)
    ∙ sym (N.⋆Assoc _ _ _)
    ∙ cong₂ N._⋆_ (sym (N.─⊗─ .F-seq _ _)) refl

-- ... and under whiskering by a strong monoidal functor.
module _ {M : MonoidalCategory ℓC ℓC'} {N : MonoidalCategory ℓD ℓD'}
         {E : MonoidalCategory ℓE ℓE'}
         (K : StrongMonoidalFunctor N E)
         (G H : StrongMonoidalFunctor M N) where
  private
    module E = MonoidalCategory E
    module K = StrongMonoidalFunctor K
  isMonoidalNat-∘ʳ : (σ : NatTrans (G .StrongMonoidalFunctor.F)
                                   (H .StrongMonoidalFunctor.F))
    → isMonoidalNat G H σ
    → isMonoidalNat (K ∘Str G) (K ∘Str H) (K.F ∘ʳ σ)
  isMonoidalNat-∘ʳ σ mσ .fst =
    E.⋆Assoc _ _ _
    ∙ cong₂ E._⋆_ refl (sym (K.F-seq _ _) ∙ cong K.F-hom (mσ .fst))
  isMonoidalNat-∘ʳ σ mσ .snd x y =
    E.⋆Assoc _ _ _
    ∙ cong₂ E._⋆_ refl
      (sym (K.F-seq _ _) ∙ cong K.F-hom (mσ .snd x y) ∙ K.F-seq _ _)
    ∙ sym (E.⋆Assoc _ _ _)
    ∙ cong₂ E._⋆_ (sym (K.μ .N-hom _)) refl
    ∙ E.⋆Assoc _ _ _

module _ {M : MonoidalCategory ℓC ℓC'} {N : MonoidalCategory ℓD ℓD'}
         {E : MonoidalCategory ℓE ℓE'}
         (K : StrongMonoidalFunctor M N)
         (G H : StrongMonoidalFunctor N E) where
  private
    module E = MonoidalCategory E
    module K = StrongMonoidalFunctor K
    module G = StrongMonoidalFunctor G
    module H = StrongMonoidalFunctor H
  isMonoidalNat-∘ˡ : (σ : NatTrans G.F H.F)
    → isMonoidalNat G H σ
    → isMonoidalNat (G ∘Str K) (H ∘Str K) (σ ∘ˡ K.F)
  isMonoidalNat-∘ˡ σ mσ .fst =
    E.⋆Assoc _ _ _
    ∙ cong₂ E._⋆_ refl (σ .N-hom _)
    ∙ sym (E.⋆Assoc _ _ _)
    ∙ cong₂ E._⋆_ (mσ .fst) refl
  isMonoidalNat-∘ˡ σ mσ .snd x y =
    E.⋆Assoc _ _ _
    ∙ cong₂ E._⋆_ refl (σ .N-hom _)
    ∙ sym (E.⋆Assoc _ _ _)
    ∙ cong₂ E._⋆_ (mσ .snd _ _) refl
    ∙ E.⋆Assoc _ _ _
