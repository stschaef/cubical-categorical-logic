{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Subcategory where
-- General Subcategory (restrictions on objects and morphisms)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓP ℓQ ℓR : Level

module _ (C : Category ℓC ℓC') where
  private
    module C = Category C
  open Category


  record DisplayedCategory : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓP)) where
    field
      D-ob : C .ob → Type ℓP
      D-Hom_[_,_] : {a b : C .ob} → (f : C [ a , b ])
                  → (x : D-ob a) → (y : D-ob b) → Type ℓP
      isSetHomf : {a b : C .ob} → {f : C [ a , b ]}
                  → {x : D-ob a} → {y : D-ob b} → isSet (D-Hom f [ x , y ])
      D-id : {a : C .ob} → {x : D-ob a} → D-Hom (C .id) [ x , x ]
      _D-⋆_ : {a b c : C .ob} → {f : C [ a , b ]} → {g : C [ b , c ]}
            → {x : D-ob a} → {y : D-ob b} → {z : D-ob c}
            → (k : D-Hom f [ x , y ]) → (l : D-Hom g [ y , z ])
            → D-Hom (f ⋆⟨ C ⟩ g) [ x , z ]
      D-⋆IdL : {a b : C .ob} → {f : C [ a , b ]}
            → {x : D-ob a} → {y : D-ob b}
            → (k : D-Hom f [ x , y ])
            → PathP (λ i → D-Hom (C .⋆IdL f i) [ x , y ]) (D-id D-⋆ k) k
      D-⋆IdR : {a b : C .ob} → {f : C [ a , b ]}
            → {x : D-ob a} → {y : D-ob b}
            → (k : D-Hom f [ x , y ])
            → PathP (λ i → D-Hom (C .⋆IdR f i) [ x , y ]) (k D-⋆ D-id) k
      D-⋆Assoc : {a b c d : C .ob}
                   → {f : C [ a , b ]} → {g : C [ b , c ]} → {h : C [ c , d ]}
                   → {x : D-ob a} → {y : D-ob b} → {z : D-ob c} → {w : D-ob d}
                   → (k : D-Hom f [ x , y ])
                   → (l : D-Hom g [ y , z ])
                   → (m : D-Hom h [ z , w ])
                   → PathP (λ i → D-Hom (C .⋆Assoc f g h i) [ x , w ])
                     ((k D-⋆ l) D-⋆ m)
                     (k D-⋆ (l D-⋆ m))

  -- when the morphism set is a prop,
  -- the Id/Assoc/isSet properties are all degenerate
  record DisplayedPoset : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓP)) where
    field
      D-ob : C .ob → Type ℓP
      D-Hom_[_,_] : {a b : C .ob} → (f : C [ a , b ])
                  → (x : D-ob a) → (y : D-ob b) → Type ℓP
      isPropHomf :{a b : C .ob} → {f : C [ a , b ]}
                  → {x : D-ob a} → {y : D-ob b} → isProp (D-Hom f [ x , y ])
      D-id : {a : C .ob} → {x : D-ob a} → D-Hom (C .id) [ x , x ]
      _D-⋆_ : {a b c : C .ob} → {f : C [ a , b ]} → {g : C [ b , c ]}
            → {x : D-ob a} → {y : D-ob b} → {z : D-ob c}
            → (k : D-Hom f [ x , y ]) → (l : D-Hom g [ y , z ])
            → D-Hom (f ⋆⟨ C ⟩ g) [ x , z ]

  DisplayedPoset→Cat : (D : DisplayedPoset {ℓP}) → DisplayedCategory {ℓP}
  DisplayedPoset→Cat D = record
    { D-ob = D-ob
    ; D-Hom_[_,_] = D-Hom_[_,_]
    ; isSetHomf = isProp→isSet (isPropHomf)
    ; D-id = D-id
    ; _D-⋆_ = _D-⋆_
    ; D-⋆IdL = λ k →
        isProp→PathP (λ i → isPropHomf {f = ((C .⋆IdL _) i)}) _ _
    ; D-⋆IdR = λ k →
        isProp→PathP (λ i → isPropHomf {f = ((C .⋆IdR _) i)}) _ _
    ; D-⋆Assoc = λ k l m →
        isProp→PathP (λ i → isPropHomf {f = ((C .⋆Assoc _ _ _) i)}) _ _
    } where
    open DisplayedPoset D

  -- the Grothendieck construction, or the generalized construction
  -- for a subcategory
  Grothendieck : DisplayedCategory {ℓP} → Category _ _
  Grothendieck D = record
    { ob =  Σ[ x ∈ C.ob ] D-ob x
    ; Hom[_,_] = λ (x , Dx) (y , Dy) →  Σ[ f ∈ C [ x , y ] ] D-Hom f [ Dx , Dy ]
    ; id = (C .id) , D-id
    ; _⋆_ = λ (f , Df) (g , Dg) → (f ⋆⟨ C ⟩ g) , (Df D-⋆ Dg)
    ; ⋆IdL = λ (f , Df) → ΣPathP ( C .⋆IdL f , D-⋆IdL Df )
    ; ⋆IdR = λ (f , Df) → ΣPathP ( C .⋆IdR f , D-⋆IdR Df )
    ; ⋆Assoc = λ (f , Df) (g , Dg) (h , Dh)
             → ΣPathP ( C .⋆Assoc f g h , D-⋆Assoc Df Dg Dh )
    ; isSetHom =  isSetΣ (C .isSetHom) (λ _ → isSetHomf)
    } where
    open DisplayedCategory D

  -- TODO: There are several results in FullSubCategory that may be true
  -- here as well
