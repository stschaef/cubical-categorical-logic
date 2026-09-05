{- Collapsing composites of identities, and interchange.

   These come up constantly when a coherence cell has identity
   components, as in the 2-monads on CAT. -}
module Cubical.Categories.Category.More where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category

private
  variable
    ℓ ℓ' : Level

open Category

module _ (P : Category ℓ ℓ') where
  cong⋆ : {u v w : P .ob}
    {a a' : P [ u , v ]} {b b' : P [ v , w ]}
    → a ≡ a' → b ≡ b' → a ⋆⟨ P ⟩ b ≡ a' ⋆⟨ P ⟩ b'
  cong⋆ p q = cong₂ (λ m n → m ⋆⟨ P ⟩ n) p q

  collapseL : {u v : P .ob}
    {a : P [ u , u ]} {b : P [ u , v ]}
    → a ≡ P .id → a ⋆⟨ P ⟩ b ≡ b
  collapseL {b = b} p = cong (λ m → m ⋆⟨ P ⟩ b) p ∙ P .⋆IdL b

  collapse : {u : P .ob} {a b : P [ u , u ]}
    → a ≡ P .id → b ≡ P .id → a ⋆⟨ P ⟩ b ≡ P .id
  collapse p q = cong₂ (λ m n → m ⋆⟨ P ⟩ n) p q ∙ P .⋆IdL (P .id)

  four : {u : P .ob}
    → (P .id {u} ⋆⟨ P ⟩ P .id) ⋆⟨ P ⟩ (P .id ⋆⟨ P ⟩ P .id) ≡ P .id
  four = collapse (P .⋆IdL (P .id)) (P .⋆IdL (P .id))

  four' : {u : P .ob}
    → P .id {u} ⋆⟨ P ⟩ ((P .id ⋆⟨ P ⟩ P .id) ⋆⟨ P ⟩ P .id) ≡ P .id
  four' = P .⋆IdL ((P .id ⋆⟨ P ⟩ P .id) ⋆⟨ P ⟩ P .id)
        ∙ cong (λ m → m ⋆⟨ P ⟩ P .id) (P .⋆IdL (P .id))
        ∙ P .⋆IdL (P .id)

  exch : {u v v' t t' s : P .ob}
    (w : P [ u , v ]) {x : P [ v , v' ]} {y : P [ v' , s ]}
    {q : P [ v , t ]} {r : P [ t , s ]} (z : P [ s , t' ])
    → x ⋆⟨ P ⟩ y ≡ q ⋆⟨ P ⟩ r
    → (w ⋆⟨ P ⟩ x) ⋆⟨ P ⟩ (y ⋆⟨ P ⟩ z)
      ≡ (w ⋆⟨ P ⟩ q) ⋆⟨ P ⟩ (r ⋆⟨ P ⟩ z)
  exch w {x = x} {y = y} {q = q} {r = r} z n =
      P .⋆Assoc w x _
    ∙ cong (λ m → w ⋆⟨ P ⟩ m) (sym (P .⋆Assoc x y z)
        ∙ cong (λ m → m ⋆⟨ P ⟩ z) n ∙ P .⋆Assoc q r z)
    ∙ sym (P .⋆Assoc w q _)
