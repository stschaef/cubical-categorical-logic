{-# OPTIONS --lossy-unification #-}
{-
  Pentagon coherence for the CAT bicategory.
-}
module Cubical.Categories.Bicategory.Instances.CAT.Pentagon where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors

open import Cubical.Categories.Bicategory.Instances.CAT.Base
open import Cubical.Categories.Bicategory.Instances.CAT.Associator

private
  variable
    ℓ ℓ' : Level

open Functor
open NatTrans
open Category

module _ {ℓ ℓ' : Level} where

  pentagon-CAT : (C D E W V : Category ℓ ℓ')
    (F : Functor C D) (G : Functor D E) (H : Functor E W) (K : Functor W V)
    →   seqCAT C W V .F-hom
            (α-trans-N-ob C D E W (F , G , H) , idTrans K)
      ⋆⟨ FUNCTOR C V ⟩
        α-trans-N-ob C D W V (F , seqCAT D E W .F-ob (G , H) , K)
      ⋆⟨ FUNCTOR C V ⟩
        seqCAT C D V .F-hom
          (idTrans F , α-trans-N-ob D E W V (G , H , K))
      ≡   α-trans-N-ob C E W V (seqCAT C D E .F-ob (F , G) , H , K)
        ⋆⟨ FUNCTOR C V ⟩
          α-trans-N-ob C D E V (F , G , seqCAT E W V .F-ob (H , K))
  pentagon-CAT C D E W V F G H K = makeNatTransPath (funExt λ c →
      cong (λ m → m ⋆⟨ V ⟩
              (K .F-hom (H .F-hom (G .F-hom (D .id {x = F .F-ob c})))
                 ⋆⟨ V ⟩ V.id))
           (cong (λ m → m ⋆⟨ V ⟩ V.id) (V.⋆IdR _ ∙ K .F-id) ∙ V.⋆IdR _)
    ∙ cong (λ n → V.id ⋆⟨ V ⟩ n)
           ( V.⋆IdR _
           ∙ cong (K .F-hom) (cong (H .F-hom) (G .F-id) ∙ H .F-id)
           ∙ K .F-id))
    where
    module C = Category C
    module D = Category D
    module E = Category E
    module V = Category V
    module W = Category W
