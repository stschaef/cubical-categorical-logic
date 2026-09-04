module Cubical.Categories.NaturalTransformation.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism renaming (iso to iIso)
open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties

open import Cubical.Categories.Instances.Functors

private
  variable
    ℓA ℓA' ℓB ℓB' ℓC ℓC' ℓC'' ℓC''' ℓD ℓD' ℓE ℓE' ℓE'' ℓE''' : Level
    ℓ ℓ' ℓ'' : Level
    B C D E : Category ℓ ℓ'

open Category
open NatTrans
open NatIso
open isIsoC

infixl 8 _∘ᵛ_
infixl 8 _∘ʰ_
_∘ᵛ_ = compTrans
_∘ʰ_ = whiskerTrans

module _ {B : Category ℓB ℓB'}
         {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'} where
  open NatTrans
  whiskerTrans' : {F F' : Functor B C} {G G' : Functor C D}
                  (β : NatTrans G G') (α : NatTrans F F')
                  → NatTrans (G ∘F F) (G' ∘F F')
  whiskerTrans' {F}{F'}{G}{G'} β α = compTrans (G' ∘ʳ α) (β ∘ˡ F)

  whiskerTrans≡whiskerTrans' : {F F' : Functor B C} {G G' : Functor C D}
                               (β : NatTrans G G') (α : NatTrans F F') →
                               whiskerTrans β α ≡ whiskerTrans' β α
  whiskerTrans≡whiskerTrans' β α = makeNatTransPath (funExt (λ x → β .N-hom _))

_∘ʰ'_ = whiskerTrans'

α : {F : Functor B C} {G : Functor C D} {H : Functor D E}
  → NatTrans (H ∘F (G ∘F F)) ((H ∘F G) ∘F F)
α = pathToNatTrans F-assoc

α⁻¹ : {F : Functor B C} {G : Functor C D} {H : Functor D E}
   → NatTrans ((H ∘F G) ∘F F) (H ∘F (G ∘F F))
α⁻¹ = pathToNatTrans (sym F-assoc)

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  module _  {F F' G G' : Functor C D} {α : NatIso F G} {β : NatIso F' G'} where
    open Functor
    makeNatIsoPathP : ∀ (p : F ≡ F') (q : G ≡ G')
                      → PathP (λ i → (x : C .ob) → D [ (p i) .F-ob x ,
                                                       (q i) .F-ob x ])
                              (α .trans .N-ob) (β .trans .N-ob)
                      → PathP (λ i → NatIso (p i) (q i)) α β

    makeNatIsoPathP p q P i .trans =
      makeNatTransPathP {α = α .trans} {β = β .trans} p q P i
    makeNatIsoPathP p q P i .nIso x =
      isProp→PathP
        (λ i → isPropIsIso (makeNatIsoPathP p q P i .trans .N-ob x))
          (α .nIso _) (β .nIso _) i

module _ {A : Category ℓA ℓA'}
         {B : Category ℓB ℓB'}
         {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'} where
  preservesNatIsosF : ∀ (𝔽 : Functor (FUNCTOR A B) (FUNCTOR C D)) →
        {F G : Functor A B} → (β : NatIso F G)
      → NatIso (𝔽 ⟅ F ⟆) (𝔽 ⟅ G ⟆)
  preservesNatIsosF 𝔽 β =
    FUNCTORIso→NatIso C D
      (preserveIsosF {F = 𝔽}
        (NatIso→FUNCTORIso A B β)
      )

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {F G : Functor C D}
         (α : NatTrans F G) where
  isNatIso : Type _
  isNatIso = ∀ x → isIsoC D (α .N-ob x)

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {F G : Functor C D}
         (α : F ≅ᶜ G) where
  NatIsoAt : ∀ x → CatIso D (F ⟅ x ⟆) (G ⟅ x ⟆)
  NatIsoAt x = (N-ob (α .trans) x) , (α .nIso x)


_∘ʳⁱ_ : ∀ (K : Functor C D) → {G H : Functor B C} (β : NatIso G H)
       → NatIso (K ∘F G) (K ∘F H)
(K ∘ʳⁱ β) .trans = K ∘ʳ (β .trans)
(K ∘ʳⁱ β) .nIso x = F-Iso {F = K} (β .trans ⟦ x ⟧ , β .nIso x) .snd

module _
  {F F' : Functor C D}
  where
  private
    module D = Category D
  opNatTrans : (F ⇒ F') → ((F' ^opF) ⇒ (F ^opF))
  opNatTrans = ⇒^opFiso .Iso.fun

  opNatIso : NatIso F F' → NatIso (F' ^opF) (F ^opF)
  opNatIso = congNatIso^opFiso .Iso.fun

  isosToNatIso : (isos : ∀ x → CatIso D (F ⟅ x ⟆) (F' ⟅ x ⟆))
    → (N-hom : ∀ x y (f : C [ x , y ]) → (F ⟪ f ⟫ D.⋆ isos y .fst) ≡ (isos x .fst D.⋆ F' ⟪ f ⟫))
    → NatIso F F'
  isosToNatIso isos are-nat = record { trans = natTrans (λ x → isos x .fst) (are-nat _ _) ; nIso = λ x → isos x .snd }

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  where

  _⋆NatTrans_ : ∀ {F G H : Functor C D} →
    NatTrans F G → NatTrans G H → NatTrans F H
  _⋆NatTrans_ = seqTrans

  _⋆NatIso_ : ∀ {F G H : Functor C D} →
    NatIso F G → NatIso G H → NatIso F H
  _⋆NatIso_ = seqNatIso

  infixr 9 _⋆NatTrans_
  infixr 9 _⋆NatIso_

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  {E : Category ℓE ℓE'}
  (F : Functor C D)
  (G : Functor D E)
  where

  private
    module E = Category E

  ∘F-^opF-NatIso :
    NatIso
      ((G ^opF) ∘F (F ^opF))
      ((G ∘F F) ^opF)
  ∘F-^opF-NatIso .trans .N-ob x = E.id
  ∘F-^opF-NatIso .trans .N-hom f = E.⋆IdL _ ∙ (sym $ E.⋆IdR _)
  ∘F-^opF-NatIso .nIso x .inv = E.id
  ∘F-^opF-NatIso .nIso x .sec = E.⋆IdL (∘F-^opF-NatIso .nIso x .inv)
  ∘F-^opF-NatIso .nIso x .ret = E.⋆IdL (N-ob (∘F-^opF-NatIso .trans) x)

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  {F : Functor C D}
  {G : Functor C D}
  where
  private
    module D = Category D
  module _ (α : NatTrans F G) (α' : singl (α .N-ob)) where
    improveN-hom : N-hom-Type F G (α' .fst)
    improveN-hom = subst (N-hom-Type F G) (α' .snd) (N-hom α)
    improveNatTrans : NatTrans F G
    improveNatTrans = natTrans (α' .fst) improveN-hom

  module _ (α : NatIso F G) (α' : singl (α .trans .N-ob)) (α⁻ : singl (symNatIso α .trans .N-ob)) where
    secαα⁻ : (x : C .ob)
      → α⁻ .fst x D.⋆ α' .fst x ≡ D.id
    secαα⁻ = subst2 (λ N-ob N-ob⁻ → (x : C .ob)
      → N-ob⁻ x D.⋆ N-ob x ≡ D.id )
      (α' .snd)
      (α⁻ .snd)
      (λ x → α .nIso x .sec)

    retαα⁻ : (x : C .ob)
      → α' .fst x D.⋆ α⁻ .fst x ≡ D.id
    retαα⁻ = subst2 (λ N-ob N-ob⁻ → (x : C .ob)
      → N-ob x D.⋆ N-ob⁻ x ≡ D.id )
      (α' .snd)
      (α⁻ .snd)
      (λ x → α .nIso x .ret)

    improveNatIso : NatIso F G
    improveNatIso = record
      { trans = improveNatTrans (α .trans) α'
      ; nIso = λ x → isiso (α⁻ .fst x)
        (secαα⁻ x)
        (retαα⁻ x) }

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  {E : Category ℓE ℓE'}
  {F : Functor C D}
  {G : Functor C E}
  {H : Functor D E}
  {H⁻ : Functor E D}
  (ρ : (H⁻ ∘F H) ≅ᶜ Id)
  where
  private
    module D = Category D
    retrMovePost' : (H ∘F F) ≅ᶜ G → F ≅ᶜ (H⁻ ∘F G)
    retrMovePost' HF≅G =
      -- F
      (symNatIso $ CAT⋆IdR {F = F})
      -- Id ∘F F
      ⋆NatIso (F ∘ˡi symNatIso ρ)
      -- (H⁻ ∘F H) ∘F F
      ⋆NatIso (symNatIso $ CAT⋆Assoc F H H⁻)
      -- H⁻ ∘F (H ∘F F)
      ⋆NatIso (H⁻ ∘ʳi HF≅G)
      -- H⁻ ∘F G

  retrMovePost : (H ∘F F) ≅ᶜ G → F ≅ᶜ (H⁻ ∘F G)
  retrMovePost HF≅G = improveNatIso (retrMovePost' HF≅G)
    (_ , (funExt λ x → D.⋆IdL _ ∙ D.⟨ refl ⟩⋆⟨ D.⋆IdL _ ⟩))
    (_ , funExt λ x → D.⋆IdR _ ∙ D.⟨ D.⋆IdR _ ⟩⋆⟨ refl ⟩)

-- Composition of natural transformation/iso "squares"

-- B F C F' C'
-- G   H    H'
-- D K E K' E'
module _
  {B : Category ℓB ℓB'}
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  {E : Category ℓE ℓE'}
  {C' : Category ℓC'' ℓC'''}
  {E' : Category ℓE'' ℓE'''}
  {F : Functor B C}
  {G : Functor B D}
  {H : Functor C E}
  {K : Functor D E}
  {F' : Functor C C'}
  {H' : Functor C' E'}
  {K' : Functor E E'}
  where
  private
    module E' = Category E'
  _□NatTrans_
    : (α : NatTrans (H ∘F F) (K ∘F G))
      (β : NatTrans (H' ∘F F') (K' ∘F H))
    →      NatTrans (H' ∘F F' ∘F F) (K' ∘F K ∘F G)
  α □NatTrans β =
    improveNatTrans (
      -- H' (F' F)
      CAT⋆Assoc F F' H' .trans
      -- (H' F') F
      ⋆NatTrans (β ∘ˡ F)
      -- (K' H) F
      ⋆NatTrans symNatIso (CAT⋆Assoc F H K') .trans
      -- K' (H F)
      ⋆NatTrans (K' ∘ʳ α))
      (_ , (funExt λ x → E'.⋆IdL _ ∙ E'.⟨ refl ⟩⋆⟨ E'.⋆IdL _ ⟩))

  infixr 9 _□NatTrans_

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  CAT⋆IdL : {F : Functor C D} → NatIso (F ∘F Id) F
  CAT⋆IdL {F = F} = record { trans = natTrans (idTrans F .N-ob) (idTrans F .N-hom) ; nIso = idNatIso F .nIso }

-- B F C F' C' === C'
-- ||  H    H'     ||
-- B = B K' E' K'' C'
module _
  {B : Category ℓB ℓB'}
  {C : Category ℓC ℓC'}
  {C' : Category ℓC'' ℓC'''}
  {E' : Category ℓE'' ℓE'''}
  {F : Functor B C}
  {F' : Functor C C'}
  {H : Functor C B}
  {H' : Functor C' E'}
  {K' : Functor B E'}
  {K'' : Functor E' C'}
  where
  private
    module C' = Category C'
    module E' = Category E'
    module K'' = Functor K''
  Mate : (ε : NatTrans (H ∘F F) Id) (α : NatTrans (H' ∘F F') (K' ∘F H)) (η : NatTrans Id (K'' ∘F H'))
    → NatTrans (F' ∘F F) (K'' ∘F K')
  Mate ε α η = improveNatTrans
    -- F' F
    ((symNatIso CAT⋆IdR .trans ⋆NatTrans (η ∘ˡ (F' ∘F F)))
    ⋆NatTrans symNatIso (CAT⋆Assoc (F' ∘F F) H' K'') .trans
    -- K'' H' F' F
    ⋆NatTrans (K'' ∘ʳ
      -- H' F' F
      (CAT⋆Assoc _ _ _ .trans
      ⋆NatTrans α ∘ˡ F
      -- K' H F
      ⋆NatTrans symNatIso (CAT⋆Assoc _ _ _) .trans
      ⋆NatTrans (K' ∘ʳ ε)
      ⋆NatTrans CAT⋆IdL .trans)
      -- H'
      ))
    -- K'' K'
    $ (λ x → η  ⟦ F' ⟅ F ⟅ x ⟆ ⟆ ⟧ C'.⋆ K'' ⟪ α ⟦ F ⟅ x ⟆ ⟧ ⟫ C'.⋆ K'' ⟪ K' ⟪ ε ⟦ x ⟧ ⟫ ⟫)
    , funExt λ x → C'.⟨ C'.⋆IdL _ ⟩⋆⟨ C'.⋆IdL _ ∙ cong K''.F-hom (E'.⋆IdL _ ∙ E'.⟨ refl ⟩⋆⟨ E'.⋆IdL _ ∙ E'.⋆IdR _ ⟩) ∙ K''.F-seq _ _ ⟩

-- Component of a path of natural transformations: the eliminator
-- matching `makeNatTransPath`.
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {F G : Functor C D}
  {α β : NatTrans F G} where
  N-obPath : α ≡ β → (c : C .Category.ob) → α .N-ob c ≡ β .N-ob c
  N-obPath p c = cong (λ γ → γ .N-ob c) p
