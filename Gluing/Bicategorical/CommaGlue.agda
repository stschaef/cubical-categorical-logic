{-# OPTIONS --lossy-unification #-}
{-
  The canonicity glue AS the comma object supplied by `CAT`'s PIE
  limits, rather than as a category proved equal to one.

  `Commaᴮ (CAT ℓ ℓ')` takes both 0-cells from a single bicategory, so
  they must share an object level and a hom level.  The syntax is
  `Category ℓ-zero ℓ-zero`, `SET ℓ-zero` is
  `Category (ℓ-suc ℓ-zero) ℓ-zero`, and so `Commaᴮ` cannot be applied
  to `Pts` at all.  It is the syntax's OBJECT level that is too low,
  and a free construction cannot simply be redeclared higher: its hom
  HIT is indexed by its objects, so its homs sit at least at their
  level, whereas here the objects must sit ABOVE the homs.

  `LiftOb` raises exactly the object level and nothing else -- the
  homs stay literally the syntax's.  After it both 0-cells are
  `Category (ℓ-suc ℓ-zero) ℓ-zero`, `Commaᴮ` applies, and the whole
  cartesian closed structure transports with `lift`/`lower` in object
  positions and no transports at all.
-}
module Gluing.Bicategorical.CommaGlue where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Instances.ChangeOfObjects
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Cartesian.More
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Exponentials.Small

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Forded
  as FreeCCC
import Gluing.Canonicity as GC

open import Gluing.Bicategorical.Artin
open import Gluing.Bicategorical.Comma using (glueCat)
open import Gluing.Bicategorical.BoolNatCanonicity

open Category
open Functor
open UniversalElement
open CartesianCategory
open CartesianClosedCategory

-- The syntax with its objects raised to `SET ℓ-zero`'s object level.
SYN : Category (ℓ-suc ℓ-zero) ℓ-zero
SYN = LiftOb FREECCC.C (ℓ-suc ℓ-zero)

-- `lower`, as a functor SYN → syntax.  An isomorphism of categories.
syn : Functor SYN FREECCC.C
syn = lowerOb FREECCC.C (ℓ-suc ℓ-zero)

-- The cartesian closed structure transports with `lift`/`lower` in
-- the object positions and nothing else, because `LiftOb` leaves the
-- homs alone.  Every clause below is the syntax's own.
SYNterm : Terminal' SYN
SYNterm .vertex = lift (FREECCC.term .vertex)
SYNterm .element = FREECCC.term .element
SYNterm .universal x = FREECCC.term .universal (lower x)

SYNbp : BinProducts SYN
SYNbp (x , y) .vertex = lift (FREECCC.bp (lower x , lower y) .vertex)
SYNbp (x , y) .element = FREECCC.bp (lower x , lower y) .element
SYNbp (x , y) .universal z =
  FREECCC.bp (lower x , lower y) .universal (lower z)

SYNexps : AllExponentiable SYN SYNbp
SYNexps c d .vertex = lift (FREECCC.exps (lower c) (lower d) .vertex)
SYNexps c d .element = FREECCC.exps (lower c) (lower d) .element
SYNexps c d .universal z =
  FREECCC.exps (lower c) (lower d) .universal (lower z)

SYNCCC : CartesianClosedCategory (ℓ-suc ℓ-zero) ℓ-zero
SYNCCC .CC .C = SYN
SYNCCC .CC .term = SYNterm
SYNCCC .CC .bp = SYNbp
SYNCCC .exps = SYNexps

-- Global points of the lifted syntax: corepresenting at `lift ⊤`.
Pts↑Cart : CartesianFunctor (SYNCCC .CC) (SET ℓ-zero)
Pts↑Cart = CorepCartesian (SYNCCC .CC) (SYNterm .vertex)

Pts↑ : Functor SYN (SET ℓ-zero)
Pts↑ = Pts↑Cart .fst

-- Both 0-cells now live in `CAT (ℓ-suc ℓ-zero) ℓ-zero`, so this is a
-- literal application of the bicategorical comma object.
CommaGlue : Category (ℓ-suc ℓ-zero) ℓ-zero
CommaGlue = glueCat {ℓ = ℓ-suc ℓ-zero} {ℓ' = ℓ-zero} Pts↑

-- ...and it is the Artin glue, on the nose.
CommaGlue≡ArtinGlue : CommaGlue ≡ ArtinGlue Pts↑
CommaGlue≡ArtinGlue = refl

-- The glue's cartesian closed structure, built on the comma object.
GLUE↑ : CartesianClosedCategory (ℓ-suc ℓ-zero) ℓ-zero
GLUE↑ .CC .C = CommaGlue
GLUE↑ .CC .term = glueTerminal' Pts↑ SYNterm
GLUE↑ .CC .bp =
  glueBinProducts Pts↑ SYNbp BinProductsSET (Pts↑Cart .snd)
GLUE↑ .exps =
  glueExponentials Pts↑ SYNbp SYNexps (Pts↑Cart .snd)

-- `rec` lands in the comma object.  The generator interpretations are
-- the ones the original glue uses, with `lift` on the syntactic
-- component -- which is the only trace the level fix leaves.
S↑ : Functor FREECCC.C CommaGlue
S↑ = rec ×⇒QUIVER GLUE↑ (mkElimInterpᴰ
  (λ { bool → ((Bool , isSetBool) , lift (↑ bool)) , fromBool
     ; nat → ((ℕ , isSetℕ) , lift (↑ nat)) , ＂_＂ })
  (λ { tr → ((λ _ → true) , [t])
             , funExt (λ u → cong₂ _⋆ₑ_ (GC.⊤→⊤IsId FREECCC.term u) refl
                           ∙ FREECCC.⋆IdL _)
     ; fl → ((λ _ → false) , [f])
             , funExt (λ u → cong₂ _⋆ₑ_ (GC.⊤→⊤IsId FREECCC.term u) refl
                           ∙ FREECCC.⋆IdL _)
     ; ze → ((λ _ → 0) , [ze])
             , funExt (λ u → cong₂ _⋆ₑ_ (GC.⊤→⊤IsId FREECCC.term u) refl
                           ∙ FREECCC.⋆IdL _)
     ; su → (suc , [su]) , funExt (λ n → refl) }))

-- the comma object's second projection, then back down the lift
projSyn↑ : Functor CommaGlue SYN
projSyn↑ .F-ob g = g .fst .snd
projSyn↑ .F-hom m = m .fst .snd
projSyn↑ .F-id = refl
projSyn↑ .F-seq _ _ = refl

T↑ : Functor FREECCC.C FREECCC.C
T↑ = syn ∘F projSyn↑ ∘F S↑

-- The level fix costs nothing definitionally: `T↑` is still a
-- STRICT cartesian closed endofunctor on the syntax, exactly as the
-- unlifted `T` is, because `Lift` has eta and `lower (lift x)` is
-- `x` on the nose.  These are the strictness facts the uniqueness
-- principle consumes.
objEq↑ : (A : FREECCC.C .ob) → T↑ ⟅ A ⟆ ≡ A
objEq↑ (↑ bool) = refl
objEq↑ (↑ nat) = refl
objEq↑ ⊤ = refl
objEq↑ (A × B) = cong₂ CCCExpr._×_ (objEq↑ A) (objEq↑ B)
objEq↑ (A ⇒ B) = cong₂ CCCExpr._⇒_ (objEq↑ A) (objEq↑ B)

T↑-⇒ : ∀ {A B} → T↑ ⟅ CCCExpr._⇒_ A B ⟆
                 ≡ CCCExpr._⇒_ (T↑ ⟅ A ⟆) (T↑ ⟅ B ⟆)
T↑-⇒ = refl

T↑-lam : ∀ {Γ A B} (h : Expr ×⇒QUIVER (CCCExpr._×_ Γ A) B)
  → T↑ ⟪ FreeCCC.lam' ×⇒QUIVER h ⟫
    ≡ FreeCCC.lam' ×⇒QUIVER (T↑ ⟪ h ⟫)
T↑-lam h = refl

