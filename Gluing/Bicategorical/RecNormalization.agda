{-# OPTIONS --lossy-unification #-}
{-
  Normalization for the free cartesian closed category, through the
  RECURSOR applied to the Artin comma category over presheaves on the
  category `Ren` of contexts and renamings.

  The glue that carries canonicity and conservativity carries the
  presheaf semantics but not reify and reflect, which are indexed by
  the type and so cannot be produced by `rec`.  They are supplied by
  moving to the category of glue objects EQUIPPED with a reify and a
  reflect: the forgetful functor to the glue is bijective on
  morphisms, so every universal property of `Artin` transfers, and
  what has to be built is the reify/reflect data at the terminal
  object, at a product and at the exponential.

  `rec`'s object action is the identity only up to the comparison
  functor `T`, so the last step identifies `T`'s comparison
  isomorphism with the transport along `T-ob : T ⟅ A ⟆ ≡ A`; that is
  what indexes the normal form by the type the morphism actually has.
-}
module Gluing.Bicategorical.RecNormalization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Quiver.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Unit

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Cartesian.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Exponentials
open import Cubical.Categories.Limits.Pullback.Alt
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.StrictHom
open import Cubical.Categories.Presheaf.Nerve
open import Cubical.Categories.Instances.Sets

import Cubical.Categories.Instances.Free.CartesianClosedCategory.Forded
  as FCCC
open import
  Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
  using (Quiver→×⇒Quiver ; ↑_ ; CCCExpr)
open CCCExpr renaming (_×_ to _×ᵗ_ ; ⊤ to ⊤ᵗ ; _⇒_ to _⇒ᵗ_)

import Gluing.Bicategorical.Artin as Artin
open import Gluing.Bicategorical.CanonicityCore using (module Exp)
open import Gluing.Bicategorical.NormalForms

private
  variable ℓQ ℓQ' : Level

open Category
open Functor
open PshHomStrict
open UniversalElement
open CartesianCategory using (C ; term ; bp)
open CartesianClosedCategory using (CC ; exps)

module _ (Q : Quiver ℓQ ℓQ') (isSetOb : isSet (Q .fst))
  (isSetMor : isSet (QuiverOver.mor (Q .snd))) where

  open NF Q isSetOb

  private
    ℓ = ℓ-max ℓQ ℓQ'
    ×⇒Q = Quiver→×⇒Quiver Q
    module Q = QuiverOver (Q .snd)
    module 𝒞 = CartesianClosedCategory FREECCC
    module E = Exp FREECCC

  -- contexts and renamings, interpreted in the syntax
  ι : Functor Ren 𝒞.C
  ι .F-ob = ⟦_⟧c
  ι .F-hom = ⌜_⌝r
  ι .F-id = ⌜⌝r-id
  ι .F-seq ρ σ = ⌜⌝r-seq ρ σ

  PSH : CartesianClosedCategory _ _
  PSH = CCC-PRESHEAF Ren ℓ

  private module PSH = CartesianClosedCategory PSH

  nerve : Functor 𝒞.C PSH.C
  nerve = Nerve ι

  nerve-bp : preservesProvidedBinProducts nerve 𝒞.bp
  nerve-bp = Nerve-pres-bp ι 𝒞.bp

  GLUE : CartesianClosedCategory _ _
  GLUE .CC .C =
    Artin.GlCCC FREECCC PSH nerve (Artin.PSHPullbacks Ren ℓ) nerve-bp
  GLUE .CC .term = Artin.glueTerminal' nerve 𝒞.term
  GLUE .CC .bp =
    Artin.bpGlCCC FREECCC PSH nerve (Artin.PSHPullbacks Ren ℓ) nerve-bp
  GLUE .exps =
    Artin.glueExponentials' FREECCC PSH nerve
      (Artin.PSHPullbacks Ren ℓ) nerve-bp

  private module GLUE = CartesianClosedCategory GLUE

  -- normal forms at a fixed type, as a presheaf on `Ren`
  NfPsh : Ty → Presheaf Ren ℓ
  NfPsh A .F-ob Γ = Nf Γ A , isSetNf isSetMor
  NfPsh A .F-hom = renNf
  NfPsh A .F-id = funExt renNfId
  NfPsh A .F-seq ρ σ = funExt (renNfSeq σ ρ)

  -- a normalization structure on a glue object: reify and reflect,
  -- natural, and compatible with the structure map
  module _ (P : Presheaf Ren ℓ) (X : Ty)
    (α : PshHomStrict P (nerve ⟅ X ⟆)) where
    private module P = PresheafNotation P

    record NormStr : Type ℓ where
      field
        reflect : ∀ Γ → Ne Γ X → P.p[ Γ ]
        reify : ∀ Γ → P.p[ Γ ] → Nf Γ X
        reflectNat : ∀ {Δ Γ} (ρ : Ren [ Δ , Γ ]) (n : Ne Γ X)
          → reflect Δ (renNe ρ n) ≡ ρ P.⋆ reflect Γ n
        reifyNat : ∀ {Δ Γ} (ρ : Ren [ Δ , Γ ]) (p : P.p[ Γ ])
          → reify Δ (ρ P.⋆ p) ≡ renNf ρ (reify Γ p)
        reifyOk : ∀ Γ (p : P.p[ Γ ]) → ⌜ reify Γ p ⌝nf ≡ α .N-ob Γ p
        reflectOk : ∀ Γ (n : Ne Γ X) → α .N-ob Γ (reflect Γ n) ≡ ⌜ n ⌝ne

  open NormStr

  StrOf : GLUE.C .ob → Type ℓ
  StrOf u = NormStr (u .fst .fst) (u .fst .snd) (u .snd)

  -- the glue with reify/reflect on its objects; the hom-sets, and so
  -- every universal property, are the glue's
  NORM : Category _ _
  NORM .ob = Σ[ u ∈ GLUE.C .ob ] StrOf u
  NORM .Hom[_,_] u v = GLUE.C [ u .fst , v .fst ]
  NORM .id = GLUE.C .id
  NORM ._⋆_ = GLUE.C ._⋆_
  NORM .⋆IdL = GLUE.C .⋆IdL
  NORM .⋆IdR = GLUE.C .⋆IdR
  NORM .⋆Assoc = GLUE.C .⋆Assoc
  NORM .isSetHom = GLUE.C .isSetHom

  -- the terminal object: reify is the unique normal form of unit type
  private
    termStr : StrOf (GLUE.term .vertex)
    termStr .reflect Γ n = ⌜ n ⌝ne
    termStr .reify Γ p = ttₙ
    termStr .reflectNat ρ n = neNat ρ n
    termStr .reifyNat ρ p = refl
    termStr .reifyOk Γ p = 𝒞.𝟙extensionality
    termStr .reflectOk Γ n = refl

  termNORM : Terminal' NORM
  termNORM .vertex = GLUE.term .vertex , termStr
  termNORM .element = GLUE.term .element
  termNORM .universal Γ = GLUE.term .universal (Γ .fst)

  -- binary products: reify a pair, reflect through the projections
  private
    module _ (gu gv : GLUE.C .ob) where
      private
        gp = GLUE.bp (gu , gv)
        γ = gp .vertex .snd

      pβ₁ : ∀ Γ ab → γ .N-ob Γ ab 𝒞.⋆ 𝒞.π₁ ≡ gu .snd .N-ob Γ (ab .fst)
      pβ₁ Γ ab i = gp .element .fst .snd i .N-ob Γ ab

      pβ₂ : ∀ Γ ab → γ .N-ob Γ ab 𝒞.⋆ 𝒞.π₂ ≡ gv .snd .N-ob Γ (ab .snd)
      pβ₂ Γ ab i = gp .element .snd .snd i .N-ob Γ ab

    module _ (u v : NORM .ob) where
      private
        γ = GLUE.bp (u .fst , v .fst) .vertex .snd

      bpStr : StrOf (GLUE.bp (u .fst , v .fst) .vertex)
      bpStr .reflect Γ n =
        u .snd .reflect Γ (π₁ₙ n) , v .snd .reflect Γ (π₂ₙ n)
      bpStr .reify Γ ab =
        pairₙ (u .snd .reify Γ (ab .fst)) (v .snd .reify Γ (ab .snd))
      bpStr .reflectNat ρ n = ΣPathP
        ( u .snd .reflectNat ρ (π₁ₙ n)
        , v .snd .reflectNat ρ (π₂ₙ n))
      bpStr .reifyNat ρ ab = cong₂ pairₙ
        (u .snd .reifyNat ρ (ab .fst)) (v .snd .reifyNat ρ (ab .snd))
      bpStr .reifyOk Γ ab = 𝒞.,p≡ {g = γ .N-ob Γ ab}
        (u .snd .reifyOk Γ (ab .fst) ∙ sym (pβ₁ (u .fst) (v .fst) Γ ab))
        (v .snd .reifyOk Γ (ab .snd) ∙ sym (pβ₂ (u .fst) (v .fst) Γ ab))
      bpStr .reflectOk Γ n = 𝒞.,p-extensionality
        (pβ₁ (u .fst) (v .fst) Γ _ ∙ u .snd .reflectOk Γ (π₁ₙ n))
        (pβ₂ (u .fst) (v .fst) Γ _ ∙ v .snd .reflectOk Γ (π₂ₙ n))

  bpNORM : BinProducts NORM
  bpNORM (u , v) .vertex = GLUE.bp (u .fst , v .fst) .vertex , bpStr u v
  bpNORM (u , v) .element = GLUE.bp (u .fst , v .fst) .element
  bpNORM (u , v) .universal Γ =
    GLUE.bp (u .fst , v .fst) .universal (Γ .fst)

  -- neutrals at a fixed type, as a presheaf, and the glue object they
  -- form; `reflect` at an exponential is transposed out of it
  NePsh : Ty → Presheaf Ren ℓ
  NePsh A .F-ob Γ = Ne Γ A , isSetNe isSetMor
  NePsh A .F-hom = renNe
  NePsh A .F-id = funExt renNeId
  NePsh A .F-seq ρ σ = funExt (renNeSeq σ ρ)

  neα : (A : Ty) → PshHomStrict (NePsh A) (nerve ⟅ A ⟆)
  neα A .N-ob Γ n = ⌜ n ⌝ne
  neα A .N-hom Δ Γ ρ n' n eq = sym (neNat ρ n') ∙ cong ⌜_⌝ne eq

  NeGl : Ty → GLUE.C .ob
  NeGl A = (NePsh A , A) , neα A

  private
    ldaApp : ∀ {X Y} → 𝒞.lda {c = X} {d = Y} (𝒞.app {c = X} {d = Y})
      ≡ 𝒞.id
    ldaApp = E.ldaExt
      (E.ldaβ _ ∙ sym (cong (𝒞._⋆ 𝒞.app) E.plId ∙ 𝒞.⋆IdL _))

    ⌜⌝r-wkRen : ∀ {Γ A} → ⌜ wkRen {Γ} {A} ⌝r ≡ 𝒞.π₁ {a = ⟦ Γ ⟧c} {b = A}
    ⌜⌝r-wkRen {Γ} {A} =
      ⌜⌝r-wk {A = A} idRen
      ∙ cong (𝒞.π₁ {a = ⟦ Γ ⟧c} {b = A} 𝒞.⋆_) (⌜⌝r-id {Γ})
      ∙ 𝒞.⋆IdR _

  -- the exponential.  Reify eta-expands: it applies the glue's
  -- evaluation to the weakening and to the reflection of a fresh
  -- variable, and abstracts.  Reflect is the transpose, out of the
  -- glue object of neutrals, of applying a neutral to the reification
  -- of its argument.
  private
    module _ (u v : NORM .ob) where
      private
        gu = u .fst
        gv = v .fst
        A = gu .fst .fst
        X = gu .fst .snd
        α = gu .snd
        B = gv .fst .fst
        Y = gv .fst .snd
        β = gv .snd
        su = u .snd
        sv = v .snd
        W : Ty
        W = 𝒞._⇒_ X Y
        ep = GLUE.exps gu gv
        eob = ep .vertex
        appD = ep .element .fst .fst
        prodOb : GLUE.C .ob → GLUE.C .ob
        prodOb g = GLUE.bp (g , gu) .vertex
        module Ap = PresheafNotation A
        module Bp = PresheafNotation B
        module Cp = PresheafNotation (eob .fst .fst)

        γNe : ∀ Δ na → prodOb (NeGl W) .snd .N-ob Δ na
          ≡ 𝒞._,p_ ⌜ na .fst ⌝ne (α .N-ob Δ (na .snd))
        γNe Δ na = sym (𝒞.,p≡
          {g = prodOb (NeGl W) .snd .N-ob Δ na}
          (sym (pβ₁ (NeGl W) gu Δ na)) (sym (pβ₂ (NeGl W) gu Δ na)))

        mPsh : PshHomStrict (prodOb (NeGl W) .fst .fst) B
        mPsh .N-ob Δ na =
          sv .reflect Δ (appₙ (na .fst) (su .reify Δ (na .snd)))
        mPsh .N-hom Δ Γ ρ na' na eq =
            sym (sv .reflectNat ρ
                  (appₙ (na' .fst) (su .reify Γ (na' .snd))))
          ∙ cong (λ z → sv .reflect Δ (appₙ (renNe ρ (na' .fst)) z))
              (sym (su .reifyNat ρ (na' .snd)))
          ∙ cong (λ z → sv .reflect Δ
                    (appₙ (z .fst) (su .reify Δ (z .snd)))) eq

        mSq : prodOb (NeGl W) .snd PSH.⋆ nerve ⟪ 𝒞.app {c = X} {d = Y} ⟫
            ≡ mPsh PSH.⋆ β
        mSq = makePshHomStrictPath (funExt₂ λ Δ na →
            cong (𝒞._⋆ 𝒞.app)
              (γNe Δ na ∙ 𝒞.⟨ refl ⟩,p⟨ sym (su .reifyOk Δ (na .snd)) ⟩)
          ∙ sym (sv .reflectOk Δ
                  (appₙ (na .fst) (su .reify Δ (na .snd)))))

        mGl : GLUE.C [ prodOb (NeGl W) , gv ]
        mGl = (mPsh , 𝒞.app {c = X} {d = Y}) , mSq

        reflGl : GLUE.C [ NeGl W , eob ]
        reflGl = GLUE.lda {c = gu} {d = gv} mGl

        appPt : ∀ Δ e' a → β .N-ob Δ (appD .N-ob Δ (e' , a))
          ≡ 𝒞._,p_ (eob .snd .N-ob Δ e') (α .N-ob Δ a) 𝒞.⋆ 𝒞.app
        appPt Δ e' a =
            sym (λ i → ep .element .snd i .N-ob Δ (e' , a))
          ∙ cong (𝒞._⋆ 𝒞.app) (sym (𝒞.,p≡
              {g = prodOb eob .snd .N-ob Δ (e' , a)}
              (sym (pβ₁ eob gu Δ (e' , a)))
              (sym (pβ₂ eob gu Δ (e' , a)))))

        vz : ∀ {Γ} → Ne (X ∷ Γ) X
        vz = var (inl refl)

      expStr : StrOf eob
      expStr .reflect Γ n = reflGl .fst .fst .N-ob Γ n
      expStr .reify Γ e = lamₙ (sv .reify (X ∷ Γ)
        (appD .N-ob (X ∷ Γ)
          (wkRen Cp.⋆ e , su .reflect (X ∷ Γ) vz)))
      expStr .reflectNat ρ n =
        sym (reflGl .fst .fst .N-hom _ _ ρ n (renNe ρ n) refl)
      expStr .reifyNat ρ e =
          cong (λ z → lamₙ (sv .reify _ z))
            (sym (appD .N-hom _ _ (liftRen ρ) _ _
              (ΣPathP
                ( sym (Cp.⋆Assoc (liftRen ρ) wkRen e)
                  ∙ Cp.⋆Assoc wkRen ρ e
                , sym (su .reflectNat (liftRen ρ) vz)))))
        ∙ cong lamₙ (sv .reifyNat (liftRen ρ) _)
      expStr .reifyOk Γ e =
          cong (𝒞.lda {c = X} {d = Y})
            ( sv .reifyOk (X ∷ Γ) _
            ∙ appPt (X ∷ Γ) (wkRen Cp.⋆ e) (su .reflect (X ∷ Γ) vz)
            ∙ cong (𝒞._⋆ 𝒞.app) (𝒞.⟨ wkPt ⟩,p⟨ vzPt ⟩))
        ∙ E.ldaExt (E.ldaβ _)
        where
        wkPt : eob .snd .N-ob (X ∷ Γ) (wkRen Cp.⋆ e)
          ≡ 𝒞.π₁ 𝒞.⋆ eob .snd .N-ob Γ e
        wkPt = sym (eob .snd .N-hom _ _ wkRen e (wkRen Cp.⋆ e) refl)
             ∙ cong (𝒞._⋆ eob .snd .N-ob Γ e) ⌜⌝r-wkRen

        vzPt : α .N-ob (X ∷ Γ) (su .reflect (X ∷ Γ) vz) ≡ 𝒞.π₂
        vzPt = su .reflectOk (X ∷ Γ) vz ∙ ⌜⌝v-inl
      expStr .reflectOk Γ n =
          sym (λ i → reflGl .snd i .N-ob Γ n)
        ∙ cong (⌜ n ⌝ne 𝒞.⋆_) ldaApp
        ∙ 𝒞.⋆IdR _

  expNORM : AllExponentiable NORM bpNORM
  expNORM u v .vertex = GLUE.exps (u .fst) (v .fst) .vertex , expStr u v
  expNORM u v .element = GLUE.exps (u .fst) (v .fst) .element
  expNORM u v .universal w =
    GLUE.exps (u .fst) (v .fst) .universal (w .fst)

  NORMCCC : CartesianClosedCategory _ _
  NORMCCC .CC .C = NORM
  NORMCCC .CC .term = termNORM
  NORMCCC .CC .bp = bpNORM
  NORMCCC .exps = expNORM

  -- the interpretation of the generators: a generating object is
  -- carried by its own normal forms, where reify is the identity and
  -- reflect is the inclusion of neutrals
  nfα : (A : Ty) → PshHomStrict (NfPsh A) (nerve ⟅ A ⟆)
  nfα A .N-ob Γ m = ⌜ m ⌝nf
  nfα A .N-hom Δ Γ ρ m' m eq = sym (nfNat ρ m') ∙ cong ⌜_⌝nf eq

  private
    atomStr : (o : Q .fst)
      → StrOf ((NfPsh (↑ o) , ↑ o) , nfα (↑ o))
    atomStr o .reflect Γ n = ne n
    atomStr o .reify Γ m = m
    atomStr o .reflectNat ρ n = refl
    atomStr o .reifyNat ρ m = refl
    atomStr o .reifyOk Γ m = refl
    atomStr o .reflectOk Γ n = refl

  atomOb : (o : Q .fst) → NORM .ob
  atomOb o = ((NfPsh (↑ o) , ↑ o) , nfα (↑ o)) , atomStr o

  private
    genPsh : (g : Q.mor)
      → PshHomStrict (NfPsh (↑ (Q.dom g))) (NfPsh (↑ (Q.cod g)))
    genPsh g .N-ob Γ m = ne (genₙ g m)
    genPsh g .N-hom Δ Γ ρ m' m eq = cong (λ z → ne (genₙ g z)) eq

  atomHom : (g : Q.mor)
    → NORM [ atomOb (Q.dom g) , atomOb (Q.cod g) ]
  atomHom g = (genPsh g , FCCC.↑ₑ ×⇒Q g) , makePshHomStrictPath refl

  S : Functor 𝒞.C NORM
  S = FCCC.rec ×⇒Q NORMCCC (FCCC.mkElimInterpᴰ atomOb atomHom)

  projSyn : Functor NORM 𝒞.C
  projSyn .F-ob u = u .fst .fst .snd
  projSyn .F-hom m = m .fst .snd
  projSyn .F-id = refl
  projSyn .F-seq _ _ = refl

  T : Functor 𝒞.C 𝒞.C
  T = projSyn ∘F S

  -- NORMALIZATION.  Reflect a variable, run the interpretation, and
  -- reify; the glue's square is exactly soundness.
  module _ {A B : Ty} (f : 𝒞.Hom[ A , B ]) where
    private
      Γ₀ : Ctx
      Γ₀ = T ⟅ A ⟆ ∷ []

      a₀ = (S ⟅ A ⟆) .snd .reflect Γ₀ (var (inl refl))
      b₀ = (S ⟪ f ⟫) .fst .fst .N-ob Γ₀ a₀

    normalize : Nf Γ₀ (T ⟅ B ⟆)
    normalize = (S ⟅ B ⟆) .snd .reify Γ₀ b₀

    soundness : ⌜ normalize ⌝nf ≡ 𝒞.π₂ 𝒞.⋆ T ⟪ f ⟫
    soundness =
        (S ⟅ B ⟆) .snd .reifyOk Γ₀ b₀
      ∙ sym (λ i → (S ⟪ f ⟫) .snd i .N-ob Γ₀ a₀)
      ∙ cong (𝒞._⋆ T ⟪ f ⟫)
          ((S ⟅ A ⟆) .snd .reflectOk Γ₀ (var (inl refl)) ∙ ⌜⌝v-inl)

  -- `T` is the identity on objects, on the nose for every closed type
  T-ob : (A : Ty) → T ⟅ A ⟆ ≡ A
  T-ob (↑ o) = refl
  T-ob (A ×ᵗ B) = cong₂ _×ᵗ_ (T-ob A) (T-ob B)
  T-ob ⊤ᵗ = refl
  T-ob (A ⇒ᵗ B) = cong₂ _⇒ᵗ_ (T-ob A) (T-ob B)

  -- and it is naturally isomorphic to the identity, by the free
  -- category's uniqueness principle, discharged exactly as for
  -- conservativity
  private
    open E using (module ⇒At)

    TCart : CartesianFunctor (FREECCC .CC) 𝒞.C
    TCart = T , λ c c' → 𝒞.bp (T ⟅ c ⟆ , T ⟅ c' ⟆) .universal

    IdCart : CartesianFunctor (FREECCC .CC) 𝒞.C
    IdCart = Id , λ c c' → 𝒞.bp (c , c') .universal

    FREE1 : Terminal 𝒞.C
    FREE1 = Terminal'ToTerminal 𝒞.term

    T-1 : preservesTerminal 𝒞.C 𝒞.C T
    T-1 = preserveOnePreservesAll 𝒞.C 𝒞.C T FREE1 (FREE1 .snd)

    Id-1 : preservesTerminal 𝒞.C 𝒞.C Id
    Id-1 = preserveOnePreservesAll 𝒞.C 𝒞.C Id FREE1 (FREE1 .snd)

    ⇒-isoT : ∀ {A B} → CatIso 𝒞.C (T ⟅ A ⟆) A
      → CatIso 𝒞.C (T ⟅ B ⟆) B
      → CatIso 𝒞.C (T ⟅ A ⇒ᵗ B ⟆) (A ⇒ᵗ B)
    ⇒-isoT f g = ⇒At.expIso f g

  T≅Id : NatIso T (Id {C = 𝒞.C})
  T≅Id = FCCC.FreeCCCFunctor≅ ×⇒Q TCart IdCart T-1 Id-1 ⇒-isoT
    (λ f g → ⇒At.evalSq f g)
    (λ f g γ h sq → ⇒At.lamSq f g γ h (T ⟪ h ⟫) sq)
    (FCCC.mkElimInterpᴰ (λ _ → idCatIso)
      (λ _ → (𝒞.⋆IdR _ ∙ sym (𝒞.⋆IdL _)) , tt))

  -- at the generating objects `T` is the identity, so normalization
  -- there is a normal form for the morphism itself
  module _ (o o' : Q .fst) (f : 𝒞.Hom[ ↑ o , ↑ o' ]) where
    private
      nat : T ⟪ f ⟫ 𝒞.⋆ 𝒞.id ≡ 𝒞.id 𝒞.⋆ f
      nat = T≅Id .NatIso.trans .NatTrans.N-hom f

      T≡ : T ⟪ f ⟫ ≡ f
      T≡ = sym (𝒞.⋆IdR _) ∙ nat ∙ 𝒞.⋆IdL f

    normalizeAt : Nf (↑ o ∷ []) (↑ o')
    normalizeAt = normalize f

    soundnessAt : ⌜ normalizeAt ⌝nf ≡ 𝒞.π₂ 𝒞.⋆ f
    soundnessAt = soundness f ∙ cong (𝒞.π₂ 𝒞.⋆_) T≡


  -- The comparison isomorphism IS the transport along `T-ob`, by
  -- induction on the type, which upgrades the natural isomorphism to
  -- a path over the objects.
  private
    ηIso : (A : Ty) → CatIso 𝒞.C (T ⟅ A ⟆) A
    ηIso A = T≅Id .NatIso.trans .NatTrans.N-ob A , T≅Id .NatIso.nIso A

    pti : {A B : Ty} → A ≡ B → CatIso 𝒞.C A B
    pti = pathToIso {C = 𝒞.C}

    idPTI : {A : Ty} → pti (refl {x = A}) .fst ≡ 𝒞.id
    idPTI = cong fst (pathToIso-refl {C = 𝒞.C})

    invPTI : {A : Ty} → pti (refl {x = A}) .snd .isIsoC.inv ≡ 𝒞.id
    invPTI = cong (λ z → z .snd .isIsoC.inv) (pathToIso-refl {C = 𝒞.C})

    module _ (A' B' : Ty) where
      mkP : (A₁ B₁ : Ty) → 𝒞.Hom[ A' , A₁ ] → 𝒞.Hom[ B' , B₁ ]
        → 𝒞.Hom[ A' ×ᵗ B' , A₁ ×ᵗ B₁ ]
      mkP A₁ B₁ x y = 𝒞._,p_ (𝒞.π₁ {a = A'} {b = B'} 𝒞.⋆ x)
                             (𝒞.π₂ {a = A'} {b = B'} 𝒞.⋆ y)

      mkE : (A₁ B₁ : Ty) → 𝒞.Hom[ A₁ , A' ] → 𝒞.Hom[ B' , B₁ ]
        → 𝒞.Hom[ A' ⇒ᵗ B' , A₁ ⇒ᵗ B₁ ]
      mkE A₁ B₁ x y = E.conj x y

      pairPTI : {A₁ B₁ : Ty} (p : A' ≡ A₁) (q : B' ≡ B₁)
        → mkP A₁ B₁ (pti p .fst) (pti q .fst)
          ≡ pti (cong₂ _×ᵗ_ p q) .fst
      pairPTI p q = J
        (λ A₁ p₁ → {B₁ : Ty} (q₁ : B' ≡ B₁)
          → mkP A₁ B₁ (pti p₁ .fst) (pti q₁ .fst)
            ≡ pti (cong₂ _×ᵗ_ p₁ q₁) .fst)
        (λ q₁ → J
          (λ B₁ q₂ → mkP A' B₁ (pti (refl {x = A'}) .fst)
                                (pti q₂ .fst)
                     ≡ pti (cong₂ _×ᵗ_ (refl {x = A'}) q₂) .fst)
          base q₁)
        p q
        where
        base : mkP A' B' (pti (refl {x = A'}) .fst)
                         (pti (refl {x = B'}) .fst)
             ≡ pti (refl {x = A' ×ᵗ B'}) .fst
        base = cong₂ (mkP A' B') idPTI idPTI
          ∙ 𝒞.,p≡ {g = 𝒞.id}
              (𝒞.⋆IdR _ ∙ sym (𝒞.⋆IdL _)) (𝒞.⋆IdR _ ∙ sym (𝒞.⋆IdL _))
          ∙ sym idPTI

      expPTI : {A₁ B₁ : Ty} (p : A' ≡ A₁) (q : B' ≡ B₁)
        → mkE A₁ B₁ (pti p .snd .isIsoC.inv) (pti q .fst)
          ≡ pti (cong₂ _⇒ᵗ_ p q) .fst
      expPTI p q = J
        (λ A₁ p₁ → {B₁ : Ty} (q₁ : B' ≡ B₁)
          → mkE A₁ B₁ (pti p₁ .snd .isIsoC.inv)
                      (pti q₁ .fst)
            ≡ pti (cong₂ _⇒ᵗ_ p₁ q₁) .fst)
        (λ q₁ → J
          (λ B₁ q₂ → mkE A' B₁ (pti (refl {x = A'}) .snd .isIsoC.inv)
                                (pti q₂ .fst)
                     ≡ pti (cong₂ _⇒ᵗ_ (refl {x = A'}) q₂) .fst)
          base q₁)
        p q
        where
        base : mkE A' B' (pti (refl {x = A'}) .snd .isIsoC.inv)
                         (pti (refl {x = B'}) .fst)
             ≡ pti (refl {x = A' ⇒ᵗ B'}) .fst
        base = cong₂ (mkE A' B') invPTI idPTI ∙ E.conjId ∙ sym idPTI

    η≡pti : (A : Ty) → ηIso A ≡ pti (T-ob A)
    η≡pti (↑ o) = CatIso≡ _ _ (sym idPTI)
    η≡pti (A ×ᵗ B) = CatIso≡ _ _
      ( cong₂ (mkP (T ⟅ A ⟆) (T ⟅ B ⟆) A B)
          (cong fst (η≡pti A)) (cong fst (η≡pti B))
      ∙ pairPTI (T ⟅ A ⟆) (T ⟅ B ⟆) (T-ob A) (T-ob B))
    η≡pti ⊤ᵗ = CatIso≡ _ _ 𝒞.𝟙extensionality
    η≡pti (A ⇒ᵗ B) = CatIso≡ _ _
      ( cong₂ (mkE (T ⟅ A ⟆) (T ⟅ B ⟆) A B)
          (cong (λ z → z .snd .isIsoC.inv) (η≡pti A))
          (cong fst (η≡pti B))
      ∙ expPTI (T ⟅ A ⟆) (T ⟅ B ⟆) (T-ob A) (T-ob B))

  private
    T-hom : {A B : Ty} (f : 𝒞.Hom[ A , B ])
      → PathP (λ i → 𝒞.Hom[ T-ob A i , T-ob B i ]) (T ⟪ f ⟫) f
    T-hom {A} {B} f =
      pathToIso-Square {C = 𝒞.C} (T-ob A) (T-ob B) _ _ sq
      where
      post1 : 𝒞.Hom[ T ⟅ B ⟆ , B ] → 𝒞.Hom[ T ⟅ A ⟆ , B ]
      post1 z = T ⟪ f ⟫ 𝒞.⋆ z

      post2 : 𝒞.Hom[ T ⟅ A ⟆ , A ] → 𝒞.Hom[ T ⟅ A ⟆ , B ]
      post2 z = z 𝒞.⋆ f

      sq : T ⟪ f ⟫ 𝒞.⋆ pti (T-ob B) .fst ≡ pti (T-ob A) .fst 𝒞.⋆ f
      sq = cong post1 (sym (cong fst (η≡pti B)))
         ∙ T≅Id .NatIso.trans .NatTrans.N-hom f
         ∙ cong post2 (cong fst (η≡pti A))

  -- NORMALIZATION, at every pair of types: the normal form produced
  -- at `T ⟅ A ⟆` transports to one at `A`, and so does soundness
  normalizeAll : {A B : Ty} (f : 𝒞.Hom[ A , B ]) → Nf (A ∷ []) B
  normalizeAll {A} {B} f =
    transport (λ i → Nf (T-ob A i ∷ []) (T-ob B i)) (normalize f)

  module _ {A B : Ty} (f : 𝒞.Hom[ A , B ]) where
    private
      tp : 𝒞.Hom[ ⟦ T ⟅ A ⟆ ∷ [] ⟧c , T ⟅ B ⟆ ]
         → 𝒞.Hom[ ⟦ A ∷ [] ⟧c , B ]
      tp = transport (λ i → 𝒞.Hom[ ⟦ T-ob A i ∷ [] ⟧c , T-ob B i ])

      nfPath : PathP (λ i → 𝒞.Hom[ ⟦ T-ob A i ∷ [] ⟧c , T-ob B i ])
        ⌜ normalize f ⌝nf ⌜ normalizeAll f ⌝nf
      nfPath i = ⌜ transport-filler
        (λ j → Nf (T-ob A j ∷ []) (T-ob B j)) (normalize f) i ⌝nf

      sqPath : PathP (λ i → 𝒞.Hom[ ⟦ T-ob A i ∷ [] ⟧c , T-ob B i ])
        (𝒞.π₂ 𝒞.⋆ T ⟪ f ⟫) (𝒞.π₂ 𝒞.⋆ f)
      sqPath i = 𝒞.π₂ {a = ⊤ᵗ} {b = T-ob A i} 𝒞.⋆ T-hom f i

    soundnessAll : ⌜ normalizeAll f ⌝nf ≡ 𝒞.π₂ 𝒞.⋆ f
    soundnessAll =
      sym (fromPathP nfPath) ∙ cong tp (soundness f) ∙ fromPathP sqPath


--------------------------------------------------------------------
-- The normalizer computes.  A walking-arrow quiver and `refl`
-- checks: refutation of a wrong normal form DIVERGES (it forces the
-- glue side), so discrimination is tested on the `Nf` data instead.
--------------------------------------------------------------------

-- the walking arrow quiver: objects {a}, one morphism g : a → a
Ob : Type
Ob = Unit

Mor : Type
Mor = Unit

Q : Quiver ℓ-zero ℓ-zero
Q = Ob , record { mor = Mor ; dom = λ _ → tt ; cod = λ _ → tt }

isSetOb : isSet (Q .fst)
isSetOb = isSetUnit

isSetMor : isSet (QuiverOver.mor (Q .snd))
isSetMor = isSetUnit

open NF Q isSetOb

private
  module 𝒞 = CartesianClosedCategory FREECCC

  A : Ty
  A = ↑ tt

  g : 𝒞.Hom[ A , A ]
  g = FCCC.↑ₑ (Quiver→×⇒Quiver Q) tt

  -- normalize the generator `g : a → a`
  nfG : Nf (A ∷ []) A
  nfG = normalizeAt Q isSetOb isSetMor tt tt g

  -- expected: the neutral `g` applied to the variable
  _ : nfG ≡ ne (genₙ tt (ne (var (inl refl))))
  _ = refl

  -- a beta redex: <g , id> then pi1.  Must REDUCE to g's normal form,
  -- not merely embed.
  redex : 𝒞.Hom[ A , A ]
  redex = 𝒞._,p_ g (𝒞.id) 𝒞.⋆ 𝒞.π₁

  _ : normalizeAt Q isSetOb isSetMor tt tt redex ≡ nfG
  _ = refl

  -- the identity normalizes to the variable
  _ : normalizeAt Q isSetOb isSetMor tt tt (𝒞.id) ≡ ne (var (inl refl))
  _ = refl

  -- HIGHER ORDER: twice = lam f. lam x. f (f x), at (A ⇒ A) ⇒ A ⇒ A.
  -- Forces `reify` under two binders, which is where `liftRen` runs.
  fx : 𝒞.Hom[ (A ⇒ᵗ A) ×ᵗ A , A ]
  fx = 𝒞.app

  ffx : 𝒞.Hom[ (A ⇒ᵗ A) ×ᵗ A , A ]
  ffx = 𝒞._,p_ 𝒞.π₁ fx 𝒞.⋆ 𝒞.app

  twice : 𝒞.Hom[ A ⇒ᵗ A , A ⇒ᵗ A ]
  twice = 𝒞.lda ffx

  Tob : Ty → Ty
  Tob X = Functor.F-ob (T Q isSetOb isSetMor) X

  nfTwice : Nf (Tob (A ⇒ᵗ A) ∷ []) (Tob (A ⇒ᵗ A))
  nfTwice = normalize Q isSetOb isSetMor twice

  -- does `T` compute on objects?
  _ : Tob A ≡ A
  _ = refl

  -- at a compound type?
  _ : Tob (A ⇒ᵗ A) ≡ A ⇒ᵗ A
  _ = refl

  -- higher order: `twice` normalizes to `\f. \x. f (f x)`
  _ : nfTwice
    ≡ lamₙ (ne (appₙ (var (inr (inl refl)))
             (ne (appₙ (var (inr (inl refl)))
               (ne (var (inl refl)))))))
  _ = refl

  -- Church one, at the same type: a DIFFERENT normal form, so the
  -- check above is discriminating and not vacuous.
  once : 𝒞.Hom[ A ⇒ᵗ A , A ⇒ᵗ A ]
  once = 𝒞.lda fx

  nfOnce : Nf (Tob (A ⇒ᵗ A) ∷ []) (Tob (A ⇒ᵗ A))
  nfOnce = normalize Q isSetOb isSetMor once

  _ : nfOnce
    ≡ lamₙ (ne (appₙ (var (inr (inl refl))) (ne (var (inl refl)))))
  _ = refl

  -- a generator under a binder: `\f. g (f x)` -- eta-expanded, so
  -- the argument is the bound variable
  gafter : 𝒞.Hom[ A ⇒ᵗ A , A ⇒ᵗ A ]
  gafter = 𝒞.lda (fx 𝒞.⋆ g)

  _ : normalize Q isSetOb isSetMor gafter
    ≡ lamₙ (ne (genₙ tt
        (ne (appₙ (var (inr (inl refl))) (ne (var (inl refl)))))))
  _ = refl

  -- two nested binders: `K = \x. \y. x`, reaching under both
  konst : 𝒞.Hom[ A , A ⇒ᵗ (A ⇒ᵗ A) ]
  konst = 𝒞.lda (𝒞.lda (𝒞.π₁ 𝒞.⋆ 𝒞.π₁))

  _ : normalize Q isSetOb isSetMor konst
    ≡ lamₙ (lamₙ (ne (var (inr (inr (inl refl))))))
  _ = refl
