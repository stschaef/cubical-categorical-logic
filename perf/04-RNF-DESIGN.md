# ReindNormalForm (RNF): the agreed design

Status: framework under construction. This file records the design and the evidence behind each
decision, so the build can be checked against it and so a later reader knows which choices were
measured and which were taste.

## The idea

Never represent a value of a dependent type `B a` directly. Represent it as a value at SOME index
`B a'` together with a path `a ≡ a'`. Then `reind` composes the stored path and leaves the payload
alone, so a nested transport can never arise and a tower of reinds is still exactly one reind.

The point is NOT that each chain link gets cheaper. It is that **the filler steps stop existing**.
Today every crossing between `p` and `reind e p` needs a `reind-filler` step to relate them, and
those steps ARE the proof: 34 of 71 chain links (48%) in `Quantifiers/Base.agda`, 11 of 28 (39%)
in `ComposeWeakening.agda`; 589 `reind-filler` occurrences library-wide, 337 standing as a whole
chain step. Under RNF the payload does not move, so N fillers collapse to ONE path-coherence step
(`RNF≡ isSet refl refl`) for the whole chain.

## Base definition

```agda
module RNF {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ') where

  opaque
    _∙ᴿ_ : ∀ {a b c : A} → a ≡ b → b ≡ c → a ≡ c     -- the ONLY place paths are composed
    p ∙ᴿ q = p ∙ q

  record ReindNormalForm (a : A) : Type (ℓ-max ℓ ℓ') where
    no-eta-equality
    constructor rnf
    field {idx} : A ; pth : a ≡ idx ; val : B idx

  reind : ∀ {a a'} → a ≡ a' → ReindNormalForm a → ReindNormalForm a'
  reind q x = rnf (sym q ∙ᴿ x .pth) (x .val)        -- BY PROJECTIONS, not pattern matching

  nf : ∀ {a} → B a → ReindNormalForm a               -- unit
  nf v = rnf refl v
  un : ∀ {a} → ReindNormalForm a → B a               -- BOUNDARY ONLY: a real transport
  un x = subst B (sym (x .pth)) (x .val)
```

## The five decisions

**D1 — `_∙ᴿ_` opaque.** Not required for correctness: transparent and opaque both check and both
keep the collapse definitional. Kept because it costs nothing measurable and is the single
throttle point if a chain ever does start nesting. Context: a >326 GB heap exhaustion was observed
in a DIFFERENT construction, where the stored path was itself built from other stored paths
(`F-seq _ _ ∙ cong₂ D._⋆_ (fᴰ .pth) (gᴰ .pth)`); a one-line opaque constant brought it to 1.94 GB.
That shape is not present here, but the throttle is free insurance.

**D2 — `no-eta-equality`, and `reind` defined BY PROJECTIONS.** Measured, not chosen: with
`no-eta-equality`, `reind q (rnf p v) = …` is rejected outright with `[SplitOnNonEtaRecord]` —
you cannot pattern-match on the record at all. Agda suggests adding `pattern` to the record
declaration; DO NOT — that disables copattern matching for the record, which this library uses
everywhere (`ComatchingDisabledForRecord`). Defining by projections works and keeps everything
definitional. **Style rule, and it belongs in the module header: never pattern-match on
`ReindNormalForm`, always project.**
Why no-eta at all: it is Amy's definitional-injectivity property (see 03-SPELLING.md), which is
what makes `_` inference work and what every source-level win on this branch turns out to rely on.

**D3 — `pth : a ≡ idx`,** not `idx ≡ a`, so `nf v = rnf refl v` is the obvious unit and `reind`
prepends.

**D4 — mirror the existing `depReasoning`/`hSetReasoning` split.** `RNF` general; a second module
taking `isSet A` adding

```agda
  RNF≡ : isSet A → {x y : ReindNormalForm a}
       → (ip : x .idx ≡ y .idx) → PathP (λ i → B (ip i)) (x .val) (y .val) → x ≡ y
```

so the path component is discharged ONCE PER CHAIN rather than once per crossing. That step is
what replaces the N `reind-filler`s, and it is the entire performance claim.

**D5 — functions: provide BOTH forms, hereditary primary.** They are not freely interderivable —
checked: crossing costs a transport in both directions, because the two normal forms sit at
different indices and the argument's payload must be moved.
  * `Fun₁ a = RNF B a → RNF C a` (hereditary) — PRIMARY.
    `reind→ q f x = reind q (f (reind (sym q) x))` creates no subst in EITHER variance;
    application is transport-free. `_⋆ᴰ_` should be built from this, i.e. composition is a USE of
    the algebra, not a new primitive.
  * `Fun₂ = RNF (λ a → B a → C a)` (family) — for when a function family genuinely is the thing
    being reindexed. Payload preservation still definitional.
  * The crossing between them is named explicitly in the interface as a transport boundary, so
    nobody does it by accident inside a chain.

## Verified definitional under exactly this design (no-eta AND opaque composition both on)

`reind-val`, `reind-idx`, `nf-val`, depth-4 `tower`, `reind→` application, `reind₂-val`.
Also verified against the REAL `Categoryᴰ`/`Fibers` rather than a toy: depth-6 tower collapse is
`refl`. Prototypes: `$SP/demo/{RNFDemo,B-nf,Chain,Design,NoEta,NoEta2,Fun}.agda`.

Closure results (from `$SP/shared/ReindNormalForm.agda`, all Agda-checked): payload preservation
and tower collapse at any depth DEFINITIONAL; ×, ⊎ and → including application DEFINITIONAL;
dependent Σ and → naturality PROPOSITIONAL but payload-constant, discharged by one `isSet` on the
base — i.e. exactly the library's existing `rectify`. Counterexample probes showing the
propositional ones genuinely cannot be `refl` are in the `NFProbe` files.

## Build order, and why it matters

1. The framework, generic in `B`.
2. The type-former algebra: ×, ⊎ (definitional), → per D5, dependent Σ with the payload-constant
   filler supplied ONCE so callers never write it.
3. Only then instantiate: `Homⁿ := ReindNormalForm (Cᴰ.Hom[_][ xᴰ , yᴰ ])` at the single
   augmentation site `Instances/Fiber.agda:32-34`, where today
   `module R … = hSetReasoning (C [ a , b ] , C.isSetHom) Cᴰ.Hom[_][ aᴰ , bᴰ ]` is instantiated and
   re-exported. `idⁿ`/`_⋆ⁿ_`/the reasoning combinators come from the algebra, not hand-written.
4. The displayed-presheaf case (`Pⱽ.reind`) is a SECOND instantiation of the SAME framework. If it
   needs anything the framework lacks, the framework is wrong and gets fixed generically. That is
   the cheapest test of the design, and it is available before committing to any conversion.

Building the specialisation first would mean re-proving closure at every instantiation, tangling
the type-former algebra with category structure, and being unable to tell whether a failure is in
the theory or the instantiation. It also keeps the augmentation of the existing displayed-category
code to a thin, auditable adapter — report the adapter diff size per site alongside any
measurement, since that is what determines adoptability.

## What would falsify this

The deliverable is the GESTALT measurement, not component perturbations: one whole prohibitively
slow proof — `∀ⱽPsh-introᴰ⁻' .N-homᴰ` (21.9 GB, in a module where 48% of chain links are fillers) —
rewritten end to end, reporting filler-step counts and total allocation before and after. Four
earlier measurements were invalid precisely because they held chain length fixed and perturbed one
component (insert a link; rename an endpoint; collapse one tower; abstract two fillers behind an
opaque lemma). Those cannot see an effect whose mechanism is that the chain gets SHORTER.

---

# RESULT: the gestalt measurement

Branch `perf-nf-wholeproof` (worktree `/home/steven/ccl-wholeproof`), from 5669a697.
GHC bytes allocated, deterministic, reproduced to ~0.1% across two rebuilds.

## Headline

    the proof (∀ⱽPsh-introᴰ⁻' .N-homᴰ), original      21.45 GB
    the proof, rewritten in RNF                        3.56 GB      6.0x  (-83%)
    Quantifiers/Base.agda, whole module     44.33 -> 27.51 GB      1.61x  (-38%)

Framework + both adapters cost 1.09 GB in that module. Full library `--build-library`:
778 modules, rc=0, no warnings.

## Chain compression — the predicted mechanism, observed

                                    steps   filler steps   substantive
    original (as written)             21          10           11
    original (as elaborated)          25          14           11
    rewritten                         13           3           10

**11 filler steps disappeared.** Source 45 -> 32 lines. The 3 survivors are irreducible boundary
crossings: two because `N-obᴰ` must return at a fixed index, one from the reindexed presheaf's
action, which was not converted. Both versions contain the same 11 unchanged base-category steps.

## The saving is not paid for elsewhere

    Properties                  135.96 -> 136.02   (+0.05%)
    ComposeWeakening             86.08 ->  86.11   (+0.03%)
    UniversalProperty/Quantifiers 3.89 ->   3.91
    cone total                  270.2  -> 253.5 GB  (-6.2%)

## Adapter sizes — the framework-first ordering vindicated

    generic framework  Cubical/Foundations/ReindNormalForm.agda   441 lines / 218 code
    Fiber.agda adapter                                            +12 lines /   3 code
    displayed-presheaf adapter                                                  2 code
    problem-specific cartesian-lift layer (Quantifiers/Base)                   49 code

The presheaf instantiation **needed nothing the framework did not already provide**, and depth-4
tower collapse is `refl` there too. That was the falsification test for the generic design and it
passed. `introⁿ (mkⁿ e v)` is DEFINITIONALLY `introπF* (Cᴰ.reind (sym e) v)`, so
`weakenπFᴰ .F-homᴰ` and `∀ⱽPsh-introᴰ⁻' .N-obᴰ` were already in normal form on the nose and needed
no editing at all — which is why the diff stays small.

## Where the fillers actually went

They did not vanish from the world. The adapter contains 8 `reind-filler` occurrences inside three
small `opaque` lemmas (`βⁿ`, `introⁿ≡`, `introⁿ-natural`), elaborated ONCE EACH IN A TINY CONTEXT
instead of once per use inside a 21 GB elaboration. That relocation, plus the chain shortening it
enables, is the mechanism — worth 17.9 GB on one proof.

## Three forced deviations from the spec above

1. **`_∙ᴿ_` must be TOP-LEVEL opaque, not inside `module RNF B`.** Inside, every instantiation gets
   a distinct opaque symbol, so a stored path built at `RNF B` is not definitionally equal to the
   same path at `RNF (λ a → B a ⊎ C a)`, and `Sums.case-reind` fails immediately. One shared symbol
   is still a single throttle point. Same for the `cong`/`cong₂` used to build stored paths.
   **D1 as written above is wrong; this supersedes it.**
2. `no-eta-equality` blocks η, so `rnf (x .pth) (x .val) ≡ x` is unavailable. `Iso-RNF`'s
   retraction becomes a copattern path; `Sums.caseRNF`/`case-reind` go through a payload helper.
   D2 and D4 are otherwise compatible — `RNF≡` by copatterns type-checks under `no-eta-equality`.
3. One `refl` lemma cannot be STATED: `DepSigma.reind-filler q x i .snd .val ≡ x .val`. Agda will
   not project through `reind-filler q x i .snd` outside a clause head under `no-eta-equality`.
   Constancy is visible in the clauses; documented rather than asserted.

## Two honest negatives

* **Removing `unfolding hSetReasoning.reind` is NOT evidence for the normal form.** The rewritten
  proof does not need it (27.48 GB without) — but neither does the original (46.01 GB without, so
  the `unfolding` was HELPING the original by 3.8%). The allocation numbers are the evidence.
* **`introⁿ` is irreducibly one transport per use.** `introᴰ` for a cartesian lift is a fibrewise
  map over a REINDEXED base (domain family `Cᴰ.Hom[_]` pulled back along `(_⋆ π)`); a normal form
  over the pulled-back family cannot receive a hom known at the base family without a transport,
  and vice versa. The win comes from paying that inside `introⁿ`/`βⁿ`/`introⁿ≡` rather than as a
  chain step — not from eliminating it.

## Why four earlier measurements said otherwise

Each held chain length fixed and perturbed one component: inserting or deleting a single link and
differencing (3.4-23.2 GB/link, 7x spread by position); renaming an endpoint to a top-level `Def`
(+0.13%); collapsing one tower (-6.2%); abstracting two adjacent fillers behind an opaque lemma
(-6.2%, and +18% at another site). The mechanism is that the chain gets SHORTER, so a
fixed-length perturbation cannot see it. The maintainer identified this; the correct framing is
"the gestalt equational proof, not just its components".

---

# RESULT: the full corpus

All four Quantifiers modules converted. Both arms fully rebuilt from scratch, then measured
module-by-module (GHC bytes allocated), with the `Fibers.RNFᴴ` adapter and framework import held
constant in both arms.

    module                                  before      after     ratio
    Quantifiers/Base                        44.333     27.639     1.60x
    Quantifiers/Properties                  52.826      8.186     6.45x
    UniversalProperty/ComposeWeakening      86.110     17.659     4.88x
    UniversalProperty/Quantifiers            3.914      3.927     1.00x  (import floor)
    CORPUS                                 187.183     57.411     3.26x  (-69.3%)

Proof terms alone, by stub-out differencing:

    Fᴰ-weakening-NatTransᴰ .N-homᴰ          22.37       1.76     12.7x
    ∀ⱽPsh-ηᴰ'                               77.45       8.99      8.6x
    ∀ⱽPsh-introᴰ⁻' .N-homᴰ (first round)    21.45       3.56      6.0x

Chain compression at the displayed level (base-category steps byte-identical in both arms):

    target                      steps        elaborated filler steps
    Fᴰ-weakening .N-homᴰ        18 -> 9              15 -> 0
    ∀ⱽPsh-ηᴰ'                   14 -> 9               9 -> 2
    ∀ⱽPsh-introᴰ⁻' .N-homᴰ      21 -> 13             14 -> 3

Surviving fillers are irreducible boundary crossings, one per definition boundary, because
`N-obᴰ` must return at a fixed index. They cannot be merged: `∀ⱽPsh-introᴰ'` cannot see inside its
abstract argument.

## THE CONTROL that settles the earlier dispute

An intermediate arm with the normal-form ENDPOINT but the ORIGINAL proof costs **52.545** against
the original's 52.858 — no better. **Neither half pays alone.** Putting the endpoint in normal
form only pays once the chain over it is too.

This directly refutes the "+0.13% from renaming the endpoint to a top-level `Def`" experiment that
had been taken as showing the endpoint-size channel was worth zero. It measured one half of a
mechanism that only works as a whole — the same error as the other three component measurements.

## Framework changes: NONE

`Cubical/Foundations/ReindNormalForm.agda` is byte-identical since its first commit; zero commits
touch it. All three proofs were absorbed by adapter lemmas, +28 code lines total in the
`UniversalQuantifierFPsh` adapter:

    βⁿe         (4 lines)  β against elementⱽ rather than π-πF*; βⁿ restated through it
    β-weakenⁿ   (8 lines)  β for the weakening functor, W γ ⋆ᴰ elementⱽ ≡ elementⱽ ⋆ᴰ γ.
                           This is the three-step/two-filler idiom every weakenπFᴰ proof
                           open-codes; one step and no fillers at the use site.
    introⁿ≡e    (9 lines)  intro≡ with elementⱽ on the right; introⁿ≡ restated through it

All the same pattern: a β/η law restated against `∫ⁿ`, absorbing its reind crossings once.
Proof diffs: Properties +40/-43, ComposeWeakening +18/-27. Four proofs, two instantiations, no
generic changes — the falsification test for the framework-first design, passed four times.

## Against the strict-Eq route

`UniversalProperty/Quantifiers` (3.92 GB) is essentially this cone's import floor. Above floor the
corpus goes **171.5 -> 41.7 GB (4.1x)**. The Eq route is 67.5 GB across 11 modules at a ~3.5 GB
floor, i.e. ~29 GB of marginal mathematics. The gap in actual mathematical content therefore closes
from ~5.9x to **~1.4x**. Different modules proving different things, so this is not a like-for-like
race — but it is now a comparison of comparable magnitudes rather than a projection, which is what
the question "is Eq still forced?" needed.

## RETRACTION: the "42% irreducible base path" does not survive

An earlier bisection attributed 32.4 GB — 42% of `∀ⱽPsh-ηᴰ'` — to a base-category path with no
`reind` in it (`change-base`'s `sym (,p≡ refl refl) ∙ ,p≡ P1 P2 ∙ sym (⋆IdL _)`), and it was
reported as a hard ceiling on what any reind change could achieve. It is not:
the whole NF proof is 8.99 GB, so the base path is AT MOST that; substituting it out moves the
module 17.659 -> 17.136, about **0.5 GB**. The term is identical in both arms, so that cost was
entangled with the six-filler `change-base` context around it, not intrinsic to `,p≡`/`⋆Assoc`
elaboration.
(Caveat: the same substitution in the ORIGINAL arm is uninformative — 86.1 -> 130.3 GB — because
replacing the path with a metavariable-ended postulate makes Agda solve both endpoints by
unification against a huge type, costing more than elaborating the path.)

## Two measurement traps, worth propagating

1. **`allocof` on a module also rebuilds any dependency whose source changed.** Changing
   `Quantifiers/Base.agda` and then measuring `Properties.agda` silently includes an 83 GB rebuild
   of `ComposeWeakening`: that is why `Properties` reads 136 GB in a Base-varying sweep and 52.8 GB
   with Base held fixed. The earlier downstream figures (135.96 / 136.02) were both contaminated
   this way — identically, so the A/B stood, but the absolutes were wrong. The 42% base-path
   bisection is a plausible casualty of the same effect.
2. **`git checkout -- <file>` silently reverted uncommitted adapter work** mid-sweep, producing an
   inconsistent pair of numbers. All figures above are from a clean full-rebuild run.
