# Orchestrator's own measurements (quiet machine unless noted)

## Baseline, HEAD 82334ffb, agda 2.9.0, warm cubical deps
Clean serial `--build-library`: **582s wall / 577s user / 4575 MiB maxrss / 424 modules**
GHC RTS: 842 GB allocated, 214 GB copied during GC, max residency 1.97 GB,
200,573 Gen-0 collections, MUT 343s + **GC 233s = 40.5% of the build**, productivity 59.5%.

## Where the time is (--profile=modules, total 576,373 ms)
By subtree: Displayed 325s (56%) / LocallySmall 95s (17%) / Instances 86s (15%) /
Presheaf 9.3s / Limits 8.2s ... Gluing only 12.6s (2%).
Concentration: top 10 modules = 37.8%, top 23 = 56%, top 50 = 73%.
So this is a *concentrated* problem, not diffuse — ~25 files carry over half the cost.

## Free win already confirmed: GHC nursery size
Single-module A/B, back-to-back, quiet machine, `Cubical/Categories/Instances/Presented.agda`:
    default (-A 4 MB)  wall 65.71s  user 64.30s  maxrss 2367 MB
    -A64M              wall 52.37s  user 51.00s  maxrss 2405 MB
    -A256M             wall 45.71s  user 44.60s  maxrss 2717 MB   <- 1.44x, +350 MB
Agda is linked `-with-rtsopts=-I0 -N1 -qb0` with no -A, so the nursery is GHC's 4 MB
default; 842 GB / 200,573 collections = 4.2 MB confirms it. This is a Makefile one-liner.

## Rebuild fan-out — the developer-experience metric
Transitive reverse-dependency closure over the 3184 internal import edges, costed with
the per-module profile times. "Edit module X, how long until the library is green again?"

    median edit   15.9s
    p75 edit     266.6s
    p90 edit     363.3s
    worst        480.0s  (Cubical.Categories.Profunctor.General, 346 downstream modules)

Distribution of downstream fan-out across the 472 modules:
    >=300 downstream:   8 modules
    100-299:          105
    20-99:             72
    1-19:             185
    0 (leaves):        89

It is bimodal: edit a leaf and you wait 16s, edit a hub and you wait 4-8 minutes.
113 of 472 modules (24%) force >=100 downstream rebuilds. This, not the 582s clean
build, is what "dead in the water" actually feels like day to day.

Caveat on the obvious fix: the hubs are NOT big grab-bag modules that could be split.
`Cubical.Data.Sigma.More` is 80 lines with 3 definitions and still has 326 downstream
modules, because fan-out is driven by position in the DAG, not module size. Splitting
the 35 `*.More` modules would therefore buy much less than it looks like it should.
The realistic lever for the hub-edit case is parallelism, not restructuring.

## Interfaces
75 MB of `.agdai` across 472 modules, largest 1.0 MB. Not a serialization bottleneck.

## REFUTED: module-copy trimming (`using (...)` on `module X = M args`)
Mechanism is real — upstream Agda does skip copy generation for names excluded by an
explicit `using` — but the magnitude is ~1-3%, not the ~30% the mikan analysis suggested.
1518 applications across 473 files, only 10 with any using/hiding/renaming. Marginal cost
per untrimmed application: Category 1.3ms, Categoryᴰ 3.25ms, Fibers 14-19ms. In real hot
modules `Typing.ApplySection` is 0.20-0.26% of the file (3.7% in the densest one).
Library-wide projection ~8s of 582s. Interface size unchanged (Agda's dead-code pass
already drops unreachable copies). Not worth a 1518-site sweep.
Related: import minimisation ceiling is `Import`+`Scoping` = 0.36-1.0% per module. Also
not worth it; commit fe0326bf is already in main, and the unmerged `minimize-imports`
branch is 265 commits and ~6 months stale for a <1% prize.

## NEW LEAD: `Positivity` is ~30% of the hottest modules
`--profile=internal` on modules that declare ZERO data and ZERO record types
(independently verified):
    UniversalProperties.agda (651 lines, 0 data, 0 record): Positivity 17,529 / 56,373 = 31%
    Reindex/UniversalQuantifier.agda (225 lines, 0 data, 0 record): 12,109 / 41,515 = 29%
    Displayed/Presheaf/Morphism.agda:                             2,109 / 16,854 = 12.5%
Other buckets on UniversalProperties: Typing.OccursCheck 19%, Serialization 11-13%,
Typing.Generalize 10%, ApplySection 0.26%, Import+Scoping 0.36%.
Nothing in the repo uses {-# NO_POSITIVITY_CHECK #-}. Under investigation.

## CONFIRMED WIN: Displayed/FixedPoint.agda — one-line pragma, ~17s (~3% of build)
The file was the ONLY one in the CBPV/FixedPoint scope lacking `--lossy-unification`.
Cause (answering the author's "TODO: Why is this so slow" at line 219): the conversion
check between the field's expected type `isFibration (reindexGuardedLogic .Cᴰ)` and the
inferred `isFibration (reindex Dᴰ.Cᴰ F)`. `--profile=definitions` puts 21,430 of 29,248 ms
in `reindexGuardedLogic`; the meta/constraint counters are TINY (2038 metas, 13 attempted
constraints) while `compare`s are 14,491 — so this is conversion/reduction, NOT the
library's usual "unification of large implicits". 17.4 GB allocated, GC 57%, for one
232-line module. With the pragma: ~23s of checking becomes ~2s. Dependents verified clean.

## Emerging theme: the cost is ELABORATED TERM SIZE, not unification
On `CBPV/Unary/Instances/StateAlg/Vertical.agda` (already lossy), `--profile=internal` of
37.4s total: Positivity 10,195 / Typing 7,667 (OccursCheck 4,189) / Serialization 5,560 /
InterfaceInstantiateFull 4,820 / Deserialization 4,585 / Termination 2,898. Only ~7.7s is
type-checking proper. The rest are phases whose cost is proportional to the size of the
elaborated proof terms. 26 GB allocated for one module.
Note again: Positivity 10.2s in a module with NO data/record declarations, vs only 1.9s in
`Free/Pure/Additive.agda` which DOES contain a 45-constructor HIT. Positivity cost tracks
term size, not datatype count.

## Also refuted (second independent measurement)
- Module-copy trimming on StateAlg/Vertical: 35.30s vs 34.72s user = nothing.
- `Typing.Generalize` (~30% of the Free/*/Additive files) is a mislabel: binding level
  variables explicitly moved 6,646ms out of Generalize and 5,988ms into the unattributed
  Typing bucket, with no change in total. Signature elaboration in deep telescopes is
  inherently that expensive.

## REVISED: module-copy trimming IS real — but the cost is NOT where the first agent looked
Two agents measured this and disagreed. The reconciliation:
 * Agent A measured `Typing.ApplySection` (the phase that CREATES the copies) on `Category`
   and `Fibers` applications in the Displayed subtree: 0.20-0.26% of a module. True.
 * Agent B measured `--profile=internal` on the LocallySmall cluster and found the cost is in
   `DeadCodeReachable` + `Serialization` — the phases that PROCESS the copies afterwards.
Creating a copy is cheap; dead-code-analysing and serialising it is not. Agent A looked at the
wrong bucket and concluded the lever was dead. It is not.

The amplification depends on how deeply nested the applied module is. `SmallFibersᴰNotation`
transitively opens `CategoryᴰNotation` (which opens `Categoryᴰ` plus ∫C / ISOCᴰ / Cⱽ), and
`record Functor` in LocallySmall *privately contains two full `CategoryNotation` copies inside
its record body*, so one `module F = Functor F` copies CategoryNotation twice.

Bisection proof: in `LocallySmall/Displayed/Instances/Sets/Base.agda`, adding the single line
`module SETᴰ = SmallFibersᴰNotation SETᴰ` moves the file 2.76s -> 20.5s
(DeadCode 0.09->10.1s, Serialization 0.16->7.3s).

Measured (contended, back-to-back), after adding `using (...)` and deleting unused aliases:
    LocallySmall/.../Instances/Sets/Base              26.08s / 1778 MB -> 3.44s /  481 MB  7.6x
    LocallySmall/.../GloballySmall/IFC/Base           27.71s / 1987 MB -> 4.21s /  602 MB  6.6x
    LocallySmall/.../NaturalTransformation/IFC/Base   45.15s / 2407 MB -> 14.68s/ 1145 MB  3.1x
    LocallySmall/.../GloballySmall/IFC/Properties     26.36s / 2847 MB -> 9.28s / 1288 MB  2.8x
    LocallySmall/.../NaturalTransformation/IFC/Eq     28.90s           -> 28.24s           1.0x
`.agdai` sizes roughly halve, corroborating the mechanism independently of wall clock.
Projected: ~40s off the 576s build (~7%) from SIX files. Full build rc=0, 200 modules, zero
warnings (checked, since CI uses -W error).

Remaining surface: **398 bare notation-module applications outside a using/hiding, 314 of them
in LocallySmall.** Structural fix at the source: hoist the two `CategoryNotation` copies out of
`record Functor` in `LocallySmall/Functor/Base.agda` (that file also has `no-eta-equality`
commented out, unlike Category / Categoryᴰ / Functorᴰ).

Also: `Instances/Sets/Base.agda` is 96 lines of `refl`s whose TYPE-CHECKING costs 0.28s and
whose interface generation costs 20s. The one file that did not move (IFC/Eq) is genuinely
large-term manipulation: 9.8s OccursCheck for only 717 metas = ~14 ms per meta.

## BIGGEST WIN SO FAR: Cubical/Categories/Instances/Presented.agda — 40x, ~9% of the build
115 lines. ALL of its cost is ONE function application.
  --profile=internal:     Typing.CheckRHS 103,949 of 106,777 ms. One RHS.
  --profile=definitions:  QuoByAx._.elim 117,015 of 119,966 ms.
  --profile=metas:        559 metas, 59 attempted constraints -- NOT a meta explosion.
                          But 230,343 compares, 118,421 of them "compare by reduction".
  +RTS -s:                85.7 GB allocated for one module = ~10% of the library's total 842 GB.
  Import floor:           a stub with the same imports checks in 1.47s, so ~64s is real work.

Bisection isolated it exactly: `CatQuotient.elim 𝓒 _≈_ reflₑ ⋆ₑ-cong 𝓓` is free; adding the `F`
argument costs 117.5s. The cost is conversion-checking
    GlobalSection 𝓓'  ==?==  GlobalSection (ReindexQuo.reindex 𝓒 _≈_ reflₑ ⋆ₑ-cong 𝓓)
where 𝓓' is *defined* to be exactly the right-hand term. Agda delta-unfolds both sides through
`EqReindex.reindex = redefine-id⋆ (Reindex.reindex 𝓓 QF) singId singSeq` and grinds structurally
through the singl-typed args -- the 8-deep implicitFunExt/funExt nests over `reind≡reind'` in
`Displayed/Instances/Reindex/Eq/Base.agda:90-108` -- comparing by brute-force reduction instead
of noticing the two sides are the same term.

Every "supply the implicit explicitly" remedy from DIAGNOSE.md FAILED here:
    expected type written out literally      116.0s
    explicit signature on 𝓓'                 114.0s
    abstract Categoryᴰ instead of PresentedCat 117.8s
    pass `_` and let unification solve it    118.4s
The only fix is not making the call: inline Quotient.More's `elim` (6 lines) into QuoByAx.elim
via copatterns so `elim F p` stays stuck until a field is projected.

Measured (contended, A/B back-to-back): 126.9/125.3/126.9s -> 3.3/3.7/2.7s, maxrss 1984->463 MB.
~40x on the module. Extrapolated to the quiet reference: 65.71s -> ~3s; the 53,544 ms profile
attribution should drop under 1s = **~9% off the 576s build**. All 12 transitive dependents
re-check rc=0.

## Measurement hygiene note (checked, not a real problem)
An agent reported the shared /home/steven/cubical/_build being "invalidated". I verified it:
288 interfaces, monotonically growing, git clean. cubical is only partially built (~288 of
~1000 modules), so the FIRST checkfile run that needs an unbuilt upstream module pays to build
it -- up to +75s, attributed to the wrong file. Always take a second reading.
