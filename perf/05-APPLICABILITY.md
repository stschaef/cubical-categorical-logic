# Which technique applies where

Three distinct mechanisms were found, with different applicability. Choosing the wrong one costs
time and can measure WORSE. This file is the screen.

## 1. RNF chain collapse

**Applies when:** a single equational chain crosses a reind MANY times. The mechanism is that
`RNF≡ isSet refl refl` discharges the path bookkeeping ONCE PER CHAIN, replacing N `reind-filler`
steps. With N = 1 there is nothing to amortise.

**The screen: count `reind-filler`s per CHAIN, not per file.** File-level counts invert the
ranking — the CBPV files have 60-70 `reind` occurrences each and are the WORST targets in the
library, because those occurrences are one per chain.

    max reind-fillers in a single chain     files
      >= 6                                    10     <- RNF territory
      3 - 5                                   25
      exactly 2                               17
      only 1                                  18

    35 files at >= 3 = 155.0s of the 576.2s build (27%), cost-weighted.

Raw data: `perf/data/chain-depth.tsv`. Deepest in the library:

     9  Displayed/Presheaf/Uncurried/Constructions/ExponentialV->D.agda
     8  Displayed/Limits/BinProduct/Fiberwise.agda
     8  Displayed/Instances/Reindex/Limits.agda
     7  Displayed/Presheaf/Uncurried/Eq/Conversion/CartesianClosedV.agda
     7  Displayed/Presheaf/Constructions/Quantifiers/{Properties,Base}.agda   <- converted
     6  Instances/Fiber.agda
     6  Displayed/Presheaf/Uncurried/Eq/Base.agda
     6  Displayed/Presheaf/Uncurried/Constructions/Exponential.agda
     6  Displayed/Presheaf/Constructions/BinProduct/LocalRepresentability/Properties.agda

**Demonstrated:** the Quantifiers corpus (depth 7) went 187.183 -> 57.411 GB, **3.26x**, and in
TIME 87.6 -> 35.5s wall (2.5x) with maxrss -42%. Proof terms 12.7x, 8.6x, 6.0x. Elaborated filler
steps 15->0, 9->2, 14->3. See 04-RNF-DESIGN.md.

**Refuted where it does not apply:** the CBPV cluster has 1 filler per chain (max 2-3 per file on
this screen). The filler skeleton in its most expensive proof is 2.3s of 29.6s (~8%), and the
adapter-lemma form measured WORSE, 26.4 -> 28.2s. That code was written with the crossings already
amortised by hand.

## 2. Total-space sharing

**Applies when:** one enormous term is elaborated more than once because two statements about it
are indexed over DIFFERENT base paths, so they cannot be a single `≡[_]`-indexed lemma.

**The fix:** state them as `Path (Σ …)` — i.e. `∫≡` — with one shared `where`. The total-space
form is not a performance trick; it is **the only form in which the sharing is statable**.

**Demonstrated:** `Uncurried/UniversalProperties` — truncation profiling showed two three-line
lemmas were 22.7 GB, 49% of the module, each independently elaborating `bpᴰ.β` at the ∫-presheaf
of the `BinProductⱽᴰ` spec. Three new private `×βⱽ∫`/`×βᴰ∫`/`×βⱽᴰ∫` lemmas, +55/-14 lines in ONE
file:

    Uncurried/UniversalProperties          46.126 -> 24.824 GB   1.86x
    Uncurried/.../ExponentialV->D          59.071 -> 16.840      3.51x  (NO source change)
    cluster                               158.84  -> 95.30       1.67x

**Chain steps did NOT move** (filler 6->6, substantive 6->6). Expensive-β elaborations went 6->3.
Step count is not the cost driver for this mechanism.

**Note on locality.** An earlier agent concluded this class of defect is strictly file-local, after
finding a `rectifyOut` fix in `UniversalProperties` did nothing for a dependent (20.836 -> 20.833).
That is true of `rectifyOut` and FALSE here: sharing a β elaboration changes what the INTERFACE
stores, so dependents that re-elaborate it benefit — hence 3.51x downstream with no source change.
Locality is a property of the mechanism, not of the defect class.

**Measured negatives that pin the mechanism down:** having the `-on` lemmas consume `×βⱽᴰ∫`
directly was neutral (26.25 -> 26.17); replacing `×ηⱽᴰ`'s subst-with-isSetHom by `rectify` and
having `-on` use `PathPΣ bpᴰ.η .snd` REGRESSED to 27.79, because `-on` then elaborates `bpᴰ.η`
twice. Sharing is the mechanism; coercion-step count is not.

## 3. No-op crossing deletion

**Applies when:** a chain step crosses an index change and does nothing else — a roundtrip, or a
combinator whose implicit is solved to a copy of its explicit argument.

Instances found and fixed:
  * `rectify (≡out X)` -> `rectifyOut X`. `rectify`'s implicit can only be `fst (PathPΣ X)`, so X
    is stored TWICE. ~300 sites across three reasoning modules, 2.2x on the hottest file.
    See 03-SPELLING.md and the `rectifyout` / `upstream-rectifyout` A/B cases.
  * `rectify $ ≡out $ ≡in {pth = P} X` -> `rectify {e = P} X`. `≡in` builds a Σ-path only for
    `≡out` to take it apart; the roundtrip is not definitional, so the term carries a full
    `ΣPathP`/`PathPΣ` pair. `StateAlg/Vertical` **26.180 -> 21.042 GB, -19.6%**, from one line.
    This exact pattern occurs nowhere else in the library (grepped); every other `≡out ∘ ≡in` has
    a real `∙` between them.

## How to choose

Profile with `--profile=internal` first. If `Positivity` + `Serialization` + `OccursCheck` +
`InterfaceInstantiateFull` dominate and `Typing.CheckRHS` is small, the module's terms are too big
and one of the three applies. Then:

    many fillers in one chain          -> RNF (mechanism 1)
    one huge term elaborated twice     -> total-space sharing (mechanism 2)
    a step that only crosses an index  -> delete it (mechanism 3)

Truncation profiling (build the file up prefix by prefix, differencing allocation) is what
localises 2 and 3; it found "two three-line lemmas are 49% of the module" and "one 24-line clause
is 66% of the module". `--profile=definitions` mis-attributes here and should only be used as a
hint.

## Latent fragility found on the way

`Displayed/CBPV/Unary/Additive.agda` opens `BinProductⱽᴰNotation` twice at one scope — directly,
and again via `BinCoProductⱽᴰNotation = BinProductⱽᴰNotation (Cᴰᴰ ^opᴰᴰ)` — with `renaming` lists
that enumerate every existing export. **Any new export from those notation modules is therefore a
`[ClashingDefinition]` there.** Worked around with `private` (costs nothing), but worth knowing
before extending them.
