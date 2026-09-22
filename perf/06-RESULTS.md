# The coalesced result: `perf-all` against `main`

`perf-all` is `perf-sweep` and `rnf-all` merged. This file records what that
tree costs to build, measured against `main` at `82334ffb`.  (The one commit
`perf-sweep` lacked from `perf-copattern-spelling` was tried, measured as a net
regression on the whole build, and reverted -- §2.)

Raw data for everything below is in `perf/data/`: `rts-*.tsv` are the verbatim
`+RTS -s` reports, `rank-*.tsv` the `--profile=modules` rankings,
`permodule-*.tsv` the single-module allocation/RSS measurements.

## 1. The headline

Clean serial `--build-library`, no profiling instrumentation, `-j1 +RTS -M24G`
identical on both arms, `_build` wiped first, the `cubical` dependency warm. The
arms were run **strictly one at a time, back to back, twice round**
(main → perf-all → … → main → perf-all), so drift hits both equally.

    arm                      wall (s)       user (s)      maxrss (MiB)  modules  rc
    main  82334ffb          506.0 / 510.5  497.8 / 502.0  4978 / 4605     472     0
    perf-all                310.0 / 277.2  304.8 / 273.7  3399 / 2941     474     0

**1.73x on user time, and 33% less peak memory.** (That is at the shipped RTS
defaults; §9 tunes the runtime as well, and reports a 2x2 of tool x tree in
which the end-to-end win reaches 4.70x.)

GHC RTS accounting for the same runs. Allocation here is deterministic: the two
repeats of each arm agree to eight significant figures (841,148,232,744 vs
841,148,215,152 bytes), so these ratios are load-immune in a way the times are not.

    arm        allocated   copied in GC  max residency  gen-0 colls  gen-1 colls/time   MUT / GC        GC share
    main       841.148 GB    214.02 GB      2.275 GB      200,346      142 / 28.4s     299.9s / 202.8s   40.3%
    perf-all   542.413 GB    102.85 GB      1.621 GB      129,052       75 /  9.6s     203.0s / 104.2s   33.9%

    allocated  -35.5%     copied  -52.0%     max residency  -28.7%     productivity  59.7% -> 66.1%

The baseline reference from `00-METHOD.md` was 842 GB allocated with GC at 40.5%
of the build; this reproduces it (841.1 GB, 40.3%) and moves it to 542 GB at 33.9%.

Note that **time improves more than allocation** (1.73x against 1.55x). That is
the nursery-survival effect from mechanism 4 arriving for free: less is allocated,
but what is allocated also dies younger, so gen-1 collections fall 142 -> 75 and
gen-1 *time* falls 28.4s -> 9.6s, a 66% cut on top of the 37% cut in gen-0 count.

### The comparison is not like-for-like

`perf-all` type-checks **437 lines of quantifier mathematics that `main` does not**
— the proofs commit `9bcc1108` had commented out with "TODO update to handle
opaque reind", restored in `5669a697` and then rewritten through the reind normal
form. Counting live (non-comment, non-blank) lines in the four affected files:
922 on `perf-all` against 458 on `main`, i.e. **+464 live lines**. Module count is
472 -> 474 for the same reason plus the new `Foundations/ReindNormalForm` and
`Displayed/Reasoning/More`.

So the honest reading of the headline is: *the same build, in 1.73x less time and
two thirds of the memory, while additionally proving the quantifier universal
property and the Beck–Chevalley reindexing properties.* A like-for-like arm was
also measured and is in §4 below; it is slightly better still.

### Measurement conditions, stated plainly

Another of the user's sessions was running short `agda` jobs on this box
throughout, so every wall/user figure carries a few percent of foreign load. The
reproducibility actually observed: `main` 506.0 / 510.5 (0.8% apart), `perf-all`
310.0 / 277.2 (11% apart, the earlier run being the more contended). That 11% is
the error bar on the time numbers. Allocation, residency and peak RSS are not
affected at that level, and the allocation ratio is the number to quote if one
number has to be quoted.

`/home/steven/cubical` was never modified: its interface count stayed at 288
before, during and after every build, so no measurement paid for an upstream
rebuild, and `git status` there shows only the pre-existing untracked `CLAUDE.md`.

## 2. Coalescing: what it took, and what it cost

`git merge rnf-all` produced 19 conflict hunks across 9 files. Every one of them
is a place where **both** branches improved the same clause — `perf-sweep`'s
`rectifyOut` sweep (`7134efb9`, 333 sites) touches all nine, and `rnf-all`'s RNF
conversions and ∫-form sharing rewrite the same clauses. They were resolved hunk
by hunk, keeping both sides:

| file | resolution |
|---|---|
| `CBPV/Unary/Instances/StateAlg/Vertical` | `rnf-all`'s `rectify {e = P}` supersedes `rectifyOut $ ≡in {pth = P}` — it deletes the `≡in`/`≡out` roundtrip entirely, which is the same win taken one step further. Every other `rectifyOut` site in the file kept. |
| `Instances/Reindex/{Limits,UniversalQuantifier}` | `rnf-all`'s packaged `reind-filler⁻²` and explicit `Dᴰ.idᴰ` arguments, re-spelled through `rectifyOut`. |
| `Presheaf/Constructions/Quantifiers/{Base,Properties}`, `.../ComposeWeakening` | the restored proofs come back in `rnf-all`'s normal-form rewrite (`perf-sweep` had them commented out), re-spelled through `rectifyOut`. |
| `Presheaf/Uncurried/{Representable,UniversalProperties}`, `Instances/Fiber` | `rnf-all`'s ∫-form sharing (`βelᴰ`, `×βⱽ∫`, `reind⋆IdL/IdR/Assoc`), again through `rectifyOut`. |

Every `X.rectify $ X.≡out $` introduced by `rnf-all` in those files was converted
to `X.rectifyOut $`. The pre-existing unqualified sites in `Presheaf/Base.agda`
and in `LocallySmall` were left alone, exactly as on `perf-sweep`.

### Did coalescing lose a previously-measured win?

**No — and it recovered one that `perf-sweep` had lost.**

The recovered one first, because it is the largest single finding in this file
after the headline. Commit `8bcea917` on `perf-sweep` is titled *"build
reindexGuardedLogic with a record expression, dropping the lossy pragma"*, and
its message explains at length why the record expression fixes
`Displayed/FixedPoint.agda`. **It does not contain the record expression.** Its
diff is `1 insertion, 14 deletions`: it removes the `--lossy-unification` pragma
that `7fd37a27` had added, and removes the comment explaining it, and stops
there. `perf-sweep`'s `FixedPoint.agda` is byte-identical to `main`'s
(`git diff main -- …/FixedPoint.agda` is empty). So that commit removed a working
fix and did not land its replacement, and nothing downstream noticed because the
module still type-checks.

Measured, single-module re-check against warm interfaces, GHC bytes allocated:

    main                                       17.388 GB
    perf-sweep (= main's spelling)             17.368 GB   <- the fix was not there
    perf-all, copattern spelling forced back   17.474 GB
    perf-all as shipped (record expression)     7.461 GB   2.34x, -10.01 GB

`rnf-all` had independently made the same change (`e8c03d78`), correctly, and the
merge brought it in. The 2.34x reproduces `03-SPELLING.md`'s 17.375 -> 7.363 GB
claim to within 1.4%, so that claim stands — it just had not been true of
`perf-sweep`. **Ten GB of the coalesced branch's advantage exists only because the
two branches were merged.** The lesson for this directory is the uncomfortable
one: a commit message is not evidence that the change is in the tree, and the
`fixedpoint` row in `perf/ab-results.tsv` (16.1753 GB on *both* arms, i.e. "this
intervention does nothing") was reporting exactly this and was read as noise.

Nothing was lost. One win shrank *and then inverted*, and that is the other
finding worth having:

> `Reindex/CartesianClosed`'s record expression for `CCCⱽReindex` measured
> 13.047 -> 12.175 GB (0.87 GB, 6.7%) on `perf-copattern-spelling` against
> `82334ffb`. On this branch `910d0a6b` has already made `UniversalQuantifiers`
> a record, so its head no longer unfolds and the `forallⱽ` spelling mismatch is
> no longer repeated once per occurrence of `Cᴰ` in the unfolded field type.
> Re-measured here at module level, interleaved: **4.790 -> 4.585 GB, −4.3%**
> (baseline re-measured afterwards at 4.790, reproducible to three decimals).
>
> It was landed on that basis, and then the **whole-build** number was taken:
>
>     perf-all without it     542,413,177,832 bytes   (B1 542,412,854,144
>                                                      B2 542,412,869,320)
>     perf-all with it        543,238,367,304         +0.825 GB
>
> It **costs about 1.03 GB downstream for every 0.21 GB it saves locally**, so
> it was reverted (`da631702`). The three no-patch builds agree to 0.00006%, so
> this is not measurement noise.

The presumed mechanism is the one `05-APPLICABILITY.md` records for ∫-form
sharing, running in reverse: changing *how* a definition is built changes what
its interface stores, and `Reindex/CartesianClosed`'s five dependents
re-elaborate `CCCⱽReindex`. Two lessons, both half-written elsewhere in this
directory and now paid for twice:

* **A per-module A/B is not sufficient evidence to land a change**, even when
  the module improves and the tree still builds. A whole-build allocation number
  costs five minutes and is deterministic. Take it.
* **"These defects are file-local" is true of `rectifyOut` and false of anything
  that changes the shape of a definition other modules consume.** The claim in
  `perf/README.md` — "fixing a module measurably does *not* speed up its
  importers, which was verified separately" — is a statement about *that* class
  of fix only, and `perf/bin/ab-suite`, which measures exactly one module per
  case, inherits the limitation. It cannot see this failure mode at all.

This is worth contrasting with the `Presented.agda` case recorded earlier in this
directory, where two candidate fixes measured 2.549 and 2.471 GB alone and 3.367 GB
together — *worse than either*. That failure mode was specifically looked for here
and did not occur: of the ten hot modules measured individually on both parents
and on the merge, none is slower on the merge, and in the per-module profile
(§5) the whole library shows six modules slower than `main`, all by under 310 ms.

## 3. Per-technique attribution

Each landed change was reverted **individually** from `perf-sweep` and the whole
library rebuilt, measuring GHC bytes allocated. Allocation is deterministic and
load-immune, so these builds were run concurrently without compromising the
numbers (their wall times are meaningless and are not reported). The reference
point is `perf-sweep` itself at 549.330 GB.

    reverted from perf-sweep                              build      the change is worth
    --                                                   549.330 GB
    R3  rectifyOut sweep (7134efb9 + a9dda177 + d876c91f) 695.538      146.21 GB   26.6%
    R1  Presented root fix (6e3a7d5e + 18e4483c)          631.860       82.53 GB   15.0%
    R2  LocallySmall notation trimming (16fd9c4c + fixup) 600.083       50.75 GB    9.2%
    R6  PropertyOver --lossy-unification (99c349e2)       554.320        4.99 GB    0.9%
    R4  UniversalQuantifiers as a record (910d0a6b)       550.395        1.07 GB    0.2%
                                                          sum          285.55 GB

`main` (841.148) minus `perf-sweep` (549.330) is 291.82 GB, against a sum of
individual contributions of 285.55 GB — so the techniques are **additive to within
2.2%**, which is what one expects if the defects really are file-local, and is
itself evidence for that claim.

A seventh revert was attempted for the FixedPoint record expression and turned out
to be a null experiment, because that change is not on `perf-sweep` at all (§2).
It is a useful accident: it rebuilt an unmodified `perf-sweep` in a *different
worktree* and got 549.029 GB against 549.330 GB, **0.05% apart**. Allocation is
therefore reproducible to eight significant figures within a worktree and to about
0.05% across worktrees — the residue is presumably absolute path length, which
this build allocates strings for. Treat 0.05% as the floor on any allocation
comparison made between different directories.

Then, on top of `perf-sweep`:

    perf-sweep                                    549.330 GB
    + rnf-all's contribution to existing maths     529.840      19.49 GB    3.5%
        of which: the FixedPoint record expression              10.01 GB
                  ∫-form sharing, reind-filler⁻², the
                  ≡in/≡out roundtrip deletion, RNF framework     9.48 GB
    + the 437 restored lines of mathematics        542.413     -12.57 GB
    perf-all as shipped                            542.413 GB

### Reading the table

* **The `rectifyOut` sweep is the single biggest lever in the tree** at 146 GB /
  26.6%, and it is also the cheapest and least clever: a purely mechanical
  rewrite of `rectify (≡out X)` to `rectifyOut X` at 333 sites, justified by the
  observation that `rectify`'s implicit can only ever be `fst (PathPΣ X)`, so `X`
  was being stored twice. Nothing about it needed a diagnosis; it needed someone
  to notice. The per-case A/B in `perf/ab-results.tsv` measured it at 2.2x on the
  hottest single file, which understated its library-wide value because it is
  spread over 56 modules.
* **`Presented` at 82.5 GB is one module.** That is 9.8% of `main`'s entire
  allocation in a 115-line file, and the fix is `Reindex/Eq/Base`'s coherence path
  split out and made `opaque`.
* **`FixedPoint`'s record expression is worth 10.01 GB and arrives from
  `rnf-all`, not from `perf-sweep`** — see §2. `ab-results.tsv`'s `fixedpoint`
  row (16.1753 GB on both arms) is correct and should be restated: it is measuring
  a commit that does not make the change its message describes.
* **An isolated per-file A/B is an upper bound on a technique's library-wide
  value**, because the other fixes in the sweep close some of the same channels:
  `910d0a6b` (`UniversalQuantifiers` as a record) measured 2.3x on the one file
  it was tried on and is 1.07 GB library-wide. And it is not even reliably an
  upper bound in sign -- see the reverted `Reindex/CartesianClosed` change in §2,
  which saves 0.21 GB on its module and costs 0.83 GB on the build.
* **`rnf-all`'s contribution to the *existing* mathematics is 19.5 GB, 3.5%.**
  Its large numbers — 3.26x on the Quantifiers corpus, 187.2 -> 57.4 GB — are
  about mathematics that `main` does not check at all. Which is the point: see
  below.

### What the restored proofs now cost

Commit `5669a697` measured the restored quantifier proofs at **+168 GB** on a
842 GB baseline, about +20%, and that is why they had been commented out. After
the RNF rewrite the same mathematics costs **12.57 GB**, 0.6% of the branch's
build — a 13x reduction in the price of the same theorems. In the profiled runs
the four modules account for 5.5s of a 272s build.

That, and not the 3.5% figure above, is the result to take from the RNF work: it
did not make the existing library much faster, it made a body of mathematics that
was *unaffordable* affordable.

## 4. The like-for-like arm

A third arm was built: `perf-all` with the four quantifier files taken from
`perf-sweep`, i.e. **every performance change and exactly `main`'s mathematical
content**. (Branch `perf-all-nomath`, commit `035f4eb5`. The RNF framework module
is still present and still built in this arm, costing 292 ms — it is not excluded,
so this arm is if anything slightly pessimistic.)

    arm                        wall (s)       user (s)      maxrss (MiB)  allocated   GC share
    main  82334ffb            506.0 / 510.5  497.8 / 502.0  4978 / 4605   841.148 GB    40.3%
    perf-all (as shipped)     310.0 / 277.2  304.8 / 273.7  3399 / 2941   542.413 GB    33.9%
    perf-all, main's maths    296.9 / 276.2  292.4 / 272.3  3189 / 3189   529.840 GB    33.6%

**Same mathematics: 1.77x on user time, 1.588x on allocation, −36% peak RSS.**

## 5. Where the time moved

From `--profile=modules`, run as a **separate** pair of builds (these numbers must
not be mixed with §1's; the instrumentation is cheap here — 487.3s profiled
against 506.0/510.5 unprofiled for `main` — but it is not free and the profiled
run also happened to catch a quieter machine).

Total attributed: `main` 482,819 ms -> like-for-like arm 265,161 ms.
`perf-all` as shipped is 272,512 ms, the difference being the restored proofs.

    module                                                   main      l-f-l    ratio
    Instances.Presented                                     58,913       596    98.8x
    Displayed.Presheaf.Uncurried.UniversalProperties         25,264     9,309    2.71x
    Displayed.FixedPoint                                     17,188     1,849    9.30x
    Displayed.Instances.Reindex.UniversalQuantifier          15,980     3,840    4.16x
    LocallySmall...NaturalTransformation.IFC.Base            15,366     4,323    3.55x
    Displayed.CBPV.Unary.Instances.StateAlg.Vertical         15,268     9,628    1.59x
    LocallySmall...Presheaf.GS.IFC.Properties                11,114       859   12.94x
    Displayed.Presheaf.Uncurried.Constructions               11,000     4,097    2.68x
    LocallySmall...NaturalTransformation.IFC.Eq               9,883     2,635    3.75x
    Displayed.Presheaf.Morphism                               9,049     4,677    1.93x
    LocallySmall...Presheaf.GS.IFC.Base                       8,740       283   30.88x
    LocallySmall.Displayed.Instances.Sets.Base                8,240       140   58.86x
    Displayed.Instances.Reindex.CartesianClosed               6,961       401   17.36x
    Displayed.Instances.PropertyOver.Cartesian                3,719        58   64.12x

The per-module profile numbers are *not* a clean per-technique decomposition —
several of these modules were touched by two or three of the techniques in §3 —
which is why §3 was measured by whole-build reverts instead.

**Nothing regressed materially.** Exactly six modules are slower, all by under
310 ms: `Uncurried.Constructions.UniversalQuantifier` +307, `Limits.Pullback.Alt`
+292, `Instances.Presheaf.Eq.CartesianClosed` +252, `Bifunctor` +198,
`Monad.Kleisli` +177, `BiKleisli.Morphism` +176. Three new modules appear:
`Foundations.ReindNormalForm` 292 ms, `Displayed.Reasoning.More` 24 ms,
`Presheaf.Constructions.Lift` 10 ms.

### Memory, per module

Single-module re-check against warm interfaces (delete one `.agdai`, re-check),
GHC bytes allocated and peak RSS. These include the per-module import and
deserialisation floor — roughly 2–3.5 GB and 300–400 MiB in these subtrees — so
the above-floor ratios are larger than shown.

    module                                          main GB   l-f-l GB   ratio   main MiB  l-f-l MiB
    Instances/Presented                              85.422     2.653    32.2x     2367       460
    Uncurried/UniversalProperties                    46.078    19.833     2.32x    3954      2141
    Reindex/UniversalQuantifier                      28.705    10.922     2.63x    4323      1508
    CBPV/.../StateAlg/Vertical                       26.035    20.615     1.26x    3280      2415
    LS .../NaturalTransformation/IFC/Base            23.454     9.704     2.42x    2661      1135
    LS .../Presheaf/GS/IFC/Properties                20.405     6.522     3.13x    3179      1163
    Displayed/FixedPoint                             17.388     7.475     2.33x    1952      1158
    LS Displayed/Instances/Sets/Base                 14.166     2.430     5.83x    1694       437
    Reindex/CartesianClosed                          13.051     4.803     2.72x    3157      1018
    PropertyOver/Cartesian                            9.010     4.033     2.23x    1361       860

Peak RSS falls roughly in step with allocation, which is what mechanism 4 predicts:
residency at a collection is set by how much intermediate structure a single
elaboration keeps live, and these fixes all shrink the terms being elaborated.

## 6. The remaining ceiling

After all of this the build is still 542 GB, 277s and 2.9 GB of RSS. What is left:

* **GC is still a third of the build** (33.9%), and the nursery is still GHC's
  4 MB default in these measurements. The Makefile's serial RTS tuning
  (`-A512M -H4G`) is landed on this branch and is *not* reflected in any number
  above, because both arms were given identical plain `-M24G` so that source
  changes could be isolated. `00-METHOD.md` measured the tuning separately at
  roughly 15% off the wall clock. That is the largest single remaining lever and
  it costs nothing but resident memory.
* **The distribution has flattened, which means there is no next `Presented`.**
  `main`'s worst module was 58.9s, 12.2% of the attributed total, and its top ten
  were 39.2%. The like-for-like arm's worst module is 9.6s, 3.6%, and its top ten
  are 23.9%. The remaining cost is spread across a few hundred modules at 1–10s
  each. Further work has to be either a broad mechanical sweep (like `rectifyOut`)
  or an attack on the per-module floor.
* **That floor is interface deserialisation**, ~1.7–2s per module in the
  `Displayed`/`LocallySmall` subtrees. At 474 modules that is on the order of
  100s — a third of the remaining build — and no source change in this sweep can
  touch it. `01-MECHANISMS.md` mechanism 3 is the one lever that does move it
  (trimming module copies shrinks what has to be written and read), and there are
  still **398 bare notation-module applications outside a `using`/`hiding`, 314
  of them in `LocallySmall`**, of which `16fd9c4c` trimmed only a handful. On the
  §3 arithmetic that handful was worth 50.75 GB; the remainder is the largest
  identified, unexploited source-level lever in the library.
* **`StateAlg/Vertical` is now the most expensive module in the tree** (9.6s,
  20.6 GB) and has improved the least of any hot module (1.26x on allocation).
  `02-NOT-LANDED.md` records a measured 1.64x for it from naming four repeated
  inline expressions (`term.patch`), not landed because it conflicted with the
  `rectifyOut` sweep and the mutual-block split. That conflict is now resolved in
  the tree; the patch should be reconciled against the current file and re-measured.
* **The CBPV cluster generally** (`StateAlg/Vertical`, `Free/BoolState/Additive`,
  `Free/Pure/Additive`) is ~27s of the 265s like-for-like build and is explicitly
  *out of scope* for RNF — `05-APPLICABILITY.md` measured the adapter form there
  as worse (26.4 -> 28.2s), because those chains cross a reind once each and there
  is nothing to amortise. Whatever is expensive there is a different mechanism and
  has not been diagnosed.

## 7. How to re-run any of this

    perf/bin/ab-suite                  # per-case A/B, GHC allocation, deterministic

`ab-suite` measures one module per case, and §2 shows that is not enough to
decide whether to land a change: it cannot see a fix that pays locally and is
charged to dependents. **Before landing anything, take a whole-build allocation
number.** It is deterministic to eight significant figures within a worktree, so
one build of each arm settles the question, and the builds may be run in
parallel because allocation is load-immune.

For the whole-build numbers: wipe `_build`, then

    agda --library-file=<libs> -j1 +RTS -M24G -s<out> -RTS --build-library

on each tree, one at a time. For the per-technique table, `git revert --no-commit`
the commit named in §3 from `perf-sweep` and do the same; those may be run
concurrently, since only the allocation figure is used.

## 8. Index of the raw data added by this file

    perf/data/rts-A1.tsv, rts-A2.tsv       main 82334ffb, the two measured builds
    perf/data/rts-B1.tsv, rts-B2.tsv       perf-all as shipped
    perf/data/rts-C1.tsv, rts-C2.tsv       perf-all with main's mathematics (§4)
    perf/data/rts-D.tsv                    perf-sweep, the attribution reference
    perf/data/rts-R1.tsv .. rts-R6.tsv     one landed technique reverted each (§3)
                                           R5 is a null experiment; see §3
    perf/data/rank-main.tsv                --profile=modules ranking, ms then module
    perf/data/rank-perfall-nomath.tsv      likewise, like-for-like arm
    perf/data/rank-perfall.tsv             likewise, as shipped
    perf/data/permodule-main.tsv           single-module GB / wall / maxrss / rc
    perf/data/permodule-perfall-nomath.tsv likewise
    perf/data/rts-sweep-*.tsv             the RTS sweep of §9; see §9 "Raw data"

## 9. RTS tuning: the four cells at their own best settings

§1–§8 measured source-level work at one fixed RTS configuration (`-j1 +RTS -M24G`,
GHC's default nursery). This section holds the sources fixed and tunes the
runtime instead, across the 2x2 of **tool** (`agda` / `mikan`) and **tree**
(`main 82334ffb` / `perf-all`). The four worktrees are

    /home/steven/mikan-bench/x2-agda-main      agda  x main       82334ffb
    /home/steven/mikan-bench/x2-agda-perfall   agda  x perf-all   6214b5f9
    /home/steven/mikan-bench/x2-main           mikan x main       mikan-2x2-main
    /home/steven/mikan-bench/x2-perfall        mikan x perf-all   mikan-2x2-perfall

with `mikan` resolving imports against `cubical-mikan` and `agda` against
`cubical-agda`. Every build is a clean serial `--build-library` (`_build` wiped,
`-j1 +RTS -M24G -N1`), taken under an exclusive `flock` so **no two builds ever
overlap**.

Both binaries are linked with the same RTS options — `Mikan.cabal` gives the
`mikan` executable `-with-rtsopts=-I0 -N1 -qb0`, which is exactly what Agda uses;
the `-A32m` in that file is on the `tasty-bench` test-suite only and does not
reach the compiler. Neither tool therefore ships a nursery default, and both
inherit GHC's 4 MiB: the untuned builds average 4.10 MiB (agda) and 4.02 MiB
(mikan) of allocation per gen-0 collection. The tuning knob is genuinely unset in
both, and the comparison across tools is fair on this axis. (One real confound
remains: `mikan` is built with GHC 9.12.2 and `agda` with GHC 9.10.3.)

### The sweep

One run per configuration. `-M24G` and `-j1` throughout; `maxrss` from
`time -v`, everything else from `+RTS -s`. Allocation, bytes copied and
collection counts are deterministic within a (cell, config) pair — repeats agree
to every digit — so only the time columns carry noise.

**agda x main** — 784.3 GiB allocated

    config        wall s  user s  maxrss  maxres  copied  gen-0   gen-1  GC s   GC%
    default        453.7   446.7  4660±264  1.84   198.3  200578    143  176.2  39.1
    -A64M          366.8   362.9    4157    1.80   142.7   12453     86  125.5  34.3
    -A256M         345.1   342.1    4465    1.76   114.2    3073     62  103.5  30.1
    -A512M         327.0   324.2    4759    1.88    96.4    1516     52   87.4  26.8
    -A1G           310.3   307.4    5233    1.67    77.7     747     37   71.8  23.2
    -A2G           295.5   292.0    6750    1.93    60.5     364     28   56.7  19.3
    -A4G           276.9   273.9    8961    2.05    40.9     175     21   39.6  14.3
    -A1G -H2G      330.9+   327.9   5139    1.80    75.4     719     36   74.1  22.5
    -A1G -H4G      295.6   293.4    5180    1.90    62.1     362     28   58.1  19.6

**agda x perf-all** — 507.0 GiB allocated

    config        wall s  user s  maxrss  maxres  copied  gen-0   gen-1  GC s   GC%
    default        273.3   269.3  3354±71   1.51    95.6  129519     76   89.2  32.8
    -A64M          219.5   217.2    3316    1.41    65.5    8047     46   59.4  27.2
    -A256M         207.5   205.7    3640    1.51    52.0    1989     35   47.9  23.2
    -A512M         200.6   198.8    3735    1.47    44.5     982     30   41.7  20.8
    -A1G           192.5   190.4    4246    1.48    36.2     482     24   34.3  17.9
    -A2G           186.0   184.0    5001    1.19    29.5     235     18   28.2  15.2
    -A4G           177.7   174.7    6666    1.21    19.8     113     14   19.6  11.1
    -A1G -H2G      218.2+   216.0   4259    1.41    36.2     462     23   38.3  17.6
    -A1G -H4G      182.8   181.0    4799    1.32    26.5     196     17   26.9  13.7

**mikan x main** — 306.3 GiB allocated

    config        wall s  user s  maxrss  maxres  copied  gen-0   gen-1  GC s   GC%
    default        204.3   200.7  4175±1216 2.31    81.5   77846     83   72.1  35.4
    -A64M          160.1   157.4    4044    1.87    57.1    4821     45   46.2  29.2
    -A256M         146.9   140.8    3897    1.61    45.2    1186     31   36.3  24.8
    -A512M         145.0   142.8    6009    2.46    40.3     585     24   32.9  22.7
    -A1G           136.9   133.8    4569    1.78    31.6     287     18   26.1  19.1
    -A2G           126.4   124.8    4970    1.38    20.2     139     14   17.2  13.5
    -A4G           121.4   119.4    6771    1.09    12.0      68      9   10.6   8.7
    -A1G -H2G      137.2   135.3    5801    2.03    30.2     265     19   25.1  18.4
    -A1G -H4G      128.5   126.8    5598    2.09    20.6     134     13   17.8  13.2

**mikan x perf-all** — 243.4 GiB allocated

    config        wall s  user s  maxrss  maxres  copied  gen-0   gen-1  GC s   GC%
    default        150.2   147.9  2364±18   1.19    50.6   61818     54   47.0  31.4
    -A64M          115.9   114.2    2613    1.20    34.1    3832     32   28.6  24.8
    -A256M         111.3   109.8    3025    1.18    27.3     941     25   23.4  21.2
    -A512M         108.0   106.9    2769    1.02    23.3     464     19   20.0  18.6
    -A1G           101.1    99.9    3358    1.10    16.5     228     14   14.4  14.3
    -A2G            96.4    94.5    4175    0.93    10.6     112      9    9.9  10.2
    -A4G            90.5    88.8    5934    0.97     5.5      55      6    5.3   5.9
    -A1G -H2G      102.8   101.6    3337    1.04    17.5     212     14   15.0  14.7
    -A1G -H4G       94.5    93.1    4844    1.17     7.0      76      8    7.1   7.2

`maxres` is GHC's own maximum residency in GiB; `copied` is bytes copied during
GC in GiB; `default` rows are the untuned baseline, reproduced from `results/reps`
(n=3 for `agda x main`, n=2 elsewhere) and carried here unchanged. A `+` marks a
figure taken inside the contended window described at the end of this section;
both `-A1G -H2G` rows so marked are superseded by the `mikan` re-measurements
recorded there. The `-A512M` row for `mikan x main` (6009 MiB / 2.46 GiB residency, both far above its `-A1G`
neighbour) was measured once and is not explained; every other row in that
column is monotone in `-A`.

### The `-A` curve has no knee in any cell

**Every cell improves monotonically all the way to `-A4G`.** The brief expected
the optimum to diverge by cell, since `agda x main` allocates 3.2x what
`mikan x perf-all` does. It does not: what diverges is only how much time is left
to win, not where the curve turns.

The mechanism is arithmetic. Enlarging the nursery buys back GC seconds almost
exactly one-for-one, and nothing else changes — allocation is bit-identical
across the whole sweep, and the mutator is unaffected until the nursery stops
fitting in cache, which never happens in the measured range:

    cell               GC s at -A1G   GC s at -A4G   GC saved   wall saved
    agda x main            71.8           39.6         32.2        33.4
    agda x perf-all        34.3           19.6         14.7        14.8
    mikan x main           26.1           10.6         15.5        15.5
    mikan x perf-all       14.4            5.3          9.1        10.6

So the ceiling on what `-A` can win is simply the cell's remaining GC time, and
that scales with allocation volume. `agda x main` still has 40s of GC at `-A4G`
and would keep paying for more nursery; `mikan x perf-all` has 5.3s left and is
done. **The real per-cell result is that the tuning is worth the same 1.5x
everywhere, and that the tool and tree wins are therefore almost exactly
multiplicative with it.**

The trade is memory, and it is close to linear: each doubling of `-A` costs
roughly the added nursery in peak RSS. `agda x main -A4G` is the fastest single
configuration measured (276.9s, 1.64x) but peaks at **8.96 GiB** — on a 31 GiB
box with an interactive `ragda` session it is not a default anyone should ship.
`mikan x main -A4G` (6.77 GiB) and `agda x perf-all -A4G` (6.67 GiB) carry the
same warning in milder form.

### `-H` is a total-heap budget, and that is why it beats `-A` on the agda arms

`-H⟨size⟩` does **not** leave an explicit `-A` alone. With `-A1G -H4G` the gen-0
count on `agda x main` falls from 747 to 362 — the same 364 that plain `-A2G`
gives — so the RTS sized the nursery to roughly `H` minus the live set and
ignored the `-A1G`. `-H2G` on the other hand changes nothing (719 collections
against 747): the live set is already ~1.8 GiB, so `H - live` is below `-A1G` and
`-A1G` stands. That makes `-H2G` a no-op that still commits a 2 GiB floor, and
it is not worth passing.

Because `-H` sets a *total* budget rather than a nursery size, it reaches an
`-A2G`-sized nursery without `-A2G`'s peak:

    agda x main       -A2G       295.5 s   6750 MiB
                      -A1G -H4G  295.6 s   5180 MiB     same speed, -1.57 GiB
    agda x perf-all   -A2G       186.0 s   5001 MiB
                      -A1G -H4G  182.8 s   4799 MiB     faster and smaller

On the mikan arms the same 4 GiB budget is *larger* than what they would have
chosen, so `-H4G` overshoots and costs RSS for little time:

    mikan x main      -A2G       126.4 s   4970 MiB
                      -A1G -H4G  128.5 s   5598 MiB     slower and bigger
    mikan x perf-all  -A2G        96.4 s   4175 MiB
                      -A1G -H4G   94.5 s   4844 MiB     1.9% faster, +669 MiB

This is the one place the four cells genuinely diverge, and it follows from the
live set: `agda x main` holds ~1.9 GiB live, `mikan x perf-all` ~0.93 GiB, so a
fixed 4 GiB heap budget hands them very different nurseries.

It also retires the earlier finding that `-A512M -H4G` was the best configuration
for `agda x main`. It was — within a grid that stopped at `-A512M`. The `-H4G`
part of it was doing an `-A`'s job, and saying `-A1G -H4G` (or `-A2G`) outright
is both faster and clearer.

### `-A` makes peak RSS deterministic

The baseline's peak-RSS column was unusable: `mikan x main` swung 3315–5034 MiB
between two identical runs, 29% relative sd. That is the RTS sizing the heap
opportunistically under `-M24G` with a 4 MiB nursery. Pinning `-A` pins the peak:

    cell               default maxrss sd     tuned maxrss sd
    agda x main           5.66%  (n=3)        0.09%  (n=3, -A1G -H4G)
    agda x perf-all       2.11%  (n=2)        0.93%  (n=3, -A1G -H4G)
    mikan x main         29.12%  (n=2)        0.00%  (n=3, -A2G)
    mikan x perf-all      0.78%  (n=2)        0.00%  (n=3, -A2G)

Under a plain `-A` the three repeats agree to the megabyte; under `-A1G -H4G`
they wander by ~45 MiB, because `-H` re-sizes adaptively. So once `-A` is set,
`maxrss` becomes as quotable as allocation, and the advice to prefer GHC's
`maximum residency` over `maxrss` applies only to the untuned baseline. Residency
itself is stable everywhere and is still the better number if one has to choose.

### Recommended configuration per cell

The budget adopted here is **peak RSS no worse than the cell's untuned peak**, so
that tuning is RAM-neutral on this box. Under that constraint:

    cell               recommended     wall s (mean ± sd, n=3)   maxrss    vs untuned
    agda x main        -A1G -H4G       296.5 ± 0.9  (0.30%)      5176 MiB    1.53x
    agda x perf-all    -A1G -H4G       183.9 ± 1.0  (0.54%)      4851 MiB    1.49x
    mikan x main       -A2G            127.1 ± 1.0  (0.76%)      4970 MiB    1.61x
    mikan x perf-all   -A2G             96.5 ± 0.2  (0.18%)      4175 MiB    1.56x

User time for the same runs: 294.3 ± 1.0, 182.1 ± 0.9, 123.3 ± 2.9, 94.7 ± 0.3.

#### Correction: the `WIN-c` confirmation block does not confirm what it labels

Audited after the fact. Two defects, both in the confirmation runs only; the
sweep grid itself is sound.

1. **The `WIN-c` runs for the two agda cells used the wrong configuration.**
   Peak residency is a reliable fingerprint of the `-A`/`-H` setting, and the
   five `agda-main-WIN-c*` runs all report 1707 MiB — the signature of plain
   `-A1G` (`agda-main-A1G-r1/r2`, 1707 MiB), not of `-A1G -H4G`
   (`A1G-H4G-r1..r4`, 1944-1950 MiB). Same for `agda-perfall`: `WIN-c` reads
   1510 MiB, matching `A1G-r*` (1510) and not `A1G-H4G-r*` (1354-1488). The
   dedicated confirmation of the agda winner therefore never ran the winner.
   The mikan cells are unaffected: their `WIN-c` residency (1417 / 954 MiB)
   matches their `A2G` runs exactly.

2. **The numbers in the table above are the sweep repeats, not the `WIN-c`
   block.** They are the last three `A1G-H4G-r*` / `A2G-q*` runs. Those are
   genuine repeats at the right settings, but the `WIN-c` block — taken later,
   in a contended window — is slower in every cell:

       cell               quoted (n=3)      WIN-c (n=5)        delta
       agda x main        296.3 +- 0.94     320.6 +- 6.70      +8.2%
       agda x perf-all    183.8 +- 0.99     196.9 +- 5.31      +7.1%
       mikan x main       128.3 +- 2.11     131.8 +- 3.55      +2.7%
       mikan x perf-all    97.2 +- 0.95      99.8 +- 2.86      +2.7%

   So "all twelve confirmation runs ... reproduce to better than 1%" describes
   the quietest triplet in each cell, not the run-to-run variance of the box.
   Honest single-run variance at a fixed configuration is nearer 3%, and the
   per-cell `sd` figures quoted above are correspondingly optimistic.

**What survives.** The ranking of configurations, the absence of a knee through
`-A4G`, the `-H`-overrides-`-A` mechanism, and the ~1.5x overall value of RTS
tuning are all read off the sweep grid and are unaffected. **What does not:**
for `agda x main`, `-A1G -H4G` (four runs: 304.2, 297.3, 295.4, 296.3; mean
298.3, sd 4.0) is *not* separated from `-A2G` (304.1, 295.3) on wall time. The
case for preferring `-A1G -H4G` there rests on peak RSS (5176 vs 6750 MiB), not
on speed, and should be stated that way.

**Also note** the `default` rows are carried over from the earlier `reps/` set
rather than measured in this sweep, so the headline 4.70x spans two measurement
sessions. It is a fair comparison of configurations but not of one sitting.

If peak memory is not a constraint, `-A4G` is worth a further 3–7% in every cell
(276.9 / 177.7 / 121.4 / 90.5 s) at 8.96 / 6.67 / 6.77 / 5.93 GiB. **Flagged:
`agda x main -A4G` at 8.96 GiB is the one configuration here that could
plausibly collide with an interactive session on a 31 GiB machine.**

### The 2x2 at each cell's own best settings

    wall s             agda        mikan      mikan speedup
    main              296.5       127.1          2.33x
    perf-all          183.9        96.5          1.91x
    perf-all speedup   1.61x       1.32x

    peak RSS           agda        mikan
    main             5176 MiB    4970 MiB
    perf-all         4851 MiB    4175 MiB

Against the untuned 2x2 (453.7 / 273.3 / 204.3 / 150.2 s) the tuning is worth
1.49–1.61x per cell, and it does not disturb the ordering: `mikan` is still worth
more than `perf-all` on `main` (2.22x untuned, 2.33x tuned), and `perf-all` is
worth slightly less once run under `mikan` (1.66x / 1.36x untuned against
1.61x / 1.32x tuned), because the RTS has already collected part of what
`perf-all` was collecting by allocating less.

**The headline: `agda x main` at its shipped defaults takes 453.7 ± 0.7 s;
`mikan x perf-all` at `-A2G` takes 96.5 ± 0.2 s. That is 4.70x on wall and 4.72x
on user time, at 4175 MiB against 4660 MiB — the whole speedup is free of any
memory cost.** Untuned, the same pair was 3.02x; the RTS contributes the
remaining 1.56x, and 3.02 x 1.56 = 4.70 recovers it exactly, so the three effects
(tool, tree, runtime) compose multiplicatively with no interaction to speak of.

### Measurement conditions

92 full-library builds went into this section (82 sweep and confirmation runs
plus the 10 untuned baseline runs), each one alone on the machine under an
exclusive lock. Most ran on a genuinely quiet box. Between 00:14 and 01:20 a
foreign single-core `agda` job (the user's `ragda` session) was intermittently
active and inflated wall times by 3–5%; every run from then on logged
`/proc/loadavg` alongside it, and each contended figure was re-measured
back-to-back against its comparison once the box cleared. Two conclusions were
reversed by those re-measurements and are recorded here only in corrected form:

* `-A1G -H2G` first appeared to cost 7–12% in all four cells. Re-run
  back-to-back against `-A1G` it costs 0.2% (`mikan x main`, 137.2 vs 136.9) and
  1.7% (`mikan x perf-all`, 102.8 vs 101.1). It is a no-op, not a regression.
* `mikan x perf-all -A4G` first measured 99.7 s, i.e. *slower* than `-A2G`, which
  would have been the only knee in the sweep. Re-run it is 90.5 s. There is no
  knee.

Both were single-run artefacts of the contended window, which is the argument for
the back-to-back discipline rather than for comparing against a figure taken at
another time. `/home/steven/cubical` and `/home/steven/mikan-bench/cubical-mikan`
were checked before and after and show only their pre-existing untracked files.

### Raw data

    perf/data/rts-sweep-<cell>-<config>-<run>.tsv    verbatim +RTS -s tail, 82 runs

where `<cell>` is one of `agda-main`, `agda-perfall`, `mikan-main`,
`mikan-perfall`, `<config>` one of `A64M A256M A512M A1G A2G A4G A1G-H2G
A1G-H4G`, and `q*`/`c*` runs are repeats of a recommended configuration. The `WIN-c` runs
are NOT: for the agda cells they were taken at plain `-A1G` (see the correction
in "Recommended configuration per cell"), and for all cells in a contended window.
The untuned baselines are the `reps/` set quoted in the `default` rows.

## 10. The argument-pinning sweep

Four agents worked disjoint clusters of the most expensive modules on
`perf-all`, one worktree each, merged afterwards. Whole-library figures are GHC
bytes allocated from clean serial `--build-library` runs, using
`-j1 +RTS -N1 -A1G -H4G -M24G`, every number a second reading.

    perf-all                549.0 GB   189.6 s   4892 MiB
    perf-all + all four     514.9 GB   176.7 s   4560 MiB
                           -34.1 GB    -12.9 s    -332 MiB
                            -6.21%      -6.8%      -6.8%

125 insertions and 103 deletions across 11 files. Per cluster, each against its
own worktree's baseline:

    LocallySmall/Eq   -19.46 GB  (-3.60%)   31/27 lines, 6 files
    representability   -7.96 GB  (-1.47%)   76/43 lines, 4 files
    CBPV               -6.96 GB  (-1.29%)   3 files
    uncurried          -6.40 GB  (-1.17%)   56 lines, 2 files

The cluster deltas sum to -40.8 GB against a merged -34.1 GB. Two branches both
improved `Exponential/Base.agda`, and each measured against its own worktree
where absolute path length moves allocation 0.1-1.4%. The -34.1 GB is the figure
measured in one worktree against one baseline and is the one to quote.

### The technique that dominated

All four agents independently converged on the same lever: **supply arguments
that were left to unification**. An unsolved implicit forces the unifier to
invert a projection and unfold an entire tower to solve it; naming the argument
stops the descent.

    StateAlg/Vertical          8 implicits, 14 lines    -5.60 GB
    presLRⱽ-Isoⱽ-natural       4 annotations            11.524 -> 8.432 GB
    Family/EqProperties        2 arguments              2.06x
    Exponential/Base           base-path arguments      1.27x

`presLRⱽ-Isoⱽ-natural` is the case that shows the mechanism. Every
`F⟨LR⟩.βᵢLR _ _ _ _` left the two explicit arguments of
`LocallyRepresentableⱽAtNotation` as metavariables, and solving them forced the
unifier through `introᴰ`, `F⟨_×ⱽ_*FᴰPᴰ⟩`, `becomesUniversalⱽ→UEⱽ` and the whole
`preservesLocalReprⱽCone` tower. The same file already pinned those arguments in
one clause and not in the neighbouring one.

This is `03-SPELLING`'s rule in its strongest form, and it is mechanical enough
to sweep for. It is not uniformly good: pinning the second `rectifyOut` in
`isLRⱽObᴰReindex` measured 6.710 -> 6.717. Every site needs its own measurement.

### Notation trimming: the discriminator

`05-APPLICABILITY` presents Mechanism 3 as general. It is not. Three clusters
measured it as a no-op and one got 30%.

    NT/IntoFiberCategory/Base, without -> with `using`:
      DeadCodeReachable      1,413 ms -> 168 ms
      module total           5,261 ms -> 3,141 ms
      own .agdai            350,418 B -> 326,231 B
      all 474 .agdai     77,522,646 B -> 77,487,038 B    (-0.046%)
      GHC allocation          9.694 GB -> 6.799 GB       (-30%)

**Total interface bytes is the wrong screen** -- it moved -0.046% while
allocation fell 30%. The copies are cheap to store and expensive to walk. The
screen that works is `DeadCode.DeadCodeReachable` on the module itself: 1.4 s of
5.3 s where the technique fires, ~0 ms where it does not.

It fires when both hold: the copied section lands in a telescope of many
`Typeω`-kinded parameters, so each copied definition's type is enormous; and the
copy is re-exported `public` through further nested module applications, so it
is
copied again at each level. `PresheafᴰNotation` has ordinary Level and Category
parameters and satisfies neither -- trimming it moved 9.882 -> 9.868 GB.

### Limits found on the other techniques

**Root-cause splitting needs a writable path type.** Opacity is the load-bearing
half. In `Quantifiers/Base` the transparent version of the split bought 0.3%,
and
the opaque version is blocked: Agda will not infer the type of an `opaque`
definition, the path's type is two large inferred morphisms, and `abstract`
fails
because the body's metas can no longer be solved from the use site.

**`Typing.Generalize` is a billing artifact, not a lever.** It was 2,133 ms, 26%
of `Free/Pure/Additive` and 58% of its typing. Writing the generalized telescope
out explicitly moved the module 17.354 -> 17.347 GB. Agda bills the whole
`isType_` of any generalized signature to that bucket.

**Interface-visible sharing amplifies.** Sharing a repeated chain opener in
`Eq/Conversion/CartesianClosedV` saved 0.388 GB in its own module and 6.224 GB
build-wide -- 16x. It changes what the interface stores, so every dependent that
re-elaborates benefits. Per-module A/B understates this class by more than an
order of magnitude, in both directions: a previously-landed change saved
0.205 GB
locally and cost +0.825 GB build-wide.

**Truncating a large HIT eliminator is not comparable prefix to prefix.**
`{-# NON_COVERING #-}` lets you cut inside a clause list, but with one clause
present `UnifyIndices` goes 39 ms -> 1,498 ms and `Coverage` 73 -> 470 ms
building
the missing-branch tree. A 1-clause prefix reads 13.9 GB against a 6.3 GB floor
where the complete 40-clause definition reads 17.2 GB. Only deletions of a few
clauses from an otherwise complete definition are trustworthy.

### Where the remaining cost is

`×ηⱽᴰ-on` (6.89 GB, 43% of `Uncurried/UniversalProperties`' own work) resisted
four interventions; one regressed +2.4%. Decomposed: signature 0.18 GB,
`where`-block 2.12, chain body 4.8. The cost is conversion against `bpᴰ.intro`
and `bpᴰ.element`, which are transparent and unfold through the whole
`RepresentationPshIso` tower, and they cannot be made rigid locally because
`πᴰ₁ = bpᴰ.element .snd .fst` needs `element` to reduce for its own type to
check.

`Free/Pure/Additive`'s `elim-F-homᴰ` is 10.94 GB, 63% of its module, and is
diffuse: the bulk is the shared case tree over the 40-constructor HIT `Tm` and
the per-clause LHS types, not any proof.

## 11. Reind normal form: the closing account

Four separate attempts. The technique is real and its domain is narrow; the
useful output is the boundary, not the speedup.

### What it bought

One win, on the proof it was designed for: the gestalt quantifier proof went
21.45 -> 3.56 GB (6.0x), with a control confirming neither half pays alone
(normal-form endpoint plus the original proof measured 52.5 GB against the
original's 52.9). It also made 437 lines of previously-abandoned quantifier
mathematics affordable; those lines cost +12.58 GB in the full build.

### What it did not buy

A faster library. In the factor lattice (§10 of the earlier write-up, arms in
`perf/data/lattice-arms.tsv`) the RNF factor is **1,487 lines -- half the
churn -- and contributes ~0 GB whole-library**. Removing its rewrites together
with the mathematics they serve, the only way they can be removed, moves the
build by -0.31 GB.

Gain per 100 lines of churn, for comparison:

    F3 propertyover     498        F2 fixedpoint      18
    F1 presented        169        F7 rectifyout      12.7
    F8 notation-trim     43        F6 rnf            ~0

### Why: the boundary theorem

Entering the representation costs one transport and leaving costs one -- exactly
the transport being removed. **The technique pays only across a closed cone of
definitions and is strictly negative applied file by file.** Every measured
application outside the one win regressed: +2.8%, +6.1%, +9.1%, +21.8%.

Applying it to the whole canonicity cone under an interface freeze (168 modules,
56 with `reind` work) converted 4 files and moved the library -0.11%, inside the
0.1-0.3% cross-worktree floor. Three of the four most expensive filler-bearing
proofs were in files with zero RNF references afterwards.

Lifting the freeze hits a type error rather than a cost. An RNF-valued fibre
folds the base presheaf's level into the fibre, so

    reind α (reind β Rᴰ)  :  ℓ-max ℓQ (ℓ-max ℓR ℓRᴰ)
    reind (α ⋆ β) Rᴰ      :  ℓ-max ℓR ℓRᴰ

and the composition law is not a well-formed statement (`[NotLeqSort]`). That is
fixable by constraining levels, but the decisive obstruction is not levels:
`PresheafᴰNotation.reind` is `subst` over whatever the fibre is, so a record
fibre gets the record substituted and the transport is relocated onto the
wrapper, not removed.

Moving the normal form to the notation layer (`p[_][_]` itself) dissolves all
three -- one layer, no nesting, no level growth, and the notation's `reind` is
the RNF projection. It then fails on **representability**: `Cᴰ [-][-, cᴰ ]` is a
displayed presheaf whose fibre *is* `Cᴰ`'s hom set, so converting the notation
entails converting `Categoryᴰ`'s homs. The seam is `introᴰ`, 261 sites.

### What it actually is

`Σ[ a' ∈ A ] (a ≡ a') × B a'` is the Ford encoding with a path -- the based path
space, coyoneda for the identity type. Nothing in it is category-theoretic. It
requires nothing of `A`; `isSet A` is needed only for the cheap eliminator, and
the coherence bookkeeping returns at higher h-levels.

It does not give regularity. `reind refl x` is not definitionally `x`, because
`sym refl ∙ p` is not definitionally `p` -- the problem moves from `subst` to
`∙`. What it gives is definitional invariance of the observables: `val`, `idx`
and `∫` are unchanged, and towers collapse (`tower _ _ _ _ _ = refl`).

**The strict-`Eq` version is the one that computes.** `Eq` is the inductive
identity type, so `substEq Eq.refl x` and `Eq.trans Eq.refl p` both reduce
definitionally. The library's forded `Eq` code is this construction at a strict
identity type, and it measured **~4.3x cheaper** than the path route for the
same mathematics in one file. That gap is the price of cubical `∙` not
computing on `refl`.

### The ranking that follows

Given cubical has no regularity, there are three responses:

1. **Do not create the transport** -- ford it, carry the equation. ~4.3x cheaper
   than paths, and the only one with definitional regularity.
2. **Defer the transport** -- this technique. One win, otherwise negative.
3. **Pay it and rectify well** -- 694 sites, ~67 GB, third-largest factor.

(1) and (3) beat (2) in this library.

### Branches

    rnf-everywhere @ d0535041     green, -0.135%, superseded by §10's rework
    rnf-strong-wip @ 558e6ad7    no build; holds the [NotLeqSort] evidence
    rnf-pointwise-nf @ f1767cfe   green, framework additions only
    rnf-pointwise-nf-wip @ 7f4dc145  no build; the representability error

Not merged into `perf-final`. The framework itself (`Cubical/Foundations/
ReindNormalForm.agda`, 441 lines) is on `perf-all` and ~250 of its lines have no
clients: `Products`, `Sums`, `Functions`, `DepSigma`, `mapRNF`, `Iso-RNF`,
`≃-RNF`. Only `RNFSet` and `map₂RNF` are used, from two files.

## 12. Structures unblocked, and the Eq question

### Displayed sets: the path route now exists

`ExponentialsⱽSETᴰueⱽ`, `ExponentialsⱽSETᴰ`, `UniversalQuantifiersSETᴰ` and
`SETᴰCCCⱽ` type-check. They had been commented out.

The blocker was not cost. Two things were wrong: `hSet` eta-splits the implicit
displayed object, producing non-pattern constraints (9 unsolved metas, rc=42),
and the author's 4-step `reind-filler⁻` chain was **ill-typed** -- the innermost
`reind` is indexed over `Z → Z` at `g*Xᴰ`, the outer three over `Z → X` at `Xᴰ`,
so they are different `∫`-Σ-types and can never be one `∙`-chain. The fix is a
3 + 1 split composed with ordinary `∙`. No amount of implicit-supplying would
have completed the code as written.

    module, constructions commented out    4.703 GB   3.00 s
    module, constructions live            31.879 GB  20.59 s

**Eq versus path, like for like.** In-file the Eq route delivers CCⱽ, CCⱽ^op,
CCCⱽ and BCCCⱽ for 0.196 GB; the path route delivers CCCⱽ alone for 27.19 GB.
That flatters Eq, whose mathematics lives in `Eq/Conversion/*`, each on a
~4.3-4.5 GB import floor. Netting the floors out, Eq's marginal mathematics is
~6 GB against the path route's 27.2 -- **~4.3x, not an order of magnitude**.

**Downstream the choice is invisible.** `Gluing/*/BoolNatCanonicity/Path.agda`
differs from its `Forded.agda` sibling in one token:

    CCC canonicity, Forded   4.765 GB
    CCC canonicity, Path     4.766 GB

The entire difference is paid once, in `Sets/Properties.agda`, and no client
sees it. The path route is not yet a replacement: no coproducts and no `^op`,
so the BiCartesianClosed gluing proofs still require `Eq`.

### Displayed presheaves: cartesian yes, closed not yet

`Instances/Presheaf/Uncurried/Strict/{Base,Cartesian,CartesianClosed}.agda` are
new and Eq-free. `Terminalsⱽ`, `BinProductsⱽ`, `isFibration` and
`CartesianCategoryⱽ` are **complete**. The vertical exponential has its
pointwise universal property (`expIsoⱽ`); what remains is the **naturality
square**, and that is exactly what the ford buys. Over the `Eq` slice the
triangle is `Eq.refl`, and the forded proof is
`Eq.pathToEq (makePshHomPath refl)`. Over the path slice it is a genuine path,
and the residual is Frobenius bookkeeping: `Δᴰ` against `Δᴰ ×Psh (δ *Pᴰ)`.

    Eq route     Eq/Base 9.347   Eq/Cartesian 3.665   Eq/CartesianClosed 9.567
    path route   Base 6.698      Cartesian 5.247      CartesianClosed 4.978

**Cost is not what forces `Eq` here.** Both routes are single-digit GB. The ford
is bought for provability.

The blocker had been that the mathematics was never written: the path-based
`PRESHEAFᴰ` in `Uncurried/Base.agda` has zero downstream users, and nothing
transfers from the forded route because the `Eq` `PRESHEAFᴰ` is a different
category -- its fibres are presheaves on the `Eq` slice. Remaining beyond the
square: the universal quantifiers and the whole op side, which exist in neither
formulation, so `EqBCCCⱽ→BCCCⱽ` has never been instantiated for presheaves at
all.

Two measurements worth keeping. The base must be the **strict** `PRESHEAF`: with
the ordinary one, `⋆IdR α = makePshHomPath refl` does not reduce on `.N-ob`
because `PshHom` is `no-eta-equality`, so each β law needs a transport of a path
in a large function space -- over 600 s for binary products alone. And never
force a `reind`: pairing the two product β laws under one `makePshHomPath` did
not finish in 500 s, where deriving η from them by `cong₂` costs 0.5 GB.

## 13. The final sweep

`{agda, mikan} x {main, perf-final}`, every cell a from-scratch
`--build-library` under an exclusive lock, parity mode so all four check
byte-identical source. Driver: `perf/bin/sweep-2x2`.

    cell                alloc GB   wall s   maxrss MiB   modules
    agda  x main           847.8    301.5         5190       469
    agda  x perf-final     547.4    189.4         4608       476
    mikan x main           330.8    130.9         4892       469
    mikan x perf-final     266.1     98.3         4318       476

    agda  : 1.55x allocation, 1.59x wall, -11% peak memory
    mikan : 1.24x allocation, 1.33x wall
    tool-to-tool on main:       2.56x allocation, 2.30x wall
    tool-to-tool on perf-final: 2.06x allocation, 1.93x wall
    corner to corner:           3.19x allocation, 3.07x wall

### The comparison is not like-for-like

`perf-final` carries 7 modules `main` does not: the displayed-sets exponentials
and quantifiers, the two path-based canonicity clients, and three Eq-free
displayed-presheaf modules. It proves strictly more.

    main         847.8 GB
    perf-all     549.0        the earlier perf work
    push-all     514.9        + this session's four clusters  -- 1.65x, pure
    perf-final   547.4        + ~32.5 GB of new mathematics

**The like-for-like speedup is 1.65x.** The new constructions cost 32.5 GB of it
back. Quote it both ways.

### Mikan is not checking the same library

Mikan rejects `--guarded` and `--rewriting`, so every mikan cell builds a
**port**
that comments out `Guarded/Later/{Base,Properties}.agda` and
`Guarded/Gluing/Canonicity.agda` -- 338 lines of 61,426, **0.55%** -- and
rewrites
two proofs for its stricter termination checker. Measured, those three modules
are ~5-6 GB of 848, about **0.7% of allocation**, so the tool ratios above are
not an artifact of the missing code. But `Guarded/Gluing/Canonicity.agda` is a
real 222-line gluing theorem that mikan does not check at all. "Mikan builds the
library" overstates it.

### The dependency diverges too

The two columns do not share a cubical. The agda cells use
`/home/steven/cubical`
@ 92166033; the mikan cells use `mikan-bench/cubical-mikan` @ 80cc9bd5, which is
that same commit plus 1lab/agda-cubical's Mikan port -- **40 `.agda` files,
+66/-89 lines**, and different library flags:

    agda  cubical: --safe --cubical --no-import-sorts --guardedness
                   -WnoUnsupportedIndexedMatch
    mikan cubical: --safe           --no-import-sorts
                   -WnoUnsupportedIndexedMatch

What the port changes:

- **The reflection API is incompatible.** `R.arg-info` takes no modality
  argument, so `varg`/`harg` and `makeAuxiliaryDef` are rewritten. This touches
  `Reflection/{Base,RecordEquiv}` and all seven `Tactics/*/Reflection` modules,
  i.e. every solver tactic. Pointing mikan at the agda cubical fails here.
- **All 20 `Cubical/Codata/*` modules lose `{-# OPTIONS --guardedness #-}`.**
- `Induction/WellFounded` and `Data/W/Indexed` change to the indexed-`Acc`
  shape -- the same termination strictness the ccl-side port needed, so it runs
  through both layers.
- `Algebra/BooleanRing/Base` is the largest single change at +30/-32.

So the mikan column is a **patched library on a patched dependency with
different flags**, not the same verification under a faster checker. The ~2x
tool ratio is real for what it measures; what it measures is not identical.

### Two harness bugs found by running it on a cold machine

Both would have fired on a fresh checkout elsewhere and looked like library
faults:

- `cubical_for()` returned the dependency path on stdout while also printing
  progress there, so the message was captured into the path. Only fires on a
  cold
  work directory. Fixed: progress to stderr.
- Mikan needs its own cubical checkout; pointing it at the agda one fails on a
  reflection pattern synonym (`R.modality R.relevant R.quantity-ω`). Fixed:
  `MIKAN_CUBICAL_DIR`.

A third is worth recording as method rather than code: `die` inside `$( )` exits
only the subshell, so a failed dependency build yields an empty path and the
cell
fails later with a confusing error.
