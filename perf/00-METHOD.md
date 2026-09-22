# Performance sweep: method and intervention log

Everything in this directory was produced by a systematic performance sweep of
`cubical-categorical-logic` at commit `82334ffb`. It is written so that every
number below can be re-measured and every claim falsified.

## 1. What was measured, and how

### Baseline
A clean serial full build, on an otherwise idle machine, with the `cubical`
dependency already warm:

```
agda +RTS -M24G -s<file> -RTS --build-library --profile=modules
```

    wall 582.1s   user 576.8s   maxrss 4575 MiB   424 modules type-checked

GHC RTS accounting for that run:

    842,418,758,504 bytes allocated in the heap
    214,532,828,648 bytes copied during GC
      1,971,393,208 bytes maximum residency
    Gen 0: 200,573 collections, 202.7s      Gen 1: 140 collections, 30.8s
    MUT 343.3s   GC 233.4s   ->  GC is 40.5% of the build, productivity 59.5%

`--profile=modules` gives per-module attribution; the ranking is in
`perf/data/rank.tsv` (ms, then module name, descending).

### Per-module attribution
`--profile=modules` totals 576,373 ms across 424 modules. Concentration:

    top 10 modules = 37.8%     top 23 = 56.4%     top 50 = 73.2%
    by subtree: Displayed 325s (56%) | LocallySmall 95s (17%) | Instances 86s (15%)
                Presheaf 9.3s | Limits 8.2s | ... | Gluing only 12.6s (2%)

This is a concentrated problem: roughly 25 files carry over half the cost.

### Which profiler view to trust
Agda's `--profile` takes `internal|definitions|metas|constraints|conversion|...`.
Hard-won lessons, each of which cost an agent real time:

* `--profile=definitions` **mis-attributes**. In `Reindex/CartesianClosed.agda` it
  billed 16.0s to a definition whose fields, when holed out, changed the module's
  time by <1s. Work done in `where`-block clause bodies lands in `Miscellaneous`.
  Treat it as a hint and confirm by bisection.
* `--profile=internal` is the view that actually cracked two of the five findings,
  because it separates type-checking from interface generation
  (`DeadCodeReachable`, `Serialization`, `Deserialization`).
* `--profile=metas,constraints` is how you *refute* the "unification of large
  implicit arguments" hypothesis that this library's source comments repeatedly
  assert. In every hot module we examined, meta and constraint counts were small
  and `compare`/`compare by reduction` counts were huge.
* `+RTS -s` is the ground truth. Allocation volume predicts time better than any
  other single number: mikan is 2.2x faster than Agda on this library almost
  exactly because it allocates 2.6x less.

### Bisection
The reliable localisation technique is to hole out one record field or one clause
at a time and re-time. A trap to know about: holing an *earlier* field makes later
ones dramatically slower (13s -> 87s in one case), because the expected type becomes
meta-blocked. Hole one field at a time, not all-but-one.

## 2. Measurement hazards on this machine

* **Contention.** Up to ten agents shared 12 cores. Wall-clock ratios measured
  back-to-back in one batch are meaningful; absolute numbers from different times
  are not. Every contended number in these notes is labelled as such.
* **Cold upstream modules.** `/home/steven/cubical` is only partially built (~288
  of its modules). The first single-file check that needs an unbuilt upstream
  module pays to build it -- up to +75s, attributed to the wrong file. One agent
  nearly abandoned a correct patch over this. Always take a second reading.
  `perf/bin/ab` discards a warm-up run of each arm for exactly this reason.
* **Interface deserialization floor.** For modules in the `Displayed`/`LocallySmall`
  subtrees the floor is ~1.7-2s quiet, ~5-6s contended. Do not compare ratios of
  small modules directly against large ones without subtracting it.

## 3. Reproducing the A/B results

```
perf/bin/ab <intervention> [reps] [extra RTS flags]
```

Interventions are listed in `perf/manifest.tsv`. The script builds a pristine
worktree at `82334ffb`, then for each rep measures the module(s) at HEAD, applies
the intervention's patch, measures again, and reverts -- **interleaved**, so drift
hits both arms equally. It reports wall, user, maxrss and `.agdai` size.

`.agdai` byte size is the primary metric where the mechanism is term size: it is
deterministic and immune to machine load. Time is the confirmation.

## 4. Interventions made to the machine (full log)

Nothing in the main checkout was modified. `git status` in
`/home/steven/cubical-categorical-logic` is clean at `82334ffb` throughout, and the
shared `cubical` dependency at `92166033` is untouched (its stray untracked
`CLAUDE.md` is dated 2026-02-01 and predates this work).

Created:
* `_build/2.9.0` in the main checkout was deleted and rebuilt once, to obtain the
  profiled baseline. A copy of the pre-existing tree was taken first.
* Git worktrees `/home/steven/ccl-perf-{lossy,mikan,par,f1..f5,imports,phase,term,coy}`,
  one per experiment, each with a copy of the warm `_build` and its own `libs.txt`
  so imports resolve to the worktree rather than the baseline.
* `/home/steven/ccl-perf-branch` on branch `perf-sweep` (this branch).
* Git worktrees `/home/steven/ccl-perf-all` (branch `perf-all`, the coalesced
  branch), `/home/steven/ccl-perf-nomath` (branch `perf-all-nomath`, the
  like-for-like arm of 06-RESULTS.md §4) and `/home/steven/ccl-main-base`
  (detached at 82334ffb, the baseline arm).  Three scratch worktrees
  `ccl-rv1..3` were used for the per-technique reverts and removed afterwards.
* A scratch directory holding the harness, profiler output and logs.

No commits were pushed anywhere; everything is local.

## Result: full-build A/B, HEAD vs this branch

Clean serial `--build-library`, no profiling instrumentation, `-M16G` to match the Makefile,
each arm preceded by a discarded warm-up build so no arm pays for cold upstream `cubical`
modules. All four rc=0, zero errors. 472 modules at HEAD, 473 on the branch (the extra is the
new `Displayed/Reasoning/More.agda`).

    arm                       wall      user      maxrss
    A  HEAD      -M16G       819.1s    784.7s    4784 MiB
    B  branch    -M16G       643.1s    593.4s    3703 MiB
    C  branch    -A256M      553.8s    523.8s    3361 MiB
    D  HEAD      -A256M      857.8s    830.9s    4618 MiB

**Source changes alone (A -> B): 1.32x on user time, and 23% less peak memory.**
With the RTS tuning as well (C): 523.8s and 3361 MiB.

Caveat, stated plainly: the machine was not quiet. Another of the user's sessions became active
partway through, and load reached 18.2 with 4 competing agda processes by the last arm. A ran
earliest and D last, which is why D appears slower than A despite -A256M -- a result that
contradicts the dedicated 18-build RTS sweep and should be treated as contaminated rather than
believed. A and B ran adjacently under comparable load, so the 1.32x is the sound figure. The
memory reduction is robust regardless, since maxrss is far less load-sensitive than time.

For per-change attribution, use `perf/bin/ab-suite`, which measures GHC allocation and is
deterministic and load-immune.

---

## Superseded by 06-RESULTS.md

The full-build A/B above was measured on `perf-sweep` alone, on a contended
machine, and is superseded. **`perf/06-RESULTS.md` is the authoritative
full-build result** for the coalesced `perf-all` branch (`perf-sweep` +
`rnf-all`): arms run strictly serially, twice
each, with `+RTS -s` accounting, a per-technique attribution by whole-build
revert, and a per-module comparison. Headline: **841.148 -> 542.413 GB allocated,
GC 40.3% -> 33.9% of the build, 1.73x on user time, -33% peak RSS** — while
additionally type-checking 437 lines of quantifier mathematics that `main` does
not.

It also records two corrections to this directory.  `8bcea917` does not contain
the change its message describes, so the `fixedpoint` row of `ab-results.tsv`
should be restated; and a per-module A/B is not sufficient evidence to land a
change, because a fix can pay locally and be charged to its dependents (one was,
and was reverted).  See 06-RESULTS.md §2.
