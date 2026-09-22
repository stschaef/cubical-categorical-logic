# perf/ — reproducing and checking the performance claims

The per-module claims in the `perf:` commits on this branch are mechanically
checkable: `perf/cases.tsv` registers one case per technique and `bin/ab-suite`
re-measures each against the pre-sweep commit. The whole-build result is in
`06-RESULTS.md` and is reproduced by building the two branches, not by the
suite.

## Quick start

    perf/bin/ab-suite                 # run every case
    perf/bin/ab-suite notation-trim   # run one
    REPS=3 perf/bin/ab-suite          # repeat each measurement

Exit status is 0 if every case reproduced its claimed ratio, 1 otherwise, so it
can be wired into CI or a pre-merge check. Raw numbers land in
`perf/ab-results.tsv` (TSV, one row per arm per module).

## What it does

Each case in `perf/cases.tsv` names some source files and the modules to
measure. For every module it is measured twice against an otherwise identical
tree:

    arm A   the case's files at the pre-sweep commit (82334ffb)
    arm B   the case's files as they are now

Only the case's own files move; every dependency stays fixed. That isolates the
one change. This is sound because these defects are **file-local** — fixing a
module measurably does *not* speed up its importers, which was verified
separately.

## Why allocation, not time

The metric is **GHC bytes allocated**, read from the RTS's own `-s` report.
Allocation is deterministic here — repeats agree to about three decimal places —
so ratios are stable across machines and immune to load. Wall time is recorded
too but is only indicative: on a loaded machine single-run wall time varies by
±30%, which is larger than several of the effects being measured.

This also means the suite needs no external `time(1)`: everything comes from the
RTS, so it is portable to any machine with Agda and a shell.

## Running it elsewhere

    git clone <repo> && git checkout perf-all
    # make sure `agda` resolves and the `cubical` dependency is available
    perf/bin/ab-suite

Knobs, all environment variables:

    AGDA=/path/to/agda     use a specific Agda (default: `agda` on PATH)
    LIBFILE=/path/libs     pass --library-file (default: ./libs.txt if present)
    BASE_COMMIT=<sha>      the arm-A commit (default: 82334ffb)
    REPS=N                 repeat each measurement N times (default 1)
    HEAP=8G                RTS -M cap (default 6G)
    TOL=0.6                fraction of the claimed ratio required to pass
    OUT=/path/out.tsv      where to write raw results

The claimed ratios in `cases.tsv` are deliberately conservative — set below the
measured values — so the suite flags a real regression rather than tripping on
machine-to-machine variation. `TOL` loosens it further.

The suite refuses to run on a dirty working tree, since it checks files in and
out of the index to switch arms.

## What is here

    00-METHOD.md      how the baseline was measured, which profiler views to
                      trust, the measurement hazards, and a log of everything
                      touched outside the repo
    01-MECHANISMS.md  the mechanisms found, with the counter-evidence that
                      refutes the "unification of large implicits" hypothesis
    02-NOT-LANDED.md  measured but not landed, and why; plus the refuted ideas
    03-SPELLING.md    the copattern/record spelling anti-pattern, measured
    04-RNF-DESIGN.md  the reind normal form: design, evidence and results
    05-APPLICABILITY.md  which of the three techniques applies where
    06-RESULTS.md     *** the authoritative full-build result for the coalesced
                      perf-all branch: arms measured serially with +RTS -s
                      accounting, per-technique attribution by whole-build
                      revert, and a per-module comparison ***
    bin/ab-suite      the A/B suite described above
    bin/ab            single-case interleaved A/B harness (older, wall-clock)
    cases.tsv         the case registry
    patches/          raw diffs from each experiment
    data/             per-module profile ranking, rebuild fan-out, RTS stats
