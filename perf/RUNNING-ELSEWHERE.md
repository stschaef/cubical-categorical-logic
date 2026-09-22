# Running the performance analysis on another machine

Everything here is self-contained apart from two dependencies you must supply:
an `agda` binary and a checkout of `agda/cubical`. Mikan is optional and needs
its own cubical.

## Prerequisites

    agda                        on PATH, or set AGDA=/path/to/agda
    agda/cubical                set CUBICAL_DIR=/path/to/cubical
    mikan            optional   set MIKAN=/path/to/mikan
    1lab/agda-cubical optional  set MIKAN_CUBICAL_DIR=/path/to/agda-cubical

Mikan cannot use the ordinary cubical: its reflection API differs
(`R.arg-info` takes no modality argument), so `Cubical/Reflection/*` and every
`Tactics/*/Reflection` module fail. Clone 1lab's port instead:

    git clone https://codeberg.org/1lab/agda-cubical

The pin used for the recorded numbers is `agda/cubical` @ 92166033 and
`1lab/agda-cubical` @ 383f7e46.

## The two scripts, and which question each answers

### `perf/bin/perf-stack` -- what each individual edit is worth

**Agda only.** Walks the per-edit branch stack bottom to top, building each
revision from scratch and differencing allocation, so each row is the cost of
one edit measured in the context it ships in.

    CUBICAL_DIR=/path/to/cubical perf/bin/perf-stack

    -d          dry run: resolve every revision, build nothing
    -r REVS     comma-separated subset instead of the full stack
    -n REPS     repeat each revision (allocation should be identical)
    -o REPORT   where to write the markdown (default perf/STACK-RESULTS.md)
    -w WORKDIR  scratch (default $TMPDIR/perf-stack-$USER)
    -k          keep each revision's _build

It uses jj when the repo is colocated and git otherwise; both resolve revisions
identically. It will NOT colocate for you -- `jj git init --colocate` snapshots
the working copy into git's index, which silently stages anything `.gitignore`
misses, and this repo's `/_build/` is root-anchored so nested `_build` dirs slip
through. Run `jj git init --colocate` yourself if you want the jj path.

Cubical is built once and shared, so the figures are the cost of THIS library.

### `perf/bin/sweep-2x2` -- agda versus mikan

Builds `{agda, mikan} x {base, head}`, one cell at a time under an exclusive
lock.

    CUBICAL_DIR=... MIKAN_CUBICAL_DIR=... MIKAN=... \
      perf/bin/sweep-2x2 -b main -H perf/merge-candidate

    -b BASE -H HEAD    revisions to compare
    -t agda,mikan      which tools
    -P                 turn OFF parity mode (see below)
    -d                 dry run

**Parity mode is on by default.** Mikan rejects `--guarded` and `--rewriting`,
so its cells build a port of each branch that stubs three `Guarded/` modules
(338 lines of 61,426; ~0.7% of allocation) and adjusts two proofs for its
stricter termination checker. By default that port is applied to the agda cells
too, so all four cells check byte-identical source. `-P` builds the agda cells
from the branch as it stands instead. Every row records which it was.

## Reading the numbers

The metric is **GHC bytes allocated**, from the RTS's own `-s` report. It is
deterministic to eight significant figures within a worktree and immune to
machine load, which is why a marginal cost of a few hundred MB is meaningful.

Wall time is recorded but is not a result: on the reference machine it varied by
up to 17% between a quiet and a contended run of identical source. Builds are
serialised for that reason.

Two traps that cost this investigation real time:

- **A cold dependency interface inflates the first reading**, by up to 20x.
  Always take a second reading of anything surprising.
- **Absolute path length shifts allocation** by 0.1-1.4%, because the build
  allocates strings for paths. Never compare a number taken in one worktree
  against one taken in another; measure your own baseline.

## Recorded results for comparison

`perf/06-RESULTS.md` has the full account: §§1-9 the earlier sweep and RTS
tuning, §10 the argument-pinning clusters, §11 the reind-normal-form closing
account, §12 the structures unblocked, §13 the final 2x2, and §14 the
per-technique A/B with its additivity and amplification checks. The headline figures, all on one
machine (12 cores, 31 GiB, `-j1 +RTS -N1 -A1G -H4G -M24G`):

    agda  x main          847.8 GB   301.5 s
    agda  x perf-final    547.4      189.4
    mikan x main          330.8      130.9
    mikan x perf-final    266.1       98.3

    cubical itself, from scratch:  agda 1136.0 GB / 381.4 s
                                   mikan 719.1 / 235.5

The dependency is ~2.7x the library, so most of a cold build is cubical.
