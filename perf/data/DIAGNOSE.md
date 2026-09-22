# How to find out WHY a module is slow

Read HARNESS.md first for the machine budget and wrapper scripts.

## Step 1 — get per-definition attribution
Agda's `--profile` takes: internal, modules, definitions, sharing, serialize,
constraints, metas, conversion, instances, sections (or `all`). The table is
printed at the end of the run, sorted descending.

    # inside your worktree, holding a slot:
    checkfile agda <worktree> <Rel/Path.agda> --profile=definitions

`checkfile` throws away stdout, so for profiling run the tool directly but
STILL take a slot — easiest is to copy checkfile into your worktree and make it
keep the output, or just run one profiling job at a time yourself with
`+RTS -N1 -M6G -RTS` and accept that you are using one of the 4 slots.

`--profile=definitions` tells you which definitions the type-checker spent its
time *reducing*. That is the single most useful view: it usually points at one
or two record constructors / projections / `reind`-style helpers that are being
unfolded over and over.

`--profile=metas,constraints,conversion` tells you the shape of the work:
how many metas were created and solved, how many constraints were woken and
re-solved, and how much time went into conversion checking. In this library the
recurring hypothesis (written down by the author in several source comments) is
that the cost is **unification of large implicit arguments**, not computing big
paths. Numbers from these counters are how you confirm or refute that.

`+RTS -s -RTS` gives allocation and GC, which is the currency that actually
matters: mikan is 2.2x faster than Agda on this library almost purely because it
allocates 2.6x less. If a source change cuts allocation, it will cut time.

## Step 2 — bisect within the file
Comment out the back half of the module and re-check; halve again. Agda reports
`Checking` per module, not per definition, so bisection is how you localise.
`--profile=definitions` usually makes this unnecessary, so try that first.

## Step 3 — the fixes that are known to work in THIS library
The author has left explicit notes in the source about what helped:

* **Supply implicit arguments explicitly.** Repeated, independent observations:
  - `Cubical/Categories/Displayed/Presheaf/Uncurried/Base.agda:218` and
    `.../LocallySmall/Displayed/Presheaf/GloballySmall/Uncurried/Base.agda:46`:
    "Cᴰ and P *must* be supplied, Cᴰ for type-checking and P for performance."
  - `Cubical/Categories/Displayed/Instances/Reindex/Limits.agda:110`:
    "the annotations on reindⱽFuncRepr are crucial for performance"
  - `Cubical/Categories/Displayed/Instances/Presheaf/Eq/Base.agda:271`:
    "This is very slow without the annotations to refl."
  This is the highest-yield technique. It works by stopping Agda from solving a
  big implicit by conversion-checking two large category/displayed-category
  terms against each other.

* **`opaque`.** 39 files already use it; `abstract` is used in exactly 1.
  Marking a definition `opaque` stops it unfolding during conversion. Commit
  9bcc1108 did this for reindexing specifically ("opaque reindexing"). Watch
  out: making something opaque can break downstream code that relied on it
  computing, so verify dependents still check.

* **Avoid nested `reind`.** `Cubical/Categories/Displayed/Instances/Sets/Properties.agda:167-181`
  records the author's own hypothesis verbatim: "the slowness isn't actually
  from computing big paths, rather its the unification of the implicit arguments
  to each of these reind fillers. If this is true, then we may mitigate the
  slowness here by removing nested reindexings."

* **`no-eta-equality`** on records that are large and never need eta. Already on
  `Category` (upstream) and on the five `Bifunctor` variants. Check whether the
  records your module is manipulating have it.

* **Module-copy trimming**: `module C = Category C` copies every name in the
  record module; `module C = Category C using (id; _⋆_; ⋆IdL)` copies three.
  Library-wide this is only 1-3% (02-NOT-LANDED.md), but on the LocallySmall
  notation modules it is much larger; see 01-MECHANISMS.md mechanism 3.

* **`--lossy-unification`**: check whether the file already has the pragma
  before proposing it; nearly every module in the library does.

## Step 4 — the bar
A speedup that breaks the build is not a speedup. After changing a file, that
file must still type-check clean (no new holes, no unsolved metas), and you must
also re-check its direct dependents — grep for modules that import yours. Do at
least a spot-check of the heaviest dependents.
