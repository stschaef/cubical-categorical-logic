# Interventions measured but NOT landed on this branch

## `term.patch` -- naming repeated inline expressions (Hypothesis D)
Measured 1.64x on `Displayed/CBPV/Unary/Instances/StateAlg/Vertical.agda`
(30.72s -> 18.72s median of 15 interleaved A/B pairs, GHC allocation
26.03 -> 16.65 GB, maxrss -24%). Binds four repeated inline expressions to
private names: `SACBPV ℓ = ∫C (StateAlgCBPV {ℓ = ℓ} .fst)`, `SACBPVᵒᵖ ℓ`,
`SACBPVᴰ ℓ`, `SACBPVᴰᵒᵖ ℓ` (12/17/6 inline occurrences). `--profile=internal`
confirms the predicted mechanism -- only term-size-proportional phases move:
Positivity -62%, InterfaceInstantiateFull -57%, Termination -63%,
OccursCheck -42%, while Typing.CheckRHS is unchanged.

**Why it is not landed:** it conflicts with the `rectifyOut` sweep (commit
7134efb9) and the mutual-block split, all three of which edit the same file.
Resolving needs a hand-merge plus a re-verify that I could not do reliably here.
The patch is kept at `perf/patches/term.patch`; reconcile it against the
current `Vertical.agda` before use. Projected library-wide payoff is only ~1.8%
and essentially all of it is this one file, which the rectifyOut sweep already
improves (maxrss -44%), so the incremental value is smaller than the raw 1.64x
suggests.

## Mikan port (`mikan.patch`) -- different toolchain, not a source change
Not a candidate for `main` as a whole. But **two of its edits are accepted by
stock Agda 2.9.0 and should land regardless**, because they cost nothing and
keep the tree portable:
  * `Cubical/Categories/Direct/Product.agda` -- `wf<Lex`: single `go` becomes
    mutual `accLex`/`accLex'`.
  * `Gluing/Category/Forded.agda` -- `NormalForm`: `o2` and `e` move from
    parameters to indices.
Verified by that agent's `ab-agda-st` run: rc=0 over 472 modules under Agda.

## Refuted, kept only as notes
* **`no-eta-equality`** on `UniversalElement` / `Section` / `Presheafᴰ`.
  `Presheafᴰ` is not a record at all (it is `Presheaf (Cᴰ / P)`, a `Functor`,
  which already has `no-eta-equality`). The other two are upstream in `cubical`.
  On `Instances/Presented.agda` -- the best possible case, 97% of it being
  `elim` returning a `GlobalSection` -- allocation was 85.422 GB with eta vs
  85.427 GB without, i.e. identical to 0.006%. Disabling eta on
  `UniversalElement` additionally breaks one site
  (`Presheaf/Constructions/Reindex.agda:145`, fixable with `Eq.J`). Not worth
  the compatibility risk. The diff that was measured is
  `perf/patches/term-cubical.patch` (it edits `cubical`, not this library).
* **Module-copy trimming on `Category`/`Fibers` applications** -- ~1-3%.
  (The LocallySmall *notation*-module trimming in commit 16fd9c4c is a
  different and much larger effect; see 01-MECHANISMS.md mechanism 3.)
* **Import minimisation** -- `Import`+`Scoping` is 0.36-1.0% per module, the
  whole ceiling. In a single-process build each interface is deserialised once
  regardless of how many modules name it.
* **`--no-positivity-check`** -- ~3%. Agda still computes the occurrence graph;
  the flag only skips the verdict. Positivity is high because terms are big.
* **Explicitly supplying implicit arguments** -- the technique the codebase
  reaches for everywhere. ~3% (noise) on the Uncurried cluster; all four
  variants failed on `Presented.agda` (114-118s against a 117s baseline); and
  on `Reindex/UniversalQuantifier.agda` naming subterms without signatures
  *breaks the build* (29 unsolved metas) while with signatures it is 10%
  *slower*. Consistent with the meta counters: this library's problem is not
  the unifier.

## Method correction worth carrying forward
`.agdai` size is a poor proxy for elaborated term size: Agda **hash-conses** on
serialization, so N inlined copies of a term cost one node on disk. The
`Vertical.agda` win shows it starkly -- time -39%, allocation -36%, interface
size -0.17%. Use `+RTS -s` allocation as the deterministic, contention-immune
signal instead.
