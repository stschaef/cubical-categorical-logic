# What actually makes this library slow

Four distinct mechanisms were identified, each confirmed by bisection. They are
*not* the mechanism the library's own source comments blame.

## The hypothesis that is wrong

Source comments in at least five places attribute slowness to unification of large
implicit arguments. The clearest statement is at
`Cubical/Categories/Displayed/Instances/Sets/Properties.agda:167-181`:

> the slowness isn't actually from computing big paths, rather its the unification
> of the implicit arguments to each of these reind fillers.

Measured meta and constraint counts in the hot modules:

| module | metas | attempted constraints | compares | time |
|---|---|---|---|---|
| `Instances/Presented` | 559 | 59 | 230,343 (118,421 by reduction) | 65.7s |
| `Reindex/UniversalQuantifier` | 2,124 | 65 | 157,985 | 24.5s |
| `Displayed/FixedPoint` | 2,038 | 13 | 14,491 | 43.9s |
| `LocallySmall/.../NT/IFC/Base` | 1,344 | 302 | -- | 20s |

A few thousand metas cannot cost 25-65 seconds. The revealing ratio is allocation
per comparison: **~180 KB allocated per comparison** on `Reindex/UniversalQuantifier`,
and ~3.2 MB per comparison for the single hottest clause. The comparisons are few
and each one is enormous.

The refined statement: unification *triggers* the work -- an implicit argument is
what forces two spellings to be compared -- but the cost is entirely in reducing
the giant terms the comparison then descends into. **Reducing the number of metas
is not the lever. Reducing the size of what gets compared, or stopping the
comparison descending at all, is.**

Corollary, measured as a negative control: metas are expensive only when they
*block* a comparison. Replacing six explicit arguments by `_` took a 24s module to
over 10 minutes. Holing a record field so the expected type became meta-blocked
took a 13s field check to 87s.

---

## Mechanism 1 -- conversion-checking two spellings of the same term

The dominant cost in the single worst module in the library.

`Cubical/Categories/Instances/Presented.agda` is 115 lines, and all of its 65s is
one function application. Bisection: `CatQuotient.elim 𝓒 _≈_ reflₑ ⋆ₑ-cong 𝓓` is
free; adding the `F` argument costs 117.5s (contended). The cost is one conversion
check,

    GlobalSection 𝓓'  ≟  GlobalSection (ReindexQuo.reindex 𝓒 _≈_ reflₑ ⋆ₑ-cong 𝓓)

where `𝓓'` is *defined to be exactly the right-hand term*. Agda's syntactic-equality
fast path misses because the two sides are spelled differently; it then delta-unfolds
both through `EqReindex.reindex = redefine-id⋆ (Reindex.reindex 𝓓 QF) singId singSeq`
and grinds structurally through the `singl`-typed arguments -- the 8-deep
`implicitFunExt`/`funExt` nests over `reind≡reind'` at
`Displayed/Instances/Reindex/Eq/Base.agda:90-108`. 85.7 GB allocated for one module,
about 10% of the library's entire allocation.

Every "supply the implicit explicitly" remedy failed: writing the expected type out
literally 116.0s, an explicit signature on `𝓓'` 114.0s, an abstract `Categoryᴰ`
117.8s, passing `_` 118.4s. The fix is to not make the call -- see intervention
`presented`.

## Mechanism 2 -- a type synonym as a record-field type is a conversion bomb

The same mechanism, in a form that generalises and has a clean fix.

In `Reindex/CartesianClosed.agda`, 100% of the module's own work is the single field
`CCCⱽReindex .forallⱽ`. The term is not expensive to elaborate -- given its own
explicit signature it costs 1.5s. It is one conversion check between the term's
type and the field's type, which differ only in spelling
(`reindex Dᴰ.Cᴰ (F .fst)` vs `CartesianCategoryⱽ.Cᴰ (CCCⱽReindex .CCⱽ)`).

`UniversalQuantifiers` was a plain `Type _` synonym. Syntactic equality misses, and
`compareAtom` whnfs both sides, **unfolding the synonym** into its Pi-type and
comparing two fully-normalised presheaf/functor towers. Note the Sigma-shaped
`ClosedⱽReindex` in the same file, built from the same call, costs ~0ms -- because
its head does not unfold.

The general shape to look for:

> A large type-level *definition* used as a record-field or Sigma-component type is a
> conversion bomb the moment the supplied term's type is spelled differently from
> the expected one.

The fix is to **make the synonym a record**, so its head never unfolds and the check
degenerates to comparing its (small) arguments -- provided the underlying
`Categoryᴰ`-valued definitions stay stuck, which they do, since `Categoryᴰ` is
`no-eta-equality` and `reindex` is copattern-defined. See intervention `reindexccc`.

Two-minute diagnostic for finding the next instance: hole out one record field at a
time and re-time. If holing a field removes almost all of the module's cost while
that field's term checks fine against its own written signature, it is this bug.

## Mechanism 3 -- untrimmed module copies, paid for in interface generation

For four files in the `LocallySmall` cluster the time is **not type-checking at all**.

| module | Total | DeadCodeReachable | Serialization | Typing |
|---|---|---|---|---|
| `NT/IFC/Base` | 44.3s | 24.8s | 6.4s | 4.8s |
| `Psh/GS/IFC/Properties` | 31.6s | 12.2s | 8.3s | 2.6s |
| `Psh/GS/IFC/Base` | 24.4s | 11.9s | 7.2s | 1.0s |
| `Instances/Sets/Base` | 21.2s | 10.9s | 6.7s | **0.28s** |

`Instances/Sets/Base.agda` is 96 lines of `refl` whose type-checking costs 0.28
seconds and whose interface generation costs 20.

Bisected to one line: adding `module SETᴰ = SmallFibersᴰNotation SETᴰ` moves the file
from 2.76s to 20.5s (DeadCode 0.09->10.1s, Serialization 0.16->7.3s). A bare module
application makes `ApplySection` materialise a copy of every definition in the
section with the argument baked into its type; `DeadCodeReachable` then walks all of
them and `Serialization` writes them. These notation modules nest deeply
(`SmallFibersᴰNotation` -> `CategoryᴰNotation` -> `Categoryᴰ` plus three further
sub-applications), so one line expands to a large transitive closure.

Adding `using (...)` returns it to 2.9s: Agda honours the directive inside
`ApplySection` and never creates the copies.

**Note on where the cost is NOT.** A separate measurement of `Typing.ApplySection`
-- the phase that *creates* the copies -- put it at 0.20-0.26% of a module, and on
that basis this lever was initially written off. That was the wrong bucket.
Creating a copy is cheap; dead-code-analysing and serialising it is not.

Remaining surface: **398 bare notation-module applications outside a
`using`/`hiding`, 314 of them in `LocallySmall`.** The amplifier at source is
`record Functor` in `LocallySmall/Functor/Base.agda`, which embeds two
`CategoryNotation` applications *inside the record body*, so every
`module F = Functor F` anywhere in the library copies them twice. That file also
has `no-eta-equality` commented out, unlike `Category`, `Categoryᴰ` and `Functorᴰ`.

## Mechanism 4 -- GHC's nursery is too small for this workload

Not a property of the library at all, and the cheapest thing on the list.

Agda is linked `-with-rtsopts=-I0 -N1 -qb0` with no `-A`, so the generation-0
allocation area is GHC's 4 MB default. Confirmed by the baseline:
842 GB allocated / 200,573 gen-0 collections = 4.2 MB per collection.

GHC's minor GC is a copying collector: the cost of a collection is proportional to
what is still *live* when it fires, not to the nursery size. The baseline copies
214 GB out of 842 GB allocated -- a **25% nursery survival rate**, where a healthy
figure is low single digits. Agda's workload is why: elaborating a term builds
metas, constraints and intermediate terms that stay reachable for a while, so at
4 MB they are still live when the nursery fills and get copied out.

A larger nursery buys fewer collections and, more importantly, lets more of that
intermediate garbage die before each collection. Cost is resident memory, roughly
the nursery size. Caution: each capability gets its own nursery, so `-A256M -N12`
is ~3 GB of nursery, not 256 MB; the parallel configuration needs separate tuning.

## Mechanism 5 -- nested `reind` makes every equational step geometrically more expensive

This is the mechanism behind the library's use of strict `Eq`, and it was measured late in the
investigation after two earlier readings of the data turned out to be wrong.

### The law

The cost of one `∙`-link in a displayed equational chain is set by the size of the chain's
ENDPOINT terms, and endpoint size is geometric in the reind-nesting depth of those endpoints.
Measured inside four real proofs, with parameter-telescope depth held flat:

    definition                            telescope  endpoint depth   GB per ∙-link
    β-πF*                                     5             1           0.275
    ∀ⱽPsh-introᴰ⁻' .N-homᴰ                   11             2           1.038
    Fᴰ-weakening-NatTransᴰ .N-homᴰ           12             3           2.949
    ∀ⱽPsh-ηᴰ'                                11             3           3.406

Telescope 11 / 12 / 11 across a 3.3x spread, so telescope depth cannot explain it. The ratio is
~3.3 per nesting level. Fitting depth 1 and 2 predicts 3.4 GB/link at depth 3; measured 2.95.

The controlled version, which isolates nesting from every other variable -- the SAME path material,
in one reind versus split across two:

    tripling the stored path inside the single existing reind      +3.40 GB
    the same material as a second nested reind (+ the 2 strip/     +11.52 GB
      re-add links that nesting forces)

3.4x more, on a 44 GB module, purely from nesting identical paths. Directly measured telescope
sensitivity for comparison: ~4% per parameter.

Nesting therefore compounds twice: each extra level multiplies every link's cost by ~3.3, AND
forces two further links (a strip and a re-add) which themselves pay the inflated rate.

### Why two earlier readings were wrong

* "The reinds are not the cost." That came from swapping six `reind-filler refl` links (genuine
  `subst`) for six `reindEq-filler Eq.refl` links (definitionally refl, zero transport ever
  created) and finding 42.359 vs 42.105 GB, 0.6% apart. Correct as far as it goes -- the marginal
  link's OWN transport is irrelevant, and the pure-link slope is linear at 1.0375 GB/link either
  way. But per-link cost is set by endpoint size, and nested reinds are the mechanism by which
  endpoints get big. The control held the endpoints fixed, so it could not have seen the effect.
* "It is parameter-telescope depth." Refuted by the table above: telescope is flat across the
  escalation, and the 6 extra parameters between `β-πF*` and `∀ⱽPsh-introᴰ⁻'` predict +24% at the
  measured 4%/param, against an observed 3.8x.

### What it costs the library

The 437 lines of path-based quantifier proofs restored in `perf-nf-abandoned` cost 187 GB against
a 19.2 GB floor -- 9.7x. Collapsing their nesting to depth 1 projects to ~57 GB (~3.3x);
collapsing one level everywhere, ~85 GB (~2.2x). Honest band: 2-3x, assuming the normal-form
machinery is itself free, which it will not be.

For scale, one proof, `∀ⱽPsh-ηᴰ'`, costs 77.5 GB today and projects to 6.3 GB at depth 1 -- which
is within the range of the strict-`Eq` route's modules (0-7 GB of marginal mathematics apiece
above a ~3.5 GB import floor). That is why this mechanism, and not any of the others documented
here, is the one that forced the `Eq` formulation.

### The countervailing measurement

Converting `reindex`'s hom to the normal form in a private cubical copy (with an opaque path
field, so not the transparent-path pathology) made SHALLOW sites worse, monotonically with the
nesting of the ambient:

    k-fold reindex ambient    baseline    normal form    penalty
    0                           2.05          2.06         +0.5%
    4                           2.23          2.45         +9.9%
    16                          3.86          4.80        +24.4%

because the baseline `reindex` hom is definitionally transparent (`Hom[ G⟪f⟫ ]`), so k nested
reindexes collapse into one hom type with a larger index, while the normal form wraps a record at
every layer. So a global representation change helps deep proofs and hurts shallow ones, and 84%
of surviving reind sites are depth 1 by COUNT -- though that denominator is count-weighted, and
cost is wildly non-uniform (four deep modules are 22% of the build).

### The design constraint, if anyone builds this

The stored path field MUST be opaque. A transparent one is superexponential in chain length: a
three-link associativity chain went 1.90 GB -> over 326 GB, heap exhausted. Making the
`isSet→SquareP` coherence opaque did not help; making the `base` field explicit rather than
implicit did not help (325.97 GB either way -- so the implicit-field question is settled and costs
nothing). Hiding the composite's path behind a one-line `opaque` constant: 326 GB -> 1.94 GB.
