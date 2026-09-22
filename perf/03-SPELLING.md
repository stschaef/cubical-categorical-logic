# The spelling anti-pattern

Named publicly by Max New on 2026-09-16
(https://types.pl/@maxsnew/117278320719486320, gist eac6ffc7e1d90fc95cbb283b063e1251),
independently hit twice in this sweep before it had a name.

## The minimal form

```agda
record R : Set where
  field n : Nat
        s : Singleton n

big-boi = 2^ 20

good : R                        -- fast at any size
good .R.n = big-boi
good .R.s = single (good .R.n)

bad : R                         -- slow for large values
bad .R.n = big-boi
bad .R.s = single big-boi
```

`s`'s expected type is `Singleton (bad .R.n)`. In `good` the supplied term's type is
syntactically identical to it, so Agda's syntactic-equality fast path hits and nothing reduces.
In `bad` it is not, so `compareAtom` whnfs both sides and unfolds `2^ 20` into a million-deep
unary tower. Max's framing of where this bites in practice: "the first field is a category and the
second is some construction proving that it has limits."

## The rule, measured

> **Conversion costs you the normalisation of the smallest subterms at which the two terms are
> spelled differently, once for every syntactic occurrence of such a subterm in the fully-unfolded
> expected type.**

Agda compares in three stages (`Conversion.hs:148` `compareAs`): pointer equality; then
`SyntacticEquality.checkSyntacticEquality`, a purely structural traversal with NO reduction and
unlimited fuel by default (`Base.hs:4587`); on a miss, `compareAtom` (`Conversion.hs:575`) which
`reduceB`s BOTH sides before even comparing heads, then recurses into the spine.

Scaling (GHC allocation; floor 2.485 GB, one "unit" of normalising a mis-spelled `2^20` = 5.30 GB):

    2^N     good    bad          clauses         GB      occurrences of n in    synonym   record-wrapped
    14     2.485   2.568         all 5 good    2.489    the expected type (k)
    16     2.485   2.817         1 of 5 bad    7.790         1                 13.121        7.819
    18     2.485   3.811         all 5 bad    28.997         2                 18.423        7.820
    20     2.485   7.787                                     4                 29.027        7.820
                                                             8                 50.236        7.821

Linear in the size of the value, linear in the number of mis-spelled clauses, and linear in the
number of occurrences in the expected type. Good spelling at k=8 is 2.542 GB — 0 units, a 20x
spread. A differently-spelled HEAD is free (one unfold, then arguments match); only a
differently-spelled ARGUMENT costs.

## The copattern corollary

> **`x .g = e` is checked against `G (x .f)` — the PROJECTION.
> `x = record { f = e₁ ; g = e₂ }` checks `e₂` against `G e₁` — THE EXPRESSION YOU WROTE.**

The two styles are not interchangeable for performance. Measured:

    x .R.n = big-boi; x .R.s = single big-boi          7.787 GB
    x = record { n = big-boi ; s = single big-boi }    2.497
    x = record { n = big-boi ; s = single (2^ 20) }    7.799
    mk big-boi (single big-boi), n bound as a Π param  2.498
    opaque                                             2.497
    copattern bad + --lossy-unification                7.840   (no help)

Five fixes, in order of preference: (i) refer through the projection; (ii) write `record{}`;
(iii) bind the big term to a Π/λ parameter so both sides see the same de Bruijn variable;
(iv) `opaque`; (v) orthogonal — make the offending type-level abbreviation a RECORD so its head
cannot unfold, which caps the cost at one unit regardless of how many times the argument occurs.

Why `--lossy-unification` sometimes helps: its first-order shortcut (`Conversion.hs:198`) fires
only when both sides are `Def f es` with the SAME head. It rescues `isFibration X` vs
`isFibration Y` (FixedPoint) and does nothing when the heads differ at the point of divergence
(the gist).

## Refinement: the shape is necessary but NOT sufficient

All four sites below have Max's "category + proof it has limits" shape. Only one is expensive.

    site                                    record                        GB before -> after
    reindexGuardedLogic (FixedPoint)        GuardedLogic (eta)            17.375 -> 7.363   2.36x
    CCCⱽReindex (Reindex/CartesianClosed)   CartesianClosedCategoryⱽ      13.037 -> 12.166  1.07x
    reindex (Reindex/Limits)                CartesianCategoryⱽ             6.937 ->  6.931  none
    CartesianPropertyOver                   CartesianCategoryᴰ             8.996 ->  8.994  none

The extra ingredient is that the RHS's inferred type must be **fully pinned**. FixedPoint's
`isFibrationReindex {ℓC = ℓC}…{D = D} Dᴰ.Cᴰ F Dᴰ.isFibCᴰ` infers `isFibration (reindex Dᴰ.Cᴰ F)`,
forcing a conversion check against `isFibration (reindexGuardedLogic .Cᴰ)`. Where the author wrote
`_` instead (Reindex/Limits: `isFibrationReindex _ Dᴰ.cartesianLifts`), the metavariable absorbs
the difference and it is free.

**Screening rule.** Do not grep every record. Grep for copattern bodies containing a hand-written
self-projection (`f args .earlierField`) or hand-supplied implicits — those are the author's own
workaround markers, i.e. places where someone already fought this. `Presheaf/Eq/CartesianClosed.agda:123`
(`PSHᴰ∀ P Qᴰ .fst` inside its own `.snd` clause) is the clearest unexamined instance.
A purely textual detector over all 472 files gave 1479 raw candidates / 448 / 236 after filtering
and was USELESS: it flagged FixedPoint for the wrong clause, because the real mismatch arrives
through an implicit argument with no textual duplication at all. The detector that works is
`--profile=definitions`: if the top entry is a value defined in this module and is >= ~40% of the
module total, suspect this bug.

## Scope: concentrated, not diffuse

1472 copattern clauses across 235 of 472 files. Demonstrably this mechanism: `Presented` (9.3% of
the build) + `FixedPoint` (3.3%) = ~12.6% in two modules. Plausibly, untested: `Reindex/Exponential`,
`Presheaf/Eq/CartesianClosed`, `TotalCategory/Monoidal`, `Instances/Functors/More`, ~3.3% more.
The other ~1460 clauses are worth 0-1%: the trap needs all three of (a) two spellings several
reduction steps apart, (b) a subterm with a large normal form, (c) a field type that is an
unfolding abbreviation repeating that subterm. Most `Category`/`Categoryᴰ`/`Functor` instances fail
(c) — `⋆IdLᴰ`'s type is a single small Hom-path, so the multiplier is ~1.
Two attempted fixes made things WORSE and were reverted (`Reindex/Monoidal` 6.047 -> 6.722;
`Instances/Functor/Base` 1.2%, not worth it).

## `{-# INLINE #-}` on record constructors: an exact no-op

Suggested in the thread by Amy (1lab) as a way to get record-expression checking while keeping
copattern syntax. It does not do that. Measured on FixedPoint: baseline 17.375, + INLINE 17.375,
+ no-eta 17.375 — byte-identical; the rewrite 7.363.

From the Agda 2.9.0 source: `Rules/Decl.hs:842-848` `{-# INLINE c #-}` only sets `conInline`;
`Rules/Def.hs:365` -> `RecordPatterns.hs:249 recordRHSToCopatterns` runs AFTER the clause is
checked and only fires on a saturated constructor application. So it cannot change how anything is
CHECKED. Amy's tip is really "write the RHS as a constructor application"; the pragma just buys
back the lazy compilation you would otherwise lose. Its one unique contribution —
`RecordPatterns.hs:321 recordExpressionsToCopatterns` already does this for eta records, so INLINE
adds it for NO-ETA records — measured 12.166 -> 12.183 GB on `CCCⱽReindex`, i.e. nothing.
It needs neither `no-eta-equality` nor a named constructor, and chaining it between a function's
signature and body does work; `InlineNoExactSplit` is not on by default. None of that helps here.

## The principle this is all an instance of

Amy (1lab), same thread:

> "you want to make enabling lossy-unification (the performance roulette!) a no-op, by making
>  things sufficiently rigid where they should be, instead of praying that conversion checking
>  *happens* to spot two applications of a very large flabby thing before they unfold."

Definitionally injective, per her: records; definitions by copattern matching in NO-ETA records;
opaque definitions; constructor-headed definitions; definitions by pattern matching where the
blocking argument is neutral. Every source-level win on this branch is an instance:
`UniversalQuantifiers` synonym -> record (2.3x); `elim` kept stuck via copatterns (Presented, 24x);
the coherence path split out and made opaque (Reindex/Eq/Base, 24x); the record expression
(FixedPoint, 2.4x).

Corollary that holds, measured: with the definition rigid, explicit implicits become unnecessary.
Dropping all six from `isFibrationReindex` costs 7.363 -> 7.364 GB in the record-expression form
(exactly free) and 17.375 -> 18.524 (+6.6%) in the copattern form. So the answer to "the fast
spelling is artificial looking code" is not to write the self-projection — it is to make the
definition rigid and then write `_`.
