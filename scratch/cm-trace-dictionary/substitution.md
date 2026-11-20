# Substitution dry run

**Pole (Lean; starts after the comparison).** The trace constructor takes an
actual `y : E(H)`, with `H = hilbertClassField K`. It forms the unaveraged
Galois sum and produces the unique `P : E(K)` mapping to it. The separate
class-group calculation reindexes the same sum by `hilbertClassArtinEquiv`.
With the existing form, non-CM lattice, rational scale, and the image
equation for this `y`, the result packages directly into
`HKRefereed.IsHeegnerTrace`. Neither the class-group identity nor this
packaging proves the image equation. The assembly dry run calls
`HKGZ.hkConsumed_of_grossZagier` with the exact original
`HKGZ.PoleCMTraceDictionary` and the separate
`HKGZ.HeegnerTraceConjugationDraft`. There is still no producer for the
former. No headline import or patch is needed to see the boundary.

**Forward rank (source dry run; only the algebraic trace step is in Lean).**
The required output of `CloudB3RC53.Prints.kolyvagin` is the existing
`KolyvaginThm1Printed`: for arbitrary modular elliptic `E/ℚ` and
`r ≤ 1` with `AnalyticRank E r`, give rank `r` and `Finite (sha E)`.
Unfolding the proposed replacement gives these steps:

| Input at the old call | Rank zero | Rank one |
| --- | --- | --- |
| Auxiliary field | BFH(i): choose a negative split discriminant with a simple zero on the twist. | BFH(ii): choose a negative split discriminant with a nonzero central twist value. |
| Derivative over the selected field | `L(E,1) L′(E^D,1)` (uncompiled rank-zero specialization). | `L′(E,1) L(E^D,1)` (base Lean theorem). |
| Trace input | Need the actual CM image on `E(H)`; the checked sum and descent work for this `E` without a non-CM hypothesis. | Same. |
| Arithmetic over the field | Need the compatible Gross–Zagier non-torsion consequence and the printed rank-one and whole-Sha consequence evaluated at that trace. | Same. |
| Output read by consumer | Sign `w(E) = +1`: trace contributes to the minus eigenspace. Show plus rank zero; restrict full Sha. | Sign `w(E) = -1`: trace contributes to the plus eigenspace. Show plus rank one; restrict full Sha. |

No Gross–Zagier instance is inferred from the trace operation. The base's height and
sign drafts take `HKRefereed.IsHeegnerTrace`, so generalizing only the
sum/descender does not give them inputs on CM target curves. The pole
conjugation draft also has the wrong sign scope for the rank-zero column.
The consumer `forwardRank_zero_of_prints` calls the rank-zero column on
`E` with no restriction on CM, model, or twist. Given the required pair,
its existing Kummer call type remains unchanged. The signed-calibration
adapter needs the rank/Sha pair from *both* columns.

Both substitutions preserve the existing theorem types. Neither supplies a
new hypothesis provider.
