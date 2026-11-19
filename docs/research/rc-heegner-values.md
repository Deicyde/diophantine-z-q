# Heegner values at the selector’s scale

**Scoped stop: the scale matches exactly, but the swap moves the missing
comparison into `CCLGenuine`.** No selector input is discharged. For the
existing `f`, `Lat`, and `κ`, the record
`{ f := f, hf := hf, Lat := Lat, hLat := hLat, hCM := hNC, κ := κ, hκ := hκ }`
has type `CSTParam E`, with `p.f = f`, `p.Lat = Lat`, and `p.κ = κ` by
definition. For `StageKummer` these are the fields of `I : GenusOddInstance W`;
the `Gz34Instance` assembly takes the same inputs explicitly. The bare value
propositions do not carry the four proofs, but their consumers already do.
`curve_scale` only chooses an analytic scale; it need not be invoked or used
to replace the scale already fixed by a consumer. This record comparison is
on-the-spot (c).

## What the cited theorem supplies

The repository’s [primary-source audit](../theorem-application-audit/evidence/parallel-geometry-acceptance-report.md#a034--heegner-norm-relations)
locates Cai–Chen–Liu, *Heegner points on modular curves*, Theorem 2.15, p. 3730.
It gives the conductor-raising degree and the unaveraged Hecke/Frobenius trace
relations on genuine geometric Heegner points of conductor `cm` on `X_K(N)`.
The family is made of CM points over the indicated ring class fields. The
manuscript uses its algebraic image `y_d = π(x_d)` (tex 2915–2923). In the split
case `X_K(N) = X₀(N)`; for each old conductor `d`, take source base conductor
`c = d`, multiplier `m = 1`, and a new prime outside `6dN D_K`. The exclusion
of extra-unit fields gives `u₁ = 1`. The normalized elliptic quotient sends the
Hecke/Frobenius formulas to (4.1), with no cusp correction. This is the use
recorded in `RC/PrintsArith/Heegner.lean:161–177`.

The theorem concerns that geometric family and has no `Lat` or `κ` parameter.
`GenuineHeegnerAnchor` adds the equality of the elliptic image, under the
specified complex embedding, with `phiAn E p.f p.Lat p.κ` at a Heegner root.
`H20Anchor.lean:40–41` calls the analytic parametrization and CM point
dictionary **CONSEQUENCE GLUE**. Field of definition of `y_d` comes from
rational evaluation on the geometric `H_d`-point; the equality to the
selector’s complex value is separate. `IsParamScale` supplies nonzero scale
and a period condition for `Γ₀(N)` invariance, but contains no comparison to
an algebraic quotient. `IsNonCMLattice` alone does not give that comparison
either. An arbitrary supplied `κ` must be matched to the rational quotient
used to push the source relation forward.

## Exact missing comparison

Let `π` be the single normalized rational parametrization used for the
source family `x_d ∈ X₀(N)(H_d)`. Fix `ι : ℚ̄ →ₐ[ℚ] ℂ`, write `ι_d` for
its restriction to the geometric `H_d ⊆ ℚ̄`, and let `Δ_d = D_K d²`. For
each `d > 0` with `Nat.Coprime d (N * |D_K|)`, the geometric-to-analytic
comparison needed to use that family is:

> There are integers `A, B, C` with `IsHeegnerForm N Δ_d A B C` whose root
> `τ_d = cmPoint A B Δ_d` represents `x_d` under `ι_d` in the usual complex
> chart, and `π_ℂ(x_d ⊗_{ι_d} ℂ) = phiAn E f Lat κ τ_d`.

The first clause identifies the same embedded CM point in the chart, with
the prescribed level structure. The second says the rational map used for
all the trace relations has the specified analytic value at those roots.
By base change this gives precisely `ι(π(x_d)) = phiAn E f Lat κ τ_d` in
the anchor, where `π(x_d)` on the left is read in `E(ℚ̄)`. The anchor itself
records only the resulting point equality with an existential form; it
does not expose `x_d`, `π`, or an orientation certificate.

The equality is the **CM-point specialization** of
`AlgebraicParametrizationAtScale` (`RC/PreparedParam/Parametrization.lean:113–119`):
given the same complex chart and the geometric CM point, substitute `τ_d`
in its `∀ τ : UpperHalfPlane` comparison for the same rational morphism.
If the map has yet to be supplied, one must realize a single rational
`π` agreeing at those roots and use it throughout. Existence of some
`π` in `AlgebraicParametrizationAtScale` does not match an independently
chosen `π` to `κ`. This dependency comparison is on-the-spot (c).

With the geometric family and its map supplied, the remaining comparison
is strictly narrower in scope than `X0Model` + `CMFieldOfDefinition X` +
`AlgebraicParametrizationAtScale E X f Lat κ`: it asks for equality on the
chosen CM family, with no construction of the full rational chart, no
descent for every Heegner form, and no comparison at general `τ`. This
compares the required data; it is not a Lean strictness theorem. The **whole**
`CCLGenuine` proposition also asks for norm relations, which are independent
inputs to this comparison and are absent from that three-part package. Even
the narrower comparison still needs the missing fixed-scale theory or a
direct proof at CM points. Treating the anchored proposition as the bare
citation would take that comparison as an extra assumption.

## Consumers and remaining work

No Lean declarations were added, so there are no compile or `#print axioms`
results for this run. `MissingParamValues`, `halgG`, and `halgR` all remain
open; no interface or hypothesis was replaced. The dependencies below are
for this candidate route, not a list of all inputs to the RC proof.

| Dependency | Owner and scope |
| --- | --- |
| Existing `CCLGenuine E K p ι` | Cloud root and source reviewer. The trace portion is supported by the archived primary-source audit; the anchored application is GLUE. The exact separate CM field-of-definition passage remains **UNVERIFIED**. No new print. |
| Same-map CM comparison above | `rc-param-at-scale`, on `rc-x0-model` for the global route. Large missing theory. The CM restriction can be used in place of the all-`τ` comparison if it is proved for the map and points used in the source application. |
| `hf`, `hLat`, `hNC`, `hκ` | Existing curve/newform and lattice wiring supplies the first two; the existing non-CM and scale owners supply `hNC` (algebraic non-CM to lattice multipliers) and `hκ` (the manuscript period/scale input). All four are already consumer inputs, not new hypotheses. |
| Class-field identification for the **same** datum | Cloud field dictionary owner. `H20DictFields.FullAnchor.field` expresses the identification of `D.H d` with `ringClassField (conductorOrder K d)` inside `K̄` after a `ℚ`-algebra equivalence `ℚ̄ ≃ K̄`. `CCLGenuine` itself does not supply it; the existence of an equivalence of closures does not identify subfields. For values alone an equivalence of these fields over `ℚ` suffices; the `relGal` and Frobenius parts of `FullAnchor` are not needed for a value. |
| Form choice and downstream index/reference pins | Root decision on #83. The current genus value uses `formAtLevel`, and `RingParamValue` uses `companionForm`; both pin `A = N` and a particular `B`. The anchor only gives some `IsHeegnerForm`. `HeegnerDatum` accepts any such form, but switching the selected point does not establish `hjg`/`hjr` or the reference-point equality in (O.1). Retain the existing witness and orientation pins. No selector widening or move by Galois conjugation was made. |

After the comparison and field identification, conductor one at
`K = ℚ(√(Dh_*))` would supply a value at the anchor's form for the genus
and Kummer lanes, and `d = |h|` at `K = ℚ(√k')` would supply the analogous
ring value. These are prospective consequences at the anchor forms. The
existing consumer propositions would still require their chosen forms, or
an approved change to accept the anchor's form.

## Known issues

- The audit confirms the location of the trace theorem, not a separate
  `CMFieldOfDefinition` theorem. The pinned offprint is not in this checkout.
  The §2 field-of-definition locator in the prepared-parameter report, and
  its Shimura (1971) Ch. 6 fallback, remain **UNVERIFIED** here.
- `CCLGenuine` is parameterized by a number field `K` and an embedding;
  the manuscript application has an imaginary quadratic field split at
  `2N`, no extra units, and conductors prime to `2N D_K`. These source
  hypotheses are not expressed by the parameter type. The anchor's `d` is
  a conductor; the prepared print's `d` is an order discriminant.
- No manuscript or primary-source error was found in the steps checked.
  The discrepancy is in treating the Lean anchor's analytic comparison
  and abstract field labels as facts furnished by the norm theorem.

## Manuscript check

- 1765–1767 — OK: nonintegral rational `j` rules out CM; `IsNonCMLattice` is the existing lattice translation.
- 1781–1788, 2836–2838 — unverified: the normalized rational quotient is the intended map; equality to `phiAn` at the given `κ` is the scoped stop.
- 2839–2844, 2915–2917 — unverified: geometric CM point and field of definition are the manuscript's inputs; the separate primary field-of-definition passage and the identification of `D.H d` were not verified.
- 2917–2922 — OK: the split-level specialization and the full old conductor match the trace theorem per the archived primary-source audit.
- 2923–2936 — OK: the geometric trace pushes through the normalized quotient, with the inverse Frobenius pair at split primes and no cusp correction, per the archived audit.
- 1974–1975, 2343–2353, 2404–2410, 2428–2431 — OK: the prepared `h` is a unit at primes of `2N` and the companion `k'` a unit at primes of `h`, giving `(|h|, N|k'|) = 1`; the same parametrization is required in both height applications.
- 2411–2416, 8209–8217 — OK: the conductor-one genus family uses discriminant `Dh_*` and the ring companion uses conductor `|h|` in its own field. Exact selector values have not been established.
- 9272–9286 — unverified: the anchor does not identify its existential form with the reference point and orientation used in (O.1).
