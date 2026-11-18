# Wild inertia from Silverberg–Zarhin Theorem 3.3

The uncited step at manuscript L817–818 is discharged in Lean and folded out of
`ZInQ.OneProof.frozenTarget`. Its replacement is
`SZRaynaud.SilverbergZarhinThm33`, from the paper already cited at L816.
The old hypothesis follows from the forward implication and the proved
`WildPeriodCoprime`. The folded theorem builds. The new leaf is pending review,
so the strict and strictest GLUE counts are unchanged.

## Print and Lean statement

A. Silverberg and Yu. G. Zarhin, *Semistable reduction and torsion subgroups of
abelian varieties*, Annales de l'Institut Fourier 45 (1995), 403–420, Theorem 3.3,
p. 405, Galois criterion of semistable reduction (attributed to Grothendieck).
The statement was read by AI from the printed page image on 11-17. It says:
let `A/F` be an abelian variety, `v` a discrete valuation on `F`, `L/F`
Galois, and `w` an extension of `v` to `L` at which `A` has semistable
reduction. For a prime `ℓ` different from the residue characteristic of `v`,
put `V = V_ℓ(A)`, `I = I(w/v)`, and `W = V^I`. Semistability at `v`
is equivalent to triviality of the action of `I` on `V/W`.

**Proposed rating: printed form for the separable closure case under the
reading below; published, provenance (b), pending review.** The Lean statement
retains the general discretely valued base, both directions, and the rational
Tate space. It specializes the Galois extension to the separable closure, the
case used by the authors, and carries the upper semistability premise explicitly:
`A` must be semistable at the restriction of `w` to some finite separable
subextension, possibly `F` itself. The disjunct for `F` gives the same case without
building a base change along the identity. Here semistability throughout is
`HasSemistableReductionSZ`, the Néron identity component over the residue field
as an extension of an abelian variety by a torus (Definition 3.1(ii), p. 405).

The action is written as
`τ(σ x − x) = σ x − x` for every pair `σ, τ ∈ I` and every `x ∈ V`.
This is the fixed subspace condition: each `σ x − x` must belong to `W`.
`VΩ` and `galVΩ` are the chosen closure versions of the existing
`PkgI3.AbVar.V` and its Galois action; both use scalar extension of the
integral Tate module. In positive characteristic, restriction from the
algebraic to the separable closure identifies the automorphism and inertia
groups: the remaining purely inseparable extension extends the valuation
uniquely and the residue field purely inseparably. Since `ℓ` is invertible
in the valuation ring, multiplication by `ℓ^n` is étale on the generic
abelian variety; its geometric kernel points are already in the separable
closure. These are the conventions identifying the objects in the leaf.
The Lean application itself is over number fields.

## Lean glue

- `SZRaynaud.tate_tmul_injective` (private):
  for any prime `ℓ` and additive abelian group `M`,
  `t ↦ 1 ⊗ t : T_ℓ(M) → ℚ_ℓ ⊗[ℤ_ℓ] T_ℓ(M)` is injective.
- `SZRaynaud.elliot_of_sz33 : SilverbergZarhinThm33 → ElliotWildInertiaTrivial`.

**ON THE SPOT (provenance (c)).** For injectivity, a tensor mapping to zero
is killed on the Tate lattice by a nonzero scalar in `ℤ_ℓ`. Cancel its
unit factor; if `ℓ^k` kills the sequence, apply the transition equations
from level `n+k` to level `n` to show every coordinate vanishes.
In the new leaf choose the base as the upper semistability witness and take
`τ = σ`. The tensor inclusion transfers the square-zero identity from
`V_ℓ` to `T_ℓ`. Now `unipSq_of_tate` projects to level `n`;
`wildPeriodCoprime_proof` gives that point a period prime to `ℓ^n`.
`PkgI2.fixed_of_unipSq_of_iterate` makes the point fixed, and the coordinate
equalities give the equality on the inverse limit. The period argument is
also on the spot; its proof and valuation sketch are in
[`elliot-wild.md`](elliot-wild.md). No step through the kernel's other
semistability predicate is needed.

## Fold

`scratch/elliot-wild2/autofold.json` replaces
`research/elliotWildInertiaTrivial` by `research/silverbergZarhinThm33`.
The dry run generated `TailZ90.lean`, and the live fold uses its two theorems:

```lean
theorem HDec.HSyn.openResearchLeaves63_of_OpenResearchLeaves64
    (n : HDec.HSyn.OpenResearchLeaves64) : HDec.HSyn.OpenResearchLeaves63
theorem HDec.HSyn.sixContactMin_of_open83
    (r : HDec.HSyn.OpenResearchLeaves64) (t : HDec.HSyn.OpenTextbookLeaves18)
    (l : HDec.HSyn.OpenAddedLeaves28) : ZInQ.SixContactMin
```

The new `frozenTarget` uses `OpenResearchLeaves64` and keeps its
`OpenTextbookLeaves18`, `OpenAddedLeaves28` and `ZInQ.PoleCompleteness`
parameters and its result `ZInQ.FrozenTarget`.

| Scope | Before: strict / strictest GLUE | Fold with pending review | If rated printed form in both columns |
| --- | ---: | ---: | ---: |
| H (33 hypotheses) | 28 / 28 | 28 / 28 | 27 / 27 |
| `frozenTarget`, with pole completeness (34 hypotheses) | 29 / 29 | 29 / 29 | 28 / 28 |

## Checks and touched files

- The real contribution built with Lake. Before the fold, `#discharges` matched
  `OpenResearchLeaves63.elliotWildInertiaTrivial` by `elliot_of_sz33` and
  listed only `SZRaynaud.SilverbergZarhinThm33` as still assumed.
- The baseline and folded `OneProof.Main` built with Lake. The folded
  `frozenTarget`, both fold theorems, and both contribution theorems have only
  `propext`, `Classical.choice`, and `Quot.sound`. The hash guard found 38
  additions and no removals; the only existing declaration with a changed
  hash was `ZInQ.OneProof.frozenTarget`.
- The open statements were regenerated from Lean, and
  `render_open.py --check` passed. The results are in
  `scratch/elliot-wild2/log.md`.

The fold changes `ZInQKernel/OneProof/Main.lean` to use the new bundle and
updates `docs/one-proof/kinds.tsv`, `credits.tsv` and `reviews.tsv`.
It regenerates `docs/one-proof/open-statements.json`, `OPEN.md`,
`pages-wanted.md`, the worked example in `CONTRIBUTING.md` and its
`scratch/contrib-kit/DischargesTest-output.txt`, and the count in
`STATUS.md`. The leaf's source entry is added to
`docs/research/locators.md`. No manuscript or existing proof body was edited.

## Known issues

Definition 3.1 defines semistability at a discrete valuation, whereas the
displayed action of `I(w/v)` on the whole rational Tate module only
descends to `L` when `L` contains the `ℓ`-power torsion. In general this
requires an infinite extension and the valuation of `L) need not be discrete.
The authors themselves apply the criterion at the separable closure in the
proof of Lemma 5.5 (p. 411) and the proof of Proposition 6.1 (pp. 412–413),
as recorded in the supplied reading. These uses motivate interpreting the
hypothesis at a finite stage. In an application from a semistable base, the
base is that stage. This convention makes no assertion about semistability
at a nondiscrete valuation. It is the interpretation to review;
the project does not invoke a semistable reduction theorem or Néron model
base change to produce the witness.

The apparent strict lower bound in the OCR of Theorem 3.5 is a known OCR
issue; the earlier page reading confirms `n ≥ 3` (see
`scratch/sz-raynaud/sz-thm35-reading.md`).

## Manuscript check

| Tex lines | Step | Verdict |
| --- | --- | --- |
| L814–815 | Adjoin `A[3]`, or `A[5]` at `p = 3`. | **OK.** Full torsion of the chosen order becomes rational; the order is at least 3 and a unit at the place. |
| L815 (L391 and L579) | Bound the enlarged local degree by `DG_0`. | **OK.** Conditional on the earlier bound `[L:ℚ] ≤ D`, the local degree of `L_v` is at most `D`. The torsion degree divides `#GL₄(𝔽_m)`, which is 24,261,120 for `m=3` and 116,064,000,000 for `m=5`. |
| L816–817 (L11077–11080) | Cite Theorem 3.5 for semistability over the enlarged field. | **OK.** Theorem 3.5 in the cited paper applies with the unramified extension trivial because all the torsion is now rational. The existing `SilverbergZarhinThm35` is unchanged. |
| L817–818 | Wild inertia acts trivially on each `V_ℓ` for `ℓ ≠ p`. | **gap filled.** The sentence had no citation. Theorem 3.3 of the paper already cited at L816 supplies square zero; the proved prime-to-ℓ period argument yields triviality on the Tate lattice, hence on its rational scalar extension. |
