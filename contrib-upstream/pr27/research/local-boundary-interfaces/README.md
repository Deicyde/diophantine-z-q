# Local conjugation and boundary interfaces

This package proves three conditional interfaces used in the derivative-switch
argument: a shared local conjugation unit and its descent to Mathlib's H¹;
the explicit cup coboundary removed by a chain trace; and a cone comparison
whose supplied right homotopy inverse preserves global and localized homology.
It does **not** prove that every required arithmetic instance supplies these
data, or prove the determinant switch or main Diophantine theorem.

## Start here

- Mathematical claims and manuscript consumers: [APPLICATION.md](APPLICATION.md).
- Exact four-module selection: [ORIGIN.json](ORIGIN.json).
- Explicit proof roots and printed definitions: [TARGETS.json](TARGETS.json).
- Reproduction, evidence and remaining checks: [VERIFICATION.md](VERIFICATION.md).
- Review findings: [FINDINGS.md](FINDINGS.md); nonauthor reports in [reviews/](reviews/).
- Proposed PR text: [PR_DESCRIPTION.md](PR_DESCRIPTION.md).

This is the specification and reader entry point for an additive, non-release
submission on upstream V13. It selects the existing bytes of four modules from
`33483f751e6dcd3f91fb303969838aca33ad0458`; no proof repair or statement change
is part of extraction. Source headers referring to older companion research
directories describe that source revision. This package's application note
supplies the compact, current map; those historical directories are not build
dependencies and are not copied into this submission.

## Frozen mathematical specification

**Local transport.** For a commutative ring R, a representation T of a group G,
a normal subgroup H, and a character α into R×, `LocalData` records the explicit
group and representation relations, including φ = dτ, τ² = 1,
T(φ) = T(τ), f = φ², φsφ⁻¹ = s^ℓ, and trivial local actions.
The common unit is **derived** as u = α(d)⁻¹. Every crossed cocycle has raw
conjugate coordinates (u f, u ℓ s). When (ℓ : R) = −1, these are (u f, −u s).
Evaluation and pullback descend to the actual Mathlib `groupCohomology.H1`.
The conjugate representation is the pulled-back representation; it is not
identified with the original one.

The minus-one specialization is intended for finite coefficient stages.
For a fixed natural ℓ it has no characteristic-zero instance. No map from a
finite Artin ring to a characteristic-zero field, passage through the retained
inner limit, or global character compatibility is proved here. The general
formula retaining ℓ holds over any commutative ring with the stated data.

**Boundary cup.** `LocalCupData` contains bilinear cup maps and the two
degreewise Leibniz identities. Given a closed l and the cycle relation
`inc u = loc g + d q`, the proved correction is

```math
l\cup\operatorname{inc}u
=l\cup\operatorname{loc}g-d(l\cup q).
```

A linear trace annihilating that differential removes the correction. The
same assumptions give invariance under boundary changes in either slot.
This is a deduction from Leibniz and a cycle equation, not an assumed
boundary-duality adjunction. It does not construct the arithmetic cup,
compact-support trace, global trace square or stored paired functionals.

**Comparison.** With H22 differential
`(d g, d u, loc g − inc u − d q)`, the map
`j(g,u,q) = (g,a u,q+h u)` commutes with the differential provided a is a
chain map in the relevant degrees and `inc − inc' a = d h + h d`.
Separately, for genuine Mathlib homological complexes, if `j ≫ q = p` and a
supplied k satisfies `k ≫ j` homotopic to the identity, then `k ≫ p` and q
induce equal homology maps, as do their composites with any localization
chain map. No existence of k is concluded.

The boundary-cup module uses third differential `−loc g + inc u − d q`.
Its local q-coordinate is the **negative** of H22's. The theorem
`fibreComparison_sign_change` records this conversion. Omitting it changes
the sign of the representative correction.

## Scope and trust

The selection contains 41 audited proof roots (including two homotopy-valued
definitions), rather than the frozen foundation's 39 targets. The packages
are disjoint: these modules import Mathlib and, in the H¹ companion, the
selected local transport module. The existing default `lake build` target
does not select them; use the dedicated runner below.

The evidence is native Lean 4.35.0 checking of fresh project artifacts with
kernel checking enabled and transitive axiom collection. Allowed axioms are
`propext`, `Quot.sound`, and `Classical.choice`. Pinned dependency caches and
the Lean standard library remain trusted imports. No paranoid run, independent
kernel replay or six-checker pass is claimed for this package. The finite
controls diagnose invalid shortcuts; they do not prove an arithmetic instance.
Model reviews are separately authored but share model/toolchain limitations.

From a checkout with the unchanged pinned dependencies and their compiled
caches available:

```sh
python3 -B research/local-boundary-interfaces/verify_native.py lean/.checks/local-boundary-fresh
python3 -B research/local-boundary-interfaces/check_controls.py
python3 -B scripts/check_audit_history.py --self-test
```

The output directory must be new. The runner supplies an explicit `LEAN_PATH`
containing its new output and dependency caches only; it unsets `LEAN_SRC_PATH`.
It checks source blob/SHA identities, dependency revisions and clean tracked
dependency sources, emits exact commands and elaborated statements, and rejects
unlisted transitive axioms. Dependency source cleanliness does not authenticate
the imported binary caches. See the verification record for cache provenance.

## Attribution and change boundary

Chey Loveday directed the research and preparation. The selected modules and
earlier source application notes were developed with Codex agents on the named
research commit; this preparation adapts their verification runners and retains
their exact mathematical source bytes. The manuscript is Elliot Glazer's V13;
Mathlib supplies the group-cohomology and homological-complex infrastructure.
The ordinary source comparisons refer to Jan Nekovář's published *Selmer
complexes*, Astérisque 310 (2006). Exact locators and provenance are in the
application and origin records. No new-discovery or specialist-acceptance
claim follows from model authorship or review.

This is not a manuscript edition or research release. The canonical manuscript,
PDFs, construction artifacts, catalogs, existing acceptance records, release
handoffs, mirrors, foundation PR #15 and frozen 39-target inputs are unchanged;
their publication-regeneration and release-synchronization duties do not apply
to these additions. Hosted checks on an eventual PR remain separate. The raw
source archive, parked four-term proposal and wider research bank are excluded;
their completion is not a merge gate for this package.
