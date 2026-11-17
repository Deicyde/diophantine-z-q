# H102 historical first-pass provider checkpoint

> This document records only the first frozen provider build at `bf6da311`.
> Later API and namespace ports supersede its failure inventory; those counts
> are not the current build status and do not establish mathematical absence.
> This is not a final gap report or an acceptance verdict. Consult the later
> `VERIFICATION_ROUND*_PRIMARY.md` records for the completed port stages.
> The final theorem is claimed only after its own exact kernel/discharge checks.

**Not discharged at this historical checkpoint.** `mumfordTorsionAlgClosed_proof : AvSplit.MumfordTorsionAlgClosed`
is an exact-type source draft with no additional argument, but its complete
geometric provider does not compile on the fixed pins. No final `#discharges`
or final-leaf axiom verdict is claimed, and no PR is ready.

## Mathematically meaningful remaining obligation

The missing usable kernel theorem is the *proved degree formula*, not merely
finiteness of multiplication:

```lean
GoodReductionJacobian.RelativeGroupLaw.endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero
  (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}}
  (f : A ⟶ Spec (CommRingCat.of K))
  (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
  (hA : AbelianSchemePropertyBundle K f)
  (g : ℕ) [SmoothOfRelativeDimension g f]
  (n : ℕ) (hn : (n : K) ≠ 0) :
  L.endDegree (L.nsmul f n RelativeGroupLaw.idPoint) = n ^ (2 * g)
```

The immutable FLT source contains a complete proof of this statement through
symmetric ample modules, the theorem of the cube, Picard/relative-line-bundle
constructions and the Euler-characteristic polynomial. Its dependency cone also
includes the residue/Riemann–Roch developments. That proof is **not yet a compiled
provider** at Lean4.35/Mathlib56a00585. The finite-étale kernel-count edge and the
all-divisor finite-group classification are separately verified, so after this
actual degree/cardinality provider is usable, the exact final-edge source needs
only ordinary compilation and independent newest-Main discharge verification.
No hypothetical `hDegree` is substituted for the missing compiled theorem.

## Useful compiled deliverables

- NativeBridges: original torsion-to-additive-subgroup equivalence and original
  product dictionary; prime-to-characteristic multiplication étale (from the
  existing closed H101 theorem), finite, and original torsion-set finiteness.
- All 25 pinned source geometry prerequisites; RelativeBridges retains original
  `A.X` and `A.grp`, derives the honest source property bundle, converts the exact
  original Krull dimension into SmoothOfRelativeDimension g, and identifies the
  original torsion with relative-law points preserving original multiplication
  and powers. Six exported bridge/definition axiom checks and the generic helper
  give precisely propext, Classical.choice, Quot.sound.
- Shared height/quotient-dimension and regular-local depth source proofs compile
  with exact AX3 checks; shared regular-stalk carrier compiles with all its original
  axiom guards.
- Independent finite-group helper 7b22028e is integrated unchanged (exact arbitrary-r,
  all-divisor cardinality-to-ZMod-power theorem, AX3).
- Independent finite-étale kernel-count cone compiles unchanged/AX3; independent
  22-file flatness cone plus quotient helper compiles/AX3; verified same-team source
  changes are integrated unchanged.

Detailed actual outputs are in VERIFICATION_NATIVE.md, VERIFICATION_CORE.md and
VERIFICATION_RELATIVE.md. Other worker evidence is preserved in its own source
families. These are prerequisite proofs, not a Mumford discharge.

## Complete provider build: actual terminal result

The frozen bf6da311a45c3cfed8969921c447427535dad7e1 provider snapshot was compiled
as a bounded direct DAG on the dedicated host with at most three Lean processes,
LEAN_NUM_THREADS=4, -M16000, and the required available-memory checks.

```
Inventoried provider graph 1332 cached 14
Provider roots: {'ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero': 'blocked'}
Totals: {'cached': 14, 'failed': 124, 'blocked': 860, 'ok': 334}
[exit code: 1]
```

Thus 334 modules newly compiled and 14 valid cached modules were available, but
124 failed and 860 were blocked. Failure ownership: **120 primary**, 3 RR55
(obsolete source snapshot; the newer verified a8726b2 delta is available), and
1 giant-owned module. No delegated source is edited by the primary after its
ownership transfer.

Primary failures include old Aut/End APIs, inlined local shorthand scopes,
PresheafOfModules tensor-map API names, ordinary exports resolving as self-exports,
premature local namespace opens, and local-instance inference. They are a
substantial unresolved source/pin port, not a reason to weaken the target.

`bulk-results.json` and `bulk-failure-summary.json` preserve every status, owner,
first diagnostic and raw log path. The output/evidence archive preserves all raw
per-module logs. No count or negative absence claim is based on relevance search.

## Source/push hygiene

The source target and all original repository modules/pins/configuration remain
unchanged. All contributed Lean files are new relative to the original baseline;
full credits/notices/licenses are retained. No new sorry/axiom, runtime code,
syntax, notation, macro or elaborator is used. The contribution does not import
OneProof.Main. Only cloud-b3/w16-h102 is pushed, with an explicit refspec; no main,
issue, PR, human outreach or merge action is taken. The parent owns any later PR
and independent final review after the full proof is green.
