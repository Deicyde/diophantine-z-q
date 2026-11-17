# semistab-assembly: the semistability clause of `bostLowerBoundAn` and `gaudronRemondThm14An`

**Result.** Under the geometric reading and the `k(s)` reading, semistability is no longer a Lean step for the two
height rows. `ZInQKernel/Contrib/OneProof/SemistablePrintedReadings.lean` (namespace `ZInQ.SemistabAssembly`, no
`sorry`) proves that the leaves' semistability clause `ZInQ.HeightFix.IsSemistableRes 𝒩` implies the print's
"the identity component of the special fibre is semi-abelian" in both readings:

* **(1) geometric reading**: `isSemistableGeomPrinted_of_res` (one lemma). At every maximal `𝔭`, the identity
  component of `𝒩 ×_{𝓞_L} κ̄(𝔭)` is an extension of an abelian variety by a split torus.
* **(2) `k(s)` reading**: `isSemistableResPrinted_of_res`. At every maximal `𝔭`, the identity component of
  `𝒩 ×_{𝓞_L} k(𝔭)` is an extension of an abelian variety over `k(𝔭)` by a torus (split over `κ̄(𝔭)`).
* **(3) bridges to the rows**: the leaves restated over the printed semistability, with both readings assumed
  at once so that each is a consequence of the print under either reading (`BostLowerBoundAnSS`,
  `GaudronRemondThm14AnSS`). The two fields follow from them: `bostLowerBoundAn_of_ss : BostLowerBoundAnSS →
  ZInQ.R3Residual.BostLowerBoundAn` and `gaudronRemondThm14An_of_ss`.

The third reading (SGA 7 IX 2.1.5 / 3.4 read as "`(G⁰)_{k̄}` contains no `𝔾_a`") needs rigidity of tori. That is
not in Lean and is the separate task ga-rigidity; it remains open. No field of `frozenTarget` changes.

## 1. What was missing (VERIFIED, read in the tree)

`IsSemistableRes 𝒩` (PrintedStableHeight.lean:578) unfolds to `HasSemiAbelianIdCompTorus (resFibre 𝒩 𝔭)`
(RaynaudSemistableOr.lean:144). Like `HasSemiAbelianIdentityComponent` (TailY.lean:76), it asserts only that
some **open connected** subgroup `U` exists. It never says that `U` is the identity component `G⁰`, which is what
the print says. The clause sits in hypothesis position (`∀ x, IsAnStableHeight A x → …`), so Lean's clause must
imply the print's. The missing step is that `U` is closed: then `U` is clopen, connected and contains the unit,
so `U = G⁰`.

## 2. Lean (all VERIFIED: compiled with `lake env lean`; axioms in §4)

| declaration | statement |
| --- | --- |
| `isClosed_range_openSubgroup_field` | an open subgroup scheme (`IsOpenImmersion`, `IsMonHom`) of a group scheme locally of finite type over **any** field is closed |
| `range_eq_connectedComponent` | an open connected subgroup has image `connectedComponent e` |
| `HasSemiAbelianG0`, `HasSemiAbelianG0Torus` | the printed forms: `HasSemiAbelianIdentityComponent` / `HasSemiAbelianIdCompTorus` verbatim, with "`U` connected" replaced by "`range U = connectedComponent e`" (i.e. `U ≅ G⁰`) |
| `hasSemiAbelianG0_of`, `hasSemiAbelianG0Torus_of` | the connected forms give the `G⁰` forms (any field, locally of finite type) |
| `IsSemistableGeomPrinted`, `IsSemistableResPrinted`, `IsSemistablePrinted` | semistable reduction as printed, read over `κ̄(𝔭)`, over `k(𝔭)`, and both |
| `isSemistableGeomPrinted_of_res` | (1) |
| `isSemistableResPrinted_of_res` | (2) |
| `isSemistablePrinted_of_res`, `isAnStableHeightSS_of` | (3): `IsAnStableHeight A x → IsAnStableHeightSS A x` |
| `BostLowerBoundAnSS`, `GaudronRemondThm14AnSS` | the new leaves: `BostLowerBoundAn` / `GaudronRemondThm14An` verbatim over `IsAnStableHeightSS` (`IsSemistableRes` replaced by `IsSemistablePrinted`) |
| `bostLowerBoundAn_of_ss`, `gaudronRemondThm14An_of_ss` | the fields from the new leaves |

**Proof of closedness over an arbitrary field.** Let `p : G_{k̄} → G` be the projection and `U_{k̄}` the base change
of `U`. `U_{k̄}` is an open subgroup of `G_{k̄}`, so it is closed by semiab-descend's `isClosed_range_openSubgroup`
(this needs `k̄` algebraically closed). `U_{k̄} = p⁻¹(U)` because the square is a pullback. `Spec k̄ → Spec k` is
integral (Mathlib `IsIntegralHom.SpecMap_iff`), so `p` is integral as a base change, hence universally closed. It
is also surjective (a base change of a surjection). So `U = p(p⁻¹ U)` is closed. This uses the closedness of `p`
rather than the openness the brief suggested: same conclusion, fewer inputs.

**Geometric reading.** `isSemistable_of_res` (PrintedStableHeight.lean:590), with `hGC := geomConnOfRationalPoint_proof`,
gives `HasSemiAbelianIdentityComponent (geomFibre 𝒩 𝔭)`. Then `hasSemiAbelianG0_of` applies over `κ̄(𝔭)`.

## 3. The new leaves, rated

* `bostLowerBoundAnSS`: **not the printed form; a consequence, GLUE**. Its semistability clause is now the print's
  under the geometric and the `k(s)` readings. Assuming both at once makes the leaf weaker than the print under
  either reading. Two things stay open, so it is GLUE like the row it replaces (count-neutral): R3' (étale
  coordinates are holomorphic charts, inside `IsAnMetricSq`; a separate worker) is still a step, and the
  2.1.5/no-`𝔾_a` reading is not covered. The Bost display remains UNVERIFIED.
* `gaudronRemondThm14AnSS`: the same rating and the same reasons. Gaudron–Rémond Thm 1.4 was read by the locator
  audit.

**Flag text for the two rows (semistability):**
"pending review: semistability clause now printed form under the geometric and k(s) readings (semistab-assembly:
IsSemistableRes ⇒ G⁰ semi-abelian over k(𝔭) and over k(𝔭)bar, proved); the SGA 7 IX 2.1.5 reading (no G_a in
(G⁰)_kbar) remains (task ga-rigidity); R3' remains a step."

**What remains, per row.**
* `bostLowerBoundAn`: R3'; the no-`𝔾_a` reading of semistability (ga-rigidity); the Bost display (UNVERIFIED).
* `gaudronRemondThm14An`: R3'; the no-`𝔾_a` reading (ga-rigidity).

Autofold spec: `scratch/semistab-assembly/autofold.json`. It discharges both fields with the new leaves (kind
consequence, flag_class `pending-review,unverified-locator`) and is count-neutral.

## 4. Checks (VERIFIED)

* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.SemistablePrintedReadings`:
  build completed successfully (16094 jobs).
* `#discharges` (`scratch/semistab-assembly/Discharges.lean`, output `discharges-output.txt`):

```
DISCHARGES [OpenResearchLeaves45.bostLowerBoundAn] by ZInQ.SemistabAssembly.bostLowerBoundAn_of_ss
  still assumes: [ZInQ.SemistabAssembly.BostLowerBoundAnSS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves45.gaudronRemondThm14An] by ZInQ.SemistabAssembly.gaudronRemondThm14An_of_ss
  still assumes: [ZInQ.SemistabAssembly.GaudronRemondThm14AnSS]
  axioms: [propext, Classical.choice, Quot.sound]
```

* `#print axioms` for `isClosed_range_openSubgroup_field`, `isSemistableGeomPrinted_of_res`, and
  `isSemistableResPrinted_of_res`: standard axioms only.
* `autofold.py … --dry-run`: exit 0. GLUE counts are unchanged: strict 5/29 → 5/29, strictest 5/29 → 5/29.
