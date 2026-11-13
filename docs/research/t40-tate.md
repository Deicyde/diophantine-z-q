# t40-tate: the Tate-curve input of T40 (`TateCuspLaurent`) is proved

Task t40-tate, 2026-11-13. Branch `wip/t40-tate` (base fork main 57a7fa26, fork main 54cc2893
merged). Results log `scratch/t40-tate/log.md`.

Marks: **VERIFIED** = compiled, or read in the source; **STANDARD** = published, with reference;
**SPECULATIVE** = assessment. Theorem numbers given from memory are UNVERIFIED.

## 0. Main result

`ZInQ.RLeaf.TateCuspLaurent` (task rleaf-elliptic, `ZInQKernel/Contrib/RLeaf/X1RationalCusp.lean`)
is **proved outright**. Consequently leaf T40 (`X1Belyi.X1RationalCusp`) and leaf T39
(`X1Belyi.X1ConstantField`) now depend only on `IgusaTransitive` (task t40-igusa).

| Declaration | Type (exact) | File |
|---|---|---|
| `ZInQ.RLeaf.tateCuspLaurent` | `ZInQ.RLeaf.TateCuspLaurent` | `ZInQKernel/Contrib/RLeaf/TateCusp.lean` |
| `ZInQ.RLeaf.x1RationalCusp_of_igusaTransitive` | `ZInQ.RLeaf.IgusaTransitive → X1Belyi.X1RationalCusp` | same |
| `ZInQ.RLeaf.x1ConstantField_of_igusaTransitive` | `ZInQ.RLeaf.IgusaTransitive → X1Belyi.X1ConstantField` | same |
| `ZInQ.RLeaf.TateCuspTorsion.tateLaurentTorsion` | `ZInQ.RLeaf.TateLaurentTorsion` | `ZInQKernel/Contrib/RLeaf/TateCuspTorsion.lean` |
| `ZInQ.RLeaf.tateCuspLaurent_of_tateLaurentTorsion` | `ZInQ.RLeaf.TateLaurentTorsion → ZInQ.RLeaf.TateCuspLaurent` | `ZInQKernel/Contrib/RLeaf/TateCuspGlue.lean` |

The target, verbatim from `X1RationalCusp.lean`:

```lean
def TateCuspLaurent : Prop :=
  ∀ N : ℕ, 0 < N → ∃ (P : EjBar.toAffine.Point) (ψ : fieldX1 P →+* LaurentSeries ℚ),
    addOrderOf P = N ∧ (∀ c : ℚ, ψ (X1Belyi.ratHom (fieldX1 P) c) = HahnSeries.C c) ∧
    ψ (algebraMap Qj (fieldX1 P) RatFunc.X) ∉ Set.range (HahnSeries.ofPowerSeries ℤ ℚ)
```

The intermediate statement (new, `TateCuspGlue.lean`; now proved):

```lean
open Classical in
def TateLaurentTorsion : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∃ (W : WeierstrassCurve (LaurentSeries ℚ)) (_ : W.IsElliptic)
    (P : W.toAffine.Point), addOrderOf P = N ∧
      W.j ∉ Set.range (HahnSeries.ofPowerSeries ℤ ℚ)
```

`#print axioms` (VERIFIED, `lake build ZInQKernel.Contrib.RLeaf.TateCusp`, exit 0; log
`scratch/t40-tate/build-tatecusp.txt`):

```
'ZInQ.RLeaf.tateCuspLaurent_of_tateLaurentTorsion' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.TateCuspTorsion.tateLaurentTorsion' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.tateCuspLaurent' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.x1RationalCusp_of_igusaTransitive' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.x1ConstantField_of_igusaTransitive' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 1. The proof

### 1.1 `TateLaurentTorsion` (`TateCuspTorsion.lean`)

* `ℚ((t))` is made a normed field by Mathlib's `Valued.toNormedField` (scoped instance), with the
  rank-one structure `hom' = WithZeroMulInt.toNNReal 2 ∘ ValueGroup₀.embedding` (`|t| = 1/2`).
  Ultrametricity is Mathlib's instance; completeness is `LaurentSeries.instLaurentSeriesComplete`
  (the normed uniform structure *is* `Valued.toUniformSpace`, so no comparison is needed).
* For `N ≥ 2`, `q = t^N` as a unit, `‖q‖ < 1` from `valuation_single_zpow`.
* `E_q := TauCeti.tateCurveAt q hq` (elliptic by `isElliptic_tateCurveAt`), and the point
  `tateUniformizationHom q hq (ofMul [t])`. Since `tateUniformizationHom` is an injective group
  homomorphism `Additive (ℚ((t))ˣ ⧸ q^ℤ) →+ E_q(ℚ((t)))`, its order is the order of `[t]`, which
  is `N` (`orderOf_mk_tU`: valuations of `t^m` and `(t^N)^k`).
* `‖j(E_q)‖ = ‖q‖⁻¹ > 1` (`TauCeti.norm_tateCurveAt_j`), so `v(j) > 1` and `j` is not a power
  series (`LaurentSeries.val_le_one_iff_eq_coe`).

### 1.2 The glue `TateLaurentTorsion → TateCuspLaurent` (`TateCuspGlue.lean`)

Given `W/ℚ((t))` elliptic with `J = j(W) ∉ ℚ[[t]]` and `P_W` of exact order `N` (for `N = 1`
use the case `N = 2` only for `W`, and the point `0`):

1. `aeval_ne_zero`: `J` is transcendental over `ℚ` (`J⁻¹ = U ∈ tℚ[[t]]`; `p(J) = 0` gives
   `p.reverse(U) = 0`, whose constant coefficient is the leading coefficient of `p`).
2. `phi J : ℚ(j) →+* ℚ((t))`, `j ↦ J` (`RatFunc.liftRingHom`), identity on `ℚ`.
3. `φ̄ : \overline{ℚ(j)} → \overline{ℚ((t))}` extending `phi` (`IsAlgClosed.lift`).
4. `T = E_j^{φ̄}` and `W` have the same `j` over `\overline{ℚ((t))}`, so Mathlib's
   `exists_variableChange_of_j_eq` gives `C` with `C • T = W`. Comparing `c₄, c₆, b₂`
   (`variableChange_c₄/c₆/b₂`) shows `u², r ∈ ℚ((t))` (this needs `c₄(W), c₆(W) ≠ 0`, i.e.
   `j ≠ 0, 1728`, true because `J ∉ ℚ[[t]]`). Tau Ceti's `addEquivVariableChange` (vendored)
   sends the image of `P_W` to a point `Q ∈ T` of order `N` with `x(Q) = u²x(P_W) + r ∈ ℚ((t))`.
5. `core`: the point map along `φ̄` (Tau Ceti `mapAlong`, vendored) is injective on
   `E_j[N] → T[N]`, both of size `N²` (leaf T36, `t36_torsionStructure`), hence bijective; the
   preimage `P` of `Q` has exact order `N` and `φ̄(x(P)) ∈ ℚ((t))`. So `φ̄` maps
   `K_N = ℚ(j)(x(P))` into `ℚ((t))` (`IntermediateField.adjoin_le_iff`), which defines `ψ`.

## 2. Tau Ceti backport (licence)

The uniformization homomorphism is on Tau Ceti main only (commit 4d91513e, Lean v4.36.0-rc2).
The import closure of `TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Homomorphism` there has
69 modules (16k lines); 12 were already vendored (commit 5a01f5fe). Choice made (VERIFIED by
compiling): the other **57 modules are taken whole from main** under
`ZInQKernel/Contrib/TauCeti/Backport/` (the oct16 versions of the 27 that exist at 5a01f5fe lack
lemmas the main TateCurve files use), and for 5 vendored modules a Backport/ file of the same path
holds only the main-version declarations missing from the vendored version (generated by
`scratch/t40-tate/extras.py`). Only six files needed changes for the pinned Mathlib (renames
`nnNormHom→nnnormHom`, `nnNorm_mul_le_max→nnnorm_mul_le_max`,
`FiniteDimensional.completeSpace→FiniteDimensional.complete`, `Module.End.coe_pow` for
`FunLike.coe_pow_eq_iterate`, no summation-filter argument of `Finset.tsum_subtype`, two
`maxHeartbeats 1000000`). Every Backport file keeps Tau Ceti's copyright header, carries a
"Backported from Tau Ceti (…, commit 4d91513e4d30, module …)" line and a
"-- Modified for the Z-in-Q kernel: …" line; `ThirdParty/TauCeti/NOTICE` has the new entries.
`python3 ~/dzq-runs/tc/diffcheck2.py`: `{'IDENT': 1647, 'NOTE-ONLY': 0, 'MOD-NOTED': 36,
'MOD-UNNOTED': 0, 'NOPROV': 111, 'NOSRC': 0}` (VERIFIED).

Caveat: Backport/ full modules keep Tau Ceti's declaration names, so none of them may be imported
together with a 5a01f5fe copy of the same module vendored at the non-Backport path (no such copy
exists at the time of writing).
