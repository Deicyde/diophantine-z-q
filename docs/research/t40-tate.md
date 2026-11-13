# t40-tate: the Tate-curve input of T40 (`TateCuspLaurent`) is proved

Task t40-tate, 2026-11-13. Branch `wip/t40-tate` (base fork main 57a7fa26, fork main 54cc2893
merged). Results log `scratch/t40-tate/log.md`.

Marks: **VERIFIED** = compiled, or read in the source; **STANDARD** = published, with reference;
**SPECULATIVE** = assessment. Theorem numbers given from memory are UNVERIFIED.

## 0. Main result

Two statements are **proved outright** (closed theorems, standard axioms only):

1. `ZInQ.RLeaf.TateCuspLaurent` (my target; task rleaf-elliptic,
   `ZInQKernel/Contrib/RLeaf/X1RationalCusp.lean`). So leaf T40 (`X1Belyi.X1RationalCusp`) and leaf
   T39 (`X1Belyi.X1ConstantField`) depend only on `IgusaTransitive`.
2. `ZInQ.RLeaf.TateMuN` (task t40-igusa's cusp statement, `ZInQKernel/Contrib/RLeaf/IgusaX0.lean`,
   agreed with t40-igusa by message). t40-igusa proved `IgusaTransitive ↔ X0Transitive ∧ TateMuN`,
   so with this T40 and T39 depend only on `X0Transitive` (Galois transitivity on cyclic subgroups
   of order `N`, i.e. irreducibility of `X₀(N)`). t40-igusa writes `T40.lean` with that reduction.

| Declaration | Type (exact) | File |
|---|---|---|
| `ZInQ.RLeaf.tateCuspLaurent` | `ZInQ.RLeaf.TateCuspLaurent` | `ZInQKernel/Contrib/RLeaf/TateCusp.lean` |
| `ZInQ.RLeaf.x1RationalCusp_of_igusaTransitive` | `ZInQ.RLeaf.IgusaTransitive → X1Belyi.X1RationalCusp` | same |
| `ZInQ.RLeaf.x1ConstantField_of_igusaTransitive` | `ZInQ.RLeaf.IgusaTransitive → X1Belyi.X1ConstantField` | same |
| `ZInQ.RLeaf.TateCuspTorsion.tateLaurentTorsion` | `ZInQ.RLeaf.TateLaurentTorsion` | `ZInQKernel/Contrib/RLeaf/TateCuspTorsion.lean` |
| `ZInQ.RLeaf.tateCuspLaurent_of_tateLaurentTorsion` | `ZInQ.RLeaf.TateLaurentTorsion → ZInQ.RLeaf.TateCuspLaurent` | `ZInQKernel/Contrib/RLeaf/TateCuspGlue.lean` |
| `ZInQ.RLeaf.tateMuN` | `ZInQ.RLeaf.TateMuN` | `ZInQKernel/Contrib/RLeaf/TateCuspMuN.lean` |
| `ZInQ.RLeaf.TateCuspMuN.tateMuNAt_of_unit` | for `F` complete ultrametric with isometric `incl : ℚ((t)) →+* F`, `N ≥ 2`, `u : Fˣ` with `orderOf [u] = N` in `Fˣ/(incl t)^ℤ` and, for each `m < N` prime to `N`, a continuous `σ : F ≃+* F` fixing `incl` with `σ u = u^m`: `TateMuNAt N (ΩF F incl)` | same |
| `ZInQ.RLeaf.TateCuspMuN.tateMuNAt_of_root` | `K` char. 0, `ζ` primitive `N`-th root, all `ζ ↦ ζ^m` induced by `K ≃+* K`: `TateMuNAt N (ΩF K((t)) (inclK K))` | same |

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
'ZInQ.RLeaf.tateMuN' depends on axioms: [propext, Classical.choice, Quot.sound]
```
(the last from `lake build ZInQKernel.Contrib.RLeaf.TateCuspMuN ZInQKernel.Contrib.RLeaf.TateCusp`,
"Build completed successfully (9394 jobs)", log `scratch/t40-tate/build-tatecuspmun.txt`).

`TateMuN` and `TateMuNAt`, verbatim from t40-igusa (`IgusaX0.lean`, `IgusaLocal.lean`):

```lean
def TateMuN : Prop :=
  ∀ N : ℕ, 0 < N → ∃ Q₀ : EjBar.toAffine.Point, addOrderOf Q₀ = N ∧
    ∀ R ∈ AddSubgroup.zmultiples Q₀, addOrderOf R = N →
      ∃ τ : Kbar ≃ₐ[Qj] Kbar, τ (xCoord Q₀) = xCoord R

def TateMuNAt (N : ℕ) (Ω : Type) [Field Ω] [Algebra Qj Ω] [DecidableEq Ω] : Prop :=
  ∃ Q₀ : (Ej.baseChange Ω).toAffine.Point, addOrderOf Q₀ = N ∧
    ∀ R ∈ AddSubgroup.zmultiples Q₀, addOrderOf R = N →
      ∃ τ : Ω ≃ₐ[Qj] Ω, τ (xCoord Q₀) = xCoord R
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

### 1.3 `TateMuN` (`TateCuspMuN.lean`)

* `K((t))` for any field `K` is a complete normed field (`rankOneK`); coefficientwise maps along
  injective field maps preserve the valuation (`valuation_mapRingHom`, via
  `valuation_le_iff_coeff_lt_eq_zero`), hence are isometric and continuous.
* Generic step (`tateMuNAt_of_unit`): `F ⊇ ℚ((t))` complete, `q = t`, `W = E_t/ℚ((t))`,
  `J = j(W)`, `Ω = \overline F` as a `ℚ(j)`-algebra by `j ↦ J`. Over `Ω`, `C • E_j = W` (same
  `j`); `u², r ∈ ℚ((t))` (`uR_mem`). `Φ : E_t(F) → E_j(Ω)` (cast, `mapAlong`, cast,
  `addEquivVariableChange`) is an injective homomorphism with `x(Φ P) = u² x(P) + r`.
  `Q₀ = Φ(P(u))`; a generator `R` of `⟨Q₀⟩` is `m • Q₀` with `m < N` prime to `N`
  (`exists_nat_zsmul_eq`, `coprime_of_addOrderOf_nsmul`), `= Φ(P(u^m))`; the given `σ` extends to
  `τ ∈ Aut(Ω/ℚ(j))` (`IsAlgClosure.equivOfEquiv`; `τ` fixes `ℚ(j)` because `σ` fixes `ℚ((t))`),
  and `σ X(q, u) = X(q, u^m)` (`TauCeti.map_tateUniformizationX`, `σ q = q`).
* Specialization: `F = ℚ(ζ_N)((t))`, `u = ζ_N` (order `N` in `F^×/t^ℤ` by valuations),
  `σ = ` coefficientwise `ζ ↦ ζ^m` (`IsCyclotomicExtension.autEquivPow`, `cyclotomic.irreducible_rat`);
  `N = 1` is trivial over `Kbar`; t40-igusa's `tateMuN_of_at` (torsion counting) moves the
  statement from `Ω` to `Kbar`.
* Kernel note (VERIFIED by bisection): with the concrete field `CyclotomicField N ℚ ((t))` the
  kernel timed out on rewrites whose instance paths differ (e.g. `map_nsmul` on
  `Additive (Fˣ ⧸ q^ℤ)`, `addOrderOf_zero` on points); stating the argument for an abstract `F`
  removed all timeouts.

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
