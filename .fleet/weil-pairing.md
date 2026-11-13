# weil-pairing — fleet summary

**Result.** Polarizations and the Weil pairing are defined over the project's `PkgI3.AbVar`.
T9 is restated over these definitions, and the T9-part of G12 is **proved from four leaves**.
File: `scratch/weil-pairing/WeilPairing.lean` (about 1200 lines). It imports only HDecomp
modules (`Objects`, `Assembly.C8`, `QM.Structures`) and Mathlib. It compiles with no `sorry`,
and the axioms are standard (VERIFIED, `#print axioms`). Report: `docs/research/weil-pairing.md`.

**Compiles:**
- Definitions:
  - torsion `A[n]` and `μ_n(K̄)` with their Galois actions;
  - `μ_n`-valued pairings: perfect, alternating, Galois-equivariant, pull-back;
  - `WeilDual` (the dual as seen by its Weil pairings), `IsDualHom`;
  - the Weil pairing `e^λ_n(x, y) = e_n(x, λy)`;
  - `SymmIsogeny`, `Polarization` (with Rosati positivity), `IsPrincipal`;
  - the ℓ-adic Weil pairing `E^λ : T_ℓA × T_ℓA → T_ℓ(μ)`;
  - `RosatiTypeMu`.
- API:
  - skew-symmetry, `e(mx, y) = e(x, y)^m`;
  - compatibility with isogenies (`weil_pullback`, `isSymmetric_pullback`, dual composition and
    uniqueness);
  - Galois equivariance;
  - nondegeneracy up to `d`, and perfectness for principal `λ`;
  - cyclotomic multiplier at finite level and ℓ-adically (Mathlib's `cyclotomicCharacter`);
  - `T_ℓ(μ) ↪ ℤ_ℓ`;
  - `E^λ` alternating with trivial kernel.
- Leaves:
  - `T09_SymmIsogenyExists` (T9 restated);
  - `T09plus_PolarizationExists`, `IsogenyQuasiInverse`, `DivisiblePoints`;
  - `LemmaP_Exists` (rv-qm-polar, existence half; a leaf candidate only, since it composes several results).
- `oldT9_of_symmIsogeny`: the new T9 together with `IsogenyQuasiInverse` implies the old
  `LeafPush.T09_WeilPairing` used by Leaves.lean.
- `g12_detInput_of_leaves`: T9, `IsogenyQuasiInverse`, `PkgI3.TateModuleFree` and
  `DivisiblePoints` imply `det ρ_ℓ(σ)² = χ_ℓ(σ)^{rank T_ℓ A}` on Objects' `V_ℓ`.
- `twist_finite_four`: C8's determinant argument from `(det r)⁴ = χ⁴`, so no Pfaffian is needed.
- Non-vacuity: T9 and T9⁺ hold at `A = 0`, the zero pairing is not perfect unless the torsion is
  trivial, and `e^λ ≠ 0` (a nonzero abelian variety cannot be built in Mathlib).

**Caveat.** The genuine dual `Pic⁰` cannot be defined: Mathlib has no line bundles or Picard
group on schemes. `WeilDual` is not unique, so leaves over it must be existential in the dual,
and all of them are. One model review found no false or over-strong leaf; its fixes are applied (`WeilDual.dualEnd`, `Polarization` is up to sign). Not stated, because they would be unsafe: the existence of dual morphisms for
every `WeilDual`, and the uniqueness half of Lemma P.

**Remains:**
- the genuine dual (needs Mathlib's Picard functor);
- the fold-in (replace the `HSyn` field `t9` by the two new leaves);
- on the actual `A`: `det V = (det r)²` from C1, then `twist_finite_four`;
- uses of Rosati positivity.
