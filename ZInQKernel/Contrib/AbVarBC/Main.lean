import ZInQKernel.Contrib.AbVarBC.KerUnit
import ZInQKernel.Contrib.AbVarBC.G9Mul

/-!
# Base change of abelian varieties: main results

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

All statements below are proved from Mathlib alone (no leaf, no hypothesis):
* `kerUnitOpen : MulRigidity.KerUnitOpen` (mul-rigidity's leaf: the unit section of `A[n]` is an
  open immersion in characteristic `0`, `n ≠ 0`), from `Tangent.ks_isOpenImmersion`;
* `mulIsogeny : G0FibreSimple.MulIsogeny` (`[n]` is finite and surjective in characteristic `0`);
* `torsionDescends`, `tateBC_bijective`: `T_ℓ(A) ≅ T_ℓ(A_L)` Galois-equivariantly;
* `abVarBaseChangeK : AbVarBaseChangeK` (the kernel-level statement);
* **`abVarBaseChange : ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange`** (task g9-derham's bridge);
* `g9Glue_of_r10Weights : G9Bridge.R10Weights → G0Galois.G9Glue`.
-/

namespace ZInQ.Contrib.AbVarBC

/-- **mul-rigidity's leaf `KerUnitOpen`, proved.** -/
theorem kerUnitOpen : MulRigidity.KerUnitOpen := by
  intro k _ _ A n hn
  exact Tangent.ks_isOpenImmersion A n hn

/-- **`MulIsogeny`, proved**: in characteristic `0`, `[n]` is finite and surjective for `n ≠ 0`. -/
theorem mulIsogeny : G0FibreSimple.MulIsogeny :=
  MulRigidity.mulIsogeny_of_kerUnitOpen kerUnitOpen

/-- `ℓ`-power torsion points of `A_L(L̄)` come from `A(K̄)` (characteristic `0`). -/
theorem torsionDescends {K : Type} [Field K] [CharZero K] (A : _root_.PkgI3.AbVar K) {L : Type}
    [Field L] [Algebra K L] (κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) (ℓ : ℕ)
    [Fact ℓ.Prime] : TorsionDescends A κ ℓ :=
  torsionDescends_of_mulIsogeny mulIsogeny A κ ℓ

/-- **`T_ℓ(A) → T_ℓ(A_L)` is bijective** (characteristic `0`). -/
theorem tateBC_bijective {K : Type} [Field K] [CharZero K] (A : _root_.PkgI3.AbVar K) {L : Type}
    [Field L] [Algebra K L] (κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) (ℓ : ℕ)
    [Fact ℓ.Prime] : Function.Bijective (tateBC A κ ℓ) :=
  tateBC_bijective_of_torsionDescends A κ ℓ (torsionDescends A κ ℓ)

/-- **Base change of abelian varieties, kernel form, proved.** -/
theorem abVarBaseChangeK : AbVarBaseChangeK :=
  abVarBaseChangeK_of_mulIsogeny mulIsogeny

/-- **`G9Bridge.AbVarBaseChange`, proved** (no hypothesis). -/
theorem abVarBaseChange : ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange :=
  abVarBaseChange_of_mulIsogeny mulIsogeny

/-- **G9 from the weight clause alone**: `R10Weights → G9Glue`. -/
theorem g9Glue_of_r10Weights (hW : ZInQ.Contrib.G9.G9Bridge.R10Weights) :
    ZInQ.Contrib.G9.G0Galois.G9Glue :=
  ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange abVarBaseChange hW

end ZInQ.Contrib.AbVarBC
