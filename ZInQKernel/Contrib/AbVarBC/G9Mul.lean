import ZInQKernel.Contrib.AbVarBC.G9Instance
import ZInQKernel.Contrib.AbVarBC.Torsion
import ZInQKernel.Contrib.AbVarBC.Mul

/-!
# Base change of abelian varieties, VI: `AbVarBaseChange` from finiteness of `[n]`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

The `V_ℓ` clause of `G9Bridge.AbVarBaseChange` needs exactly the descent of `ℓ`-power torsion
points (`TorsionDescends`), which follows from finiteness of `[ℓⁿ]`
(`torsionDescends_of_isFinite`). Finiteness of `[n]` is mul-rigidity's `MulIsogeny`
(Mumford §4; Milne Thm 8.2), which mul-rigidity reduced to the single point statement
`KerUnitOpen` and further to two cotangent-space glue statements. Hence:

* `abVarBaseChangeK_of_mulIsogeny`: the kernel-level statement `AbVarBaseChangeK`;
* `abVarBaseChange_of_mulIsogeny`, `…_of_kerUnitOpen`, `…_of_mulEtale`, `…_of_cotangent`;
* `g9Glue_of_kerUnitOpen`, `g9Glue_of_cotangent`.
-/

open CategoryTheory AlgebraicGeometry Limits

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.AbVarBC

/-- **The statement of `G9Bridge.AbVarBaseChange` over the kernel's `PkgI3.AbVar`**, with the
witness pinned to `A.baseChange L`. -/
def AbVarBaseChangeK : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A : _root_.PkgI3.AbVar K) (L : Type) [Field L]
    (i : K →+* L) (ℓ : ℕ) [Fact ℓ.Prime],
    letI : Algebra K L := i.toAlgebra
    (A.baseChange L).dim = A.dim ∧
      ∃ c : (A.baseChange L).V ℓ ≃ₗ[ℚ_[ℓ]] A.V ℓ,
        ∀ σ v, c ((A.baseChange L).galRep ℓ σ v) =
          A.galRep ℓ (Field.absoluteGaloisGroup.map i σ) (c v)

/-- `AbVarBaseChangeK` from torsion descent. -/
theorem abVarBaseChangeK_of_torsionDescends
    (hD : ∀ (K : Type) [Field K] [CharZero K] (A : _root_.PkgI3.AbVar K) (L : Type) [Field L]
      (i : K →+* L) (ℓ : ℕ) [Fact ℓ.Prime],
      letI : Algebra K L := i.toAlgebra
      TorsionDescends A (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) ℓ) :
    AbVarBaseChangeK := by
  intro K _ _ A L _ i ℓ _
  letI : Algebra K L := i.toAlgebra
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  have hb := tateBC_bijective_of_torsionDescends A κ ℓ (hD K A L i ℓ)
  exact ⟨A.dim_baseChange L, vBC A κ ℓ hb, fun σ v =>
    vBC_galRep A κ ℓ hb (Field.absoluteGaloisGroup.map i σ) σ (map_comm i σ) v⟩

/-- `MulIsogeny` gives torsion descent. -/
theorem torsionDescends_of_mulIsogeny (h : G0FibreSimple.MulIsogeny) {K : Type} [Field K]
    [CharZero K] (A : _root_.PkgI3.AbVar K) {L : Type} [Field L] [Algebra K L]
    (κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) (ℓ : ℕ) [hℓ : Fact ℓ.Prime] :
    TorsionDescends A κ ℓ :=
  torsionDescends_of_isFinite A κ ℓ fun n =>
    (h K A _ (by exact_mod_cast (pow_pos hℓ.out.pos n).ne')).1

/-- **`AbVarBaseChangeK` from `MulIsogeny`.** -/
theorem abVarBaseChangeK_of_mulIsogeny (h : G0FibreSimple.MulIsogeny) : AbVarBaseChangeK :=
  abVarBaseChangeK_of_torsionDescends fun K _ _ A L _ i ℓ _ => by
    letI : Algebra K L := i.toAlgebra
    exact torsionDescends_of_mulIsogeny h A _ ℓ

/-- **`AbVarBaseChange` from `MulIsogeny`** (`[n]` finite and surjective in characteristic 0). -/
theorem abVarBaseChange_of_mulIsogeny (h : G0FibreSimple.MulIsogeny) :
    ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange :=
  abVarBaseChange_of_torsionDescends fun K _ _ A L _ i ℓ _ => by
    letI : Algebra K L := i.toAlgebra
    exact torsionDescends_of_mulIsogeny h A _ ℓ

/-- **`AbVarBaseChange` from the point statement `KerUnitOpen`** (the unit section of `A[n]` is an
open immersion, char 0, `n ≠ 0`; a consequence of the published `MulEtale`). -/
theorem abVarBaseChange_of_kerUnitOpen (h : MulRigidity.KerUnitOpen) :
    ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange :=
  abVarBaseChange_of_mulIsogeny (MulRigidity.mulIsogeny_of_kerUnitOpen h)

/-- **`AbVarBaseChange` from `MulEtale`** (Mumford §4 Appl. 2, Milne Thm 8.2; char 0). -/
theorem abVarBaseChange_of_mulEtale (h : MulRigidity.MulEtale) :
    ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange :=
  abVarBaseChange_of_mulIsogeny (MulRigidity.mulIsogeny_of_mulEtale h)

/-- **`AbVarBaseChange` from the two cotangent-space glue statements** (no literature leaf). -/
theorem abVarBaseChange_of_cotangent (h1 : MulRigidity.KerUnitOpenOfCotangentSurj)
    (h2 : MulRigidity.CotangentMulN) : ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange :=
  abVarBaseChange_of_mulIsogeny (MulRigidity.mulIsogeny_of_cotangent h1 h2)

/-- `G9Glue` from `KerUnitOpen` and the weight clause. -/
theorem g9Glue_of_kerUnitOpen (h : MulRigidity.KerUnitOpen)
    (hW : ZInQ.Contrib.G9.G9Bridge.R10Weights) : ZInQ.Contrib.G9.G0Galois.G9Glue :=
  ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange (abVarBaseChange_of_kerUnitOpen h) hW

/-- `G9Glue` from the two cotangent glue statements and the weight clause. -/
theorem g9Glue_of_cotangent (h1 : MulRigidity.KerUnitOpenOfCotangentSurj)
    (h2 : MulRigidity.CotangentMulN) (hW : ZInQ.Contrib.G9.G9Bridge.R10Weights) :
    ZInQ.Contrib.G9.G0Galois.G9Glue :=
  ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange (abVarBaseChange_of_cotangent h1 h2) hW

end ZInQ.Contrib.AbVarBC
