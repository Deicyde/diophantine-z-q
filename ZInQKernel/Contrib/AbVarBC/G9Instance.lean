import ZInQKernel.Contrib.AbVarBC.Tate
import ZInQKernel.Contrib.G9.LocalModel

/-!
# Base change of abelian varieties, IV: the instance `G9Bridge.AbVarBaseChange`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

`G9Bridge.AbVarBaseChange` (task g9-derham, `ZInQKernel/Contrib/G9/LocalModel.lean`) is stated over
two verbatim copies of the kernel's abelian varieties: `ZInQ.Contrib.G9.PkgI3.AbVar`
(`Contrib/G9/I3Layer.lean`) and `ZInQ.Contrib.G9.PkgI4.I3.AbVar` (`Contrib/G9/I4Layer.lean`).
§1 transports between the copies and the kernel's `PkgI3.AbVar` (all identities are `rfl`);
§2 derives the instance from the general lemmas of `Contrib/AbVarBC/{Dim,Points,Tate}.lean`.

* `abVarBaseChange_of_torsionDescends`: from descent of `ℓ`-power torsion points;
* `abVarBaseChange_of_tateModuleFree`: from leaf T26 `PkgI3.TateModuleFree` (I3.M0);
* `g9Glue_of_tateModuleFree`: `TateModuleFree → R10Weights → G9Glue`.
-/

open CategoryTheory AlgebraicGeometry Limits

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.AbVarBC

/-! ## §1. Transport between the copies -/

section Transport

variable {K : Type} [Field K]

/-- G9's copy of pkg-I3's abelian variety, as a kernel `PkgI3.AbVar`. -/
def ofG9 (A : ZInQ.Contrib.G9.PkgI3.AbVar K) : _root_.PkgI3.AbVar K :=
  @_root_.PkgI3.AbVar.mk K _ A.X A.grp A.proper A.smooth A.geomInt

/-- A kernel `PkgI3.AbVar`, as pkg-I4's copy `PkgI4.I3.AbVar` (in G9's namespace). -/
def toI4 (A : _root_.PkgI3.AbVar K) : ZInQ.Contrib.G9.PkgI4.I3.AbVar K :=
  @ZInQ.Contrib.G9.PkgI4.I3.AbVar.mk K _ A.X A.grp A.proper A.smooth A.geomInt

theorem dim_ofG9 (A : ZInQ.Contrib.G9.PkgI3.AbVar K) : (ofG9 A).dim = A.dim := rfl

theorem dim_toI4 (A : _root_.PkgI3.AbVar K) : (toI4 A).dim = A.dim := rfl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `V_ℓ` of G9's copy is `V_ℓ` of the kernel's object (identity map). -/
noncomputable def vOfG9 (A : ZInQ.Contrib.G9.PkgI3.AbVar K) : A.V ℓ ≃ₗ[ℚ_[ℓ]] (ofG9 A).V ℓ :=
  LinearEquiv.refl ℚ_[ℓ] (A.V ℓ)

theorem vOfG9_galRep (A : ZInQ.Contrib.G9.PkgI3.AbVar K) (σ : Field.absoluteGaloisGroup K)
    (v : A.V ℓ) : vOfG9 ℓ A (A.galRep ℓ σ v) = (ofG9 A).galRep ℓ σ (vOfG9 ℓ A v) := rfl

theorem vOfG9_symm_galRep (A : ZInQ.Contrib.G9.PkgI3.AbVar K) (σ : Field.absoluteGaloisGroup K)
    (v : (ofG9 A).V ℓ) :
    (vOfG9 ℓ A).symm ((ofG9 A).galRep ℓ σ v) = A.galRep ℓ σ ((vOfG9 ℓ A).symm v) := rfl

/-- `V_ℓ` of pkg-I4's copy is `V_ℓ` of the kernel's object (identity map). -/
noncomputable def vToI4 (A : _root_.PkgI3.AbVar K) : (toI4 A).V ℓ ≃ₗ[ℚ_[ℓ]] A.V ℓ :=
  LinearEquiv.refl ℚ_[ℓ] (A.V ℓ)

theorem vToI4_galRep (A : _root_.PkgI3.AbVar K) (σ : Field.absoluteGaloisGroup K)
    (v : (toI4 A).V ℓ) : vToI4 ℓ A ((toI4 A).galRep ℓ σ v) = A.galRep ℓ σ (vToI4 ℓ A v) := rfl

end Transport

/-! ## §2. The instance -/

/-- `Field.absoluteGaloisGroup.map i` is restriction along the `K`-embedding `K̄ → L̄` it is
built from (`IsAlgClosed.lift`). -/
theorem map_comm {K L : Type} [Field K] [Field L] (i : K →+* L) :
    letI : Algebra K L := i.toAlgebra
    ∀ (σ : Field.absoluteGaloisGroup L) (x : AlgebraicClosure K),
      (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
          (galK (Field.absoluteGaloisGroup.map i σ) x) =
        galK σ ((IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) x) := by
  letI : Algebra K L := i.toAlgebra
  let g0 : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := g0.toAlgebra
  exact fun σ x =>
    AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars K σ) (AlgebraicClosure K) x

/-- **`AbVarBaseChange` from descent of `ℓ`-power torsion points.** The hypothesis is the
statement "every `ℓ`-power torsion point of `A_L(L̄)` comes from `A(K̄)`" for the kernel's
objects and the embedding `K̄ → L̄` of `Field.absoluteGaloisGroup.map`. -/
theorem abVarBaseChange_of_torsionDescends
    (hD : ∀ (K : Type) [Field K] [CharZero K] (A : _root_.PkgI3.AbVar K) (L : Type) [Field L]
      (i : K →+* L) (ℓ : ℕ) [Fact ℓ.Prime],
      letI : Algebra K L := i.toAlgebra
      TorsionDescends A (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) ℓ) :
    ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange := by
  intro K _ _ A L _ i ℓ _
  letI : Algebra K L := i.toAlgebra
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  have hb := tateBC_bijective_of_torsionDescends (ofG9 A) κ ℓ (hD K (ofG9 A) L i ℓ)
  refine ⟨toI4 ((ofG9 A).baseChange L),
    (vToI4 ℓ _).trans ((vBC (ofG9 A) κ ℓ hb).trans (vOfG9 ℓ A).symm), ?_, ?_⟩
  · exact (dim_toI4 _).trans (((ofG9 A).dim_baseChange L).trans (dim_ofG9 A))
  · intro σ v
    simp only [LinearEquiv.trans_apply]
    rw [vToI4_galRep, vBC_galRep (ofG9 A) κ ℓ hb (Field.absoluteGaloisGroup.map i σ) σ
      (map_comm i σ)]
    exact vOfG9_symm_galRep ℓ A _ _

/-- **`AbVarBaseChange` from leaf T26 (`PkgI3.TateModuleFree`, Mumford §§4, 18-19).** -/
theorem abVarBaseChange_of_tateModuleFree (hT : _root_.PkgI3.TateModuleFree) :
    ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange := by
  intro K _ _ A L _ i ℓ hℓ
  letI : Algebra K L := i.toAlgebra
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  have hb := tateBC_bijective_of_tateModuleFree (ofG9 A) κ ℓ hT
    (Nat.cast_ne_zero.mpr hℓ.out.ne_zero)
  refine ⟨toI4 ((ofG9 A).baseChange L),
    (vToI4 ℓ _).trans ((vBC (ofG9 A) κ ℓ hb).trans (vOfG9 ℓ A).symm), ?_, ?_⟩
  · exact (dim_toI4 _).trans (((ofG9 A).dim_baseChange L).trans (dim_ofG9 A))
  · intro σ v
    simp only [LinearEquiv.trans_apply]
    rw [vToI4_galRep, vBC_galRep (ofG9 A) κ ℓ hb (Field.absoluteGaloisGroup.map i σ) σ
      (map_comm i σ)]
    exact vOfG9_symm_galRep ℓ A _ _

/-- **G9 from T26 and the weight clause**: `TateModuleFree → R10Weights → G9Glue`. -/
theorem g9Glue_of_tateModuleFree (hT : _root_.PkgI3.TateModuleFree)
    (hW : ZInQ.Contrib.G9.G9Bridge.R10Weights) : ZInQ.Contrib.G9.G0Galois.G9Glue :=
  ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange (abVarBaseChange_of_tateModuleFree hT) hW

end ZInQ.Contrib.AbVarBC
