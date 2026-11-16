import ZInQKernel.OneProof.H.TailS
import ZInQKernel.Contrib.G9.G9

/-!
# Fixed scalars for the de Rham space over a finite extension

The field is an arbitrary finite extension of `ℚ_p`, not necessarily Galois.
The map `gfToGqp` is restriction along the chosen `embF : ℚ̄_p → F̄`;
`embF_gfToGqp` supplies the compatibility used here. A separable Hensel lift
produces the `B_dR⁺` scalar lift, and uniqueness makes it fixed by `G_F`.

This supplies scalar normalization only. It does not prove the de Rham
comparison for abelian varieties or construct their periods.
-/

namespace ZInQ.Contrib.PadicDeRhamScalars

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4
open ZInQ.Contrib.HodgeSplit
open scoped TensorProduct

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

section PlusScalars

attribute [local instance] ZInQ.Contrib.G9.algPlus

/-- The embedding `F → ℂ_p` behind the existing `gfToGqp`. -/
def cpEmbeddingOver : F →ₐ[ℚ_[p]] ℂ_[p] :=
  (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).comp (phiF p F)

/-- No normality of `F/ℚ_p` is needed to fix its own elements. -/
theorem cpEmbeddingOver_fixed (σ : Field.absoluteGaloisGroup F) (x : F) :
    cpAct p (gfToGqp p F σ) (cpEmbeddingOver p F x) = cpEmbeddingOver p F x := by
  have hx : gfToGqp p F σ (phiF p F x) = phiF p F x := by
    apply (embF_bijective p F).injective
    rw [embF_gfToGqp, embF_phiF]
    exact (galF F σ).commutes x
  change cpAct p (gfToGqp p F σ) ((phiF p F x : PadicAlgCl p) : ℂ_[p]) =
    ((phiF p F x : PadicAlgCl p) : ℂ_[p])
  rw [cpAct_coe, hx]

/-- A separable Hensel lift of `F` into `B_dR⁺`, for any finite `F/ℚ_p`. -/
theorem exists_scalarPlusOver :
    ∃ ι : F →ₐ[ℚ_[p]] BDeRhamPlus 𝓞_ℂ_[p] p,
      ∀ x, thetaAlg p (ι x) = cpEmbeddingOver p F x :=
  exists_hensel_lift (thetaAlg p) (BdrKer.Cp.thetaPlusCp_surjective p)
    (isUnit_of_thetaAlg_ne_zero p) (cpEmbeddingOver p F)

def scalarPlusOver : F →ₐ[ℚ_[p]] BDeRhamPlus 𝓞_ℂ_[p] p :=
  (exists_scalarPlusOver p F).choose

theorem scalarPlusOver_residue (x : F) :
    thetaAlg p (scalarPlusOver p F x) = cpEmbeddingOver p F x :=
  (exists_scalarPlusOver p F).choose_spec x

/-- Uniqueness of the separable Hensel lift gives `G_F`-fixed scalars. -/
theorem scalarPlusOver_fixed (σ : Field.absoluteGaloisGroup F) (x : F) :
    DR.bdrPlusMap p (oAct p (gfToGqp p F σ)) (scalarPlusOver p F x) =
      scalarPlusOver p F x := by
  exact hensel_lift_natural (thetaAlg p) (cpEmbeddingOver p F)
    (scalarPlusOver p F) (scalarPlusOver_residue p F)
    (sPlus p (gfToGqp p F σ)) (AlgHom.id ℚ_[p] F) (fun y => by
      change BdrKer.Cp.thetaPlusCp p
        (DR.bdrPlusMap p (oAct p (gfToGqp p F σ)) (scalarPlusOver p F y)) =
          cpEmbeddingOver p F y
      rw [thetaPlusCp_bdrPlusMap, ← thetaAlg_apply, scalarPlusOver_residue,
        cpEmbeddingOver_fixed]) x

/-- The `F`-scalar map into the existing `BdR`. -/
def scalarEmbeddingOver : F →ₐ[ℚ_[p]] BdR p :=
  { (algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p)).comp
      (scalarPlusOver p F).toRingHom with
    commutes' := fun c => by
      change algebraMap _ (BdR p) (scalarPlusOver p F (algebraMap ℚ_[p] F c)) =
        qpToBdR p c
      rw [AlgHom.commutes]
      rfl }

theorem scalarEmbeddingOver_fixed (σ : Field.absoluteGaloisGroup F) (x : F) :
    bdrAct p (gfToGqp p F σ) (scalarEmbeddingOver p F x) =
      scalarEmbeddingOver p F x := by
  change bdrAct p (gfToGqp p F σ)
    (algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) (scalarPlusOver p F x)) =
      algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) (scalarPlusOver p F x)
  rw [bdrAct, DR.bdrMap, IsLocalization.map_eq, scalarPlusOver_fixed]

end PlusScalars

variable {F}
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

/-- The fixed space has an `F`-scalar structure, so `[F:ℚ_p]` divides its
`ℚ_p`-dimension. This is divisibility only, not the comparison equality. -/
theorem finrank_dvd_ddrSpaceOver
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) :
    Module.finrank ℚ_[p] F ∣ Module.finrank ℚ_[p] (ddrSpaceOver p ρ) := by
  rw [ddrSpaceOver_eq_DspAct]
  exact finrank_dvd_Dsp_of_emb ((bdrActHom p).comp (gfToGqp p F))
    (fun σ => ρ σ) Set.univ (scalarEmbeddingOver p F) (fun σ _ x b => by
      change bdrAct p (gfToGqp p F σ) (scalarEmbeddingOver p F x * b) =
        scalarEmbeddingOver p F x * bdrAct p (gfToGqp p F σ) b
      rw [map_mul, scalarEmbeddingOver_fixed])

/-- The map identity in `TailS.isDeRhamOver_iff_tensor_dual`, made explicit. -/
theorem tensorDual_ddr_map [FiniteDimensional ℚ_[p] V]
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) :
    Submodule.map (tensorDualEquiv p (V := V)).toLinearMap (ddrTensorOver p ρ.dual) =
      ddrSpaceOver p ρ := by
  ext φ
  constructor
  · rintro ⟨x, hx, rfl⟩ σ w
    have h := congrArg (fun y => tensorDualEquiv p (V := V) y (ρ σ w)) (hx σ)
    rw [tensorDualEquiv_map, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at h
    exact h.symm
  · intro hφ
    refine ⟨(tensorDualEquiv p (V := V)).symm φ, fun σ => ?_, by simp⟩
    apply (tensorDualEquiv p (V := V)).injective
    refine LinearMap.ext fun v => ?_
    rw [tensorDualEquiv_map, LinearEquiv.apply_symm_apply]
    have h := hφ σ (ρ σ⁻¹ v)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] at h
    rw [h]
    rfl

theorem finrank_ddrTensorOver_dual [FiniteDimensional ℚ_[p] V]
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) :
    Module.finrank ℚ_[p] (ddrTensorOver p ρ.dual) =
      Module.finrank ℚ_[p] (ddrSpaceOver p ρ) := by
  rw [← tensorDual_ddr_map p ρ, LinearEquiv.finrank_map_eq]

/-- Scalar divisibility for the tensor-dual form of the existing target. -/
theorem finrank_dvd_ddrTensorOver_dual [FiniteDimensional ℚ_[p] V]
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) :
    Module.finrank ℚ_[p] F ∣ Module.finrank ℚ_[p] (ddrTensorOver p ρ.dual) := by
  rw [finrank_ddrTensorOver_dual]
  exact finrank_dvd_ddrSpaceOver p ρ

/-- For infinite input and infinite invariants, the generic predicate degenerates
to `0 = 0`. This is not a counterexample to the abelian-variety comparison:
`finiteDimensional_of_decomp` supplies finiteness of `V_p(A)` from the
Hodge–Tate decomposition. -/
theorem isDeRhamTensorOver_of_infinite_infinite
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (hV : ¬FiniteDimensional ℚ_[p] V)
    (hD : ¬FiniteDimensional ℚ_[p] (ddrTensorOver p ρ)) :
    IsDeRhamTensorOver p ρ := by
  letI : Module.Free ℚ_[p] (ddrTensorOver p ρ) :=
    Module.Free.of_divisionRing ℚ_[p] (ddrTensorOver p ρ)
  unfold IsDeRhamTensorOver
  rw [Module.finrank_of_not_finite hD, Module.finrank_of_not_finite hV, mul_zero]

/-- For finite nonzero input, the equation cannot hide infinite invariants. -/
theorem finiteDimensional_ddr_of_isDeRham [FiniteDimensional ℚ_[p] V] [Nontrivial V]
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (h : IsDeRhamTensorOver p ρ) : FiniteDimensional ℚ_[p] (ddrTensorOver p ρ) := by
  apply FiniteDimensional.of_finrank_pos
  change Module.finrank ℚ_[p] (ddrTensorOver p ρ) =
    Module.finrank ℚ_[p] F * Module.finrank ℚ_[p] V at h
  rw [h]
  exact Nat.mul_pos Module.finrank_pos Module.finrank_pos

end
end ZInQ.Contrib.PadicDeRhamScalars
