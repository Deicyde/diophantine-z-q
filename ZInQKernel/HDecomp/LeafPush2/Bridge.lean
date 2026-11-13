import ZInQKernel.HDecomp.LeafPush2.R22
import ZInQKernel.HDecomp.Analytic.QMLattice

/-! Glue of `docs/research/h-decomposition.md`, new in task hdec-adopt4 (no draft).
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

/-!
# R22's period-matrix data on bp-analytic's tori

leaf-push2's R22 (`ZInQ.LeafPush2.R22_Pazuki`) quantifies over `Ω` with `IsSiegel Ω` and
`IsPeriodMatrix Λ Ω` and uses `ZInQ.LeafPush2.thetaConst`; bp-analytic (`BPAnalytic`, in
`ZInQKernel/HDecomp/Analytic/`) has the Siegel space `SiegelSpace 2`, the lattices
`periodLattice Ω` and pkg-I1's `thetaConst`. This file identifies them:

* `isSiegel_iff`: `IsSiegel Ω ↔ Ω ∈ SiegelSpace 2` (the same definition);
* `isPeriodMatrix_periodLattice`: `Ω` is a period matrix of `Ωℤ² + ℤ²`;
* `isPeriodMatrix_of_map`: the condition is invariant under `ℂ`-linear isomorphisms;
* `isSiegel_Omega`, `isPeriodMatrix_qmLattice`: for `Im τ > 0`, pkg-I1's `Ω(τ)` is in `𝔥₂` and
  is a period matrix of the QM lattice `ι(𝒪)(τ, 1)ᵀ`, so R22's `Ω`-quantifier is non-empty on
  every QM torus;
* `thetaConst_eq`: leaf-push2's theta constant is pkg-I1's (`2πi·vᵀ(b/2) = πi·vᵀb`).
-/

namespace ZInQ.LeafPush2

open Matrix

/-- leaf-push2's `IsSiegel` is bp-analytic's Siegel space `𝔥₂`. -/
theorem isSiegel_iff (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    IsSiegel Ω ↔ Ω ∈ BPAnalytic.SiegelSpace 2 := Iff.rfl

/-- `Ω` is a period matrix of `Ωℤ² + ℤ²` (with `T = id`). -/
theorem isPeriodMatrix_periodLattice (Ω : Matrix (Fin 2) (Fin 2) ℂ)
    (hΩ : (Ω.map Complex.im).det ≠ 0) :
    IsPeriodMatrix (BPAnalytic.periodLattice Ω hΩ) Ω :=
  ⟨LinearEquiv.refl ℂ _, fun z => by
    simpa using BPAnalytic.mem_periodLattice_iff Ω hΩ z⟩

/-- Transport along a `ℂ`-linear isomorphism: if `Ω` is a period matrix of `Λ` and `F` maps `Λ`
onto `Λ'`, then `Ω` is a period matrix of `Λ'`. -/
theorem isPeriodMatrix_of_map {Λ Λ' : Submodule ℤ (Fin 2 → ℂ)} {Ω : Matrix (Fin 2) (Fin 2) ℂ}
    (h : IsPeriodMatrix Λ Ω) (F : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ))
    (hF : Λ.map (F.toLinearMap.restrictScalars ℤ) = Λ') : IsPeriodMatrix Λ' Ω := by
  obtain ⟨T, hT⟩ := h
  refine ⟨F.symm.trans T, fun z => ?_⟩
  have hz : z ∈ Λ' ↔ F.symm z ∈ Λ := by
    rw [← hF, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hy
      exact ⟨F.symm z, hy, by simp⟩
  rw [hz, hT]
  rfl

/-- pkg-I1's period matrix `Ω(τ)` lies in `𝔥₂` for `Im τ > 0`. -/
theorem isSiegel_Omega {τ : ℂ} (hτ : 0 < τ.im) : IsSiegel (BPAnalytic.QM.Omega τ) :=
  BPAnalytic.QM.Omega_mem_siegelSpace hτ

/-- `Ω(τ)` is a period matrix of the QM lattice `Λ_τ = ι(𝒪)(τ, 1)ᵀ` (`T = F'(τ)⁻¹`). With
`isSiegel_Omega`: on every QM torus `ℂ²/Λ_τ` some `Ω` satisfies R22's hypotheses `IsSiegel Ω`
and `IsPeriodMatrix Λ_τ Ω`. -/
theorem isPeriodMatrix_qmLattice {τ : ℂ} (hτ : τ.im ≠ 0) :
    IsPeriodMatrix (BPAnalytic.QM.qmLattice hτ) (BPAnalytic.QM.Omega τ) :=
  isPeriodMatrix_of_map
    (isPeriodMatrix_periodLattice _ (BPAnalytic.QM.det_im_Omega_ne_zero hτ))
    (BPAnalytic.QM.FpEquiv hτ).toLinearEquiv (BPAnalytic.QM.map_periodLattice_Omega hτ)

/-- leaf-push2's theta constant `θ[a;b](0, Ω)` is pkg-I1's (`BPAnalytic.thetaConst`). -/
theorem thetaConst_eq (Ω : Matrix (Fin 2) (Fin 2) ℂ) (m : Char2) :
    thetaConst Ω m = BPAnalytic.thetaConst m Ω := by
  unfold thetaConst BPAnalytic.thetaConst
  congr 1
  funext n
  congr 2
  have : (fun i => ((m.2 i : ℕ) : ℂ) / 2) = (1 / 2 : ℂ) • fun i => ((m.2 i : ℕ) : ℂ) := by
    funext i; simp [div_eq_inv_mul]
  rw [this, dotProduct_smul, smul_eq_mul]
  ring

end ZInQ.LeafPush2
