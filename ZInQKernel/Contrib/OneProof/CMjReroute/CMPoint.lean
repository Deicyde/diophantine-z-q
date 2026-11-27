import ZInQKernel.Contrib.OneProof.CMjReroute.Dictionary
import ZInQKernel.Contrib.OneProof.CMFibreSplit.CurveOrder

/-!
# The CM point at a representative

Let `Q/ℂ` be a QM abelian surface uniformized `ι`-compatibly by `Λ_τ = ι(𝒪)(τ, 1)ᵀ`, and let
`φ ∈ End_𝒪(Q)` not be an integer. The analytic representation gives `β ∈ 𝒪` with
`ι(β)(τ, 1)ᵀ = λ(τ, 1)ᵀ` (`RayClassCFT.cmAnalytic_of`). Then:

* `β ∉ ℚ`: otherwise `β ∈ 𝒪 ∩ ℚ = ℤ`, and `φ − β` has analytic representation `0`, so `φ = β`;
* the pure part `β₀ = β − Re β` satisfies `β₀² = d ∈ ℚ` and `ι(β₀)(τ, 1)ᵀ = mu(τ, 1)ᵀ`, `mu = λ − Re β`,
  `mu² = d`; and `d < 0`: if `d ≥ 0` then `mu` is real, and a real eigenvalue of `ι(β₀)` with the non-real
  eigenvector `(τ, 1)ᵀ` forces `β₀ = 0` (`eq_zero_of_eig_real`);
* `q : ℚ(√d) → B`, `√d ↦ β₀`, and `κ : √d ↦ mu` make `τ` the CM point of `q` (`exists_cmPoint`), and
  `β = q(Re β + √d)`.
-/

noncomputable section

namespace HDec.CMBranch.CMjReroute

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.LeafQM _root_.LeafQM.AV ShimuraCFT RayClassCFT
open _root_.ZInQ.LeafPush2 (CPts IsUniformization)
open HDec.CMBranch.FibreSplit Polynomial

/-- `𝒪 ∩ ℚ = ℤ`. -/
theorem exists_int_of_inO_rat {r : ℚ} (h : InO (algebraMap ℚ LeafQM.B r)) : ∃ n : ℤ, r = n := by
  obtain ⟨c, hc⟩ := h
  have e1 := congrArg QuaternionAlgebra.imI hc
  have e2 := congrArg QuaternionAlgebra.imJ hc
  have e3 := congrArg QuaternionAlgebra.imK hc
  have e0 := congrArg QuaternionAlgebra.re hc
  simp [QuaternionAlgebra.algebraMap_eq, LeafQM.ofInt] at e0 e1 e2 e3
  refine ⟨c 0, ?_⟩
  have h2 : (c 2 : ℚ) = 0 := by linarith
  have h3 : (c 3 : ℚ) = 0 := by linarith
  rw [e0, h2]; ring

/-- **A real eigenvalue at a non-real eigenvector**: a pure quaternion `x` with
`ι(x)(τ, 1)ᵀ = mu(τ, 1)ᵀ`, `mu ∈ ℝ`, is `0`. -/
theorem eq_zero_of_eig_real {τ : ℂ} (hτ : τ.im ≠ 0) {x : LeafQM.B} (hre : x.re = 0) {mu : ℂ}
    (hmu : mu.im = 0) (h : Matrix.mulVec (iotaC x) ![τ, 1] = mu • ![τ, 1]) : x = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [iotaC_apply, iota_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hre] at h0 h1
  have i0 := congrArg Complex.im h0
  have r0 := congrArg Complex.re h0
  have i1 := congrArg Complex.im h1
  have r1 := congrArg Complex.re h1
  simp [hmu] at i0 r0 i1 r1
  have hs : (√2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr two_pos
  have hs2 : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  -- row 1, imaginary part
  have a1 : (x.imJ : ℝ) - x.imK * √2 = 0 := by
    rcases i1 with h | h
    · linarith
    · exact absurd h hτ
  -- row 1 real part and row 0 imaginary part
  have a2 : mu.re = -(x.imI * √2) := by
    have : ((x.imJ : ℝ) - x.imK * √2) * τ.re - x.imI * √2 = mu.re := by linarith
    rw [a1, zero_mul, zero_sub] at this; exact this.symm
  have a3 : (x.imI : ℝ) * √2 = mu.re := i0.resolve_right hτ
  have hI : (x.imI : ℝ) = 0 := by
    have : (x.imI : ℝ) * √2 = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hs
  have hmur : mu.re = 0 := by rw [← a3, hI, zero_mul]
  -- row 0 real part
  have a4 : -3 * (x.imJ : ℝ) - 3 * x.imK * √2 = 0 := by
    have : (x.imI : ℝ) * √2 * τ.re + (-3 * x.imJ - 3 * x.imK * √2) = mu.re * τ.re := by linarith
    rw [hI, hmur] at this; linarith
  have hK : (x.imK : ℝ) = 0 := by
    have : (x.imK : ℝ) * √2 = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hs
  have hJ : (x.imJ : ℝ) = 0 := by rw [hK, zero_mul, sub_zero] at a1; exact a1
  ext <;> simp_all

/-- A complex number whose square is a nonnegative real is real. -/
theorem im_eq_zero_of_sq {mu : ℂ} {d : ℝ} (hd : 0 ≤ d) (h : mu * mu = d) : mu.im = 0 := by
  have hi := congrArg Complex.im h
  have hr := congrArg Complex.re h
  simp at hi hr
  by_contra hne
  have hre : mu.re = 0 := by
    have : mu.re * mu.im * 2 = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact (mul_eq_zero.mp h').resolve_right hne
    · norm_num at h'
  rw [hre] at hr
  have : 0 < mu.im * mu.im := mul_self_pos.mpr hne
  linarith

/-- The pure part of a quaternion of `B = (2, −3 | ℚ)` squares to a rational number. -/
theorem pure_sq (β : LeafQM.B) :
    (β - algebraMap ℚ LeafQM.B β.re) * (β - algebraMap ℚ LeafQM.B β.re) =
      algebraMap ℚ LeafQM.B (2 * β.imI ^ 2 - 3 * β.imJ ^ 2 + 6 * β.imK ^ 2) := by
  ext <;> simp [QuaternionAlgebra.algebraMap_eq] <;> ring

/-- The lift of an integer endomorphism is the scalar. -/
theorem liftM_intCast (hHL : ZInQ.HomUnify.HomLinearLift) {τ : UpperHalfPlane} {Q : QML3 ℂ}
    {Φu : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ)}
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu) (n : ℤ) :
    liftM hHL hU ((n : PkgI3.AbVar.End Q.A)) = (n : ℂ) • LinearMap.id := by
  have hneg1 : liftM hHL hU (-1 : PkgI3.AbVar.End Q.A) = -LinearMap.id := by
    have h := liftM_add hHL hU (1 : PkgI3.AbVar.End Q.A) (-1)
    rw [add_neg_cancel, liftM_zero, liftM_one] at h
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h.symm
  induction n using Int.induction_on with
  | zero => simp [liftM_zero]
  | succ k ih =>
    rw [Int.cast_add, Int.cast_one, liftM_add, ih, liftM_one, Int.cast_add, Int.cast_one, add_smul,
      one_smul]
  | pred k ih =>
    rw [Int.cast_sub, Int.cast_one, sub_eq_add_neg, liftM_add, ih, hneg1, Int.cast_sub,
      Int.cast_one, sub_eq_add_neg, add_smul, neg_smul, one_smul]

/-- **The CM point at a representative.** -/
theorem exists_cmPoint (hcorr : ZInQ.HomUnify.HomLatticeCorr) {τ : UpperHalfPlane} {Q : QML3 ℂ}
    {Φu : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ)}
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu)
    (hι : HDec.HSyn.G0Split.FibreQM.IotaCompatible Q Φu) {φ : PkgI3.AbVar.End Q.A}
    (hφ : φ ∈ com Q.q) (hne : ∀ n : ℤ, φ ≠ (n : PkgI3.AbVar.End Q.A)) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyComplex K),
      Module.finrank ℚ K = 2 ∧ ∃ (q : K →ₐ[ℚ] LeafQM.B) (κ : K →+* ℂ), IsCMPoint q κ τ := by
  have hτ := τ.im_pos.ne'
  have hHL := ZInQ.HomUnify.homLinearLift_of_corr hcorr
  set v : Fin 2 → ℂ := ![(τ : ℂ), 1] with hv
  set lam : ℂ := liftM hHL hU φ ![1, 0] 0
  have hlam : ∀ z, liftM hHL hU φ z = lam • z := fun z => liftM_scalar hHL hU hι hφ z
  have hmem : lam • v ∈ LamT τ := by
    rw [← hlam v, ← hU.2.1, liftM_spec hHL hU, (hU.2.1 v).2 (qmVec0_mem hτ)]
    exact MonObj.one_comp _
  obtain ⟨β, hβO, hβ⟩ := exists_of_mem_qmLattice hτ hmem
  -- `β ∉ ℚ`
  have hnotrat : β ∉ Set.range (algebraMap ℚ LeafQM.B) := by
    rintro ⟨r, rfl⟩
    obtain ⟨n, rfl⟩ := exists_int_of_inO_rat hβO
    apply hne n
    have hl : lam = n := by
      have h1 := congrFun hβ 1
      rw [AlgHom.commutes, Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal] at h1
      simpa [hv] using h1.symm
    apply end_eq_of_lift (N := (n : ℂ) • LinearMap.id) hcorr hU
    · intro z
      show Φu ((n : ℂ) • z) = _
      rw [← hl, ← hlam z, liftM_spec hHL hU]
    · intro z
      show Φu ((n : ℂ) • z) = _
      have := liftM_spec hHL hU ((n : PkgI3.AbVar.End Q.A)) z
      rw [liftM_intCast hHL hU n] at this
      simpa using this
  -- the pure part
  set β₀ := β - algebraMap ℚ LeafQM.B β.re with hβ₀def
  set d : ℚ := 2 * β.imI ^ 2 - 3 * β.imJ ^ 2 + 6 * β.imK ^ 2 with hd_def
  set mu : ℂ := lam - (β.re : ℂ) with hmudef
  have hsq : β₀ * β₀ = algebraMap ℚ LeafQM.B d := pure_sq β
  have hre0 : β₀.re = 0 := by simp [hβ₀def, QuaternionAlgebra.algebraMap_eq]
  have heig0 : Matrix.mulVec (iotaC β₀) v = mu • v := by
    rw [hβ₀def, map_sub, Matrix.sub_mulVec, hβ, AlgHom.commutes]
    ext i
    rw [Pi.sub_apply, Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]
    simp [hmudef, sub_mul, Pi.algebraMap_apply]
  have hb : β₀ * β₀ + (0 : ℚ) • β₀ + algebraMap ℚ LeafQM.B (-d) = 0 := by
    rw [hsq, zero_smul, add_zero, ← map_add, add_neg_cancel, map_zero]
  have hmu : mu * mu + (0 : ℚ) • mu + algebraMap ℚ ℂ (-d) = 0 := eig_rel (by simp [hv]) heig0 hb
  have hmusq : mu * mu = ((d : ℝ) : ℂ) := by
    have : mu * mu = algebraMap ℚ ℂ d := by
      rw [zero_smul, add_zero, map_neg] at hmu; linear_combination hmu
    rw [this]; simp
  -- `d < 0`
  have hd : d < 0 := by
    by_contra hcon
    push Not at hcon
    have him := im_eq_zero_of_sq (by exact_mod_cast hcon) hmusq
    have h0 := eq_zero_of_eig_real hτ hre0 him heig0
    apply hnotrat
    exact ⟨β.re, (sub_eq_zero.mp h0).symm⟩
  have := fact_irr hd
  have := numberField_kd hd
  have := isTotallyComplex_kd hd
  have hk := finrank_kd hd
  set y : Kd d := AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d : ℚ[X])
  have hy : ∀ r : ℚ, y ≠ r := fun r h => root_not_rat hd ⟨r, by rw [eq_ratCast]; exact h.symm⟩
  have hyq : y * y + ((0 : ℚ) : Kd d) * y + ((-d : ℚ) : Kd d) = 0 := by
    have := root_sq (d := d)
    rw [pow_two] at this
    rw [this]; push_cast; simp
  let q : Kd d →ₐ[ℚ] LeafQM.B := liftQuad hk hy hyq β₀ hb
  let κA : Kd d →ₐ[ℚ] ℂ := liftQuad hk hy hyq mu hmu
  refine ⟨Kd d, inferInstance, inferInstance, inferInstance, hk, q, κA.toRingHom, fun a => ?_⟩
  obtain ⟨r, s, rfl⟩ := exists_rat_repr hk hy a
  show Matrix.mulVec (iotaC (q _)) _ = _
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, liftQuad_apply, liftQuad_apply, map_add,
    AlgHom.commutes, map_smul, Matrix.add_mulVec, Matrix.smul_mulVec, heig0]
  ext i
  fin_cases i
  · simp [hv, Matrix.algebraMap_eq_diagonal, Algebra.smul_def]; ring
  · simp [hv, Matrix.algebraMap_eq_diagonal, Algebra.smul_def]

end HDec.CMBranch.CMjReroute
