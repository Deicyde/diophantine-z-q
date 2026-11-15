import RayGlueI
import ZInQKernel.Contrib.HomUnify.Corr

/-! # rayclass-cft, Part G3: the glue `CMAnalytic` from the bundle's textbook leaf `HomLinearLift`

`HomLinearLift` (hom-unify, the lifting half of T11(a); a field of the bundle through
`HomLatticeCorr`): every endomorphism `f` of `Q.A` lifts to a `ℂ`-linear `M` with `Φ(Mz) = f(Φ z)`.
The lift is unique (a `ℂ`-subspace of the countable lattice is `0`), so `f ↦ M_f` is a ring map;
for `f ∈ End_𝒪(Q)` it commutes with `ι(i)`, `ι(j)`, hence is a scalar `λ_f`; `λ_f(τ, 1)ᵀ ∈ Λ_τ`
gives a unique `β_f ∈ 𝒪` with `ι(β_f)(τ, 1)ᵀ = λ_f(τ, 1)ᵀ`. -/

set_option linter.all false

noncomputable section

namespace RayClassCFT

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV ShimuraCFT
open ZInQ.LeafPush2 (CPts IsUniformization)

/-! ## G3a. The lattice `Λ_τ` -/

theorem qmLattice_countable {τ : ℂ} (hτ : τ.im ≠ 0) :
    (BPAnalytic.QM.qmLattice hτ : Set (Fin 2 → ℂ)).Countable := by
  refine (Set.countable_range (fun c : Fin 4 → ℤ => ∑ i, c i • BPAnalytic.QM.qmVec τ i)).mono ?_
  intro x hx
  rw [SetLike.mem_coe, BPAnalytic.QM.qmLattice_eq, Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, hc⟩ := hx
  exact ⟨c, hc⟩

/-- A `ℂ`-linear map with values in `Λ_τ` is `0`. -/
theorem linear_eq_zero_of_mem {τ : ℂ} (hτ : τ.im ≠ 0) (N : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))
    (h : ∀ z, N z ∈ BPAnalytic.QM.qmLattice hτ) : N = 0 := by
  refine LinearMap.ext fun z => ?_
  by_contra hz
  have hc := qmLattice_countable hτ
  have : (Set.univ : Set ℂ).Countable := by
    have hinj : Function.Injective (fun c : ℂ => c • N z) := smul_left_injective ℂ hz
    refine Set.MapsTo.countable_of_injOn (f := fun c : ℂ => c • N z) ?_ hinj.injOn hc
    intro c _
    have := h (c • z)
    rwa [map_smul] at this
  exact not_countable_complex this

theorem qmVec0_mem {τ : ℂ} (hτ : τ.im ≠ 0) : ![τ, 1] ∈ BPAnalytic.QM.qmLattice hτ := by
  rw [BPAnalytic.QM.qmLattice_eq]
  have := Submodule.subset_span (R := ℤ) (Set.mem_range_self (f := BPAnalytic.QM.qmVec τ) 0)
  rwa [BPAnalytic.QM.qmVec, BPAnalytic.QM.latVec0] at this

/-- `ι(b)(τ, 1)ᵀ` for `b ∈ B`, `τ ∉ ℝ`, is `0` only for `b = 0`. -/
theorem iota_eig_zero {τ : ℂ} (hτ : τ.im ≠ 0) {b : LeafQM.B}
    (h : Matrix.mulVec (iotaC b) ![τ, 1] = 0) : b = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [iotaC_apply, iota_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have i0 := congrArg Complex.im h0
  have r0 := congrArg Complex.re h0
  have i1 := congrArg Complex.im h1
  have r1 := congrArg Complex.re h1
  simp at i0 r0 i1 r1
  have hs : (√2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr two_pos
  have a1 : (b.re : ℝ) + b.imI * √2 = 0 := i0.resolve_right hτ
  have a2 : (b.imJ : ℝ) - b.imK * √2 = 0 := i1.resolve_right hτ
  have a3 : (b.re : ℝ) - b.imI * √2 = 0 := by
    have : (b.imJ - b.imK * √2) * τ.re + (b.re - b.imI * √2) = (0 : ℝ) := by linear_combination r1
    rw [a2, zero_mul, zero_add] at this; exact this
  have a4 : -3 * (b.imJ : ℝ) - 3 * b.imK * √2 = 0 := by
    have : (b.re + b.imI * √2) * τ.re + (-3 * b.imJ - 3 * b.imK * √2) = (0 : ℝ) := by
      linear_combination r0
    rw [a1, zero_mul, zero_add] at this; exact this
  have hre : (b.re : ℝ) = 0 := by linear_combination (a1 + a3) / 2
  have himI : (b.imI : ℝ) = 0 := by
    have : (b.imI : ℝ) * √2 = 0 := by linear_combination (a1 - a3) / 2
    exact (mul_eq_zero.mp this).resolve_right hs
  have himK : (b.imK : ℝ) = 0 := by
    have : (b.imK : ℝ) * √2 = 0 := by linear_combination -(a4 + 3 * a2) / 6
    exact (mul_eq_zero.mp this).resolve_right hs
  have himJ : (b.imJ : ℝ) = 0 := by linear_combination a2 + √2 * himK
  ext <;> simp_all

theorem iota_eig_inj {τ : ℂ} (hτ : τ.im ≠ 0) {b b' : LeafQM.B}
    (h : Matrix.mulVec (iotaC b) ![τ, 1] = Matrix.mulVec (iotaC b') ![τ, 1]) : b = b' := by
  rw [← sub_eq_zero]
  apply iota_eig_zero hτ
  rw [map_sub, Matrix.sub_mulVec, h, sub_self]

/-- Elements of `Λ_τ` are `ι(β)(τ, 1)ᵀ` with `β ∈ 𝒪`. -/
theorem exists_of_mem_qmLattice {τ : ℂ} (hτ : τ.im ≠ 0) {x : Fin 2 → ℂ}
    (hx : x ∈ BPAnalytic.QM.qmLattice hτ) :
    ∃ β : LeafQM.B, InO β ∧ Matrix.mulVec (iotaC β) ![τ, 1] = x := by
  rw [BPAnalytic.QM.qmLattice_eq, Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  refine ⟨LeafQM.ofInt c, ⟨c, rfl⟩, ?_⟩
  have e : LeafQM.ofInt c = ∑ i, c i • BPAnalytic.QM.oBasis i := by
    ext <;> simp [LeafQM.ofInt, BPAnalytic.QM.oBasis, Fin.sum_univ_four] <;> ring
  rw [e, map_sum, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Matrix.smul_mulVec]
  rfl

/-! ## G3b. The analytic representation on `End_𝒪(Q)` -/

section Lift

variable {τ : UpperHalfPlane} {Q : QML3 ℂ} {Φu : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ)}

abbrev LamT (τ : UpperHalfPlane) := BPAnalytic.QM.qmLattice τ.im_pos.ne'

theorem lift_unique (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu)
    {M M' : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)} (h : ∀ z, Φu (M z) = Φu (M' z)) : M = M' := by
  have hz : ∀ z, (M - M') z ∈ LamT τ := fun z => by
    rw [← hU.2.1]
    have e := hU.1 ((M - M') z) (M' z)
    rw [LinearMap.sub_apply, sub_add_cancel, h z] at e
    first
    | exact left_eq_mul.1 e
    | exact (self_eq_mul_left.1 e)
    | exact (mul_eq_right.1 e.symm)
  exact sub_eq_zero.1 (linear_eq_zero_of_mem τ.im_pos.ne' (M - M') hz)

theorem dim_two (Q : QML3 ℂ) : Q.A.dim = ((2 : ℕ) : WithBot ℕ∞) := by
  rw [Q.surface]; rfl

/-- The lift `M_f` of an endomorphism (`HomLinearLift`). -/
def liftM (hHL : ZInQ.HomUnify.HomLinearLift) (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu)
    (f : PkgI3.AbVar.End Q.A) : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
  (hHL ℂ Q.A Q.A (RingHom.id ℂ) 2 2 (LamT τ) (LamT τ) Φu Φu (dim_two Q) (dim_two Q) hU hU f).choose

theorem liftM_spec (hHL : ZInQ.HomUnify.HomLinearLift)
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu) (f : PkgI3.AbVar.End Q.A) (z : Fin 2 → ℂ) :
    Φu (liftM hHL hU f z) = Φu z ≫ f.hom :=
  (hHL ℂ Q.A Q.A (RingHom.id ℂ) 2 2 (LamT τ) (LamT τ) Φu Φu (dim_two Q) (dim_two Q) hU hU f).choose_spec z

theorem liftM_mul (hHL : ZInQ.HomUnify.HomLinearLift)
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu) (f g : PkgI3.AbVar.End Q.A) :
    liftM hHL hU (f * g) = liftM hHL hU f ∘ₗ liftM hHL hU g := by
  refine lift_unique hU fun z => ?_
  rw [liftM_spec hHL hU, LinearMap.comp_apply, liftM_spec hHL hU, liftM_spec hHL hU, Category.assoc]
  rfl

theorem liftM_add (hHL : ZInQ.HomUnify.HomLinearLift)
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu) (f g : PkgI3.AbVar.End Q.A) :
    liftM hHL hU (f + g) = liftM hHL hU f + liftM hHL hU g := by
  refine lift_unique hU fun z => ?_
  rw [liftM_spec hHL hU, LinearMap.add_apply, hU.1, liftM_spec hHL hU, liftM_spec hHL hU, PkgI3.AbVar.Hom.hom_add,
    MonObj.comp_mul]

theorem liftM_one (hHL : ZInQ.HomUnify.HomLinearLift)
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu) :
    liftM hHL hU (1 : PkgI3.AbVar.End Q.A) = LinearMap.id := by
  refine lift_unique hU fun z => ?_
  rw [liftM_spec hHL hU, LinearMap.id_apply]
  exact Category.comp_id _

theorem liftM_zero (hHL : ZInQ.HomUnify.HomLinearLift)
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu) :
    liftM hHL hU (0 : PkgI3.AbVar.End Q.A) = 0 := by
  refine lift_unique hU fun z => ?_
  rw [liftM_spec hHL hU, LinearMap.zero_apply, PkgI3.AbVar.Hom.hom_zero, MonObj.comp_one]
  exact ((hU.2.1 0).2 (Submodule.zero_mem _)).symm

/-- `ι(i)`, `ι(j)` as elements of `𝒪`. -/
def oI : LeafQM.O := ⟨⟨0, 1, 0, 0⟩, ⟨![0, 1, 0, 0], by ext <;> simp [LeafQM.ofInt]⟩⟩
def oJ : LeafQM.O := ⟨⟨0, 0, 1, 0⟩, ⟨![-1, 0, 2, 0], by ext <;> simp [LeafQM.ofInt]⟩⟩

theorem liftM_comm (hHL : ZInQ.HomUnify.HomLinearLift)
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu)
    (hι : HDec.HSyn.G0Split.FibreQM.IotaCompatible Q Φu) {φ : PkgI3.AbVar.End Q.A}
    (hφ : φ ∈ com Q.q) (a : LeafQM.O) (z : Fin 2 → ℂ) :
    liftM hHL hU φ ((HDec.HSyn.G0Split.FibreQM.qmMat a).mulVec z) =
      (HDec.HSyn.G0Split.FibreQM.qmMat a).mulVec (liftM hHL hU φ z) := by
  have h := congrArg (fun M => M z) (lift_unique hU (M := liftM hHL hU φ ∘ₗ
    Matrix.mulVecLin (HDec.HSyn.G0Split.FibreQM.qmMat a))
    (M' := Matrix.mulVecLin (HDec.HSyn.G0Split.FibreQM.qmMat a) ∘ₗ liftM hHL hU φ) fun z => by
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply]
      rw [liftM_spec hHL hU, hι, hι, liftM_spec hHL hU, Category.assoc, Category.assoc]
      have hc := (Subring.mem_centralizer_iff.1 hφ) (Q.q.iota a) ⟨a, rfl⟩
      have := congrArg PkgI3.AbVar.Hom.hom hc
      exact congrArg (fun g => Φu z ≫ g) this.symm)
  simpa using h

theorem qmMat_oI : HDec.HSyn.G0Split.FibreQM.qmMat oI = !![(√2 : ℂ), 0; 0, -(√2 : ℂ)] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [HDec.HSyn.G0Split.FibreQM.qmMat, oI, iota_eq]

theorem qmMat_oJ : HDec.HSyn.G0Split.FibreQM.qmMat oJ = !![(0 : ℂ), -3; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [HDec.HSyn.G0Split.FibreQM.qmMat, oJ, iota_eq]

/-- **Lifts of `End_𝒪` are scalars.** -/
theorem liftM_scalar (hHL : ZInQ.HomUnify.HomLinearLift)
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu)
    (hι : HDec.HSyn.G0Split.FibreQM.IotaCompatible Q Φu) {φ : PkgI3.AbVar.End Q.A}
    (hφ : φ ∈ com Q.q) (z : Fin 2 → ℂ) :
    liftM hHL hU φ z = (liftM hHL hU φ ![1, 0] 0) • z := by
  set M := liftM hHL hU φ
  have hs : (√2 : ℂ) ≠ 0 := BPAnalytic.QM.sqrt2_ne_zero
  have hI0 := liftM_comm hHL hU hι hφ oI ![1, 0]
  have hI1 := liftM_comm hHL hU hι hφ oI ![0, 1]
  have hJ0 := liftM_comm hHL hU hι hφ oJ ![1, 0]
  rw [qmMat_oI] at hI0 hI1
  rw [qmMat_oJ] at hJ0
  have e0 : (!![(√2 : ℂ), 0; 0, -(√2 : ℂ)]).mulVec ![1, 0] = (√2 : ℂ) • ![1, 0] := by
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct]
  have e1 : (!![(√2 : ℂ), 0; 0, -(√2 : ℂ)]).mulVec ![0, 1] = (-(√2 : ℂ)) • ![0, 1] := by
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct]
  have eJ : (!![(0 : ℂ), -3; 1, 0]).mulVec ![1, 0] = ![0, 1] := by
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct]
  rw [e0, map_smul] at hI0
  rw [e1, map_smul] at hI1
  rw [eJ] at hJ0
  have u1 : M ![1, 0] 1 = 0 := by
    have := congrFun hI0 1
    simp [Matrix.mulVec, dotProduct] at this
    have h2 : (√2 : ℂ) * (2 * M ![1, 0] 1) = 0 := by linear_combination this
    have := (mul_eq_zero.mp h2).resolve_left hs
    linear_combination this / 2
  have w0 : M ![0, 1] 0 = 0 := by
    have := congrFun hI1 0
    simp [Matrix.mulVec, dotProduct] at this
    have h2 : (√2 : ℂ) * (2 * M ![0, 1] 0) = 0 := by linear_combination -this
    have := (mul_eq_zero.mp h2).resolve_left hs
    linear_combination this / 2
  have w1 : M ![0, 1] 1 = M ![1, 0] 0 := by
    have := congrFun hJ0 1
    simpa [Matrix.mulVec, dotProduct] using this
  have hz : z = z 0 • ![1, 0] + z 1 • ![0, 1] := by
    ext i; fin_cases i <;> simp
  rw [hz, map_add, map_smul, map_smul]
  ext i; fin_cases i <;> simp [u1, w0, w1] <;> ring

end Lift

/-! ## G3c. `CMAnalytic` -/

/-- **The glue `CMAnalytic`, proved from the bundle's textbook leaf `HomLinearLift`.** -/
theorem cmAnalytic_of (hHL : ZInQ.HomUnify.HomLinearLift) : CMAnalytic := by
  intro τ Q Φu hU hι
  have hτ := τ.im_pos.ne'
  set v : Fin 2 → ℂ := ![(τ : ℂ), 1]
  let lam : PkgI3.AbVar.End Q.A → ℂ := fun f => liftM hHL hU f ![1, 0] 0
  have hlam : ∀ φ : com Q.q, ∀ z, liftM hHL hU φ z = lam φ • z :=
    fun φ z => liftM_scalar hHL hU hι φ.2 z
  -- `λ_φ (τ, 1)ᵀ ∈ Λ_τ`
  have hmem : ∀ φ : com Q.q, lam φ • v ∈ LamT τ := fun φ => by
    rw [← hlam φ v, ← hU.2.1, liftM_spec hHL hU, (hU.2.1 v).2 (qmVec0_mem hτ)]
    exact MonObj.one_comp _
  choose β hβO hβ using fun φ : com Q.q => exists_of_mem_qmLattice hτ (hmem φ)
  -- `λ` on products, sums, `1`, `0`
  have lam_mul : ∀ φ ψ : com Q.q,
      lam ((φ * ψ : com Q.q) : PkgI3.AbVar.End Q.A) = lam φ * lam ψ := by
    intro φ ψ
    have h := congrArg (fun M => M ![1, 0]) (liftM_mul hHL hU φ ψ)
    simp only [LinearMap.comp_apply] at h
    rw [hlam ψ, map_smul, hlam φ] at h
    show liftM hHL hU ((φ : PkgI3.AbVar.End Q.A) * ψ) ![1, 0] 0 = _
    rw [h]; simp [lam, mul_comm]
  have lam_add : ∀ φ ψ : com Q.q,
      lam ((φ + ψ : com Q.q) : PkgI3.AbVar.End Q.A) = lam φ + lam ψ := by
    intro φ ψ
    have h := congrArg (fun M => M ![1, 0]) (liftM_add hHL hU φ ψ)
    simp only [LinearMap.add_apply] at h
    show liftM hHL hU ((φ : PkgI3.AbVar.End Q.A) + ψ) ![1, 0] 0 = _
    rw [h]; simp [lam]
  have lam_one : lam ((1 : com Q.q) : PkgI3.AbVar.End Q.A) = 1 := by
    show liftM hHL hU 1 ![1, 0] 0 = 1
    rw [liftM_one]; simp
  have lam_zero : lam ((0 : com Q.q) : PkgI3.AbVar.End Q.A) = 0 := by
    show liftM hHL hU 0 ![1, 0] 0 = 0
    rw [liftM_zero]; simp
  refine ⟨{ toFun := β, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ },
    fun φ => ⟨hβO φ, lam φ, hβ φ⟩⟩
  · apply iota_eig_inj hτ
    rw [hβ, lam_one, map_one, Matrix.one_mulVec, one_smul]
  · intro φ ψ
    apply iota_eig_inj hτ
    rw [hβ, lam_mul, map_mul, ← Matrix.mulVec_mulVec, hβ, Matrix.mulVec_smul, hβ, smul_smul,
      mul_comm]
  · apply iota_eig_inj hτ
    rw [hβ, lam_zero, map_zero, Matrix.zero_mulVec, zero_smul]
  · intro φ ψ
    apply iota_eig_inj hτ
    rw [hβ, lam_add, map_add, Matrix.add_mulVec, hβ, hβ, add_smul]

/-- **`RayClassCM` with the glue `RingOfIntegersGen`, `QHatIntegral` and `CMAnalytic` discharged**
(`CMAnalytic` from the bundle's textbook leaf `HomLinearLift`). -/
theorem rayClassCM_of4 (hL : ShimuraMainThmIDeligneY3AbU)
    (hMR : LeafQM.AV.R1UnivRigid.MumfordRigidityCore) (hCN : ClassNumberOneB)
    (hB : CMBaseChange) (hHL : ZInQ.HomUnify.HomLinearLift) : ShimuraGlue.Ray.RayClassCM :=
  rayClassCM_of3 hL hMR hCN hB (cmAnalytic_of hHL)

end RayClassCFT

#print axioms RayClassCFT.cmAnalytic_of
#print axioms RayClassCFT.rayClassCM_of4
