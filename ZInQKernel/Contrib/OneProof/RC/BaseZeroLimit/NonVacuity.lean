import ZInQKernel.Contrib.OneProof.RC.BaseZeroLimit.Assembly
import ZInQKernel.Contrib.OneProof.RC.BaseZeroAssembly.NonVacuity

/-!
# Lane RC30 (base zero), part 5: the new hypothesis structures are satisfiable

Every declaration here is `PROVED`.

For the inner limit of (4.5) (`Boundary.lean`):

* `traceStage a`: a `SplitNormStage` with trace `a` (trivial ring-class group, `y_r = a − 2`), so
  the moving multiplier is `m = a − 2`;
* `innerLimit45Base_nonvacuous`: an `InnerLimit45Base` whose stage identities are only
  approximate (the defect at stage `i` is `−2^i ≠ 0`), whose multipliers `m_i = 1 + 2^i` move with
  the stage and converge to `m = 1`, with a nonzero boundary map `d` and a nonzero central cycle
  `z̄ = 1`: the inputs hold together and do not force `z̄ = 0` (for a non-torsion point);
* `retainedStageExample a i`: a `RetainedStage45` at every precision `i` (a Selmer cone with a
  nonzero global boundary, the two local facts, the class identifications and a chain-map model
  projection), so the inputs of `RetainedStage45.exists_witness` (lane RC25's `boundary45_finite`)
  hold together; its witness is forced to be `v ≡ 7`;
* `innerLimit45Base_ofStages_nonvacuous`: the constructor `InnerLimit45Base.ofStages` applies to
  these retained stages with moving traces `a_i = 3 + 2^i`, giving `z̄ = 1 ≠ 0`; through
  `toBoundary45Base` this is a `Boundary45Base` of lane RC25;
* `nonempty_innerLimit45Base_iff` (transparency, as `nonempty_centralSelmerComparison_iff_hcentral`
  for the central comparison): an `InnerLimit45Base`
  exists iff `z̄ = L κ(P)` for some additive `κ` and `L ≠ 0`, the characterization of lane RC25's
  `Boundary45Base`; as abstract inputs the two structures are equivalent, and the gain is that the
  limit statement `hlim` is now proved from the steps of the text (stage boundaries, inner limit,
  comparison), each named with its kind.

For the central comparison (`Central.lean`):

* `centralSelmerComparison_nonvacuous`: a comparison for groups of coranks `1` and `0`
  (`ℚ₂/ℤ₂` and the trivial group) and the zero `1 × 1` model, with `hcentral`;
* `centralSelmerComparison_of_selmer`: under the lemma's hypothesis `SelmerCorankOneOverK ℓ k`,
  a comparison for the genuine Selmer groups of `E_ℓ`, `E_ℓ^{(k)}` and the zero `1 × 1` model.

For the core (`Assembly.lean`):

* `constLimit c`: inner-limit data with central cycle `c`, for any `c ∈ ℚ₂`;
* `baseZeroCoreLimit_nonvacuous`: under `SelmerCorankOneOverK ℓ D.kfin`, for every interface data
  whose base coordinate is (the image of) `f ∈ Λ`, a `BaseZeroCoreLimit` with generic coordinate
  `f` and central cycle `f(0)`; `baseZeroCoreLimit_not_forced`: with `f = 1` neither is zero (the
  specified point `1 ∈ ℤ` is not torsion, so the height formula does not apply). The Heegner data
  of the leaf model are not constructed (unchanged from lanes RC0/RC25).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.BaseZeroLimit

open Filter Topology Matrix Module ZInQ.Manuscript.RC.Limits ZInQ.Manuscript.RC.BaseZeroAssembly
open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
  ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Rings ZInQ.Contrib.CloudB3RC53

/-! ## A stage with any trace -/

/-- The stage with trace `a`: `Δ` trivial, `E(H_r) = E(K) = ℤ`, `y_1 = 1`, `y_r = a − 2`; (4.1)
reads `a − 2 = a − 1 − 1`, and the weighted point is `W = a − 2 = (a − 2) • 1`. -/
def traceStage (a : ℤ) : SplitNormStage (1 : ℤ) where
  Pt := ℤ
  Δ := Unit
  act := 1
  N := ⊤
  decN := fun x => isTrue (Subgroup.mem_top x)
  T := Finset.univ
  hT := fun _ => ⟨(), ⟨Finset.mem_univ _, Subgroup.mem_top _⟩, fun y _ => Subsingleton.elim y ()⟩
  y1 := 1
  hy1 := fun _ _ => rfl
  yr := a - 2
  a := a
  σ := 1
  hnorm := by
    simp only [Finset.sum_filter, Subgroup.mem_top, ite_true, Finset.univ_unique,
      Finset.sum_singleton, MonoidHom.one_apply, Module.End.one_apply, smul_eq_mul, mul_one]
    ring
  incl := AddMonoidHom.id ℤ
  hincl := Function.injective_id
  hP := by simp
  W := a - 2
  hW := by simp

@[simp] theorem traceStage_a (a : ℤ) : (traceStage a).a = a := rfl

@[simp] theorem traceStage_W (a : ℤ) : (traceStage a).W = a - 2 := rfl

/-- The ultralimit of a constant tuple. PROVED. -/
theorem ulimVec_const {N : ℕ} (U : Ultrafilter ℕ) (v : Fin N → ℤ_[2]) :
    ulimVec U (fun _ => v) = v :=
  funext fun a => ulim_const U (v a)

/-- `2^i → 0` in `ℤ₂`, along any nonprincipal ultrafilter. PROVED. -/
theorem ulim_two_pow {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) :
    ulim U (fun i => (2 : ℤ_[2]) ^ i) = 0 :=
  ulim_eq_zero_of_mem twoAdicStage_tendsToZero hU
    (Eventually.of_forall fun _ => mem_twoAdicStage_iff.mpr (dvd_refl _))

/-- `1 + 2^i → 1` in `ℤ₂`. PROVED. -/
theorem ulim_one_add_two_pow {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) :
    ulim U (fun i => 1 + (2 : ℤ_[2]) ^ i) = 1 := by
  rw [ulim_add U (fun _ => (1 : ℤ_[2])) (fun i => (2 : ℤ_[2]) ^ i), ulim_two_pow hU, ulim_one,
    add_zero]

/-- The projection `ℚ₂² → ℚ₂¹` on the first coordinate (a comparison killing the second,
boundary, coordinate). -/
def proj0 : (Fin 2 → ℚ_[2]) →ₗ[ℚ_[2]] (Fin 1 → ℚ_[2]) :=
  LinearMap.pi fun _ => LinearMap.proj 0

@[simp] theorem proj0_apply (x : Fin 2 → ℚ_[2]) (j : Fin 1) : proj0 x j = x 0 := rfl

/-- The `2 × 1` boundary matrix `(0, 1)ᵀ`. -/
def bdMat : Matrix (Fin 2) (Fin 1) ℤ_[2] := !![0; 1]

theorem proj0_bdMat (v : Fin 1 → ℚ_[2]) : proj0 (bdMat.map PadicInt.Coe.ringHom *ᵥ v) = 0 := by
  funext j
  simp [bdMat, Matrix.mulVec, dotProduct]

/-! ## The inner-limit data, with approximate stage identities -/

/-- **The inputs of the inner limit of (4.5) hold together and do not force `z̄ = 0`** (PROVED):
an `InnerLimit45Base` over the group `ℤ` with the non-torsion point `1`, stages with moving traces
`a_i = 3 + 2^i` (`m_i = 1 + 2^i → 1`), the retained data `ζ_i = (1, 1)`, `j_i = (1, 0)`,
`d_i = (0, 1)ᵀ`, `v_i = 1`, the comparison `x ↦ x₀` and `κ(x) = x`. The stage identity at stage
`i` has the nonzero defect `−2^i` (it holds only modulo `2^i`), and the central cycle is `1`. -/
theorem innerLimit45Base_nonvacuous :
    ∃ B : InnerLimit45Base (1 : ℤ) 1 (fun _ => (1 : ℚ_[2])),
      (fun _ : Fin 1 => (1 : ℚ_[2])) ≠ 0 ∧ B.mu = 1 ∧
      (∀ i, (B.stage i).a - 2 = 1 + 2 ^ i) ∧
      (∀ i, ∃ a : Fin B.N, B.zeta i a - ((B.L * ((B.stage i).a - 2) : ℤ) : ℤ_[2]) * B.jay i a -
        (B.dd i *ᵥ B.vv i) a = -(2 : ℤ_[2]) ^ i) ∧
      (∀ i, B.dd i ≠ 0) := by
  refine ⟨{
    U := hyperfilter ℕ
    hU := hyperfilter_le_cofinite
    stage := fun i => traceStage (3 + 2 ^ i)
    L := 1
    hL := one_ne_zero
    N := 2
    M0 := 1
    zeta := fun _ => ![1, 1]
    jay := fun _ => ![1, 0]
    dd := fun _ => bdMat
    vv := fun _ => ![1]
    hstage := Eventually.of_forall fun i a => ?_
    pi0 := proj0
    hpi := ?_
    hz := ?_
    kappa := constKappa 1
    hkappa := ?_ }, fun h => one_ne_zero (congrFun h 0), ?_, fun i => ?_,
    fun i => ⟨⟨0, Nat.zero_lt_two⟩, ?_⟩, fun i h => ?_⟩
  · rw [mem_twoAdicStage_iff]
    fin_cases a
    · refine ⟨-1, ?_⟩
      simp [bdMat, Matrix.mulVec, dotProduct]
      ring
    · exact ⟨0, by simp [bdMat, Matrix.mulVec, dotProduct]⟩
  · intro v
    rw [ulimMat_const]
    exact proj0_bdMat v
  · funext j
    rw [proj0_apply, toQVec, ulimVec_const]
    simp
  · funext j
    rw [proj0_apply, toQVec, ulimVec_const]
    simp [constKappa]
  · change ulim (hyperfilter ℕ) (fun i => ((((3 + 2 ^ i : ℤ) - 2 : ℤ)) : ℤ_[2])) = 1
    have h : (fun i => ((((3 + 2 ^ i : ℤ) - 2 : ℤ)) : ℤ_[2])) = fun i => 1 + (2 : ℤ_[2]) ^ i := by
      funext i
      push_cast
      ring
    rw [h]
    exact ulim_one_add_two_pow hyperfilter_le_cofinite
  · simp only [traceStage_a]
    ring
  · simp [bdMat, Matrix.mulVec, dotProduct]
    ring
  · have := congrFun (congrFun h 1) 0
    simp [bdMat] at this

/-! ## A retained stage at every precision -/

/-- The model projection in degree one of the example cone: `((x, y), u, l) ↦ (x, y) mod 2^i`. -/
def exP1 (i : ℕ) : (ℤ × ℤ) × PUnit × PUnit →+ (Fin 2 → ℤ_[2] ⧸ twoAdicStage i) where
  toFun t := ![Ideal.Quotient.mk (twoAdicStage i) (t.1.1 : ℤ_[2]),
    Ideal.Quotient.mk (twoAdicStage i) (t.1.2 : ℤ_[2])]
  map_zero' := by
    funext j
    fin_cases j <;> simp
  map_add' x y := by
    funext j
    fin_cases j <;> simp

/-- The model projection in degree zero of the example cone: `(v, w) ↦ v mod 2^i`. -/
def exP0 (i : ℕ) : ℤ × PUnit →+ (Fin 1 → ℤ_[2] ⧸ twoAdicStage i) where
  toFun t := ![Ideal.Quotient.mk (twoAdicStage i) (t.1 : ℤ_[2])]
  map_zero' := by
    funext j
    fin_cases j
    simp
  map_add' x y := by
    funext j
    fin_cases j
    simp

/-- **A retained stage at precision `i` for the stage with trace `a`** (PROVED to satisfy every
field): the cone has global cochains `ℤ → ℤ² → 0` with `d g = (0, g)`, class map the first
coordinate (`H¹ = ℤ`, the Kummer map the identity of `E(K) = ℤ`), zero local terms (so the two
local facts hold), the cycle of `z_i(0)` is `(a − 2, 7)` (class `L W = a − 2`, `L = 1`) and that
of `j_i(b₁)` is `(1, 0)` (class `P = 1`); the model projection is the reduction modulo `2^i`, with
model differential `(0, 1)ᵀ`. -/
def retainedStageExample (a : ℤ) (i : ℕ) : RetainedStage45 (1 : ℤ) 1 i 2 1 where
  S := traceStage a
  G0 := ℤ
  G1 := ℤ × ℤ
  G2 := PUnit
  U0 := PUnit
  U1 := PUnit
  U2 := PUnit
  L0 := PUnit
  L1 := PUnit
  H1 := ℤ
  dG0 := AddMonoidHom.inr ℤ ℤ
  dG1 := 0
  dU0 := 0
  dU1 := 0
  dL0 := 0
  loc0 := 0
  loc1 := 0
  ι0 := 0
  ι1 := 0
  hloc := fun _ => rfl
  hι := fun _ => rfl
  honto := fun _ _ => ⟨PUnit.unit, rfl, rfl⟩
  hinj := fun _ _ _ => ⟨PUnit.unit, rfl⟩
  cls := AddMonoidHom.fst ℤ ℤ
  hexact := fun c _ hc => ⟨c.2, Prod.ext (by simpa using hc.symm) rfl⟩
  δ := AddMonoidHom.id ℤ
  zG := (a - 2, 7)
  jG := (1, 0)
  zU := PUnit.unit
  jU := PUnit.unit
  zL := PUnit.unit
  jL := PUnit.unit
  hzG := rfl
  hjG := rfl
  hzU := rfl
  hjU := rfl
  hz := rfl
  hj := rfl
  hzcls := by simp
  hjcls := rfl
  p1 := exP1 i
  p0 := exP0 i
  dC := bdMat
  hdC := fun v w => by
    funext j
    fin_cases j <;> simp [exP1, exP0, bdMat, Matrix.mulVec, dotProduct]
  zeta := ![((a - 2 : ℤ) : ℤ_[2]), 7]
  jay := ![1, 0]
  hzeta := by
    funext j
    fin_cases j <;> simp [exP1, map_ofNat]
  hjay := by
    funext j
    fin_cases j <;> simp [exP1]

/-- **The inputs of `RetainedStage45.exists_witness` hold together** (PROVED): at every precision
`i` and trace `a`, `retainedStageExample a i` is a retained stage; its retained witness exists and
the model differential is nonzero. -/
theorem retainedStage45_nonvacuous (a : ℤ) (i : ℕ) :
    ∃ C : RetainedStage45 (1 : ℤ) 1 i 2 1, C.S.a = a ∧ C.dC ≠ 0 ∧
      ∃ v : Fin 1 → ℤ_[2], ∀ b : Fin 2,
        C.zeta b - ((1 * (C.S.a - 2) : ℤ) : ℤ_[2]) * C.jay b - (C.dC *ᵥ v) b ∈ twoAdicStage i :=
  ⟨retainedStageExample a i, rfl, fun h => by
    have := congrFun (congrFun h 1) 0
    simp [retainedStageExample, bdMat] at this,
    (retainedStageExample a i).exists_witness⟩

/-- **The constructor `InnerLimit45Base.ofStages` applies** (PROVED): with the retained stages
`retainedStageExample (3 + 2^i) i` (moving traces, `m_i = 1 + 2^i`), the comparison `x ↦ x₀` and
`κ(x) = x`, the inner-limit data exist with central cycle `z̄ = 1 ≠ 0`, and lane RC25's
`Boundary45Base` follows through `toBoundary45Base`. -/
theorem innerLimit45Base_ofStages_nonvacuous :
    ∃ B : InnerLimit45Base (1 : ℤ) 1 (fun _ => (1 : ℚ_[2])),
      (fun _ : Fin 1 => (1 : ℚ_[2])) ≠ 0 ∧ B.mu = 1 ∧
      Nonempty (Boundary45Base (1 : ℤ) 1 (fun _ => (1 : ℚ_[2]))) := by
  have hzeta : ulimVec (hyperfilter ℕ) (fun i => (retainedStageExample (3 + 2 ^ i) i).zeta) =
      ![1, 7] := by
    funext j
    fin_cases j
    · change ulim (hyperfilter ℕ) (fun i => ((((3 + 2 ^ i : ℤ) - 2 : ℤ)) : ℤ_[2])) = 1
      have h : (fun i => ((((3 + 2 ^ i : ℤ) - 2 : ℤ)) : ℤ_[2])) =
          fun i => 1 + (2 : ℤ_[2]) ^ i := by
        funext i
        push_cast
        ring
      rw [h]
      exact ulim_one_add_two_pow hyperfilter_le_cofinite
    · exact ulim_const _ _
  have hjay : ulimVec (hyperfilter ℕ) (fun i => (retainedStageExample (3 + 2 ^ i) i).jay) =
      ![1, 0] := ulimVec_const _ _
  have hdC : ulimMat (hyperfilter ℕ) (fun i => (retainedStageExample (3 + 2 ^ i) i).dC) =
      bdMat := ulimMat_const _ _
  let B : InnerLimit45Base (1 : ℤ) 1 (fun _ => (1 : ℚ_[2])) :=
    InnerLimit45Base.ofStages (hyperfilter ℕ) hyperfilter_le_cofinite 1 one_ne_zero 2 1
      (fun i => retainedStageExample (3 + 2 ^ i) i) proj0
      (fun v => by rw [hdC]; exact proj0_bdMat v)
      (by
        funext j
        rw [proj0_apply, toQVec, hzeta]
        simp)
      (constKappa 1)
      (by
        funext j
        rw [proj0_apply, toQVec, hjay]
        simp [constKappa])
  refine ⟨B, fun h => one_ne_zero (congrFun h 0), ?_, ⟨B.toBoundary45Base⟩⟩
  change ulim (hyperfilter ℕ) (fun i => ((((3 + 2 ^ i : ℤ) - 2 : ℤ)) : ℤ_[2])) = 1
  have h : (fun i => ((((3 + 2 ^ i : ℤ) - 2 : ℤ)) : ℤ_[2])) = fun i => 1 + (2 : ℤ_[2]) ^ i := by
    funext i
    push_cast
    ring
  rw [h]
  exact ulim_one_add_two_pow hyperfilter_le_cofinite

/-! ## What the inner-limit data amount to -/

/-- A stage for any specified point `P`: `Δ` trivial, `E(H_r) = E(K)`, `y_1 = y_r = P`, trace
`a = 3` (so `m = 1` and `W = P`). -/
def selfStage {G : Type} [AddCommGroup G] (P : G) : SplitNormStage P where
  Pt := G
  Δ := Unit
  act := 1
  N := ⊤
  decN := fun x => isTrue (Subgroup.mem_top x)
  T := Finset.univ
  hT := fun _ => ⟨(), ⟨Finset.mem_univ _, Subgroup.mem_top _⟩, fun y _ => Subsingleton.elim y ()⟩
  y1 := P
  hy1 := fun _ _ => rfl
  yr := P
  a := 3
  σ := 1
  hnorm := by
    simp only [Finset.sum_filter, Subgroup.mem_top, ite_true, Finset.univ_unique,
      Finset.sum_singleton, MonoidHom.one_apply, Module.End.one_apply, inv_one]
    abel
  incl := AddMonoidHom.id G
  hincl := Function.injective_id
  hP := by simp
  W := P
  hW := by simp

/-- A vector of `ℚ₂ⁿ` becomes integral after multiplication by a power of two. PROVED. -/
theorem exists_two_pow_integral {n : ℕ} (v : Fin n → ℚ_[2]) :
    ∃ K : ℕ, ∀ a, ‖(2 : ℚ_[2]) ^ K * v a‖ ≤ 1 := by
  choose k hk using fun a => exists_two_pow_mul_norm_le_one (v a)
  refine ⟨∑ b, k b, fun a => ?_⟩
  have hle : k a ≤ ∑ b, k b := Finset.single_le_sum (fun b _ => Nat.zero_le _) (Finset.mem_univ a)
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact norm_mul_le_one (norm_two_pow_le_one _) (hk a)

/-- **What the inner-limit data amount to** (transparency, as
`nonempty_centralSelmerComparison_iff_hcentral` for the central comparison; the same
characterization holds for lane RC25's `Boundary45Base`: forward by `Boundary45Base.h45`, backward
by this theorem and `InnerLimit45Base.toBoundary45Base`): `InnerLimit45Base P n z̄` is inhabited
iff `z̄ = L κ(P)` for
an additive `κ : G → ℚ₂ⁿ` and an integer `L ≠ 0`. The forward direction is `central` (with
`κ := m κ`); for the converse, constant stages of trace `3`, the integral data `2^K κ(P)` and the
comparison `2^{-K}`. So for a torsion specified point the inputs are equivalent to `z̄ = 0`, as for
lane RC25. PROVED. -/
theorem nonempty_innerLimit45Base_iff {G : Type} [AddCommGroup G] {P : G} {n : ℕ}
    {zbar : Fin n → ℚ_[2]} :
    Nonempty (InnerLimit45Base P n zbar) ↔
      ∃ (κ : G →+ (Fin n → ℚ_[2])) (L : ℤ), L ≠ 0 ∧ zbar = (L : ℚ_[2]) • κ P := by
  constructor
  · rintro ⟨B⟩
    refine ⟨(DistribSMul.toAddMonoidHom (Fin n → ℚ_[2]) (B.mu : ℚ_[2])).comp B.kappa, B.L, B.hL,
      ?_⟩
    simpa using B.central
  · rintro ⟨κ, L, hL, hz⟩
    obtain ⟨K, hK⟩ := exists_two_pow_integral (κ P)
    let j : Fin n → ℤ_[2] := fun a => ⟨(2 : ℚ_[2]) ^ K * κ P a, hK a⟩
    have hj : toQVec j = (2 : ℚ_[2]) ^ K • κ P := rfl
    have h2 : ((2 : ℚ_[2]) ^ K) ≠ 0 := pow_ne_zero _ two_ne_zero
    refine ⟨{
      U := hyperfilter ℕ
      hU := hyperfilter_le_cofinite
      stage := fun _ => selfStage P
      L := L
      hL := hL
      N := n
      M0 := 0
      zeta := fun _ => (L : ℤ_[2]) • j
      jay := fun _ => j
      dd := fun _ => 0
      vv := fun _ => 0
      hstage := Eventually.of_forall fun i a => ?_
      pi0 := ((2 : ℚ_[2]) ^ K)⁻¹ • LinearMap.id
      hpi := fun v => by simp
      hz := ?_
      kappa := κ
      hkappa := ?_ }⟩
    · simp only [selfStage, Pi.smul_apply, smul_eq_mul, Matrix.zero_mulVec, Pi.zero_apply,
        sub_zero]
      push_cast
      ring_nf
      exact Ideal.zero_mem _
    · rw [ulimVec_const]
      have hzj : toQVec ((L : ℤ_[2]) • j) = (L : ℚ_[2]) • toQVec j := by
        funext a
        simp [toQVec]
      rw [hzj, hj, hz]
      simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
      rw [mul_comm ((2 : ℚ_[2]) ^ K)⁻¹, mul_assoc, mul_inv_cancel₀ h2, mul_one]
    · rw [ulimVec_const, hj]
      simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
      rw [inv_mul_cancel₀ h2, one_smul]

/-! ## The central comparison -/

/-- The zero `1 × 1` model has one-dimensional central kernel. PROVED. -/
theorem finrank_ker_zero_model :
    finrank ℚ_[2] (LinearMap.ker
      ((0 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) Rings.LambdaT).map Rings.rhoT).mulVecLin) = 1 :=
  finrank_ker_of_rank_eq _ (by rw [Matrix.map_zero _ (map_zero _), Matrix.rank_zero])

/-- **The comparison input holds together with its use** (PROVED): for `S₁ = ℚ₂/ℤ₂` (corank `1`),
`S₂` trivial (corank `0`) and the zero `1 × 1` model, a `CentralSelmerComparison` exists, and its
`hcentral` holds. -/
theorem centralSelmerComparison_nonvacuous :
    ∃ _ : CentralSelmerComparison Q2Z2 PUnit
      (0 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) Rings.LambdaT),
      ((0 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) Rings.LambdaT).map Rings.rhoT).rank = 0 := by
  obtain ⟨C⟩ := (nonempty_centralSelmerComparison_iff z2Corank_Q2Z2_one
    z2Corank_punit_zero).mpr finrank_ker_zero_model
  exact ⟨C, C.hcentral z2Corank_Q2Z2_one z2Corank_punit_zero⟩

/-- **The comparison for the genuine Selmer groups, under the lemma's hypothesis** (PROVED): if
`SelmerCorankOneOverK ℓ k`, a `CentralSelmerComparison` for `Sel_{2^∞}(E_ℓ/ℚ)`,
`Sel_{2^∞}(E_ℓ^{(k)}/ℚ)` and the zero `1 × 1` model exists. -/
theorem centralSelmerComparison_of_selmer {ℓ : ℕ} {k : ℤ} (hSel : SelmerCorankOneOverK ℓ k) :
    Nonempty (CentralSelmerComparison (selmerTwoPower (Ecurve ℓ)) (selmerTwoPower (Etw ℓ k))
      (0 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) Rings.LambdaT)) :=
  (nonempty_centralSelmerComparison_iff hSel.1 hSel.2).mpr finrank_ker_zero_model

/-! ## The core -/

/-- Inner-limit data with central cycle `c`, for any `c ∈ ℚ₂`: constant stages of trace `3`
(`m = 1`), `L = 1`, the cycles `ζ = j = 1`, no degree-zero term, the comparison `x ↦ c x` and
`κ(x) = x c`. -/
def constLimit (c : ℚ_[2]) : InnerLimit45Base (1 : ℤ) 1 (fun _ => c) where
  U := hyperfilter ℕ
  hU := hyperfilter_le_cofinite
  stage := fun _ => traceStage 3
  L := 1
  hL := one_ne_zero
  N := 1
  M0 := 0
  zeta := fun _ _ => 1
  jay := fun _ _ => 1
  dd := fun _ => 0
  vv := fun _ => 0
  hstage := Eventually.of_forall fun _ _ => by
    simp only [traceStage_a, Matrix.zero_mulVec, Pi.zero_apply, sub_zero]
    norm_num
  pi0 := c • LinearMap.id
  hpi := fun v => by simp
  hz := by
    rw [ulimVec_const]
    funext j
    simp [toQVec]
  kappa := constKappa c
  hkappa := by
    rw [ulimVec_const]
    funext j
    simp [toQVec, constKappa]

/-- **The base-zero core with the inner limit and the central comparison is satisfiable**
(PROVED), under the lemma's hypothesis `SelmerCorankOneOverK ℓ D.kfin`: if `D.uPrim F 0` is the
image of `f ∈ Λ`, there is a `BaseZeroCoreLimit D F 1` whose degree-one/two matrix window is
`[A --0--> A]` (the stored complex `threeTermComplex 0 0` has `A` in degrees `0, 1, 2` and zero
differentials), the cycle `z = f`, the functional `1`, generic coordinate `f` and central cycle
`f(0)`. The example lives at the infinite-order point `1 ∈ ℤ` of `G = ℤ` (not a point of `E(K)`;
the Heegner data are not constructed). At a torsion point the core forces `u_{prim,0}(0) = 0`. -/
theorem baseZeroCoreLimit_nonvacuous {ℓ : ℕ} (D : RCData ℓ) (Fam : Family)
    (hSel : SelmerCorankOneOverK ℓ D.kfin) (f : Uniform.Lambda) (hf : D.uPrim Fam 0 = lamIncl f) :
    ∃ M : BaseZeroCoreLimit D Fam (1 : ℤ),
      M.uprim = algebraMap Uniform.Lambda (FractionRing Uniform.Lambda) f ∧
        ∀ i, Rings.rhoT (M.z i) = lambdaEvalZero f := by
  classical
  refine ⟨{
    m := 0
    Dm := 0
    central := (centralSelmerComparison_of_selmer hSel).some
    z := fun _ => algebraMap Uniform.Lambda LambdaT f
    hz := by simp
    CU := PairedFunctional.threeTermComplex (M := Fin 1 → Rings.LambdaT)
      (N := Fin 1 → Rings.LambdaT) (M' := Fin 1 → Rings.LambdaT) 0 0 (by simp)
    e1 := LinearEquiv.refl _ _
    e2 := LinearEquiv.refl _ _
    hd := by
      intro y
      simp only [PairedFunctional.threeTermComplex_d_one_two, Matrix.zero_mulVec]
      rfl
    lam := LinearMap.proj 0
    hlam := by
      intro y
      simp only [PairedFunctional.threeTermComplex_d_one_two]
      rfl
    uprim := algebraMap LambdaT (FractionRing Uniform.Lambda) (algebraMap Uniform.Lambda LambdaT f)
    hu := ?_
    limit := ?_
    hprimId := by
      rw [hf]
      exact isTExpansion_algebraMap_lambdaT f }, ?_, ?_⟩
  · intro w _ hrep
    have hw0 : w 0 = 1 := by
      have h := hrep (Pi.single 0 1)
      rw [dotProduct_single, mul_one] at h
      exact h.symm.trans (by rfl)
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.vecMulVec_apply, Matrix.adjugate_fin_one, hw0]
  · have hz : (fun i : Fin (0 + 1) => Rings.rhoT (algebraMap Uniform.Lambda LambdaT f)) =
        fun _ => lambdaEvalZero f := by
      funext i
      exact rhoT_algebraMap f
    exact hz ▸ constLimit (lambdaEvalZero f)
  · exact algebraMap_lambdaT_lambda f
  · intro i
    exact rhoT_algebraMap f

/-- **The core does not force the conclusion** (PROVED): with `f = 1` the generic coordinate and
the central cycle are `1 ≠ 0`; the specified point `1 ∈ ℤ` has infinite order, so the height
formula (the only source of `z̄ = 0`) does not apply. The example lives at the infinite-order point
`1 ∈ ℤ` of `G = ℤ` (not a point of `E(K)`; the Heegner data are not constructed). At a torsion
point the core forces `u_{prim,0}(0) = 0`. -/
theorem baseZeroCoreLimit_not_forced {ℓ : ℕ} (D : RCData ℓ) (Fam : Family)
    (hSel : SelmerCorankOneOverK ℓ D.kfin) (hf : D.uPrim Fam 0 = lamIncl 1) :
    ∃ M : BaseZeroCoreLimit D Fam (1 : ℤ), M.uprim ≠ 0 ∧ ∀ i, Rings.rhoT (M.z i) ≠ 0 := by
  obtain ⟨M, hu, hz⟩ := baseZeroCoreLimit_nonvacuous D Fam hSel 1 hf
  refine ⟨M, ?_, fun i => ?_⟩
  · rw [hu, map_one]
    exact one_ne_zero
  · rw [hz i, map_one]
    exact one_ne_zero

end ZInQ.Manuscript.RC.BaseZeroLimit
