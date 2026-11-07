import ZInQKernel.Multiplication.Local.FormalGroupLaw
import ZInQKernel.Multiplication.Local.TruncationError
import ZInQKernel.Multiplication.Local.PointMap
import ZInQKernel.Multiplication.FormalLog.LogAdd

/-!
# The formal logarithm of `y² = x³ + A x` and its isometry range

Blueprint: `multiplication/local/formal-logarithm.md`, `multiplication/local/logarithm-isometry.md`.

`formalLog A = Σ_{r ≥ 1} b_{r-1} T^r / r` (`FormalLog.lean`), `b_0 = 1`, `b_i ∈ 𝒪` when
`v(A) ≥ 0`, and `ellLog P = log(z(P))` (`TruncationError.lean`).

* Part 1 of formal-logarithm: `d/dT log = Σ bₙ Tⁿ` (`derivative_formalLog`), which is the
  expansion `dz/√(1 - 4Az⁴) = dz/(1 - 2Az ω(z))` of `dx/(2y)` (`logarithm-series.md`), and
  `log ∘ F = log + log` (`formalLog_formalAdd`).
* Part 2: convergence on `v(t) > 0` (`summable_log`) and the homomorphism property
  `λ(P + Q) = λ(P) + λ(Q)` (`ellLog_add`), hence `λ([n]P) = n λ(P)` (`ellLog_zsmul`).
* Isometry: for `(p - 1) k > e`, on `W_k(K)` the logarithm is injective,
  `v(λ(P)) = v(z(P))` and `v(z([n]P)) = v(z(P)) + v(n)`; for `p` odd, `e = 1` this is all of
  `W₁(K)`, which is then torsion-free.
-/

namespace ZInQ.Mult

open PowerSeries WeierstrassCurve WeierstrassCurve.Affine WithZero

/-! ### Part 1 -/

/-- `d/dT log(T) = Σ bₙ Tⁿ`: the derivative of the formal logarithm is the invariant
differential series. -/
theorem derivative_formalLog {F : Type*} [Field F] [CharZero F] (A : F) :
    derivative (R := F) (formalLog A) = invDiffSeries A := by
  ext n
  rw [coeff_derivative, formalLog, invDiffSeries, coeff_mk, coeff_mk]
  have := logCoeffA_mul A (r := n + 1) (by omega)
  push_cast at this
  rw [this]

/-- `b_0 = 1` and `bᵢ ∈ 𝒪` for `v(A) ≥ 0`. -/
theorem invDiffCoeff_spec {K : Type*} [Field K] [Valued K ℤᵐ⁰] {A : K} (hA : 0 ≤ vK K A) :
    invDiffCoeff A 0 = 1 ∧ ∀ n, 0 ≤ vK K (invDiffCoeff A n) :=
  ⟨invDiffCoeff_zero A, fun n => vge_invDiffCoeff hA n⟩

/-- **The formal logarithm is a homomorphism of formal groups**: `log(F(T₁, T₂)) =
log(T₁) + log(T₂)` in `K⟦T₁, T₂⟧`. -/
theorem formalLog_formalAdd {F : Type*} [Field F] [CharZero F] (A : F) :
    PowerSeries.subst (formalAdd A) (formalLog A) =
      PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) (formalLog A) +
        PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) (formalLog A) :=
  formalLog_formalAdd_aux A

/-! ### Part 2 -/

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰] [CompleteSpace K] [DecidableEq K]
variable {p e : ℕ} [Fact p.Prime]

/-- **The formal logarithm is a homomorphism** `W₁(K) → (K, +)`. -/
theorem ellLog_add (h : ResidueChar K p e) {A : K} (hA : 0 ≤ vK K A)
    {P Q : (shortCurve A).toAffine.Point} (hP : P ∈ W1 (vK K) A) (hQ : Q ∈ W1 (vK K) A) :
    ellLog (P + Q) = ellLog P + ellLog Q :=
  evalLog_zCoord_add h hA hP hQ

omit [Valued K ℤᵐ⁰] [CompleteSpace K] [DecidableEq K] [Fact p.Prime] in
theorem logCoeffA_eq_zero_of_even {A : K} {r : ℕ} (hr : Even r) : logCoeffA A r = 0 := by
  unfold logCoeffA invDiffCoeff
  split_ifs with h0 h4
  · rfl
  · exfalso; obtain ⟨k, rfl⟩ := hr; omega
  · rw [zero_div]

omit [CompleteSpace K] [DecidableEq K] [Fact p.Prime] in
/-- `log` is odd. -/
theorem evalLog_neg (A t : K) : evalLog A (-t) = -evalLog A t := by
  rw [evalLog, evalLog, ← tsum_neg]
  congr 1; funext r
  rcases Nat.even_or_odd r with hr | hr
  · rw [logCoeffA_eq_zero_of_even hr]; simp
  · rw [hr.neg_pow]; ring

omit [CompleteSpace K] [DecidableEq K] [Fact p.Prime] in
theorem evalLog_zero (A : K) : evalLog A 0 = 0 := by
  have : (fun r : ℕ => logCoeffA A r * (0 : K) ^ r) = fun _ => 0 := by
    funext r; rcases r with _ | r <;> simp [logCoeffA]
  rw [evalLog, this, tsum_zero]

omit [CompleteSpace K] [DecidableEq K] [Fact p.Prime] in
theorem ellLog_zero {A : K} : ellLog (0 : (shortCurve A).toAffine.Point) = 0 := by
  rw [ellLog, zCoord_zero, evalLog_zero]

omit [CompleteSpace K] [Fact p.Prime] in
theorem ellLog_neg {A : K} (P : (shortCurve A).toAffine.Point) : ellLog (-P) = -ellLog P := by
  rw [ellLog, ellLog, zCoord_neg, evalLog_neg]

/-- `λ([n]P) = n λ(P)` for `P ∈ W₁(K)`. -/
theorem ellLog_zsmul (h : ResidueChar K p e) {A : K} (hA : 0 ≤ vK K A)
    {P : (shortCurve A).toAffine.Point} (hP : P ∈ W1 (vK K) A) (n : ℤ) :
    ellLog (n • P) = n * ellLog P := by
  let f : formalNbhd A hA →+ K :=
    { toFun := fun Q => ellLog (Q : (shortCurve A).toAffine.Point)
      map_zero' := ellLog_zero
      map_add' := fun Q R => ellLog_add h hA ((mem_formalNbhd_iff hA _).mp Q.2)
        ((mem_formalNbhd_iff hA _).mp R.2) }
  have hP' : P ∈ formalNbhd A hA := (mem_formalNbhd_iff hA P).mpr hP
  have := f.map_zsmul n ⟨P, hP'⟩
  simpa [f, zsmul_eq_mul] using this

/-! ### The isometry range -/

/-- `v(λ(P)) = v(z(P))` on `W_k(K)` for `(p - 1) k > e`. -/
theorem ellLog_val_eq (h : ResidueChar K p e) {A : K} (hA : 0 ≤ vK K A) {k : ℤ}
    (hk : (e : ℤ) < ((p : ℤ) - 1) * k) {P : (shortCurve A).toAffine.Point}
    (hP : P ∈ formalFilt A hA k) : vK K (ellLog P) = vK K (zCoord P) := by
  rcases P with _ | ⟨x, y, hxy⟩
  · rw [point_zero_eq, ellLog_zero, zCoord_zero]
  obtain ⟨N, hN, -, -, -, hz, -⟩ := formal_val_x_y hA hxy hP.1
  have hkN : k ≤ N := by have := hP.2; rw [hz] at this; exact_mod_cast this
  have hp1 : (0 : ℤ) ≤ (p : ℤ) - 1 := by have := (Fact.out : p.Prime).two_le; omega
  exact (evalLog_isometry h hA hz (lt_of_lt_of_le hk (by nlinarith))).2

/-- **The logarithm is injective on `W_k(K)`** for `(p - 1) k > e`. -/
theorem ellLog_injOn (h : ResidueChar K p e) {A : K} (hA : 0 ≤ vK K A) {k : ℤ}
    (hk : (e : ℤ) < ((p : ℤ) - 1) * k) :
    Set.InjOn ellLog (formalFilt A hA k : Set (shortCurve A).toAffine.Point) := by
  intro P hP Q hQ hPQ
  have hd : P - Q ∈ formalFilt A hA k := (formalFilt A hA k).sub_mem hP hQ
  have hW1 : ∀ R ∈ formalFilt A hA k, R ∈ W1 (vK K) A := fun R hR => hR.1
  have hl : ellLog (P - Q) = 0 := by
    rw [sub_eq_add_neg, ellLog_add h hA (hW1 P hP) (hW1 _ ((formalFilt A hA k).neg_mem hQ)),
      ellLog_neg, hPQ, add_neg_cancel]
  have hv := ellLog_val_eq h hA hk hd
  rw [hl, (vK K).map_zero] at hv
  have hz : zCoord (P - Q) = 0 := ((vK K).top_iff).mp hv.symm
  have := zCoord_injOn hA (hW1 _ hd) (zero_mem_W1 (vK K)) (by rw [hz, zCoord_zero])
  exact sub_eq_zero.mp this

/-- **`v(z([n]P)) = v(z(P)) + v(n)`** on `W_k(K)`, `(p - 1) k > e`, for `n ≠ 0`. -/
theorem val_z_zsmul_eq (h : ResidueChar K p e) [CharZero K] {A : K} (hA : 0 ≤ vK K A) {k : ℤ}
    (hk : (e : ℤ) < ((p : ℤ) - 1) * k) {P : (shortCurve A).toAffine.Point}
    (hP : P ∈ formalFilt A hA k) {n : ℤ} :
    vK K (zCoord (n • P)) = vK K (zCoord P) + vK K (n : K) := by
  have hnP := zsmul_mem_formalFilt hA hP n
  rw [← ellLog_val_eq h hA hk hnP, ← ellLog_val_eq h hA hk hP, ellLog_zsmul h hA hP.1,
    (vK K).map_mul, add_comm]

/-- **At an odd unramified prime the isometry range is all of `W₁(K)`**: `λ` is injective on
`W₁(K)`, `v(λ(P)) = v(z(P))`, and `W₁(K)` is torsion-free. -/
theorem ellLog_unramified [CharZero K] (h : ResidueChar K p 1) (hp2 : p ≠ 2) {A : K} (hA : 0 ≤ vK K A) :
    Set.InjOn ellLog (W1 (vK K) A) ∧
      (∀ P ∈ W1 (vK K) A, vK K (ellLog P) = vK K (zCoord P)) ∧
      (∀ P ∈ W1 (vK K) A, ∀ n : ℤ, n ≠ 0 → n • P = 0 → P = 0) := by
  have hk : ((1 : ℕ) : ℤ) < ((p : ℤ) - 1) * 1 := by
    have := (Fact.out : p.Prime).two_le
    have : p ≠ 2 := hp2
    push_cast; omega
  have hset : (formalFilt A hA 1 : Set (shortCurve A).toAffine.Point) = W1 (vK K) A :=
    coe_formalNbhd hA
  refine ⟨hset ▸ ellLog_injOn h hA hk, fun P hP => ellLog_val_eq h hA hk ((mem_formalNbhd_iff hA P).mpr hP),
    fun P hP n hn hnP => ?_⟩
  have hl := ellLog_zsmul h hA hP n
  rw [hnP] at hl
  have h0 : ellLog (0 : (shortCurve A).toAffine.Point) = 0 := ellLog_zero
  rw [h0] at hl
  have hn' : (n : K) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hP0 : ellLog P = 0 := by
    rcases mul_eq_zero.mp hl.symm with h1 | h1
    · exact absurd h1 hn'
    · exact h1
  have := ellLog_injOn h hA hk ((mem_formalNbhd_iff hA P).mpr hP) (zero_mem _) (by rw [hP0, h0])
  exact this

end ZInQ.Mult
