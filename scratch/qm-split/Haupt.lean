import TailK

/-!
# qm-split, row H-88 `QMHauptmodulBase3`: base copied from leafq-check

Lines 1-934 and 1326-2563 of `scratch/leafq-check/Fold.lean` @ w54 (leafq-check's fold over leaf-fold4's chain:
`GammaStarGen`, the valence split with `EllipticOrderLe6` proved, the `QMHauptmodul` reductions with the row
`QMHauptmodulBase3`), copied verbatim; the qm-split part is the last section of this file.

(Original header follows.)

# leafq-check: the fold (check over leaf-fold4's olean chain)

`scratch/leafq-check/GammaStarGen.lean`'s proof, run over leaf-fold4's chain (`import TailK`, so the
statement is the chain's own constant `HDec.HSyn.G0Split.FibreQM.PeriodGlue.GammaStarGen`), and
`sixContactMin_of_open5`: `sixContactMin_of_open4` without the field `gammaStarGen`.
Check: `scratch/leafq-check/chk.sh scratch/leafq-check/Fold.lean` (needs leaf-fold4's chain, see chk.sh).
-/

set_option linter.all false

namespace HDec.LeafQCheck

open HSyn.G0Split.FibreQM.PeriodGlue (x4 x6 GammaStarGen)

/-! ## The proof of `GammaStarGen` (leafq-check)

Idea (all numerics in `scratch/leafq-check/py/`). `y = i + j ∈ 𝒪` has `y² = −1`; it is the pure
quaternion of the fixed point `√2 + i` of `ι(x₄)`. For `x ∈ N(𝒪)` with `nrd x > 0` the conjugate
`v = x y x⁻¹` is again a pure element of `𝒪` with `v² = −1`, and `pairY v = −2b + 3c` (for
`v = bi + cj + dk`) is `cosh` of the hyperbolic distance between the fixed points of `v` and `y`; it
is a positive integer. If `pairY v ≥ 2`, conjugating by one of `x₆`, `x₆⁻¹`, `x₆x₄`, `(x₄x₆)⁻¹`
lowers it (the four lowerings are `b + 3d`, `b − 3d`, `−5b + 6c + 3d`, `−5b + 6c − 3d`, and
`3·nrd v − (pairY v)²` is a sum of two products of them). If `pairY v = 1` then `v = y`, so `x`
commutes with `y`, `x = a + by`, and the integrality of `x j x⁻¹` forces `x ∈ ℚ^× ⟨x₄⟩`. -/

open PkgI1

theorem sqrt2_sq' : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)

theorem iota_apply (x : PkgI1.B) : PkgI1.iota x =
    !![(x.re : ℝ) + x.imI * √2, -3 * (x.imJ : ℝ) - 3 * √2 * x.imK;
       (x.imJ : ℝ) - √2 * x.imK, (x.re : ℝ) - x.imI * √2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PkgI1.iota, PkgI1.Mi, PkgI1.Mj, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem iota_mul (x y : PkgI1.B) : PkgI1.iota (x * y) = PkgI1.iota x * PkgI1.iota y := by
  rw [iota_apply, iota_apply, iota_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    (try simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]) <;> (try ring_nf)

/-- The reduced norm. -/
def nrd (x : PkgI1.B) : ℚ := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2

theorem det_iota_eq (x : PkgI1.B) : (PkgI1.iota x).det = (nrd x : ℝ) := by
  rw [iota_apply, Matrix.det_fin_two_of, nrd]
  push_cast
  linear_combination (-(x.imI : ℝ) ^ 2 - 3 * (x.imK : ℝ) ^ 2) * sqrt2_sq'

theorem nrd_mul (x y : PkgI1.B) : nrd (x * y) = nrd x * nrd y := by
  simp [nrd]; ring

theorem iota_ratCast (q : ℚ) : PkgI1.iota (q : PkgI1.B) = (q : ℝ) • 1 := by
  rw [iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp

/-- `y = i + j`. -/
def yq : PkgI1.B := ⟨0, 1, 1, 0⟩
/-- `⟨v, y⟩` for the bilinear form of `nrd` on pure quaternions (`= cosh d` on the hyperboloid). -/
def pairY (v : PkgI1.B) : ℚ := -2 * v.imI + 3 * v.imJ
/-- `x₄⁻¹`. -/
def x4i : PkgI1.B := ⟨1 / 2, -1 / 2, -1 / 2, 0⟩
/-- `x₆⁻¹`. -/
def x6i : PkgI1.B := ⟨-1 / 2, 0, -1 / 6, 0⟩

theorem yq_sq : yq * yq = -1 := by ext <;> simp [yq] <;> norm_num

/-! ### Membership in `𝒪` by coordinates -/

theorem inO_iff (v : PkgI1.B) : PkgI1.InO v ↔ ∃ n0 n1 n2 n3 : ℤ,
    v = ⟨n0 + n2 / 2, n1 + n3 / 2, n2 / 2, n3 / 2⟩ := by
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n 0, n 1, n 2, n 3, ?_⟩
    ext <;> simp [PkgI1.oBasis, Fin.sum_univ_four] <;> ring
  · rintro ⟨n0, n1, n2, n3, rfl⟩
    refine ⟨![n0, n1, n2, n3], ?_⟩
    ext <;> simp [PkgI1.oBasis, Fin.sum_univ_four] <;> ring

theorem inO_yq : PkgI1.InO yq := (inO_iff _).2 ⟨-1, 1, 2, 0, by ext <;> simp [yq] <;> norm_num⟩
theorem inO_qj : PkgI1.InO PkgI1.qj :=
  (inO_iff _).2 ⟨-1, 0, 2, 0, by ext <;> simp [PkgI1.qj] <;> norm_num⟩

/-! ### `x₄`, `x₆` normalize `𝒪` -/

theorem conj_x4 : ∀ w, PkgI1.InO w → PkgI1.InO (x4 * w * x4i) ∧ PkgI1.InO (x4i * w * x4) := by
  intro w hw
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff w).1 hw
  constructor
  · refine (inO_iff _).2 ⟨n0 + 2*n1 - n2, -n1 + n2 + n3, -4*n1 + 3*n2, -2*n1 + n2 - n3, ?_⟩
    ext <;> simp [x4, x4i] <;> ring
  · refine (inO_iff _).2 ⟨n0 + 2*n1 - n2 + 2*n3, -3*n1 + 2*n2 - 3*n3, -4*n1 + 3*n2 - 4*n3,
      2*n1 - n2 + n3, ?_⟩
    ext <;> simp [x4, x4i] <;> ring

theorem conj_x6 : ∀ w, PkgI1.InO w → PkgI1.InO (x6 * w * x6i) ∧ PkgI1.InO (x6i * w * x6) := by
  intro w hw
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff w).1 hw
  constructor
  · refine (inO_iff _).2 ⟨n0, -n3, n2, n1 + n3, ?_⟩
    ext <;> simp [x6, x6i] <;> ring
  · refine (inO_iff _).2 ⟨n0, n1 + n3, n2, -n1, ?_⟩
    ext <;> simp [x6, x6i] <;> ring

theorem x4_x4i : x4 * x4i = 1 := by ext <;> simp [x4, x4i] <;> norm_num
theorem x4i_x4 : x4i * x4 = 1 := by ext <;> simp [x4, x4i] <;> norm_num
theorem x6_x6i : x6 * x6i = 1 := by ext <;> simp [x6, x6i] <;> norm_num
theorem x6i_x6 : x6i * x6 = 1 := by ext <;> simp [x6, x6i] <;> norm_num

/-! ### Elementary quaternion facts -/

theorem pure_of_sq {v : PkgI1.B} (h : v * v = -1) :
    v.re = 0 ∧ -2 * v.imI ^ 2 + 3 * v.imJ ^ 2 - 6 * v.imK ^ 2 = 1 := by
  have h1 : v.re ^ 2 + 2 * v.imI ^ 2 - 3 * v.imJ ^ 2 + 6 * v.imK ^ 2 = -1 := by
    have := congrArg QuaternionAlgebra.re h; simp at this; linear_combination this
  have h2 : v.re * v.imI = 0 := by
    have := congrArg QuaternionAlgebra.imI h; simp at this; linear_combination this / 2
  have h3 : v.re * v.imJ = 0 := by
    have := congrArg QuaternionAlgebra.imJ h; simp at this; linear_combination this / 2
  have h4 : v.re * v.imK = 0 := by
    have := congrArg QuaternionAlgebra.imK h; simp at this; linear_combination this / 2
  have key : v.re ^ 2 * (v.re ^ 2 + 1) = 0 := by
    linear_combination v.re ^ 2 * h1 - 2 * (v.re * v.imI) * h2 + 3 * (v.re * v.imJ) * h3
      - 6 * (v.re * v.imK) * h4
  have hre : v.re = 0 := by
    rcases mul_eq_zero.1 key with h | h
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    · nlinarith [sq_nonneg v.re]
  refine ⟨hre, ?_⟩
  rw [hre] at h1; linear_combination -h1

theorem inv_eq {x z : PkgI1.B} (hxz : x * z = 1) (hN : nrd x ≠ 0) :
    z = ⟨x.re / nrd x, -x.imI / nrd x, -x.imJ / nrd x, -x.imK / nrd x⟩ := by
  set w : PkgI1.B := ⟨x.re / nrd x, -x.imI / nrd x, -x.imJ / nrd x, -x.imK / nrd x⟩ with hw_def
  have hN' : x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 ≠ 0 := hN
  have hw : w * x = 1 := by
    ext <;> simp [w, nrd] <;> field_simp <;> ring
  calc z = (w * x) * z := by rw [hw, one_mul]
    _ = w * (x * z) := mul_assoc _ _ _
    _ = w := by rw [hxz, mul_one]

theorem pairY_ge {x z : PkgI1.B} (hxz : x * z = 1) (hpos : 0 < nrd x) :
    1 ≤ pairY (x * yq * z) := by
  rw [inv_eq hxz hpos.ne']
  have hN' : 0 < x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 := hpos
  have e : pairY (x * yq * ⟨x.re / nrd x, -x.imI / nrd x, -x.imJ / nrd x, -x.imK / nrd x⟩) =
      1 + 12 * ((x.imI - x.imJ) ^ 2 + x.imK ^ 2) /
        (x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2) := by
    simp [pairY, yq, nrd]; field_simp; ring
  rw [e]
  have : 0 ≤ 12 * ((x.imI - x.imJ) ^ 2 + x.imK ^ 2) /
      (x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2) := by positivity
  linarith

theorem conj_sq {x z : PkgI1.B} (hxz : x * z = 1) (hzx : z * x = 1) :
    (x * yq * z) * (x * yq * z) = -1 := by
  calc (x * yq * z) * (x * yq * z) = x * (yq * ((z * x) * (yq * z))) := by
        simp only [mul_assoc]
    _ = -(x * z) := by rw [hzx, one_mul, ← mul_assoc yq yq z, yq_sq]; simp
    _ = -1 := by rw [hxz]

theorem pairY_int {v : PkgI1.B} (hv : PkgI1.InO v) (hre : v.re = 0) : ∃ m : ℤ, pairY v = m := by
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff v).1 hv
  have h : (n2 : ℚ) = -2 * n0 := by
    have := hre; simp only at this; linarith
  refine ⟨-2 * n1 - n3 - 3 * n0, ?_⟩
  simp only [pairY]; push_cast; rw [h]; ring

theorem eq_yq {v : PkgI1.B} (hre : v.re = 0) (hn : -2 * v.imI ^ 2 + 3 * v.imJ ^ 2 - 6 * v.imK ^ 2 = 1)
    (h1 : pairY v = 1) : v = yq := by
  have h3 : 3 * v.imJ = 1 + 2 * v.imI := by simp only [pairY] at h1; linarith
  have key : (v.imI - 1) ^ 2 + 9 * v.imK ^ 2 = 0 := by
    linear_combination (-3 / 2) * hn + (1 / 2) * (3 * v.imJ + 1 + 2 * v.imI) * h3
  have hb : v.imI = 1 := by nlinarith [sq_nonneg (v.imI - 1), sq_nonneg v.imK]
  have hd : v.imK = 0 := by nlinarith [sq_nonneg (v.imI - 1), sq_nonneg v.imK]
  have hc : v.imJ = 1 := by linarith
  ext <;> simp [yq, hre, hb, hc, hd]

/-! ### The subgroup and the predicate `P` -/

/-- The subgroup of the statement. -/
def Hgen : Subgroup (GL (Fin 2) ℝ) := Subgroup.closure
    ({γ : GL (Fin 2) ℝ | (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x4} ∪
      {γ : GL (Fin 2) ℝ | (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x6} ∪
      {γ : GL (Fin 2) ℝ | ∃ q : ℚ, q ≠ 0 ∧ (γ : Matrix (Fin 2) (Fin 2) ℝ) = (q : ℝ) • 1})

/-- Every element of `GL₂(ℝ)` with matrix `ι(x)` lies in the subgroup. -/
def P (x : PkgI1.B) : Prop :=
  ∀ γ : GL (Fin 2) ℝ, (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → γ ∈ Hgen

theorem det_ne {x : PkgI1.B} (h : nrd x ≠ 0) : (PkgI1.iota x).det ≠ 0 := by
  rw [det_iota_eq]; exact_mod_cast h

/-- The element of `GL₂(ℝ)` with matrix `ι(x)`. -/
noncomputable def glOf (x : PkgI1.B) (h : nrd x ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (PkgI1.iota x) (det_ne h)

theorem coe_glOf (x : PkgI1.B) (h : nrd x ≠ 0) :
    (glOf x h : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x := rfl

theorem P_x4 : P x4 := fun _ h => Subgroup.subset_closure (Or.inl (Or.inl h))
theorem P_x6 : P x6 := fun _ h => Subgroup.subset_closure (Or.inl (Or.inr h))
theorem P_rat (q : ℚ) (hq : q ≠ 0) : P (q : PkgI1.B) := fun _ h =>
  Subgroup.subset_closure (Or.inr ⟨q, hq, h.trans (iota_ratCast q)⟩)

theorem P_mul {s x : PkgI1.B} (hs : P s) (hx : P x) (ds : nrd s ≠ 0) (dx : nrd x ≠ 0) :
    P (s * x) := by
  intro γ hγ
  have : γ = glOf s ds * glOf x dx := by
    ext1; rw [Units.val_mul, coe_glOf, coe_glOf, hγ, iota_mul]
  rw [this]; exact Hgen.mul_mem (hs _ rfl) (hx _ rfl)

theorem P_cancel {s x : PkgI1.B} (hs : P s) (hsx : P (s * x)) (ds : nrd s ≠ 0) : P x := by
  intro γ hγ
  have h1 : glOf s ds * γ ∈ Hgen := hsx _ (by rw [Units.val_mul, coe_glOf, hγ, iota_mul])
  have : γ = (glOf s ds)⁻¹ * (glOf s ds * γ) := by group
  rw [this]; exact Hgen.mul_mem (Hgen.inv_mem (hs _ rfl)) h1

theorem P_x4i : P x4i := by
  refine P_cancel P_x4 ?_ (by norm_num [nrd, x4])
  rw [x4_x4i]; simpa using P_rat 1 one_ne_zero

theorem P_x6i : P x6i := by
  refine P_cancel P_x6 ?_ (by norm_num [nrd, x6])
  rw [x6_x6i]; simpa using P_rat 1 one_ne_zero

/-! ### The descent step -/

theorem descent {v : PkgI1.B} (hre : v.re = 0)
    (hn : -2 * v.imI ^ 2 + 3 * v.imJ ^ 2 - 6 * v.imK ^ 2 = 1) (h2 : 2 ≤ pairY v) :
    pairY (x6 * v * x6i) < pairY v ∨ pairY (x6i * v * x6) < pairY v ∨
      pairY (x6 * x4 * v * (x4i * x6i)) < pairY v ∨
      pairY (x6i * x4i * v * (x4 * x6)) < pairY v := by
  have e1 : pairY (x6 * v * x6i) = -v.imI + 3 * v.imJ + 3 * v.imK := by
    simp [pairY, x6, x6i, hre]; ring
  have e2 : pairY (x6i * v * x6) = -v.imI + 3 * v.imJ - 3 * v.imK := by
    simp [pairY, x6, x6i, hre]; ring
  have e3 : pairY (x6 * x4 * v * (x4i * x6i)) = -7 * v.imI + 9 * v.imJ + 3 * v.imK := by
    simp [pairY, x6, x6i, x4, x4i, hre]; ring
  have e4 : pairY (x6i * x4i * v * (x4 * x6)) = -7 * v.imI + 9 * v.imJ - 3 * v.imK := by
    simp [pairY, x6, x6i, x4, x4i, hre]; ring
  rw [e1, e2, e3, e4]
  by_contra hc
  push_neg at hc
  obtain ⟨c1, c2, c3, c4⟩ := hc
  simp only [pairY] at h2 c1 c2 c3 c4
  nlinarith [mul_nonneg (sub_nonneg.2 c1) (sub_nonneg.2 c4),
    mul_nonneg (sub_nonneg.2 c2) (sub_nonneg.2 c3)]

/-! ### The base case: `x` commutes with `y` -/

theorem nrd_ratCast (q : ℚ) : nrd (q : PkgI1.B) = q ^ 2 := by simp [nrd]

theorem P_base {x z : PkgI1.B} (hxz : x * z = 1) (hzx : z * x = 1)
    (hN : ∀ w, PkgI1.InO w → PkgI1.InO (x * w * z) ∧ PkgI1.InO (z * w * x))
    (hpos : 0 < nrd x) (hv : x * yq * z = yq) : P x := by
  have hcomm : x * yq = yq * x := by
    calc x * yq = x * yq * (z * x) := by rw [hzx, mul_one]
      _ = (x * yq * z) * x := by simp only [mul_assoc]
      _ = yq * x := by rw [hv]
  have hd : x.imK = 0 := by
    have := congrArg QuaternionAlgebra.imI hcomm; simp [yq] at this; linarith
  have hc : x.imJ = x.imI := by
    have := congrArg QuaternionAlgebra.imK hcomm; simp [yq] at this; linarith
  obtain ⟨a, b, hx⟩ : ∃ a b : ℚ, x = ⟨a, b, b, 0⟩ :=
    ⟨x.re, x.imI, by ext <;> simp [hc, hd]⟩
  have hNx : nrd x = a ^ 2 + b ^ 2 := by rw [hx]; simp only [nrd]; ring
  have hN' : 0 < a ^ 2 + b ^ 2 := hNx ▸ hpos
  have hu_eq : x * PkgI1.qj * z =
      ⟨0, 6 * b ^ 2 / (a ^ 2 + b ^ 2), (a ^ 2 + 5 * b ^ 2) / (a ^ 2 + b ^ 2),
        2 * a * b / (a ^ 2 + b ^ 2)⟩ := by
    rw [inv_eq hxz hpos.ne', hNx, hx]
    ext <;> simp [PkgI1.qj] <;> field_simp <;> ring
  obtain ⟨n0, n1, n2, n3, hu'⟩ := (inO_iff _).1 (hN _ inO_qj).1
  rw [hu_eq] at hu'
  have eJ : (a ^ 2 + 5 * b ^ 2) / (a ^ 2 + b ^ 2) = (n2 : ℚ) / 2 :=
    congrArg QuaternionAlgebra.imJ hu'
  have eK : 2 * a * b / (a ^ 2 + b ^ 2) = (n3 : ℚ) / 2 := congrArg QuaternionAlgebra.imK hu'
  have hn2 : (n2 : ℚ) = 2 * (a ^ 2 + 5 * b ^ 2) / (a ^ 2 + b ^ 2) := by
    rw [mul_div_assoc, eJ]; ring
  have hn3 : (n3 : ℚ) = 4 * a * b / (a ^ 2 + b ^ 2) := by
    rw [show 4 * a * b / (a ^ 2 + b ^ 2) = 2 * (2 * a * b / (a ^ 2 + b ^ 2)) by ring, eK]; ring
  have hq : ((n2 : ℚ) - 6) ^ 2 + 4 * (n3 : ℚ) ^ 2 = 16 := by
    rw [hn2, hn3]; field_simp; ring
  have hz : (n2 - 6) ^ 2 + 4 * n3 ^ 2 = 16 := by exact_mod_cast hq
  have hn3b : -2 ≤ n3 ∧ n3 ≤ 2 := by constructor <;> nlinarith [sq_nonneg (n2 - 6)]
  have hn2b : 2 ≤ n2 ∧ n2 ≤ 10 := by constructor <;> nlinarith [sq_nonneg n3]
  have hcase : n2 = 2 ∨ n2 = 6 ∨ n2 = 10 := by
    obtain ⟨l3, u3⟩ := hn3b; obtain ⟨l2, u2⟩ := hn2b
    interval_cases n3 <;> interval_cases n2 <;> first | omega | (exfalso; revert hz; norm_num)
  have hb2 : (n2 : ℚ) * (a ^ 2 + b ^ 2) = 2 * (a ^ 2 + 5 * b ^ 2) := by
    rw [hn2]; field_simp
  have nx4 : nrd x4 ≠ 0 := by norm_num [nrd, x4]
  have nx4i : nrd x4i ≠ 0 := by norm_num [nrd, x4i]
  rcases hcase with h | h | h
  · -- `b = 0`: `x = a`
    rw [h] at hb2; push_cast at hb2
    have hb0 : b = 0 := by nlinarith [sq_nonneg b]
    have ha0 : a ≠ 0 := by intro h0; rw [hb0, h0] at hN'; norm_num at hN'
    have : x = ((a : ℚ) : PkgI1.B) := by rw [hx, hb0]; ext <;> simp
    rw [this]; exact P_rat a ha0
  · -- `a = ± b`
    rw [h] at hb2; push_cast at hb2
    have hab : (b - a) * (b + a) = 0 := by linear_combination (-1 / 4) * hb2
    have ha0 : a ≠ 0 := by
      intro h0; rw [h0] at hab; have : b = 0 := by nlinarith [sq_nonneg b]
      rw [h0, this] at hN'; norm_num at hN'
    rcases mul_eq_zero.1 hab with h' | h'
    · have : x = ((a : ℚ) : PkgI1.B) * x4 := by
        rw [hx, show b = a by linarith]; ext <;> simp [x4]
      rw [this]
      exact P_mul (P_rat a ha0) P_x4 (by rw [nrd_ratCast]; exact pow_ne_zero 2 ha0) nx4
    · have : x = ((2 * a : ℚ) : PkgI1.B) * x4i := by
        rw [hx, show b = -a by linarith]
        ext <;> simp [x4i, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
          QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> ring
      have h2a : (2 * a : ℚ) ≠ 0 := mul_ne_zero two_ne_zero ha0
      rw [this]
      exact P_mul (P_rat (2 * a) h2a) P_x4i (by rw [nrd_ratCast]; exact pow_ne_zero 2 h2a) nx4i
  · -- `a = 0`: `x = b y = (b/2) x₄²`
    rw [h] at hb2; push_cast at hb2
    have ha0 : a = 0 := by nlinarith [sq_nonneg a]
    have hb0 : b ≠ 0 := by intro h0; rw [ha0, h0] at hN'; norm_num at hN'
    have : x = ((b / 2 : ℚ) : PkgI1.B) * (x4 * x4) := by
      have h44 : x4 * x4 = ⟨0, 2, 2, 0⟩ := by ext <;> simp [x4] <;> norm_num
      rw [hx, ha0, h44]; ext <;> simp <;> ring
    have hb2' : (b / 2 : ℚ) ≠ 0 := div_ne_zero hb0 two_ne_zero
    rw [this]
    have h44 : nrd (x4 * x4) ≠ 0 := by rw [nrd_mul]; exact mul_ne_zero nx4 nx4
    exact P_mul (P_rat (b / 2) hb2') (P_mul P_x4 P_x4 nx4 nx4)
      (by rw [nrd_ratCast]; exact pow_ne_zero 2 hb2') h44

/-! ### The induction -/

theorem nrd_x6 : nrd x6 = 3 := by norm_num [nrd, x6]
theorem nrd_x6i : nrd x6i = 1 / 3 := by norm_num [nrd, x6i]
theorem nrd_x4 : nrd x4 = 2 := by norm_num [nrd, x4]
theorem nrd_x4i : nrd x4i = 1 / 2 := by norm_num [nrd, x4i]

/-- One step: if `(s, si)` is a pair of mutually inverse normalizers of `𝒪` with `P s`, `nrd s > 0`,
the claim for `s * x` gives the claim for `x`. -/
theorem key (n : ℕ) : ∀ x z : PkgI1.B, x * z = 1 → z * x = 1 →
    (∀ w, PkgI1.InO w → PkgI1.InO (x * w * z) ∧ PkgI1.InO (z * w * x)) → 0 < nrd x →
    pairY (x * yq * z) ≤ n → P x := by
  induction n with
  | zero =>
    intro x z hxz _ _ hpos hle
    have := pairY_ge hxz hpos
    push_cast at hle; linarith
  | succ n ih =>
    intro x z hxz hzx hN hpos hle
    have hvO : PkgI1.InO (x * yq * z) := (hN _ inO_yq).1
    obtain ⟨hre, hn⟩ := pure_of_sq (conj_sq hxz hzx)
    obtain ⟨m, hm⟩ := pairY_int hvO hre
    have hge := pairY_ge hxz hpos
    -- a step by a pair `(s, si)`
    have step : ∀ s si : PkgI1.B, s * si = 1 → si * s = 1 →
        (∀ w, PkgI1.InO w → PkgI1.InO (s * w * si) ∧ PkgI1.InO (si * w * s)) →
        P s → 0 < nrd s → pairY (s * (x * yq * z) * si) < pairY (x * yq * z) → P x := by
      intro s si hs1 hs2 hsN hPs hspos hlt
      have hx' : P (s * x) := by
        refine ih (s * x) (z * si) ?_ ?_ ?_ ?_ ?_
        · calc s * x * (z * si) = s * (x * z) * si := by simp only [mul_assoc]
            _ = 1 := by rw [hxz, mul_one, hs1]
        · calc z * si * (s * x) = z * (si * s) * x := by simp only [mul_assoc]
            _ = 1 := by rw [hs2, mul_one, hzx]
        · intro w hw
          constructor
          · have := (hsN _ (hN w hw).1).1
            have e : s * x * w * (z * si) = s * (x * w * z) * si := by simp only [mul_assoc]
            rw [e]; exact this
          · have := (hN _ (hsN w hw).2).2
            have e : z * si * w * (s * x) = z * (si * w * s) * x := by simp only [mul_assoc]
            rw [e]; exact this
        · rw [nrd_mul]; exact mul_pos hspos hpos
        · have hvO' : PkgI1.InO (s * (x * yq * z) * si) := (hsN _ hvO).1
          have hsq : (s * (x * yq * z) * si) * (s * (x * yq * z) * si) = -1 := by
            calc (s * (x * yq * z) * si) * (s * (x * yq * z) * si)
                = s * ((x * yq * z) * ((si * s) * (x * yq * z))) * si := by
                  simp only [mul_assoc]
              _ = -1 := by
                  rw [hs2, one_mul, conj_sq hxz hzx]; simp [hs1]
          obtain ⟨hre', _⟩ := pure_of_sq hsq
          obtain ⟨m', hm'⟩ := pairY_int hvO' hre'
          have e : s * x * yq * (z * si) = s * (x * yq * z) * si := by simp only [mul_assoc]
          rw [e, hm']
          rw [hm, hm'] at hlt
          have hlt' : m' < m := by exact_mod_cast hlt
          have hle' : (m : ℚ) ≤ (n + 1 : ℕ) := hm ▸ hle
          have : m ≤ (n + 1 : ℤ) := by exact_mod_cast hle'
          have : (m' : ℚ) ≤ (n : ℤ) := by exact_mod_cast (by omega : m' ≤ (n : ℤ))
          exact_mod_cast this
      exact P_cancel hPs hx' hspos.ne'
    by_cases h1 : pairY (x * yq * z) = 1
    · exact P_base hxz hzx hN hpos (eq_yq hre hn h1)
    · have h2 : 2 ≤ pairY (x * yq * z) := by
        rw [hm] at h1 hge ⊢
        have : (1 : ℤ) ≤ m := by exact_mod_cast hge
        have : m ≠ 1 := by intro h; apply h1; rw [h]; norm_num
        have : (2 : ℤ) ≤ m := by omega
        exact_mod_cast this
      have hN6 := conj_x6
      have hN4 := conj_x4
      rcases descent hre hn h2 with h | h | h | h
      · exact step x6 x6i x6_x6i x6i_x6 conj_x6 P_x6 (by rw [nrd_x6]; norm_num) h
      · exact step x6i x6 x6i_x6 x6_x6i (fun w hw => ⟨(conj_x6 w hw).2, (conj_x6 w hw).1⟩)
          P_x6i (by rw [nrd_x6i]; norm_num) h
      · refine step (x6 * x4) (x4i * x6i) ?_ ?_ ?_
          (P_mul P_x6 P_x4 (by rw [nrd_x6]; norm_num) (by rw [nrd_x4]; norm_num))
          (by rw [nrd_mul, nrd_x6, nrd_x4]; norm_num) ?_
        · calc x6 * x4 * (x4i * x6i) = x6 * (x4 * x4i) * x6i := by simp only [mul_assoc]
            _ = 1 := by rw [x4_x4i, mul_one, x6_x6i]
        · calc x4i * x6i * (x6 * x4) = x4i * (x6i * x6) * x4 := by simp only [mul_assoc]
            _ = 1 := by rw [x6i_x6, mul_one, x4i_x4]
        · intro w hw
          constructor
          · have := (conj_x6 _ (conj_x4 w hw).1).1
            have e : x6 * x4 * w * (x4i * x6i) = x6 * (x4 * w * x4i) * x6i := by simp only [mul_assoc]
            rw [e]; exact this
          · have := (conj_x4 _ (conj_x6 w hw).2).2
            have e : x4i * x6i * w * (x6 * x4) = x4i * (x6i * w * x6) * x4 := by simp only [mul_assoc]
            rw [e]; exact this
        · simpa only [mul_assoc] using h
      · refine step (x6i * x4i) (x4 * x6) ?_ ?_ ?_
          (P_mul P_x6i P_x4i (by rw [nrd_x6i]; norm_num) (by rw [nrd_x4i]; norm_num))
          (by rw [nrd_mul, nrd_x6i, nrd_x4i]; norm_num) ?_
        · calc x6i * x4i * (x4 * x6) = x6i * (x4i * x4) * x6 := by simp only [mul_assoc]
            _ = 1 := by rw [x4i_x4, mul_one, x6i_x6]
        · calc x4 * x6 * (x6i * x4i) = x4 * (x6 * x6i) * x4i := by simp only [mul_assoc]
            _ = 1 := by rw [x6_x6i, mul_one, x4_x4i]
        · intro w hw
          constructor
          · have := (conj_x6 _ (conj_x4 w hw).2).2
            have e : x6i * x4i * w * (x4 * x6) = x6i * (x4i * w * x4) * x6 := by simp only [mul_assoc]
            rw [e]; exact this
          · have := (conj_x4 _ (conj_x6 w hw).1).1
            have e : x4 * x6 * w * (x6i * x4i) = x4 * (x6 * w * x6i) * x4i := by simp only [mul_assoc]
            rw [e]; exact this
        · simpa only [mul_assoc] using h

/-! ### `GammaStarGen` -/

/-- **`GammaStarGen` is a theorem** (leafq-check; from Mathlib only, no leaf). -/
theorem gammaStarGen_proof : HSyn.G0Split.FibreQM.PeriodGlue.GammaStarGen := by
  intro γ hγ
  obtain ⟨x, ⟨z, hxz, hzx, hN⟩, hγx, hdet⟩ := hγ
  have hpos : 0 < nrd x := by
    rw [hγx, det_iota_eq] at hdet; exact_mod_cast hdet
  exact key ⌈pairY (x * yq * z)⌉₊ x z hxz hzx hN hpos (Nat.le_ceil _) γ hγx



namespace VB

open HSyn.G0Split.FibreQM.PeriodMap (U ValenceBoundGammaStar)
open UpperHalfPlane (num denom denom_ne_zero)

/-! ## The split (leafq-check) -/

open scoped ENNReal

/-- **`e_P`**: the order of the stabilizer of `P` in `Γ*/ℚ^×`, counted as the number of distinct Möbius
maps `z ↦ γ • z` with `γ ∈ Γ*`, `γ • P = P` (the image of `Γ*` in `PSL₂(ℝ)` acts faithfully on `ℍ`; the
rational scalars act trivially). `Nat.card` is `0` if the stabilizer were infinite. -/
noncomputable def ellOrder (P : UpperHalfPlane) : ℕ :=
  Nat.card {f : UpperHalfPlane → UpperHalfPlane //
    ∃ γ ∈ PkgI1.GammaStar, γ • P = P ∧ f = fun z => γ • z}

/-- **LEAF (the valence formula for `Γ*`, inequality form over a finite set of inequivalent points).**
For `F` holomorphic on `ℍ`, not identically zero, with `|F(γτ)| det(γ)^m = |cτ+d|^{2m}|F(τ)|` for all
`γ ∈ Γ*` (weight `k = 2m`, unitary multiplier), and every finite set `T` of pairwise `Γ*`-inequivalent
points: `Σ_{P ∈ T} ord_P(F)/e_P ≤ m/12`.

Published form: for a Fuchsian group `Γ` of the first kind without cusps and `F ≠ 0` an automorphic form of
weight `k` (unitary multiplier), `Σ_{P ∈ Γ\ℍ} ord_P(F)/e_P = (k/4π)·vol(Γ\ℍ) = (k/2)(2g − 2 + Σ_j(1 − 1/e_j))`
(Shimura, *Introduction to the arithmetic theory of automorphic functions*, 1971, Prop. 2.16 and
Thm. 2.20 / formula (2.4.x); Rankin, *Modular forms and functions*, 1977, Thm. 4.1.4 for arbitrary
unitary multiplier systems; theorem numbers UNVERIFIED), with the signature `(0; 2, 4, 6)` of
`Γ*/ℚ^× = N_B(𝒪)⁺/ℚ^×` for the quaternion algebra of discriminant 6 (Takeuchi, J. Fac. Sci. Univ. Tokyo
24 (1977), the arithmetic triangle group `(2,4,6)`; Elkies, ANTS-III (1998) §3; locators UNVERIFIED), so the
right side is `m·(−2 + 1/2 + 3/4 + 5/6) = m/12`. Dropping the points outside `T` (all terms are `≥ 0`)
gives the inequality. A consequence of the published statements. -/
def ValenceFormulaGammaStar : Prop :=
  ∀ (m : ℕ) (F : ℂ → ℂ), AnalyticOnNhd ℂ F U → (∃ z ∈ U, F z ≠ 0) →
    (∀ γ ∈ PkgI1.GammaStar, ∀ z : UpperHalfPlane,
      ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖) →
    ∀ T : Finset UpperHalfPlane,
      (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ PkgI1.GammaStar, γ • z ≠ w) →
      ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (ellOrder z : ℝ≥0∞) ≤ (m : ℝ≥0∞) / 12

/-- **The stabilizer bound `1 ≤ e_P ≤ 6`** (proved below, `ellipticOrderLe6_proof`; the elliptic points of `Γ*` have orders `2, 4, 6`: the
signature `(0; 2, 4, 6)`, Takeuchi 1977; or, independently of the signature, the crystallographic
restriction: for `γ = ι(x)` fixing `P`, `trd(x)²/nrd(x)` is the trace of conjugation by `x` on the
lattice `𝒪`, an integer, so the rotation angle at `P` is a multiple of `π/2` or `π/3`). -/
def EllipticOrderLe6 : Prop := ∀ P : UpperHalfPlane, 0 < ellOrder P ∧ ellOrder P ≤ 6

/-- **The valence count (proved).** `ValenceBoundGammaStar` from the valence formula and `e_P ≤ 6`:
`Σ_T ord_P ≤ Σ_T 6·ord_P/e_P ≤ 6·m/12`. -/
theorem valenceBound_of (h1 : ValenceFormulaGammaStar) (h2 : EllipticOrderLe6) :
    ValenceBoundGammaStar := by
  intro m F hF hne haut T hT
  have hV := h1 m F hF hne haut T hT
  rw [← ENat.toENNReal_le]
  have hsum : ((∑ z ∈ T, analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) =
      ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) :=
    map_sum ENat.toENNRealRingHom _ _
  rw [ENat.toENNReal_mul, hsum, ENat.toENNReal_coe, ENat.toENNReal_ofNat]
  have key : ∀ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) ≤
      6 * (((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (ellOrder z : ℝ≥0∞)) := by
    intro z _
    obtain ⟨h0, h6⟩ := h2 z
    set a : ℝ≥0∞ := ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞)
    calc a = 6 * (a / 6) := (ENNReal.mul_div_cancel (by norm_num) (by norm_num)).symm
      _ ≤ 6 * (a / (ellOrder z : ℝ≥0∞)) := by
        gcongr
        exact_mod_cast h6
  calc 2 * ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞)
      ≤ 2 * ∑ z ∈ T, 6 * (((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (ellOrder z : ℝ≥0∞)) := by
        gcongr with z hz; exact key z hz
    _ = 12 * ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (ellOrder z : ℝ≥0∞) := by
        rw [← Finset.mul_sum, ← mul_assoc]; norm_num
    _ ≤ 12 * ((m : ℝ≥0∞) / 12) := by gcongr
    _ = m := ENNReal.mul_div_cancel (by norm_num) (by norm_num)


/-! ## `EllipticOrderLe6` proved (crystallographic restriction; leafq-check)

For `γ = ι(x) ∈ Γ*` fixing `P`, put `μ = cP + d` and `ζ = det γ/μ² = μ̄/μ` (the rotation multiplier at `P`).
Then `|ζ| = 1`, `2 Re ζ = trd(x)²/nrd(x) − 2`, and `trd(x)²/nrd(x) = 4 re(x)²/nrd(x)` is the trace of
conjugation by `x` on the lattice `𝒪`, an integer; so `ζ` is one of the eight numbers
`±1, ±i, (±1 ± i√3)/2`. `γ ↦ ζ` is multiplicative on the stabilizer and determines the Möbius map, and a
product `(±1/2 ± i√3/2)·(±i)` is not among the eight, so the stabilizer embeds in `μ₄` or in `μ₆`. -/

section Elliptic

open PkgI1 ComplexConjugate

theorem sqrt2_sq' : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)

theorem iota_apply (x : PkgI1.B) : PkgI1.iota x =
    !![(x.re : ℝ) + x.imI * √2, -3 * (x.imJ : ℝ) - 3 * √2 * x.imK;
       (x.imJ : ℝ) - √2 * x.imK, (x.re : ℝ) - x.imI * √2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PkgI1.iota, PkgI1.Mi, PkgI1.Mj] <;> ring

theorem iota_mul (x y : PkgI1.B) : PkgI1.iota (x * y) = PkgI1.iota x * PkgI1.iota y := by
  rw [iota_apply, iota_apply, iota_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    (try simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]) <;> (try ring_nf)

/-- The reduced norm. -/
def nrd (x : PkgI1.B) : ℚ := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2

theorem det_iota_eq (x : PkgI1.B) : (PkgI1.iota x).det = (nrd x : ℝ) := by
  rw [iota_apply, Matrix.det_fin_two_of, nrd]
  push_cast
  linear_combination (-(x.imI : ℝ) ^ 2 - 3 * (x.imK : ℝ) ^ 2) * sqrt2_sq'

theorem inO_iff (v : PkgI1.B) : PkgI1.InO v ↔ ∃ n0 n1 n2 n3 : ℤ,
    v = ⟨n0 + n2 / 2, n1 + n3 / 2, n2 / 2, n3 / 2⟩ := by
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n 0, n 1, n 2, n 3, ?_⟩
    ext <;> simp [PkgI1.oBasis, Fin.sum_univ_four] <;> ring
  · rintro ⟨n0, n1, n2, n3, rfl⟩
    refine ⟨![n0, n1, n2, n3], ?_⟩
    ext <;> simp [PkgI1.oBasis, Fin.sum_univ_four] <;> ring

theorem inv_eq {x z : PkgI1.B} (hxz : x * z = 1) (hN : nrd x ≠ 0) :
    z = ⟨x.re / nrd x, -x.imI / nrd x, -x.imJ / nrd x, -x.imK / nrd x⟩ := by
  set w : PkgI1.B := ⟨x.re / nrd x, -x.imI / nrd x, -x.imJ / nrd x, -x.imK / nrd x⟩ with hw_def
  have hN' : x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 ≠ 0 := hN
  have hw : w * x = 1 := by
    ext <;> simp [w, nrd] <;> field_simp <;> ring
  calc z = (w * x) * z := by rw [hw, one_mul]
    _ = w * (x * z) := mul_assoc _ _ _
    _ = w := by rw [hxz, mul_one]

/-- The integer coordinates of `w ∈ 𝒪` in N5's basis. -/
theorem inO_coords {w : PkgI1.B} (hw : PkgI1.InO w) : ∃ n0 n1 n2 n3 : ℤ,
    w.re - w.imJ = n0 ∧ w.imI - w.imK = n1 ∧ 2 * w.imJ = n2 ∧ 2 * w.imK = n3 := by
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff w).1 hw
  exact ⟨n0, n1, n2, n3, by simp, by simp, by simp; ring, by simp; ring⟩

theorem oBasis_mem (k : Fin 4) : PkgI1.InO (PkgI1.oBasis k) := by
  rw [inO_iff]
  fin_cases k
  · exact ⟨1, 0, 0, 0, by ext <;> simp [PkgI1.oBasis]⟩
  · exact ⟨0, 1, 0, 0, by ext <;> simp [PkgI1.oBasis]⟩
  · exact ⟨0, 0, 1, 0, by ext <;> simp [PkgI1.oBasis]⟩
  · exact ⟨0, 0, 0, 1, by ext <;> simp [PkgI1.oBasis]⟩

/-- **The trace of conjugation by `x` on `𝒪` is the integer `4 re(x)²/nrd(x)`.** -/
theorem adTrace_int {x z : PkgI1.B} (hxz : x * z = 1)
    (hN : ∀ w, PkgI1.InO w → PkgI1.InO (x * w * z) ∧ PkgI1.InO (z * w * x)) (hn : nrd x ≠ 0) :
    ∃ k : ℤ, 4 * x.re ^ 2 / nrd x = k := by
  obtain ⟨a0, -, -, -, ha0, -, -, -⟩ := inO_coords (hN _ (oBasis_mem 0)).1
  obtain ⟨-, a1, -, -, -, ha1, -, -⟩ := inO_coords (hN _ (oBasis_mem 1)).1
  obtain ⟨-, -, a2, -, -, -, ha2, -⟩ := inO_coords (hN _ (oBasis_mem 2)).1
  obtain ⟨-, -, -, a3, -, -, -, ha3⟩ := inO_coords (hN _ (oBasis_mem 3)).1
  refine ⟨a0 + a1 + a2 + a3, ?_⟩
  push_cast
  rw [← ha0, ← ha1, ← ha2, ← ha3, inv_eq hxz hn]
  have hn' : x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 ≠ 0 := hn
  simp [PkgI1.oBasis, nrd]
  field_simp
  ring

/-- `Γ*` is closed under products. -/
theorem gammaStar_mul {γ γ' : GL (Fin 2) ℝ} (h : γ ∈ PkgI1.GammaStar) (h' : γ' ∈ PkgI1.GammaStar) :
    γ * γ' ∈ PkgI1.GammaStar := by
  obtain ⟨x, ⟨z, hxz, hzx, hN⟩, hγ, hd⟩ := h
  obtain ⟨x', ⟨z', hxz', hzx', hN'⟩, hγ', hd'⟩ := h'
  refine ⟨x * x', ⟨z' * z, ?_, ?_, fun w hw => ⟨?_, ?_⟩⟩, ?_, ?_⟩
  · calc x * x' * (z' * z) = x * (x' * z') * z := by simp only [mul_assoc]
      _ = 1 := by rw [hxz', mul_one, hxz]
  · calc z' * z * (x * x') = z' * (z * x) * x' := by simp only [mul_assoc]
      _ = 1 := by rw [hzx, mul_one, hzx']
  · have := (hN _ (hN' w hw).1).1
    have e : x * x' * w * (z' * z) = x * (x' * w * z') * z := by simp only [mul_assoc]
    rw [e]; exact this
  · have := (hN' _ (hN w hw).2).2
    have e : z' * z * w * (x * x') = z' * (z * w * x) * x' := by simp only [mul_assoc]
    rw [e]; exact this
  · rw [Units.val_mul, hγ, hγ', iota_mul]
  · rw [Units.val_mul, Matrix.det_mul]; exact mul_pos hd hd'

theorem one_mem_gammaStar' : (1 : GL (Fin 2) ℝ) ∈ PkgI1.GammaStar := by
  refine ⟨1, ⟨1, mul_one 1, mul_one 1, fun w hw => by simpa using hw⟩, ?_, by simp⟩
  rw [iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp

/-- The rotation multiplier `det γ / (cP + d)²`. -/
noncomputable def zeta (γ : GL (Fin 2) ℝ) (P : UpperHalfPlane) : ℂ :=
  (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) / denom γ P ^ 2

theorem fixed_data {γ : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    {P : UpperHalfPlane} (hP : γ • P = P) :
    (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 =
        2 * (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * P.re + (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 =
        -(γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (P.re ^ 2 + P.im ^ 2) := by
  have hd' : 0 < γ.det.val := by rwa [Matrix.GeneralLinearGroup.val_det_apply]
  have h := congrArg (fun w : UpperHalfPlane => (w : ℂ)) hP
  rw [UpperHalfPlane.coe_smul_of_det_pos hd', div_eq_iff (denom_ne_zero γ P)] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [UpperHalfPlane.num, UpperHalfPlane.denom] at hre him
  have hq := P.im_pos
  have ha : ((γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 - 2 * (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * P.re -
      (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1) * P.im = 0 := by linear_combination him
  have ha' := (mul_eq_zero.1 ha).resolve_right hq.ne'
  refine ⟨by linarith, ?_⟩
  have : (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 =
      2 * (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * P.re + (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
    linarith
  rw [this] at hre
  linear_combination hre

theorem det_eq_normSq {γ : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    {P : UpperHalfPlane} (hP : γ • P = P) :
    (γ : Matrix (Fin 2) (Fin 2) ℝ).det = Complex.normSq (denom γ P) := by
  obtain ⟨ha, hb⟩ := fixed_data hd hP
  rw [Matrix.det_fin_two, ha, hb]
  simp [UpperHalfPlane.denom, Complex.normSq_apply]
  ring

theorem zeta_eq {γ : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    {P : UpperHalfPlane} (hP : γ • P = P) : zeta γ P = conj (denom γ P) / denom γ P := by
  have h0 := denom_ne_zero γ P
  unfold zeta
  rw [det_eq_normSq hd hP, Complex.normSq_eq_conj_mul_self]
  field_simp

theorem zeta_normSq {γ : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    {P : UpperHalfPlane} (hP : γ • P = P) : Complex.normSq (zeta γ P) = 1 := by
  rw [zeta_eq hd hP, map_div₀, Complex.normSq_conj, div_self]
  exact (Complex.normSq_pos.2 (denom_ne_zero γ P)).ne'

theorem zeta_re {γ : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    {P : UpperHalfPlane} (hP : γ • P = P) :
    2 * (zeta γ P).re = ((γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2 /
      (γ : Matrix (Fin 2) (Fin 2) ℝ).det - 2 := by
  have hpos := Complex.normSq_pos.2 (denom_ne_zero γ P)
  obtain ⟨ha, -⟩ := fixed_data hd hP
  rw [zeta_eq hd hP, det_eq_normSq hd hP, Complex.div_re, ha]
  simp only [Complex.conj_re, Complex.conj_im]
  have hn : Complex.normSq (denom γ P) = (denom γ P).re ^ 2 + (denom γ P).im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  have hre : (denom γ P).re = (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * P.re +
      (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by simp [UpperHalfPlane.denom]
  field_simp
  rw [hn, hre]
  ring

/-- The eight values. -/
noncomputable def w1 : ℂ := ⟨-1 / 2, √3 / 2⟩
noncomputable def w2 : ℂ := ⟨-1 / 2, -(√3 / 2)⟩
noncomputable def w3 : ℂ := ⟨1 / 2, √3 / 2⟩
noncomputable def w4 : ℂ := ⟨1 / 2, -(√3 / 2)⟩

theorem sqrt3_sq : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem unit_cases (ζ : ℂ) (h1 : Complex.normSq ζ = 1) (k : ℤ) (hk : 2 * ζ.re = k - 2) :
    ζ = 1 ∨ ζ = -1 ∨ ζ = Complex.I ∨ ζ = -Complex.I ∨ ζ = w1 ∨ ζ = w2 ∨ ζ = w3 ∨ ζ = w4 := by
  rw [Complex.normSq_apply] at h1
  have hk0 : (0 : ℝ) ≤ k := by nlinarith [sq_nonneg ζ.im, sq_nonneg (ζ.re + 1)]
  have hk4 : (k : ℝ) ≤ 4 := by nlinarith [sq_nonneg ζ.im, sq_nonneg (ζ.re - 1)]
  have hk0' : 0 ≤ k := by exact_mod_cast hk0
  have hk4' : k ≤ 4 := by exact_mod_cast hk4
  have s3 := sqrt3_sq
  interval_cases k
  · -- re = -1
    have hr : ζ.re = -1 := by push_cast at hk; linarith
    have hi : ζ.im = 0 := by nlinarith [sq_nonneg ζ.im]
    right; left; exact Complex.ext (by simp [hr]) (by simp [hi])
  · -- re = -1/2
    have hr : ζ.re = -1 / 2 := by push_cast at hk; linarith
    have hi : (ζ.im - √3 / 2) * (ζ.im + √3 / 2) = 0 := by
      rw [hr] at h1; linear_combination h1 - s3 / 4
    rcases mul_eq_zero.1 hi with h | h
    · right; right; right; right; left; exact Complex.ext (by simp [w1, hr]) (by simp [w1]; linarith)
    · right; right; right; right; right; left
      exact Complex.ext (by simp [w2, hr]) (by simp [w2]; linarith)
  · -- re = 0
    have hr : ζ.re = 0 := by push_cast at hk; linarith
    have hi : (ζ.im - 1) * (ζ.im + 1) = 0 := by rw [hr] at h1; linear_combination h1
    rcases mul_eq_zero.1 hi with h | h
    · right; right; left; exact Complex.ext (by simp [hr]) (by simp; linarith)
    · right; right; right; left; exact Complex.ext (by simp [hr]) (by simp; linarith)
  · -- re = 1/2
    have hr : ζ.re = 1 / 2 := by push_cast at hk; linarith
    have hi : (ζ.im - √3 / 2) * (ζ.im + √3 / 2) = 0 := by
      rw [hr] at h1; linear_combination h1 - s3 / 4
    rcases mul_eq_zero.1 hi with h | h
    · right; right; right; right; right; right; left
      exact Complex.ext (by simp [w3, hr]) (by simp [w3]; linarith)
    · right; right; right; right; right; right; right
      exact Complex.ext (by simp [w4, hr]) (by simp [w4]; linarith)
  · -- re = 1
    have hr : ζ.re = 1 := by push_cast at hk; linarith
    have hi : ζ.im = 0 := by nlinarith [sq_nonneg ζ.im]
    left; exact Complex.ext (by simp [hr]) (by simp [hi])


theorem sigma_of_pos {g : GL (Fin 2) ℝ} (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det) (w : ℂ) :
    UpperHalfPlane.σ g w = w := by
  have h' : 0 < g.det.val := by rwa [Matrix.GeneralLinearGroup.val_det_apply]
  simp [UpperHalfPlane.σ, hg]

theorem zeta_mul {γ γ' : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    (hd' : 0 < (γ' : Matrix (Fin 2) (Fin 2) ℝ).det) {P : UpperHalfPlane} (hP' : γ' • P = P) :
    zeta (γ * γ') P = zeta γ P * zeta γ' P := by
  have hden : denom (γ * γ') P = denom γ P * denom γ' P := by
    rw [UpperHalfPlane.denom_cocycle_σ, hP', sigma_of_pos hd']
  have h0 := denom_ne_zero γ P
  have h0' := denom_ne_zero γ' P
  unfold zeta
  rw [hden, Units.val_mul, Matrix.det_mul]
  push_cast
  field_simp

theorem zeta_inj {γ γ' : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    (hd' : 0 < (γ' : Matrix (Fin 2) (Fin 2) ℝ).det) {P : UpperHalfPlane} (hP : γ • P = P)
    (hP' : γ' • P = P) (h : zeta γ P = zeta γ' P) (z : UpperHalfPlane) : γ • z = γ' • z := by
  rw [zeta_eq hd hP, zeta_eq hd' hP'] at h
  have h0 := denom_ne_zero γ P
  have h0' := denom_ne_zero γ' P
  rw [div_eq_div_iff h0 h0'] at h
  -- `u v' = v u'` for `μ = u + iv`, `μ' = u' + iv'`
  have him := congrArg Complex.im h
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at him
  set u := (denom γ P).re
  set v := (denom γ P).im
  set u' := (denom γ' P).re
  set v' := (denom γ' P).im
  have hpar : u * v' = v * u' := by linarith
  have hn : 0 < u ^ 2 + v ^ 2 := by
    have := Complex.normSq_pos.2 h0; rw [Complex.normSq_apply] at this; nlinarith
  set r := (u * u' + v * v') / (u ^ 2 + v ^ 2) with hr
  have hu' : u' = r * u := by rw [hr]; field_simp; linear_combination (-v) * hpar
  have hv' : v' = r * v := by rw [hr]; field_simp; linear_combination u * hpar
  -- entries
  obtain ⟨ha, hb⟩ := fixed_data hd hP
  obtain ⟨ha', hb'⟩ := fixed_data hd' hP'
  have hq := P.im_pos
  have hc : v = (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * P.im := by simp [v, UpperHalfPlane.denom]
  have hc' : v' = (γ' : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * P.im := by simp [v', UpperHalfPlane.denom]
  have hdd : u = (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * P.re + (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
    simp [u, UpperHalfPlane.denom]
  have hdd' : u' = (γ' : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * P.re +
      (γ' : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by simp [u', UpperHalfPlane.denom]
  have e10 : (γ' : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = r * (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by
    have : ((γ' : Matrix (Fin 2) (Fin 2) ℝ) 1 0 - r * (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0) * P.im = 0 := by
      linear_combination -hc' + r * hc + hv'
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hq.ne')
  have e11 : (γ' : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = r * (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
    have := hu'; rw [hdd', hdd, e10] at this; linarith
  have e00 : (γ' : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = r * (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := by
    rw [ha', ha, e10, e11]; ring
  have e01 : (γ' : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = r * (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := by
    rw [hb', hb, e10]; ring
  have hr0 : r ≠ 0 := by
    intro h0r; apply h0'; apply Complex.ext
    · change u' = 0; rw [hu', h0r, zero_mul]
    · change v' = 0; rw [hv', h0r, zero_mul]
  have hdpos : 0 < γ.det.val := by rwa [Matrix.GeneralLinearGroup.val_det_apply]
  have hdpos' : 0 < γ'.det.val := by rwa [Matrix.GeneralLinearGroup.val_det_apply]
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos hdpos, UpperHalfPlane.coe_smul_of_det_pos hdpos']
  have hz0 := denom_ne_zero γ z
  have hz0' := denom_ne_zero γ' z
  rw [div_eq_div_iff hz0 hz0']
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom]
  rw [e00, e01, e10, e11]
  push_cast
  ring

theorem zeta_cases_gammaStar {γ : GL (Fin 2) ℝ} (hγ : γ ∈ PkgI1.GammaStar) {P : UpperHalfPlane}
    (hP : γ • P = P) :
    zeta γ P = 1 ∨ zeta γ P = -1 ∨ zeta γ P = Complex.I ∨ zeta γ P = -Complex.I ∨
      zeta γ P = w1 ∨ zeta γ P = w2 ∨ zeta γ P = w3 ∨ zeta γ P = w4 := by
  obtain ⟨x, ⟨z, hxz, -, hN⟩, hγx, hd⟩ := hγ
  have hn : nrd x ≠ 0 := by
    intro h0; rw [hγx, det_iota_eq, h0] at hd; simp at hd
  obtain ⟨k, hk⟩ := adTrace_int hxz hN hn
  refine unit_cases _ (zeta_normSq hd hP) k ?_
  rw [zeta_re hd hP, hγx, det_iota_eq, iota_apply]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  have hk' : (4 * (x.re : ℝ) ^ 2 / (nrd x : ℝ)) = k := by exact_mod_cast hk
  rw [← hk']
  ring

theorem w_mul_I_re (ζ : ℂ) (hζ : ζ = w1 ∨ ζ = w2 ∨ ζ = w3 ∨ ζ = w4) (ξ : ℂ)
    (hξ : ξ = Complex.I ∨ ξ = -Complex.I) : (ζ * ξ).re = √3 / 2 ∨ (ζ * ξ).re = -(√3 / 2) := by
  rcases hξ with rfl | rfl <;> rcases hζ with rfl | rfl | rfl | rfl <;>
    simp [w1, w2, w3, w4]

theorem eight_re (ζ : ℂ) (h : ζ = 1 ∨ ζ = -1 ∨ ζ = Complex.I ∨ ζ = -Complex.I ∨ ζ = w1 ∨ ζ = w2 ∨
    ζ = w3 ∨ ζ = w4) : ζ.re = 1 ∨ ζ.re = -1 ∨ ζ.re = 0 ∨ ζ.re = 1 / 2 ∨ ζ.re = -1 / 2 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [w1, w2, w3, w4]

theorem sqrt3_half_ne (t : ℝ) (ht : t = √3 / 2 ∨ t = -(√3 / 2)) :
    ¬ (t = 1 ∨ t = -1 ∨ t = 0 ∨ t = 1 / 2 ∨ t = -1 / 2) := by
  have s3 := sqrt3_sq
  have hs : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  rcases ht with rfl | rfl <;> rintro (h | h | h | h | h) <;> nlinarith

/-- **`EllipticOrderLe6` is a theorem** (leafq-check; Mathlib only). -/
theorem ellipticOrderLe6_proof : EllipticOrderLe6 := by
  intro P
  set S := {f : UpperHalfPlane → UpperHalfPlane //
    ∃ γ ∈ PkgI1.GammaStar, γ • P = P ∧ f = fun z => γ • z}
  have hdet : ∀ γ ∈ PkgI1.GammaStar, 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det :=
    fun γ ⟨_, _, _, hd⟩ => hd
  -- either all multipliers lie in `μ₄` or all lie in `μ₆`
  let m4 : Fin 4 → ℂ := ![1, -1, Complex.I, -Complex.I]
  let m6 : Fin 6 → ℂ := ![1, -1, w1, w2, w3, w4]
  have hZ : ∃ Z : Finset ℂ, Z.card ≤ 6 ∧
      ∀ γ ∈ PkgI1.GammaStar, γ • P = P → zeta γ P ∈ Z := by
    by_cases h4 : ∀ γ ∈ PkgI1.GammaStar, γ • P = P →
        (zeta γ P = 1 ∨ zeta γ P = -1 ∨ zeta γ P = Complex.I ∨ zeta γ P = -Complex.I)
    · refine ⟨Finset.univ.image m4, (Finset.card_image_le).trans (by simp), fun γ hγ hP => ?_⟩
      rw [Finset.mem_image]
      rcases h4 γ hγ hP with h | h | h | h
      · exact ⟨0, Finset.mem_univ _, by simp [m4, h]⟩
      · exact ⟨1, Finset.mem_univ _, by simp [m4, h]⟩
      · exact ⟨2, Finset.mem_univ _, by simp [m4, h]⟩
      · exact ⟨3, Finset.mem_univ _, by simp [m4, h]⟩
    · push_neg at h4
      obtain ⟨γ2, hγ2, hP2, h2⟩ := h4
      have h2w : zeta γ2 P = w1 ∨ zeta γ2 P = w2 ∨ zeta γ2 P = w3 ∨ zeta γ2 P = w4 := by
        rcases zeta_cases_gammaStar hγ2 hP2 with h | h | h | h | h
        · exact absurd h h2.1
        · exact absurd h h2.2.1
        · exact absurd h h2.2.2.1
        · exact absurd h h2.2.2.2
        · exact h
      refine ⟨Finset.univ.image m6, (Finset.card_image_le).trans (by simp), fun γ hγ hP => ?_⟩
      rw [Finset.mem_image]
      rcases zeta_cases_gammaStar hγ hP with h | h | h | h | h | h | h | h
      · exact ⟨0, Finset.mem_univ _, by simp [m6, h]⟩
      · exact ⟨1, Finset.mem_univ _, by simp [m6, h]⟩
      · exfalso
        have hm := zeta_cases_gammaStar (gammaStar_mul hγ2 hγ) (by rw [mul_smul, hP, hP2])
        rw [zeta_mul (hdet _ hγ2) (hdet _ hγ) hP] at hm
        exact sqrt3_half_ne _ (w_mul_I_re _ h2w _ (Or.inl h)) (eight_re _ hm)
      · exfalso
        have hm := zeta_cases_gammaStar (gammaStar_mul hγ2 hγ) (by rw [mul_smul, hP, hP2])
        rw [zeta_mul (hdet _ hγ2) (hdet _ hγ) hP] at hm
        exact sqrt3_half_ne _ (w_mul_I_re _ h2w _ (Or.inr h)) (eight_re _ hm)
      · exact ⟨2, Finset.mem_univ _, by simp [m6, h]⟩
      · exact ⟨3, Finset.mem_univ _, by simp [m6, h]⟩
      · exact ⟨4, Finset.mem_univ _, by simp [m6, h]⟩
      · exact ⟨5, Finset.mem_univ _, by simp [m6, h]⟩
  obtain ⟨Z, hZc, hZ⟩ := hZ
  let Ψ : S → Z := fun f => ⟨zeta (Classical.choose f.2) P,
    hZ _ (Classical.choose_spec f.2).1 (Classical.choose_spec f.2).2.1⟩
  have hΨ : Function.Injective Ψ := by
    intro f f' hff
    have h := congrArg Subtype.val hff
    simp only [Ψ] at h
    obtain ⟨hγ, hP, hf⟩ := Classical.choose_spec f.2
    obtain ⟨hγ', hP', hf'⟩ := Classical.choose_spec f'.2
    apply Subtype.ext
    rw [hf, hf']
    funext z
    exact zeta_inj (hdet _ hγ) (hdet _ hγ') hP hP' h z
  have hfin : Finite S := Finite.of_injective Ψ hΨ
  have hne : Nonempty S :=
    ⟨⟨fun z => (1 : GL (Fin 2) ℝ) • z, 1, one_mem_gammaStar', one_smul _ _, rfl⟩⟩
  refine ⟨Nat.card_pos, ?_⟩
  calc Nat.card S ≤ Nat.card Z := Nat.card_le_card_of_injective Ψ hΨ
    _ = Z.card := Nat.card_eq_finsetCard Z
    _ ≤ 6 := hZc

/-- **`ValenceBoundGammaStar` from the valence formula alone.** -/
theorem valenceBound_of_formula (h1 : ValenceFormulaGammaStar) : ValenceBoundGammaStar :=
  valenceBound_of h1 ellipticOrderLe6_proof

end Elliptic


end VB
end HDec.LeafQCheck


/-! ## `QMHauptmodul` (copied from `QMHauptmodulCM.lean`) -/


namespace HDec.LeafQCheck.HM

open PkgI1

theorem sqrt2_sq' : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)

theorem iota_apply (x : PkgI1.B) : PkgI1.iota x =
    !![(x.re : ℝ) + x.imI * √2, -3 * (x.imJ : ℝ) - 3 * √2 * x.imK;
       (x.imJ : ℝ) - √2 * x.imK, (x.re : ℝ) - x.imI * √2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PkgI1.iota, PkgI1.Mi, PkgI1.Mj, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem iota_mul (x y : PkgI1.B) : PkgI1.iota (x * y) = PkgI1.iota x * PkgI1.iota y := by
  rw [iota_apply, iota_apply, iota_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    (try simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]) <;> (try ring_nf)

/-- The reduced norm. -/
def nrd (x : PkgI1.B) : ℚ := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2

theorem det_iota_eq (x : PkgI1.B) : (PkgI1.iota x).det = (nrd x : ℝ) := by
  rw [iota_apply, Matrix.det_fin_two_of, nrd]
  push_cast
  linear_combination (-(x.imI : ℝ) ^ 2 - 3 * (x.imK : ℝ) ^ 2) * sqrt2_sq'

theorem nrd_mul (x y : PkgI1.B) : nrd (x * y) = nrd x * nrd y := by
  simp [nrd]; ring

theorem iota_ratCast (q : ℚ) : PkgI1.iota (q : PkgI1.B) = (q : ℝ) • 1 := by
  rw [iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp

theorem inO_iff (v : PkgI1.B) : PkgI1.InO v ↔ ∃ n0 n1 n2 n3 : ℤ,
    v = ⟨n0 + n2 / 2, n1 + n3 / 2, n2 / 2, n3 / 2⟩ := by
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n 0, n 1, n 2, n 3, ?_⟩
    ext <;> simp [PkgI1.oBasis, Fin.sum_univ_four] <;> ring
  · rintro ⟨n0, n1, n2, n3, rfl⟩
    refine ⟨![n0, n1, n2, n3], ?_⟩
    ext <;> simp [PkgI1.oBasis, Fin.sum_univ_four] <;> ring

theorem inv_eq {x z : PkgI1.B} (hxz : x * z = 1) (hN : nrd x ≠ 0) :
    z = ⟨x.re / nrd x, -x.imI / nrd x, -x.imJ / nrd x, -x.imK / nrd x⟩ := by
  set w : PkgI1.B := ⟨x.re / nrd x, -x.imI / nrd x, -x.imJ / nrd x, -x.imK / nrd x⟩ with hw_def
  have hN' : x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 ≠ 0 := hN
  have hw : w * x = 1 := by
    ext <;> simp [w, nrd] <;> field_simp <;> ring
  calc z = (w * x) * z := by rw [hw, one_mul]
    _ = w * (x * z) := mul_assoc _ _ _
    _ = w := by rw [hxz, mul_one]



/-! ### The hyperboloid form -/

/-- The bilinear form of `nrd` on pure quaternions. -/
def form (v u : PkgI1.B) : ℚ := -2 * v.imI * u.imI + 3 * v.imJ * u.imJ - 6 * v.imK * u.imK

/-- Two timelike vectors in the upper cone (`imJ > 0`) pair positively (reverse Cauchy–Schwarz). -/
theorem form_pos {v u : PkgI1.B} (hv : 0 < form v v) (hu : 0 < form u u) (hv' : 0 < v.imJ)
    (hu' : 0 < u.imJ) : 0 < form v u := by
  simp only [form] at *
  set X := 2 * v.imI * u.imI + 6 * v.imK * u.imK
  have hL : X ^ 2 ≤ (2 * v.imI ^ 2 + 6 * v.imK ^ 2) * (2 * u.imI ^ 2 + 6 * u.imK ^ 2) := by
    nlinarith [sq_nonneg (v.imI * u.imK - v.imK * u.imI)]
  have hSv : 0 ≤ 2 * v.imI ^ 2 + 6 * v.imK ^ 2 := by positivity
  have hSu : 0 ≤ 2 * u.imI ^ 2 + 6 * u.imK ^ 2 := by positivity
  have hP : (2 * v.imI ^ 2 + 6 * v.imK ^ 2) * (2 * u.imI ^ 2 + 6 * u.imK ^ 2) <
      (3 * v.imJ ^ 2) * (3 * u.imJ ^ 2) := by
    apply mul_lt_mul'' <;> nlinarith
  by_contra hc
  push_neg at hc
  have hX : 3 * v.imJ * u.imJ ≤ X := by linarith
  have h0 : 0 < 3 * v.imJ * u.imJ := by positivity
  nlinarith

theorem imJ_pos_of_form {v u : PkgI1.B} (hv : 0 < form v v) (hu : 0 < form u u) (hu' : 0 < u.imJ)
    (h : 0 < form v u) : 0 < v.imJ := by
  rcases lt_trichotomy v.imJ 0 with hn | hz | hp
  · have h' := form_pos (v := -v) (by simpa [form] using hv) hu (by simpa using hn) hu'
    simp [form] at h' h
    linarith
  · simp [form, hz] at hv; nlinarith [sq_nonneg v.imI, sq_nonneg v.imK]
  · exact hp

theorem pure_of_sqN {v : PkgI1.B} (N : ℚ) (hN : 0 < N) (h : v * v = -((N : ℚ) : PkgI1.B)) :
    v.re = 0 ∧ form v v = N := by
  have h1 : v.re ^ 2 + 2 * v.imI ^ 2 - 3 * v.imJ ^ 2 + 6 * v.imK ^ 2 = -N := by
    have := congrArg QuaternionAlgebra.re h; simp at this; linear_combination this
  have h2 : v.re * v.imI = 0 := by
    have := congrArg QuaternionAlgebra.imI h; simp at this; linear_combination this / 2
  have h3 : v.re * v.imJ = 0 := by
    have := congrArg QuaternionAlgebra.imJ h; simp at this; linear_combination this / 2
  have h4 : v.re * v.imK = 0 := by
    have := congrArg QuaternionAlgebra.imK h; simp at this; linear_combination this / 2
  have key : v.re ^ 2 * (v.re ^ 2 + N) = 0 := by
    linear_combination v.re ^ 2 * h1 - 2 * (v.re * v.imI) * h2 + 3 * (v.re * v.imJ) * h3
      - 6 * (v.re * v.imK) * h4
  have hre : v.re = 0 := by
    rcases mul_eq_zero.1 key with h | h
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    · nlinarith [sq_nonneg v.re]
  refine ⟨hre, ?_⟩
  rw [hre] at h1; simp only [form]; linear_combination -h1

/-! ### The generic orbit induction -/

/-- Normalizer data: `g` and its inverse `gi` normalize `𝒪`, `nrd g > 0`. -/
def NormData (g gi : PkgI1.B) : Prop :=
  g * gi = 1 ∧ gi * g = 1 ∧ (∀ z, PkgI1.InO z → PkgI1.InO (g * z * gi) ∧ PkgI1.InO (gi * z * g)) ∧
    0 < nrd g

theorem NormData.one : NormData 1 1 :=
  ⟨mul_one 1, mul_one 1, fun z hz => by simpa using hz, by norm_num [nrd]⟩

theorem NormData.mul {g gi h hi : PkgI1.B} (hg : NormData g gi) (hh : NormData h hi) :
    NormData (g * h) (hi * gi) := by
  obtain ⟨g1, g2, g3, g4⟩ := hg
  obtain ⟨h1, h2, h3, h4⟩ := hh
  refine ⟨?_, ?_, fun z hz => ⟨?_, ?_⟩, ?_⟩
  · calc g * h * (hi * gi) = g * (h * hi) * gi := by simp only [mul_assoc]
      _ = 1 := by rw [h1, mul_one, g1]
  · calc hi * gi * (g * h) = hi * (gi * g) * h := by simp only [mul_assoc]
      _ = 1 := by rw [g2, mul_one, h2]
  · have e : g * h * z * (hi * gi) = g * (h * z * hi) * gi := by simp only [mul_assoc]
    rw [e]; exact (g3 _ (h3 z hz).1).1
  · have e : hi * gi * z * (g * h) = hi * (gi * z * g) * h := by simp only [mul_assoc]
    rw [e]; exact (h3 _ (g3 z hz).2).2
  · rw [nrd_mul]; exact mul_pos g4 h4

theorem NormData.symm {g gi : PkgI1.B} (hg : NormData g gi) : NormData gi g := by
  obtain ⟨g1, g2, g3, g4⟩ := hg
  refine ⟨g2, g1, fun z hz => ⟨(g3 z hz).2, (g3 z hz).1⟩, ?_⟩
  have h := congrArg nrd g1
  rw [nrd_mul] at h
  have : nrd (1 : PkgI1.B) = 1 := by norm_num [nrd]
  rw [this] at h
  nlinarith [mul_pos g4 g4]

theorem orbit_of_descent (E : PkgI1.B → Prop) (meas : PkgI1.B → ℚ) (b : PkgI1.B)
    (hint : ∀ w, E w → ∃ k : ℕ, meas w = k)
    (hbase : ∀ w, E w → meas w ≤ meas b → w = b)
    (hstep : ∀ w, E w → meas b < meas w → ∃ s si, NormData s si ∧ E (s * w * si) ∧
      meas (s * w * si) < meas w) :
    ∀ w, E w → ∃ g gi, NormData g gi ∧ g * b * gi = w := by
  intro w hw
  obtain ⟨k, hk⟩ := hint w hw
  induction k using Nat.strong_induction_on generalizing w with
  | _ k ih =>
    by_cases hb : meas w ≤ meas b
    · exact ⟨1, 1, NormData.one, by rw [hbase w hw hb]; simp⟩
    · push_neg at hb
      obtain ⟨s, si, hs, hE, hlt⟩ := hstep w hw hb
      obtain ⟨k', hk'⟩ := hint _ hE
      have hkk : k' < k := by rw [hk, hk'] at hlt; exact_mod_cast hlt
      obtain ⟨g, gi, hg, hgb⟩ := ih k' hkk _ hE hk'
      refine ⟨si * g, gi * s, hs.symm.mul hg, ?_⟩
      have h2 : si * s = 1 := hs.2.1
      calc si * g * b * (gi * s) = si * (g * b * gi) * s := by simp only [mul_assoc]
        _ = si * (s * w * si) * s := by rw [hgb]
        _ = (si * s) * w * (si * s) := by simp only [mul_assoc]
        _ = w := by rw [h2, one_mul, mul_one]

/-! ### Elements -/

def a4 : PkgI1.B := ⟨1, 1, 1, 0⟩
def a4i : PkgI1.B := ⟨1 / 2, -1 / 2, -1 / 2, 0⟩
def a6 : PkgI1.B := ⟨-3 / 2, 0, 1 / 2, 0⟩
def a6i : PkgI1.B := ⟨-1 / 2, 0, -1 / 6, 0⟩
def mu : PkgI1.B := ⟨0, 0, 2, 1⟩
def mui : PkgI1.B := ⟨0, 0, -1 / 3, -1 / 6⟩
/-- `y = i + j` (`y² = −1`). -/
def by4 : PkgI1.B := ⟨0, 1, 1, 0⟩
/-- `j` (`j² = −3`). -/
def bj : PkgI1.B := ⟨0, 0, 1, 0⟩

theorem conj_a4 : ∀ w, PkgI1.InO w → PkgI1.InO (a4 * w * a4i) ∧ PkgI1.InO (a4i * w * a4) := by
  intro w hw
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff w).1 hw
  constructor
  · refine (inO_iff _).2 ⟨n0 + 2*n1 - n2, -n1 + n2 + n3, -4*n1 + 3*n2, -2*n1 + n2 - n3, ?_⟩
    ext <;> simp [a4, a4i] <;> ring
  · refine (inO_iff _).2 ⟨n0 + 2*n1 - n2 + 2*n3, -3*n1 + 2*n2 - 3*n3, -4*n1 + 3*n2 - 4*n3, 2*n1 - n2 + n3, ?_⟩
    ext <;> simp [a4, a4i] <;> ring

theorem conj_a6 : ∀ w, PkgI1.InO w → PkgI1.InO (a6 * w * a6i) ∧ PkgI1.InO (a6i * w * a6) := by
  intro w hw
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff w).1 hw
  constructor
  · refine (inO_iff _).2 ⟨n0, -n3, n2, n1 + n3, ?_⟩
    ext <;> simp [a6, a6i] <;> ring
  · refine (inO_iff _).2 ⟨n0, n1 + n3, n2, -n1, ?_⟩
    ext <;> simp [a6, a6i] <;> ring

theorem conj_mu : ∀ w, PkgI1.InO w → PkgI1.InO (mu * w * mui) ∧ PkgI1.InO (mui * w * mu) := by
  intro w hw
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff w).1 hw
  constructor
  · refine (inO_iff _).2 ⟨n0 - n2 + 2*n3, -n1 - n2 + n3, 3*n2 - 4*n3, 2*n2 - 3*n3, ?_⟩
    ext <;> simp [mu, mui] <;> ring
  · refine (inO_iff _).2 ⟨n0 - n2 + 2*n3, -n1 - n2 + n3, 3*n2 - 4*n3, 2*n2 - 3*n3, ?_⟩
    ext <;> simp [mu, mui] <;> ring

theorem nd_a4 : NormData a4 a4i :=
  ⟨by ext <;> simp [a4, a4i] <;> norm_num, by ext <;> simp [a4, a4i] <;> norm_num, conj_a4,
    by norm_num [nrd, a4]⟩
theorem nd_a6 : NormData a6 a6i :=
  ⟨by ext <;> simp [a6, a6i] <;> norm_num, by ext <;> simp [a6, a6i] <;> norm_num, conj_a6,
    by norm_num [nrd, a6]⟩
theorem nd_mu : NormData mu mui :=
  ⟨by ext <;> simp [mu, mui] <;> norm_num, by ext <;> simp [mu, mui] <;> norm_num, conj_mu,
    by norm_num [nrd, mu]⟩

/-! ### The orbit predicate and conjugation -/

/-- Pure elements `w ∈ 𝒪` with `w² = −N` on the upper sheet. -/
def EN (N : ℚ) (w : PkgI1.B) : Prop :=
  PkgI1.InO w ∧ w * w = -((N : ℚ) : PkgI1.B) ∧ 0 < w.imJ

theorem scal_mid (s si : PkgI1.B) (q : ℚ) : s * ((q : ℚ) : PkgI1.B) * si = ((q : ℚ) : PkgI1.B) * (s * si) := by
  ext <;> simp <;> ring

theorem EN_conj {N : ℚ} (hN : 0 < N) {s si u b w : PkgI1.B} (hs : NormData s si)
    (hu : 0 < form u u) (hu' : 0 < u.imJ) (hb : 0 < form b b) (hb' : 0 < b.imJ)
    (hf : ∀ v : PkgI1.B, v.re = 0 → form (s * v * si) b = form v u) (hw : EN N w) :
    EN N (s * w * si) := by
  obtain ⟨hO, hsq, hJ⟩ := hw
  obtain ⟨hre, hqf⟩ := pure_of_sqN N hN hsq
  have hsq' : (s * w * si) * (s * w * si) = -((N : ℚ) : PkgI1.B) := by
    calc (s * w * si) * (s * w * si) = s * (w * ((si * s) * (w * si))) := by simp only [mul_assoc]
      _ = s * (w * w) * si := by rw [hs.2.1, one_mul]; simp only [mul_assoc]
      _ = -((N : ℚ) : PkgI1.B) := by rw [hsq, mul_neg, neg_mul, scal_mid, hs.1, mul_one]
  refine ⟨(hs.2.2.1 w hO).1, hsq', ?_⟩
  obtain ⟨hre', hqf'⟩ := pure_of_sqN N hN hsq'
  refine imJ_pos_of_form (by rw [hqf']; exact hN) hb hb' ?_
  rw [hf w hre]
  exact form_pos (by rw [hqf]; exact hN) hu hJ hu'

theorem nat_of_int {x : ℚ} {m : ℤ} (h : x = m) (hp : 0 < x) : ∃ k : ℕ, x = k := by
  have hm : 0 ≤ m := by have := h ▸ hp; exact_mod_cast this.le
  exact ⟨m.toNat, by rw [h]; exact_mod_cast (Int.toNat_of_nonneg hm).symm⟩

theorem pure_coords {w : PkgI1.B} (hw : PkgI1.InO w) (hre : w.re = 0) :
    ∃ n0 n1 n3 : ℤ, w.imJ = -n0 ∧ w.imI = n1 + n3 / 2 ∧ w.imK = n3 / 2 := by
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff w).1 hw
  have h : (n2 : ℚ) = -2 * n0 := by have := hre; simp only at this; linarith
  exact ⟨n0, n1, n3, by simp only; rw [h]; ring, rfl, rfl⟩

/-! ### Orbit of `y` (`w² = −1`) -/

theorem orbit4 : ∀ w, EN 1 w → ∃ g gi, NormData g gi ∧ g * by4 * gi = w := by
  have hb : 0 < form by4 by4 := by norm_num [form, by4]
  have hb' : 0 < by4.imJ := by norm_num [by4]
  refine orbit_of_descent (EN 1) (fun w => form w by4) by4 ?_ ?_ ?_
  · intro w ⟨hO, hsq, hJ⟩
    obtain ⟨hre, hqf⟩ := pure_of_sqN 1 one_pos hsq
    obtain ⟨n0, n1, n3, hc, hb1, hd⟩ := pure_coords hO hre
    refine nat_of_int (m := -2 * n1 - n3 - 3 * n0) ?_ (form_pos (by rw [hqf]; norm_num) hb hJ hb')
    simp only [form, by4]; rw [hc, hb1]; push_cast; ring
  · intro w ⟨hO, hsq, hJ⟩ hle
    obtain ⟨hre, hqf⟩ := pure_of_sqN 1 one_pos hsq
    simp only [form, by4] at hle hqf
    norm_num at hle
    have h1 : w.imI = 1 := by nlinarith [sq_nonneg (w.imI - 1), sq_nonneg w.imK, sq_nonneg (3 * w.imJ - 1 - 2 * w.imI)]
    have h2 : w.imK = 0 := by nlinarith [sq_nonneg (w.imI - 1), sq_nonneg w.imK, sq_nonneg (3 * w.imJ - 1 - 2 * w.imI)]
    have h3 : w.imJ = 1 := by nlinarith [sq_nonneg (w.imI - 1), sq_nonneg w.imK, sq_nonneg (3 * w.imJ - 1 - 2 * w.imI)]
    ext <;> simp [by4, hre, h1, h2, h3]
  · intro w hw hlt
    obtain ⟨hO, hsq, hJ⟩ := hw
    obtain ⟨hre, hqf⟩ := pure_of_sqN 1 one_pos hsq
    obtain ⟨n0, n1, n3, hc, hb1, hd⟩ := pure_coords hO hre
    have hint : form w by4 = ((-2 * n1 - n3 - 3 * n0 : ℤ) : ℚ) := by
      simp only [form, by4]; rw [hc, hb1]; push_cast; ring
    have h2 : 2 ≤ form w by4 := by
      have h1 : form by4 by4 = 1 := by norm_num [form, by4]
      rw [h1, hint] at hlt; rw [hint]
      have : (1 : ℤ) < -2 * n1 - n3 - 3 * n0 := by exact_mod_cast hlt
      exact_mod_cast (show (2 : ℤ) ≤ -2 * n1 - n3 - 3 * n0 by omega)
    have e1 : ∀ v : PkgI1.B, v.re = 0 → form (a6 * v * a6i) by4 = form v ⟨0, 1/2, 1, -1/2⟩ := by
      intro v hv; simp [form, by4, a6, a6i, hv]; ring
    have e2 : ∀ v : PkgI1.B, v.re = 0 → form (a6i * v * a6) by4 = form v ⟨0, 1/2, 1, 1/2⟩ := by
      intro v hv; simp [form, by4, a6, a6i, hv]; ring
    have e3 : ∀ v : PkgI1.B, v.re = 0 →
        form (a6 * a4 * v * (a4i * a6i)) by4 = form v ⟨0, 7/2, 3, -1/2⟩ := by
      intro v hv; simp [form, by4, a6, a6i, a4, a4i, hv]; ring
    have e4 : ∀ v : PkgI1.B, v.re = 0 →
        form (a6i * a4i * v * (a4 * a6)) by4 = form v ⟨0, 7/2, 3, 1/2⟩ := by
      intro v hv; simp [form, by4, a6, a6i, a4, a4i, hv]; ring
    have hw : EN 1 w := ⟨hO, hsq, hJ⟩
    by_cases c1 : form w ⟨0, 1/2, 1, -1/2⟩ < form w by4
    · exact ⟨_, _, nd_a6, EN_conj one_pos nd_a6 (by norm_num [form]) (by norm_num) hb hb' e1 hw,
        by rw [e1 w hre]; exact c1⟩
    by_cases c2 : form w ⟨0, 1/2, 1, 1/2⟩ < form w by4
    · exact ⟨_, _, nd_a6.symm, EN_conj one_pos nd_a6.symm (by norm_num [form]) (by norm_num) hb hb'
        e2 hw, by rw [e2 w hre]; exact c2⟩
    by_cases c3 : form w ⟨0, 7/2, 3, -1/2⟩ < form w by4
    · exact ⟨_, _, nd_a6.mul nd_a4, EN_conj one_pos (nd_a6.mul nd_a4) (by norm_num [form])
        (by norm_num) hb hb' e3 hw, by rw [e3 w hre]; exact c3⟩
    by_cases c4 : form w ⟨0, 7/2, 3, 1/2⟩ < form w by4
    · exact ⟨_, _, nd_a6.symm.mul nd_a4.symm, EN_conj one_pos (nd_a6.symm.mul nd_a4.symm)
        (by norm_num [form]) (by norm_num) hb hb' e4 hw, by rw [e4 w hre]; exact c4⟩
    exfalso
    push_neg at c1 c2 c3 c4
    simp only [form, by4] at c1 c2 c3 c4 h2 hqf
    nlinarith [mul_nonneg (sub_nonneg.2 c1) (sub_nonneg.2 c4),
      mul_nonneg (sub_nonneg.2 c2) (sub_nonneg.2 c3)]

/-! ### Orbit of `j` (`w² = −3`) -/

theorem orbit3 : ∀ w, EN 3 w → ∃ g gi, NormData g gi ∧ g * bj * gi = w := by
  have hb : 0 < form bj bj := by norm_num [form, bj]
  have hb' : 0 < bj.imJ := by norm_num [bj]
  refine orbit_of_descent (EN 3) (fun w => form w bj) bj ?_ ?_ ?_
  · intro w ⟨hO, hsq, hJ⟩
    obtain ⟨hre, hqf⟩ := pure_of_sqN 3 (by norm_num) hsq
    obtain ⟨n0, n1, n3, hc, hb1, hd⟩ := pure_coords hO hre
    refine nat_of_int (m := -3 * n0) ?_ (form_pos (by rw [hqf]; norm_num) hb hJ hb')
    simp only [form, bj]; rw [hc]; push_cast; ring
  · intro w ⟨hO, hsq, hJ⟩ hle
    obtain ⟨hre, hqf⟩ := pure_of_sqN 3 (by norm_num) hsq
    simp only [form, bj] at hle hqf
    norm_num at hle
    have h3 : w.imJ ≤ 1 := by linarith
    have h1 : w.imI = 0 := by nlinarith [sq_nonneg w.imI, sq_nonneg w.imK]
    have h2 : w.imK = 0 := by nlinarith [sq_nonneg w.imI, sq_nonneg w.imK]
    have h4 : w.imJ = 1 := by nlinarith [sq_nonneg w.imI, sq_nonneg w.imK]
    ext <;> simp [bj, hre, h1, h2, h4]
  · intro w hw hlt
    obtain ⟨hO, hsq, hJ⟩ := hw
    obtain ⟨hre, hqf⟩ := pure_of_sqN 3 (by norm_num) hsq
    obtain ⟨n0, n1, n3, hc, hb1, hd⟩ := pure_coords hO hre
    have h2 : 2 ≤ w.imJ := by
      have h1 : form bj bj = 3 := by norm_num [form, bj]
      simp only [form, bj] at hlt; norm_num at hlt
      rw [hc] at hlt ⊢
      have : (1 : ℤ) < -n0 := by exact_mod_cast (show (1 : ℚ) < -(n0 : ℚ) by linarith)
      exact_mod_cast (show (2 : ℤ) ≤ -n0 by omega)
    have e1 : ∀ v : PkgI1.B, v.re = 0 → form (a4 * v * a4i) bj = form v ⟨0, 3, 3, -1⟩ := by
      intro v hv; simp [form, bj, a4, a4i, hv]; ring
    have e2 : ∀ v : PkgI1.B, v.re = 0 → form (a4i * v * a4) bj = form v ⟨0, 3, 3, 1⟩ := by
      intro v hv; simp [form, bj, a4, a4i, hv]; ring
    have e3 : ∀ v : PkgI1.B, v.re = 0 →
        form (a4 * a6 * v * (a6i * a4i)) bj = form v ⟨0, 0, 3, -2⟩ := by
      intro v hv; simp [form, bj, a6, a6i, a4, a4i, hv]; ring
    have e4 : ∀ v : PkgI1.B, v.re = 0 →
        form (a4i * a6i * v * (a6 * a4)) bj = form v ⟨0, 0, 3, 2⟩ := by
      intro v hv; simp [form, bj, a6, a6i, a4, a4i, hv]; ring
    have e5 : ∀ v : PkgI1.B, v.re = 0 →
        form (a4 * a6 * a6 * v * (a6i * (a6i * a4i))) bj = form v ⟨0, -3, 3, -1⟩ := by
      intro v hv; simp [form, bj, a6, a6i, a4, a4i, hv]; ring
    have e6 : ∀ v : PkgI1.B, v.re = 0 →
        form (a4i * a6i * a6i * v * (a6 * (a6 * a4))) bj = form v ⟨0, -3, 3, 1⟩ := by
      intro v hv; simp [form, bj, a6, a6i, a4, a4i, hv]; ring
    have hw : EN 3 w := ⟨hO, hsq, hJ⟩
    by_cases c1 : form w ⟨0, 3, 3, -1⟩ < form w bj
    · exact ⟨_, _, nd_a4, EN_conj (by norm_num : (0:ℚ) < 3) nd_a4 (by norm_num [form]) (by norm_num) hb hb' e1 hw,
        by rw [e1 w hre]; exact c1⟩
    by_cases c2 : form w ⟨0, 3, 3, 1⟩ < form w bj
    · exact ⟨_, _, nd_a4.symm, EN_conj (by norm_num : (0:ℚ) < 3) nd_a4.symm (by norm_num [form]) (by norm_num) hb hb' e2 hw,
        by rw [e2 w hre]; exact c2⟩
    by_cases c3 : form w ⟨0, 0, 3, -2⟩ < form w bj
    · exact ⟨_, _, (nd_a4.mul nd_a6), EN_conj (by norm_num : (0:ℚ) < 3) (nd_a4.mul nd_a6) (by norm_num [form]) (by norm_num) hb hb' e3 hw,
        by rw [e3 w hre]; exact c3⟩
    by_cases c4 : form w ⟨0, 0, 3, 2⟩ < form w bj
    · exact ⟨_, _, (nd_a4.symm.mul nd_a6.symm), EN_conj (by norm_num : (0:ℚ) < 3) (nd_a4.symm.mul nd_a6.symm) (by norm_num [form]) (by norm_num) hb hb' e4 hw,
        by rw [e4 w hre]; exact c4⟩
    by_cases c5 : form w ⟨0, -3, 3, -1⟩ < form w bj
    · exact ⟨_, _, ((nd_a4.mul nd_a6).mul nd_a6), EN_conj (by norm_num : (0:ℚ) < 3) ((nd_a4.mul nd_a6).mul nd_a6) (by norm_num [form]) (by norm_num) hb hb' e5 hw,
        by rw [e5 w hre]; exact c5⟩
    by_cases c6 : form w ⟨0, -3, 3, 1⟩ < form w bj
    · exact ⟨_, _, ((nd_a4.symm.mul nd_a6.symm).mul nd_a6.symm), EN_conj (by norm_num : (0:ℚ) < 3) ((nd_a4.symm.mul nd_a6.symm).mul nd_a6.symm) (by norm_num [form]) (by norm_num) hb hb' e6 hw,
        by rw [e6 w hre]; exact c6⟩
    exfalso
    push_neg at c1 c2 c3 c4 c5 c6
    simp only [form, bj] at c1 c2 c3 c4 c5 c6 hqf
    have h1 : 0 ≤ -w.imI + w.imJ + w.imK := by linarith
    have h2' : 0 ≤ -w.imI + w.imJ - w.imK := by linarith
    have h3 : 0 ≤ w.imJ + 2 * w.imK := by linarith
    have h4 : 0 ≤ w.imJ - 2 * w.imK := by linarith
    have h5 : 0 ≤ w.imI + w.imJ + w.imK := by linarith
    have h6 : 0 ≤ w.imI + w.imJ - w.imK := by linarith
    have : w.imJ ^ 2 ≤ -2 * w.imI ^ 2 + 3 * w.imJ ^ 2 - 6 * w.imK ^ 2 := by
      nlinarith [mul_nonneg h1 h6, mul_nonneg h2' h5, mul_nonneg h3 h4, mul_nonneg h1 h2',
        mul_nonneg h5 h6, mul_nonneg h1 h5, mul_nonneg h2' h6, mul_nonneg h3 h1, mul_nonneg h3 h2',
        mul_nonneg h3 h5, mul_nonneg h3 h6, mul_nonneg h4 h1, mul_nonneg h4 h2', mul_nonneg h4 h5,
        mul_nonneg h4 h6]
    nlinarith

/-! ### Orbit of `μ = 2j + ij` (`w² = −6`) -/

theorem orbit24 : ∀ w, EN 6 w → ∃ g gi, NormData g gi ∧ g * mu * gi = w := by
  have hb : 0 < form mu mu := by norm_num [form, mu]
  have hb' : 0 < mu.imJ := by norm_num [mu]
  refine orbit_of_descent (EN 6) (fun w => form w mu) mu ?_ ?_ ?_
  · intro w ⟨hO, hsq, hJ⟩
    obtain ⟨hre, hqf⟩ := pure_of_sqN 6 (by norm_num) hsq
    obtain ⟨n0, n1, n3, hc, hb1, hd⟩ := pure_coords hO hre
    refine nat_of_int (m := -6 * n0 - 3 * n3) ?_ (form_pos (by rw [hqf]; norm_num) hb hJ hb')
    simp only [form, mu]; rw [hc, hd]; push_cast; ring
  · intro w ⟨hO, hsq, hJ⟩ hle
    obtain ⟨hre, hqf⟩ := pure_of_sqN 6 (by norm_num) hsq
    simp only [form, mu] at hle hqf
    norm_num at hle
    have hcd : w.imJ ≤ w.imK + 1 := by linarith
    have hsq3 : w.imJ ^ 2 ≤ (w.imK + 1) ^ 2 := by
      have := mul_self_le_mul_self hJ.le hcd; nlinarith
    have h1 : w.imI = 0 := by nlinarith [sq_nonneg w.imI, sq_nonneg (w.imK - 1)]
    have h2 : w.imK = 1 := by nlinarith [sq_nonneg w.imI, sq_nonneg (w.imK - 1)]
    have h4 : w.imJ = 2 := by
      rw [h1, h2] at hqf; nlinarith
    ext <;> simp [mu, hre, h1, h2, h4]
  · intro w hw hlt
    obtain ⟨hO, hsq, hJ⟩ := hw
    obtain ⟨hre, hqf⟩ := pure_of_sqN 6 (by norm_num) hsq
    obtain ⟨n0, n1, n3, hc, hb1, hd⟩ := pure_coords hO hre
    have h2 : 3 ≤ 2 * w.imJ - 2 * w.imK := by
      simp only [form, mu] at hlt; norm_num at hlt
      rw [hc, hd] at hlt ⊢
      have : (2 : ℤ) < -2 * n0 - n3 := by
        exact_mod_cast (show (2 : ℚ) < -2 * (n0 : ℚ) - n3 by linarith)
      have h3 : (3 : ℤ) ≤ -2 * n0 - n3 := by omega
      have : (3 : ℚ) ≤ -2 * (n0 : ℚ) - n3 := by exact_mod_cast h3
      linarith
    have e1 : ∀ v : PkgI1.B, v.re = 0 → form (a6 * v * a6i) mu = form v ⟨0, 3/2, 2, 1/2⟩ := by
      intro v hv; simp [form, mu, a6, a6i, hv]; ring
    have e2 : ∀ v : PkgI1.B, v.re = 0 → form (a6i * v * a6) mu = form v ⟨0, -3/2, 2, 1/2⟩ := by
      intro v hv; simp [form, mu, a6, a6i, hv]; ring
    have e3 : ∀ v : PkgI1.B, v.re = 0 →
        form (a4 * a6i * a6i * v * (a6 * (a6 * a4i))) mu = form v ⟨0, 3/2, 4, 5/2⟩ := by
      intro v hv; simp [form, mu, a6, a6i, a4, a4i, hv]; ring
    have e4 : ∀ v : PkgI1.B, v.re = 0 →
        form (a6 * mu * v * (mui * a6i)) mu = form v ⟨0, -3/2, 4, 5/2⟩ := by
      intro v hv; simp [form, mu, mui, a6, a6i, hv]; ring
    have hw : EN 6 w := ⟨hO, hsq, hJ⟩
    by_cases c1 : form w ⟨0, 3/2, 2, 1/2⟩ < form w mu
    · exact ⟨_, _, nd_a6, EN_conj (by norm_num : (0:ℚ) < 6) nd_a6 (by norm_num [form]) (by norm_num) hb hb' e1 hw,
        by rw [e1 w hre]; exact c1⟩
    by_cases c2 : form w ⟨0, -3/2, 2, 1/2⟩ < form w mu
    · exact ⟨_, _, nd_a6.symm, EN_conj (by norm_num : (0:ℚ) < 6) nd_a6.symm (by norm_num [form]) (by norm_num) hb hb' e2 hw,
        by rw [e2 w hre]; exact c2⟩
    by_cases c3 : form w ⟨0, 3/2, 4, 5/2⟩ < form w mu
    · exact ⟨_, _, ((nd_a4.mul nd_a6.symm).mul nd_a6.symm), EN_conj (by norm_num : (0:ℚ) < 6) ((nd_a4.mul nd_a6.symm).mul nd_a6.symm) (by norm_num [form]) (by norm_num) hb hb' e3 hw,
        by rw [e3 w hre]; exact c3⟩
    by_cases c4 : form w ⟨0, -3/2, 4, 5/2⟩ < form w mu
    · exact ⟨_, _, (nd_a6.mul nd_mu), EN_conj (by norm_num : (0:ℚ) < 6) (nd_a6.mul nd_mu) (by norm_num [form]) (by norm_num) hb hb' e4 hw,
        by rw [e4 w hre]; exact c4⟩
    exfalso
    push_neg at c1 c2 c3 c4
    simp only [form, mu] at c1 c2 c3 c4 hqf
    have h1 : 0 ≤ -w.imI + w.imK := by linarith
    have h2' : 0 ≤ w.imI + w.imK := by linarith
    have h3 : 0 ≤ -w.imI + 2 * w.imJ - 3 * w.imK := by linarith
    have h4 : 0 ≤ w.imI + 2 * w.imJ - 3 * w.imK := by linarith
    have : 3 * (w.imJ - w.imK) ^ 2 ≤ -2 * w.imI ^ 2 + 3 * w.imJ ^ 2 - 6 * w.imK ^ 2 := by
      nlinarith [mul_nonneg h1 h4, mul_nonneg h2' h3, sq_nonneg w.imI]
    nlinarith

/-! ### `QMHauptmodul` from its values at three points -/

/-- `(1 + j)/2` (period-map's `x3`; `x3² − x3 + 1 = 0`). -/
def x3 : PkgI1.B := ⟨1 / 2, 0, 1 / 2, 0⟩

/-- **LEAF candidate (narrowed `QMHauptmodul`).** `PkgI1.QMHauptmodul` with each of its three CM clauses
asserted only at the fixed points of `ι(x)` for one element: `x = i + j` (`x² = −1`), `x = (1 + j)/2`
(`x² − x + 1 = 0`) and `x = 2j + ij` (`x² = −6`), the elliptic points `√2 + i`, `i√3`, `i√(9 + 6√2)` of
orders 4, 6, 2. Weaker than `QMHauptmodul`; `qmHauptmodul_of_base` recovers it, because the CM points of
each discriminant form one `Γ*`-orbit (`orbit4`, `orbit3`, `orbit24`). -/
def QMHauptmodulBase : Prop :=
  ∃ f : UpperHalfPlane → OnePoint ℂ, Continuous f ∧
    (∀ τ : UpperHalfPlane, PkgI1.jDen (PkgI1.Omega τ) ≠ 0 →
      f τ = ((PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) : ℂ) : OnePoint ℂ)) ∧
    (∀ τ τ' : UpperHalfPlane, f τ = f τ' ↔ ∃ γ ∈ PkgI1.GammaStar, γ • τ = τ') ∧
    Function.Surjective f ∧
    (∀ γ : GL (Fin 2) ℝ, (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota by4 →
      ∀ τ : UpperHalfPlane, γ • τ = τ → f τ = ((0 : ℂ) : OnePoint ℂ)) ∧
    (∀ γ : GL (Fin 2) ℝ, (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x3 →
      ∀ τ : UpperHalfPlane, γ • τ = τ → f τ = (OnePoint.infty : OnePoint ℂ)) ∧
    (∀ γ : GL (Fin 2) ℝ, (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota mu →
      ∀ τ : UpperHalfPlane, γ • τ = τ → f τ = ((-16/27 : ℂ) : OnePoint ℂ))

theorem det_ne' {x : PkgI1.B} (h : nrd x ≠ 0) : (PkgI1.iota x).det ≠ 0 := by
  rw [det_iota_eq]; exact_mod_cast h

/-- The element of `GL₂(ℝ)` with matrix `ι(x)`. -/
noncomputable def glOf (x : PkgI1.B) (h : nrd x ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (PkgI1.iota x) (det_ne' h)

theorem coe_glOf (x : PkgI1.B) (h : nrd x ≠ 0) :
    (glOf x h : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x := rfl

theorem iota_one : PkgI1.iota 1 = 1 := by
  rw [iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp

theorem glOf_mem {g gi : PkgI1.B} (hg : NormData g gi) : glOf g hg.2.2.2.ne' ∈ PkgI1.GammaStar :=
  ⟨g, ⟨gi, hg.1, hg.2.1, hg.2.2.1⟩, rfl, by rw [coe_glOf, det_iota_eq]; exact_mod_cast hg.2.2.2⟩

/-- **The transfer step.** If `f` is constant on `Γ*`-orbits and takes the value `val` at the fixed points
of `ι(b)`, it takes `val` at the fixed points of `ι(g b g⁻¹)` for every normalizer `g`. -/
theorem transfer {f : UpperHalfPlane → OnePoint ℂ}
    (hfib : ∀ τ τ' : UpperHalfPlane, f τ = f τ' ↔ ∃ γ ∈ PkgI1.GammaStar, γ • τ = τ')
    {b : PkgI1.B} {val : OnePoint ℂ}
    (hbase : ∀ γ : GL (Fin 2) ℝ, (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota b →
      ∀ τ : UpperHalfPlane, γ • τ = τ → f τ = val)
    {g gi : PkgI1.B} (hg : NormData g gi) (γ₁ : GL (Fin 2) ℝ)
    (hγ₁ : (γ₁ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota (g * b * gi)) (τ : UpperHalfPlane)
    (hτ : γ₁ • τ = τ) : f τ = val := by
  have hgi := hg.symm
  set G := glOf g hg.2.2.2.ne'
  set G' := glOf gi hgi.2.2.2.ne'
  have hGG' : G * G' = 1 := by
    ext1; rw [Units.val_mul, coe_glOf, coe_glOf, ← iota_mul, hg.1, iota_one]; rfl
  have hval := hbase (G' * γ₁ * G) (by
    rw [Units.val_mul, Units.val_mul, coe_glOf, coe_glOf, hγ₁, ← iota_mul, ← iota_mul]
    congr 1
    calc gi * (g * b * gi) * g = (gi * g) * b * (gi * g) := by simp only [mul_assoc]
      _ = b := by rw [hg.2.1, one_mul, mul_one]) (G' • τ) (by
    rw [mul_smul, mul_smul, ← mul_smul G G', hGG', one_smul, hτ])
  rw [← hval]
  exact (hfib τ (G' • τ)).2 ⟨G', glOf_mem hgi, rfl⟩ |>.symm.symm

theorem inO_neg {x : PkgI1.B} (h : PkgI1.InO x) : PkgI1.InO (-x) := by
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff x).1 h
  exact (inO_iff _).2 ⟨-n0, -n1, -n2, -n3, by ext <;> simp <;> ring⟩

theorem inO_two_sub {x : PkgI1.B} (h : PkgI1.InO x) : PkgI1.InO (2 * x - 1) := by
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff x).1 h
  refine (inO_iff _).2 ⟨2 * n0 - 1, 2 * n1, 2 * n2, 2 * n3, ?_⟩
  ext <;> simp [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat,
    QuaternionAlgebra.imK_ofNat] <;> ring

theorem imJ_ne_zero {N : ℚ} (hN : 0 < N) {v : PkgI1.B} (h : v * v = -((N : ℚ) : PkgI1.B)) :
    v.imJ ≠ 0 := by
  obtain ⟨-, hq⟩ := pure_of_sqN N hN h
  intro h0; simp [form, h0] at hq; nlinarith [sq_nonneg v.imI, sq_nonneg v.imK]

/-- An upper-sheet representative of `±v`. -/
theorem upper_of {N : ℚ} (hN : 0 < N) {v : PkgI1.B} (hO : PkgI1.InO v)
    (h : v * v = -((N : ℚ) : PkgI1.B)) : EN N v ∨ EN N (-v) := by
  rcases lt_or_gt_of_ne (imJ_ne_zero hN h) with hl | hl
  · right; exact ⟨inO_neg hO, by rw [neg_mul_neg, h], by simpa using hl⟩
  · left; exact ⟨hO, h, hl⟩

theorem iota_neg (x : PkgI1.B) : PkgI1.iota (-x) = -PkgI1.iota x := by
  rw [iota_apply, iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

theorem neg_one_sq_cast : -((1 : ℚ) : PkgI1.B) = -1 := by simp

/-- **`QMHauptmodul` from `QMHauptmodulBase` (proved).** -/
theorem qmHauptmodul_of_base (h : QMHauptmodulBase) : PkgI1.QMHauptmodul := by
  obtain ⟨f, hc, hform, hfib, hsurj, h4, h3, h24⟩ := h
  refine ⟨f, hc, hform, hfib, hsurj, ?_, ?_, ?_⟩
  · intro x hO hx γ hγ τ hτ
    have hx' : x * x = -((1 : ℚ) : PkgI1.B) := by rw [hx]; simp
    rcases upper_of one_pos hO hx' with hE | hE
    · obtain ⟨g, gi, hg, hgx⟩ := orbit4 x hE
      exact transfer hfib h4 hg γ (by rw [hgx, hγ]) τ hτ
    · obtain ⟨g, gi, hg, hgx⟩ := orbit4 (-x) hE
      exact transfer hfib h4 hg (-γ) (by rw [hgx, iota_neg, Units.val_neg, hγ]) τ
        (by rw [UpperHalfPlane.neg_smul, hτ])
  · intro x hO hx γ hγ τ hτ
    have hw : (2 * x - 1) * (2 * x - 1) = -((3 : ℚ) : PkgI1.B) := by
      have : (2 * x - 1) * (2 * x - 1) = 4 * (x * x - x + 1) - 3 := by
        ext <;> simp [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
          QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> ring
      rw [this, hx]; simp
    have hx1 : x * (1 - x) = 1 := by
      have : x * (1 - x) = -(x * x - x + 1) + 1 := by noncomm_ring
      rw [this, hx, neg_zero, zero_add]
    rcases upper_of (by norm_num : (0 : ℚ) < 3) (inO_two_sub hO) hw with hE | hE
    · obtain ⟨g, gi, hg, hgx⟩ := orbit3 _ hE
      have hgx3 : g * x3 * gi = x := by
        have e : x3 = (1 / 2 : ℚ) • (1 + bj) := by ext <;> simp [x3, bj]
        have : g * x3 * gi = (1 / 2 : ℚ) • (g * gi + g * bj * gi) := by
          rw [e]; simp only [mul_add, add_mul, mul_one, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
        rw [this, hg.1, hgx]
        ext <;> simp [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
          QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> ring
      exact transfer hfib h3 hg γ (by rw [hgx3, hγ]) τ hτ
    · obtain ⟨g, gi, hg, hgx⟩ := orbit3 _ hE
      have hgx3 : g * x3 * gi = 1 - x := by
        have e : x3 = (1 / 2 : ℚ) • (1 + bj) := by ext <;> simp [x3, bj]
        have : g * x3 * gi = (1 / 2 : ℚ) • (g * gi + g * bj * gi) := by
          rw [e]; simp only [mul_add, add_mul, mul_one, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
        rw [this, hg.1, hgx]
        ext <;> simp [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
          QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> ring
      have hinv : ((γ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota (1 - x) := by
        have h1 : (γ : Matrix (Fin 2) (Fin 2) ℝ) * PkgI1.iota (1 - x) = 1 := by
          rw [hγ, ← iota_mul, hx1, iota_one]
        calc ((γ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
            = ((γ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
                ((γ : Matrix (Fin 2) (Fin 2) ℝ) * PkgI1.iota (1 - x)) := by rw [h1, mul_one]
          _ = PkgI1.iota (1 - x) := by
            rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      exact transfer hfib h3 hg γ⁻¹ (by rw [hgx3, hinv]) τ (by
        conv_lhs => rw [← hτ]
        rw [inv_smul_smul])
  · intro x hO hx γ hγ τ hτ
    have hx' : x * x = -((6 : ℚ) : PkgI1.B) := by rw [hx]; simp
    rcases upper_of (by norm_num : (0 : ℚ) < 6) hO hx' with hE | hE
    · obtain ⟨g, gi, hg, hgx⟩ := orbit24 x hE
      exact transfer hfib h24 hg γ (by rw [hgx, hγ]) τ hτ
    · obtain ⟨g, gi, hg, hgx⟩ := orbit24 (-x) hE
      exact transfer hfib h24 hg (-γ) (by rw [hgx, iota_neg, Units.val_neg, hγ]) τ
        (by rw [UpperHalfPlane.neg_smul, hτ])

end HDec.LeafQCheck.HM

/-! ### Weight 20: `∏θ_m² ∘ Ω` (period-glue's `G8` machinery with `ThetaModularity`'s second clause)

Copied from `scratch/leaf-fold4/Leaves4.lean` (period-glue, lines 116948-117320) with `G8 → G20`,
`thetaSum8 → thetaProd2`, exponents `4, 8 → 10, 20` and the first clause of `ThetaModularity` replaced by
the second. -/

namespace HDec.HSyn.G0Split.FibreQM.PeriodGlue.LQ20
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)
open Complex Matrix HSyn.G0Split.FibreQM HSyn.G0Split.FibreQM.PeriodMap HSyn.G0Split.FibreQM.PeriodGlue
open UpperHalfPlane (num denom σ coe_smul_of_det_pos denom_ne_zero)

/-- `Π/dF¹⁰ = ∏θ_m²(Ω(τ)) / ((τ − 3)(τ + 1))¹⁰`, a weight-20 automorphic form of `Γ*`. -/
noncomputable def G20 (z : ℂ) : ℂ := PkgI1.thetaProd2 (PkgI1.Omega z) / ((z - 3) * (z + 1)) ^ 10


/-- `g ∈ GL₂(ℝ)⁺` and `G20` has the exact automorphy of `S8WeightExact` for `g`. -/
def G20Auto (γ : GL (Fin 2) ℝ) : Prop :=
  0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det ∧ ∀ z : UpperHalfPlane,
    G20 ((γ • z : UpperHalfPlane) : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ^ 10 =
      denom γ z ^ 20 * G20 (z : ℂ)

theorem g20Auto_one : G20Auto 1 := by
  refine ⟨by simp, fun z => ?_⟩
  simp [UpperHalfPlane.denom]

theorem g20Auto_mul {g h : GL (Fin 2) ℝ} (hg : G20Auto g) (hh : G20Auto h) : G20Auto (g * h) := by
  refine ⟨by rw [Units.val_mul, det_mul]; exact mul_pos hg.1 hh.1, fun z => ?_⟩
  rw [mul_smul, denom_mul_pos g h hh.1, Units.val_mul, det_mul]
  have e1 := hg.2 (h • z)
  have e2 := hh.2 z
  push_cast
  calc G20 ((g • h • z : UpperHalfPlane) : ℂ) *
        (((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) * ((h : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ)) ^ 10
      = (G20 ((g • h • z : UpperHalfPlane) : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ 10) *
          ((h : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ 10 := by ring
    _ = denom g ((h • z : UpperHalfPlane) : ℂ) ^ 20 * (G20 ((h • z : UpperHalfPlane) : ℂ) *
          ((h : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ 10) := by rw [e1]; ring
    _ = _ := by rw [e2]; ring

theorem g20Auto_inv {g : GL (Fin 2) ℝ} (hg : G20Auto g) : G20Auto g⁻¹ := by
  have hd : ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det =
      ((g : Matrix (Fin 2) (Fin 2) ℝ).det)⁻¹ := by
    rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  refine ⟨by rw [hd]; exact inv_pos.mpr hg.1, fun z => ?_⟩
  set z' := g⁻¹ • z with hz'
  have e := hg.2 z'
  rw [hz', smul_inv_smul] at e
  have hc := denom_mul_pos g g⁻¹ (by rw [hd]; exact inv_pos.mpr hg.1) z
  rw [mul_inv_cancel] at hc
  have h1 : denom (1 : GL (Fin 2) ℝ) z = 1 := by simp [UpperHalfPlane.denom]
  rw [h1] at hc
  have hD : denom g ((g⁻¹ • z : UpperHalfPlane) : ℂ) ≠ 0 := denom_ne_zero _ _
  have hdet : ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ≠ 0 := by exact_mod_cast hg.1.ne'
  rw [hd]
  push_cast
  have key : G20 ((g⁻¹ • z : UpperHalfPlane) : ℂ) = G20 (z : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ 10 /
      denom g ((g⁻¹ • z : UpperHalfPlane) : ℂ) ^ 20 := by
    rw [eq_div_iff (pow_ne_zero _ hD), e]; ring
  rw [key]
  have hinv : denom g⁻¹ z = (denom g ((g⁻¹ • z : UpperHalfPlane) : ℂ))⁻¹ :=
    (eq_inv_of_mul_eq_one_right hc.symm)
  rw [hinv]
  field_simp

theorem g20Auto_scalar {g : GL (Fin 2) ℝ} (q : ℚ) (hq : q ≠ 0)
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = (q : ℝ) • 1) : G20Auto g := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℝ).det = (q : ℝ) ^ 2 := by
    rw [hg, Matrix.det_smul, Matrix.det_one]; simp
  have hpos : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; positivity
  have e00 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = q := by rw [hg]; simp
  have e01 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by rw [hg]; simp
  have e10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by rw [hg]; simp
  have e11 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = q := by rw [hg]; simp
  refine ⟨hpos, fun z => ?_⟩
  have hden : denom g z = (q : ℂ) := by simp [UpperHalfPlane.denom, e10, e11]
  have hsm : g • z = z := by
    ext1
    rw [coe_smul_of_det_pos (by rwa [detv]), hden]
    simp only [UpperHalfPlane.num, e00, e01]
    have : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    field_simp
    push_cast; ring
  rw [hsm, hden, hdet]
  push_cast; ring

/-- The automorphy group of `G20` (a subgroup of `GL₂(ℝ)⁺`). -/
def G20AutoSubgroup : Subgroup (GL (Fin 2) ℝ) where
  carrier := {γ | G20Auto γ}
  one_mem' := g20Auto_one
  mul_mem' := g20Auto_mul
  inv_mem' := g20Auto_inv

theorem g20Auto_of_sp (hT : PkgI1.ThetaModularity) (g : GL (Fin 2) ℝ)
    (hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    (hrel : ∀ z : ℂ, 0 < z.im →
      PkgI1.spAct M (PkgI1.Omega z) = PkgI1.Omega (num g z / denom g z))
    (ε : ℂ) (hε : ε ^ 10 = 1)
    (hfac : ∀ z : ℂ, 0 < z.im →
      PkgI1.spFactor M (PkgI1.Omega z) * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) *
        ((z - 3) * (z + 1)) =
      ε * denom g z ^ 2 * ((num g z / denom g z - 3) * (num g z / denom g z + 1))) :
    G20Auto g := by
  refine ⟨hdet, fun z => ?_⟩
  have hw : ((g • z : UpperHalfPlane) : ℂ) = num g z / denom g z :=
    coe_smul_of_det_pos (by rwa [detv]) z
  have hwim : 0 < (num g z / denom g z).im := by rw [← hw]; exact (g • z).im_pos
  have hmod := (hT M hM (PkgI1.Omega z) (omegaSiegel_proof z z.im_pos)).2
  rw [hrel z z.im_pos] at hmod
  have hf := hfac z z.im_pos
  unfold G20
  rw [hw, hmod]
  have hf10 : (PkgI1.spFactor M (PkgI1.Omega z) * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) *
      ((z - 3) * (z + 1))) ^ 10 =
      (denom g z ^ 2 * ((num g z / denom g z - 3) * (num g z / denom g z + 1))) ^ 10 := by
    rw [hf, mul_assoc, mul_pow, hε, one_mul]
  obtain ⟨h3, h4⟩ := sub3_add1_ne z.im_pos
  obtain ⟨h5, h6⟩ := sub3_add1_ne hwim
  have hD : denom g z ≠ 0 := denom_ne_zero g z
  have hW : ((num g z / denom g z - 3) * (num g z / denom g z + 1)) ^ 10 ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero h5 h6)
  have hZ : (((z : ℂ) - 3) * ((z : ℂ) + 1)) ^ 10 ≠ 0 := pow_ne_zero _ (mul_ne_zero h3 h4)
  rw [div_mul_eq_mul_div, mul_div_assoc', div_eq_div_iff hW hZ]
  linear_combination (PkgI1.thetaProd2 (PkgI1.Omega z)) * hf10

theorem g20Auto_gen (hT : PkgI1.ThetaModularity) (g : GL (Fin 2) ℝ)
    (hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (hMs : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    (A B C D : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.map (Int.cast : ℤ → ℂ) = Matrix.fromBlocks A B C D)
    (hI1 : ∀ z : ℂ, dFh (num g z) (denom g z) • (A * Nf z + dF z • B) =
      Nfh (num g z) (denom g z) * (C * Nf z + dF z • D))
    (hI2 : ∀ z : ℂ, (C * Nf z + dF z • D).det * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) *
      ((z - 3) * (z + 1)) = -1 * dF z ^ 2 * ((num g z - 3 * denom g z) * (num g z + denom g z))) :
    G20Auto g := by
  have hw : ∀ z : ℂ, 0 < z.im → 0 < (num g z / denom g z).im := fun z hz => by
    have := (g • (⟨z, hz⟩ : UpperHalfPlane)).im_pos
    rwa [← UpperHalfPlane.coe_im, coe_smul_of_det_pos (by rwa [detv])] at this
  have hV : ∀ z : ℂ, 0 < z.im → denom g z ≠ 0 := fun z hz =>
    UpperHalfPlane.denom_ne_zero_of_im g hz.ne'
  have hP : ∀ z : ℂ, 0 < z.im → (C * Nf z + dF z • D).det ≠ 0 := fun z hz h0 => by
    have e := hI2 z
    rw [h0, zero_mul, zero_mul] at e
    obtain ⟨h5, h6⟩ := sub3_add1_ne (hw z hz)
    have h7 : num g z - 3 * denom g z ≠ 0 := fun h => h5 (by
      rw [show num g z = 3 * denom g z by linear_combination h, mul_div_assoc,
        div_self (hV z hz)]; ring)
    have h8 : num g z + denom g z ≠ 0 := fun h => h6 (by
      rw [show num g z = -denom g z by linear_combination h, neg_div, div_self (hV z hz)]; ring)
    have := dF_ne hz
    have : -1 * dF z ^ 2 * ((num g z - 3 * denom g z) * (num g z + denom g z)) ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ this)) (mul_ne_zero h7 h8)
    exact this e.symm
  refine g20Auto_of_sp hT g hdet M hMs (fun z hz => ?_) (-1) (by norm_num) (fun z hz => ?_)
  · exact spAct_of_poly M A B C D hM z _ _ (hV z hz) (dF_ne hz) (dF_ne (hw z hz)) (hP z hz) (hI1 z)
  · exact spFactor_of_poly M A B C D hM z _ _ _ (hV z hz) (dF_ne hz) (hI2 z)

theorem iota_x4 : PkgI1.iota x4 = !![1 + √2, -3; 1, 1 - √2] := by
  rw [iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp [x4]

theorem iota_x6 : PkgI1.iota x6 = !![-3 / 2, -3 / 2; 1 / 2, -3 / 2] := by
  rw [iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp [x6] <;> norm_num

theorem g20Auto_g4 (hT : PkgI1.ThetaModularity) {g : GL (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x4) : G20Auto g := by
  rw [iota_x4] at hg
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 2 := by
    rw [hg, Matrix.det_fin_two_of]; linear_combination (-1 : ℝ) * sqrt2_sq'
  have hnum : ∀ z : ℂ, num g z = (√2 : ℂ) * z + z - 3 := fun z => by
    simp only [UpperHalfPlane.num, hg]; simp; ring
  have hden : ∀ z : ℂ, denom g z = -(√2 : ℂ) + z + 1 := fun z => by
    simp only [UpperHalfPlane.denom, hg]; simp; ring
  refine g20Auto_gen hT g (by rw [hdet]; norm_num) M4 M4_symp A4 B4 C4 D4 M4_map
    (fun z => by rw [hnum, hden]; exact I1_g4 z) (fun z => ?_)
  rw [hnum, hden, hdet]; push_cast; exact I2_g4 z

theorem g20Auto_g6 (hT : PkgI1.ThetaModularity) {g : GL (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x6) : G20Auto g := by
  rw [iota_x6] at hg
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 3 := by
    rw [hg, Matrix.det_fin_two_of]; norm_num
  have hnum : ∀ z : ℂ, num g z = -3 * z / 2 - 3 / 2 := fun z => by
    simp only [UpperHalfPlane.num, hg]; simp; ring
  have hden : ∀ z : ℂ, denom g z = z / 2 - 3 / 2 := fun z => by
    simp only [UpperHalfPlane.denom, hg]; simp; ring
  refine g20Auto_gen hT g (by rw [hdet]; norm_num) M6 M6_symp A6 B6 C6 D6 M6_map
    (fun z => by rw [hnum, hden]; exact I1_g6 z) (fun z => ?_)
  rw [hnum, hden, hdet]; push_cast; exact I2_g6 z

/-- **The exact weight-20 automorphy of `G20` on all of `Γ*`** (from R4 and `GammaStarGen`). -/
theorem s20WeightExact_of (hT : PkgI1.ThetaModularity) (hG : GammaStarGen) :
    ∀ γ ∈ PkgI1.GammaStar, ∀ z : UpperHalfPlane,
      G20 ((γ • z : UpperHalfPlane) : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ^ 10 =
        denom γ z ^ 20 * G20 (z : ℂ) := by
  intro γ hγ z
  have hmem : γ ∈ G20AutoSubgroup := by
    refine (Subgroup.closure_le (K := G20AutoSubgroup)).mpr ?_ (hG γ hγ)
    rintro g ((hg | hg) | ⟨q, hq, hg⟩)
    · exact g20Auto_g4 hT hg
    · exact g20Auto_g6 hT hg
    · exact g20Auto_scalar q hq hg
  exact hmem.2 z

end HDec.HSyn.G0Split.FibreQM.PeriodGlue.LQ20

namespace HDec.LeafQCheck.HM

open PkgI1

/-! ### The disc −4 clause is a computation: `j_θ(√2 + i) = 0` -/

open HSyn.G0Split.FibreQM.PeriodGlue (th1 thT thetaConst_factor Omega0 omega_cm4 s8Omega0_proof τ1 τ2)

/-- The odd one-variable theta constant `Θ[1,1](τ)` vanishes (`n ↦ −n − 1`). -/
theorem th1_one_one (τ : ℂ) : th1 1 1 τ = 0 := by
  let e : ℤ ≃ ℤ := ⟨fun n => -n - 1, fun n => -n - 1, fun n => by ring, fun n => by ring⟩
  have hfe : ∀ n, thT 1 1 τ (e n) = -thT 1 1 τ n := by
    intro n
    simp only [thT, e, Equiv.coe_fn_mk]
    have : Real.pi * Complex.I * (((-n - 1 : ℤ) : ℂ) + ((1 : ℕ) : ℂ) / 2) ^ 2 * τ +
        Real.pi * Complex.I * (((-n - 1 : ℤ) : ℂ) + ((1 : ℕ) : ℂ) / 2) * ((1 : ℕ) : ℂ) =
        (Real.pi * Complex.I * ((n : ℂ) + ((1 : ℕ) : ℂ) / 2) ^ 2 * τ +
          Real.pi * Complex.I * ((n : ℂ) + ((1 : ℕ) : ℂ) / 2) * ((1 : ℕ) : ℂ)) +
        ((-2 * n - 1 : ℤ) : ℂ) * (Real.pi * Complex.I) := by push_cast; ring
    rw [this, Complex.exp_add, HSyn.G0Split.FibreQM.PeriodGlue.exp_int_piI]
    have h2 : ((-1 : ℂ)) ^ (-2 * n - 1) = -1 := by
      rw [zpow_sub₀ (by norm_num), zpow_mul, zpow_neg, zpow_one]
      norm_num
    rw [h2]; ring
  have h := e.tsum_eq (thT 1 1 τ)
  simp only [hfe, tsum_neg] at h
  unfold th1
  linear_combination -h / 2

theorem thetaProd2_omega0 : PkgI1.thetaProd2 Omega0 = 0 := by
  unfold PkgI1.thetaProd2
  apply Finset.prod_eq_zero (i := (![1, 1], ![0, 0])) (by decide)
  rw [thetaConst_factor]
  simp [th1_one_one]

theorem jNum_tau4 : PkgI1.jNum (PkgI1.Omega ((√2 : ℂ) + Complex.I)) = 0 := by
  rw [omega_cm4]; unfold PkgI1.jNum; rw [thetaProd2_omega0]; ring

theorem jDen_tau4 : PkgI1.jDen (PkgI1.Omega ((√2 : ℂ) + Complex.I)) ≠ 0 := by
  rw [omega_cm4]; unfold PkgI1.jDen; exact pow_ne_zero _ s8Omega0_proof

/-- The fixed point of `ι(i + j)` in `ℍ` is `√2 + i`. -/
theorem fixed_by4 {γ : GL (Fin 2) ℝ} (hγ : (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota by4)
    {τ : UpperHalfPlane} (hτ : γ • τ = τ) : (τ : ℂ) = (√2 : ℂ) + Complex.I := by
  have hM : (γ : Matrix (Fin 2) (Fin 2) ℝ) = !![√2, -3; 1, -√2] := by
    rw [hγ, iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp [by4]
  have hdet : 0 < γ.det.val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hM, Matrix.det_fin_two_of]
    nlinarith [sqrt2_sq']
  have h := congrArg (fun w : UpperHalfPlane => (w : ℂ)) hτ
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet, div_eq_iff (UpperHalfPlane.denom_ne_zero γ τ)] at h
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hM, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons] at h
  have s2 : (√2 : ℂ) * √2 = 2 := by
    rw [← Complex.ofReal_mul, sqrt2_sq']; norm_num
  have hq : ((τ : ℂ) - √2 - Complex.I) * ((τ : ℂ) - √2 + Complex.I) = 0 := by
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    push_cast at h
    linear_combination (-1 : ℂ) * h + s2 - hI
  rcases mul_eq_zero.1 hq with h1 | h1
  · linear_combination h1
  · exfalso
    have := congrArg Complex.im h1
    simp at this
    linarith [τ.im_pos]

/-- **`QMHauptmodulBase` without its disc −4 clause.** The value `0` at `√2 + i` follows from the formula
clause, since `∏θ_m(Ω(√2+i)) = 0` (the characteristic `((1,1),(0,0))`, `Ω(√2+i)` being a product
matrix) and `Σθ⁸(Ω(√2+i)) ≠ 0` (period-glue's certified `S8Omega0`). -/
def QMHauptmodulBase2 : Prop :=
  ∃ f : UpperHalfPlane → OnePoint ℂ, Continuous f ∧
    (∀ τ : UpperHalfPlane, PkgI1.jDen (PkgI1.Omega τ) ≠ 0 →
      f τ = ((PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) : ℂ) : OnePoint ℂ)) ∧
    (∀ τ τ' : UpperHalfPlane, f τ = f τ' ↔ ∃ γ ∈ PkgI1.GammaStar, γ • τ = τ') ∧
    Function.Surjective f ∧
    (∀ γ : GL (Fin 2) ℝ, (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x3 →
      ∀ τ : UpperHalfPlane, γ • τ = τ → f τ = (OnePoint.infty : OnePoint ℂ)) ∧
    (∀ γ : GL (Fin 2) ℝ, (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota mu →
      ∀ τ : UpperHalfPlane, γ • τ = τ → f τ = ((-16/27 : ℂ) : OnePoint ℂ))

theorem base_of_base2 (h : QMHauptmodulBase2) : QMHauptmodulBase := by
  obtain ⟨f, hc, hform, hfib, hsurj, h3, h24⟩ := h
  refine ⟨f, hc, hform, hfib, hsurj, fun γ hγ τ hτ => ?_, h3, h24⟩
  have hτ4 := fixed_by4 hγ hτ
  have hd : PkgI1.jDen (PkgI1.Omega τ) ≠ 0 := by rw [hτ4]; exact jDen_tau4
  rw [hform τ hd, hτ4, jNum_tau4, zero_div]

/-- **`QMHauptmodul` from `QMHauptmodulBase2` (proved).** -/
theorem qmHauptmodul_of_base2 (h : QMHauptmodulBase2) : PkgI1.QMHauptmodul :=
  qmHauptmodul_of_base (base_of_base2 h)

/-! ### The disc −3 clause from the valence bound: the pole of `j_θ` at `i√3` -/

open HSyn.G0Split.FibreQM.PeriodMap (G8 U tau3 tau4 thetaOmegaAnalytic_proof s8OrderCM3_of
  ValenceBoundGammaStar isOpen_U isPreconnected_U)

/-- `Σθ⁸ ∘ Ω`. -/
noncomputable def Sf (z : ℂ) : ℂ := PkgI1.thetaSum8 (PkgI1.Omega z)
/-- `∏θ² ∘ Ω`. -/
noncomputable def Pf (z : ℂ) : ℂ := PkgI1.thetaProd2 (PkgI1.Omega z)
/-- `(z − 3)(z + 1)`. -/
def Zf (z : ℂ) : ℂ := (z - 3) * (z + 1)

theorem Zf_ne {z : ℂ} (hz : 0 < z.im) : Zf z ≠ 0 := by
  unfold Zf
  have h3 : z - 3 ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
  have h4 : z + 1 ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
  exact mul_ne_zero h3 h4

theorem Zf_analytic (z : ℂ) : AnalyticAt ℂ Zf z := by unfold Zf; fun_prop

theorem Sf_analytic : AnalyticOnNhd ℂ Sf U := thetaOmegaAnalytic_proof.1
theorem Pf_analytic : AnalyticOnNhd ℂ Pf U := thetaOmegaAnalytic_proof.2

theorem jDenO_eq (z : ℂ) : PkgI1.jDen (PkgI1.Omega z) = Sf z ^ 5 := rfl
theorem jNumO_eq (z : ℂ) : PkgI1.jNum (PkgI1.Omega z) = 3779136 * Pf z ^ 2 := rfl

theorem tau4_coe : (tau4 : ℂ) = (√2 : ℂ) + Complex.I := rfl
theorem tau3_coe : (tau3 : ℂ) = (√3 : ℂ) * Complex.I := rfl

theorem Sf_tau4 : Sf (tau4 : ℂ) ≠ 0 := by
  unfold Sf; rw [tau4_coe, omega_cm4]; exact s8Omega0_proof

theorem Pf_tau4 : Pf (tau4 : ℂ) = 0 := by
  unfold Pf; rw [tau4_coe, omega_cm4]; exact thetaProd2_omega0

/-- `jDen ∘ Ω` is analytic on `ℍ` and nowhere locally zero. -/
theorem jDenO_analytic : AnalyticOnNhd ℂ (fun z => PkgI1.jDen (PkgI1.Omega z)) U :=
  fun z hz => (Sf_analytic z hz).pow 5

theorem jDenO_order_ne_top {z : ℂ} (hz : z ∈ U) :
    analyticOrderAt (fun z => PkgI1.jDen (PkgI1.Omega z)) z ≠ ⊤ := by
  intro htop
  have hev := analyticOrderAt_eq_top.1 htop
  have h0 := jDenO_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_U hz hev
  have h4 := h0 (show (tau4 : ℂ) ∈ U from tau4.im_pos)
  simp only [Pi.zero_apply, jDenO_eq] at h4
  exact Sf_tau4 (pow_eq_zero_iff (by norm_num) |>.1 h4)

/-- Near every point of `ℍ`, `jDen ∘ Ω ≠ 0` off that point. -/
theorem jDenO_eventually_ne {z : ℂ} (hz : z ∈ U) :
    ∀ᶠ w in nhdsWithin z {z}ᶜ, PkgI1.jDen (PkgI1.Omega w) ≠ 0 := by
  rcases (jDenO_analytic z hz).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd (analyticOrderAt_eq_top.2 h) (jDenO_order_ne_top hz)
  · exact h

open Filter Topology in
theorem map_coe_punctured (τ0 : UpperHalfPlane) :
    Filter.map (fun τ : UpperHalfPlane => (τ : ℂ)) (𝓝[≠] τ0) = 𝓝[≠] (τ0 : ℂ) := by
  rw [UpperHalfPlane.isOpenEmbedding_coe.map_nhdsWithin_eq]
  have himg : (fun τ : UpperHalfPlane => (τ : ℂ)) '' {τ0}ᶜ = U ∩ {(τ0 : ℂ)}ᶜ := by
    ext z
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨τ.im_pos, fun h => hτ (UpperHalfPlane.ext h)⟩
    · rintro ⟨hz, hne⟩
      exact ⟨⟨z, hz⟩, fun h => hne (by rw [← h]; rfl), rfl⟩
  rw [himg, nhdsWithin_inter_of_mem]
  exact mem_nhdsWithin_of_mem_nhds (isOpen_U.mem_nhds τ0.im_pos)

open Filter Topology in
instance punctured_neBot (τ0 : UpperHalfPlane) : (𝓝[≠] τ0).NeBot := by
  rw [← Filter.map_neBot_iff (fun τ : UpperHalfPlane => (τ : ℂ)), map_coe_punctured]
  infer_instance

open Filter Topology in
theorem eventually_jDen_ne_H (τ0 : UpperHalfPlane) :
    ∀ᶠ τ : UpperHalfPlane in 𝓝[≠] τ0, PkgI1.jDen (PkgI1.Omega (τ : ℂ)) ≠ 0 := by
  have h := jDenO_eventually_ne (z := (τ0 : ℂ)) τ0.im_pos
  rw [← map_coe_punctured] at h
  exact Filter.eventually_map.1 h

open Filter Topology in
theorem value_infty_of_tendsto {f : UpperHalfPlane → OnePoint ℂ} (hc : Continuous f) {h : ℂ → ℂ}
    (τ0 : UpperHalfPlane) (hev : ∀ᶠ τ : UpperHalfPlane in 𝓝[≠] τ0, f τ = ((h τ : ℂ) : OnePoint ℂ))
    (ht : Tendsto h (𝓝[≠] (τ0 : ℂ)) (Bornology.cobounded ℂ)) : f τ0 = OnePoint.infty := by
  have h1 : Tendsto f (𝓝[≠] τ0) (𝓝 (f τ0)) := hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hcoe : Tendsto (fun z : ℂ => (z : OnePoint ℂ)) (Bornology.cobounded ℂ) (𝓝 OnePoint.infty) := by
    rw [Metric.cobounded_eq_cocompact, ← Filter.coclosedCompact_eq_cocompact]
    exact OnePoint.tendsto_coe_infty
  have hh : Tendsto (fun τ : UpperHalfPlane => h τ) (𝓝[≠] τ0) (Bornology.cobounded ℂ) :=
    ht.comp (le_of_eq (map_coe_punctured τ0))
  have h2 : Tendsto f (𝓝[≠] τ0) (𝓝 OnePoint.infty) :=
    (hcoe.comp hh).congr' (hev.mono fun τ hτ => hτ.symm)
  exact tendsto_nhds_unique h1 h2

open Filter Topology in
theorem value_of_eventually {f : UpperHalfPlane → OnePoint ℂ} (hc : Continuous f) (τ0 : UpperHalfPlane)
    (v : OnePoint ℂ) (hev : ∀ᶠ τ : UpperHalfPlane in 𝓝[≠] τ0, f τ = v) : f τ0 = v := by
  have h1 : Tendsto f (𝓝[≠] τ0) (𝓝 (f τ0)) := hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto f (𝓝[≠] τ0) (𝓝 v) := tendsto_const_nhds.congr' (hev.mono fun τ hτ => hτ.symm)
  exact tendsto_nhds_unique h1 h2

open Filter Topology in
/-- If `f = g · h` near `z` with `h` analytic and nonzero at `z`, the orders of `f` and `g` agree. -/
theorem order_eq_of_mul {f g h : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z) (hh : AnalyticAt ℂ h z)
    (hh0 : h z ≠ 0) (hfg : f =ᶠ[𝓝 z] g * h) : analyticOrderAt f z = analyticOrderAt g z := by
  rw [analyticOrderAt_congr hfg, analyticOrderAt_mul hg hh,
    analyticOrderAt_eq_zero.2 (Or.inr hh0), add_zero]

open Filter Topology in
theorem Zf_eventually_ne {z : ℂ} (hz : 0 < z.im) : ∀ᶠ w in 𝓝 z, Zf w ≠ 0 :=
  (Zf_analytic z).continuousAt.eventually_ne (Zf_ne hz)

theorem G8_eq (z : ℂ) : G8 z = Sf z / Zf z ^ 4 := rfl
theorem G20_eq (z : ℂ) : HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20 z = Pf z / Zf z ^ 10 := rfl

theorem G8_analytic {z : ℂ} (hz : z ∈ U) : AnalyticAt ℂ G8 z := by
  have : G8 = fun w => Sf w / Zf w ^ 4 := rfl
  rw [this]; exact (Sf_analytic z hz).div ((Zf_analytic z).pow 4) (pow_ne_zero _ (Zf_ne hz))

theorem G20_analytic {z : ℂ} (hz : z ∈ U) : AnalyticAt ℂ HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20 z := by
  have : HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20 = fun w => Pf w / Zf w ^ 10 := rfl
  rw [this]; exact (Pf_analytic z hz).div ((Zf_analytic z).pow 10) (pow_ne_zero _ (Zf_ne hz))

open Filter Topology in
theorem ord_Sf_eq {z : ℂ} (hz : z ∈ U) : analyticOrderAt Sf z = analyticOrderAt G8 z := by
  refine order_eq_of_mul (h := fun w => Zf w ^ 4) (G8_analytic hz) ((Zf_analytic z).pow 4)
    (pow_ne_zero _ (Zf_ne hz)) ?_
  filter_upwards [Zf_eventually_ne hz] with w hw
  simp only [Pi.mul_apply, G8_eq]
  field_simp

open Filter Topology in
theorem ord_Pf_eq {z : ℂ} (hz : z ∈ U) :
    analyticOrderAt Pf z = analyticOrderAt HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20 z := by
  refine order_eq_of_mul (h := fun w => Zf w ^ 10) (G20_analytic hz) ((Zf_analytic z).pow 10)
    (pow_ne_zero _ (Zf_ne hz)) ?_
  filter_upwards [Zf_eventually_ne hz] with w hw
  simp only [Pi.mul_apply, G20_eq]
  field_simp

/-- The fixed point of `ι((1 + j)/2)` in `ℍ` is `i√3`. -/
theorem fixed_x3 {γ : GL (Fin 2) ℝ} (hγ : (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x3)
    {τ : UpperHalfPlane} (hτ : γ • τ = τ) : τ = tau3 := by
  have hM : (γ : Matrix (Fin 2) (Fin 2) ℝ) = !![1/2, -3/2; 1/2, 1/2] := by
    rw [hγ, iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp [x3] <;> norm_num
  have hdet : 0 < γ.det.val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hM, Matrix.det_fin_two_of]; norm_num
  have h := congrArg (fun w : UpperHalfPlane => (w : ℂ)) hτ
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet, div_eq_iff (UpperHalfPlane.denom_ne_zero γ τ)] at h
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hM, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons] at h
  have s3 : (√3 : ℂ) * √3 = 3 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hq : ((τ : ℂ) - √3 * Complex.I) * ((τ : ℂ) + √3 * Complex.I) = 0 := by
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    push_cast at h
    linear_combination (-2 : ℂ) * h - Complex.I * Complex.I * s3 - 3 * hI
  apply UpperHalfPlane.ext
  rcases mul_eq_zero.1 hq with h1 | h1
  · rw [tau3_coe]; linear_combination h1
  · exfalso
    have := congrArg Complex.im h1
    simp at this
    have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)
    linarith [τ.im_pos]

theorem enat_aux {a b : ℕ∞} (h : 2 * (a + b) ≤ 10) (hb : 1 ≤ b) : a ≤ 4 := by
  induction a using ENat.recTopCoe with
  | top => simp at h
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp at h
    | coe b =>
      have h' : 2 * (a + b) ≤ 10 := by exact_mod_cast h
      have hb' : 1 ≤ b := by exact_mod_cast hb
      exact_mod_cast (show a ≤ 4 by omega)

theorem mero_neg_aux {N D : ℂ → ℂ} {z : ℂ} (hN : AnalyticAt ℂ N z) (hD : AnalyticAt ℂ D z)
    (hn : analyticOrderAt N z ≤ 8) (hd : 10 ≤ analyticOrderAt D z) (hdt : analyticOrderAt D z ≠ ⊤) :
    meromorphicOrderAt (fun w => N w / D w) z < 0 := by
  have e : (fun w => N w / D w) = N / D := rfl
  rw [e, meromorphicOrderAt_div hN.meromorphicAt hD.meromorphicAt, hN.meromorphicOrderAt_eq,
    hD.meromorphicOrderAt_eq]
  generalize analyticOrderAt N z = n at hn
  generalize analyticOrderAt D z = d at hd hdt
  induction n using ENat.recTopCoe with
  | top => simp at hn
  | coe n =>
    induction d using ENat.recTopCoe with
    | top => exact absurd rfl hdt
    | coe d =>
      have hn' : n ≤ 8 := by exact_mod_cast hn
      have hd' : 10 ≤ d := by exact_mod_cast hd
      simp only [ENat.map_coe]
      have h := (show (n : ℤ) - d < 0 by omega)
      have e2 : ((n : ℤ) : WithTop ℤ) - ((d : ℤ) : WithTop ℤ) = (((n : ℤ) - d : ℤ) : WithTop ℤ) := rfl
      rw [e2]
      exact_mod_cast h

/-- **`QMHauptmodulBase2` without its disc −3 clause.** What is left: the Hauptmodul property and the
value `−16/27` at the order-2 point. -/
def QMHauptmodulBase3 : Prop :=
  ∃ f : UpperHalfPlane → OnePoint ℂ, Continuous f ∧
    (∀ τ : UpperHalfPlane, PkgI1.jDen (PkgI1.Omega τ) ≠ 0 →
      f τ = ((PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) : ℂ) : OnePoint ℂ)) ∧
    (∀ τ τ' : UpperHalfPlane, f τ = f τ' ↔ ∃ γ ∈ PkgI1.GammaStar, γ • τ = τ') ∧
    Function.Surjective f ∧
    (∀ γ : GL (Fin 2) ℝ, (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota mu →
      ∀ τ : UpperHalfPlane, γ • τ = τ → f τ = ((-16/27 : ℂ) : OnePoint ℂ))

set_option maxHeartbeats 1000000 in
open UpperHalfPlane (denom denom_ne_zero) in
open Filter Topology in
/-- **The pole at `i√3` (proved)** from Igusa's `ThetaModularity` (R4), `GammaStarGen` (proved) and the
valence bound: `ord_{i√3}(Σθ⁸∘Ω) ≥ 2` (period-map's `S8OrderCM3`), and the valence bound for
`G20 = ∏θ²∘Ω/dF¹⁰` (weight 20) at `{i√3, √2+i}` with `G20(√2+i) = 0` gives `ord_{i√3}(∏θ²∘Ω) ≤ 4`, so
`ord(jNum∘Ω) ≤ 8 < 10 ≤ ord(jDen∘Ω)` and `jNum/jDen → ∞`. -/
theorem base2_of_base3 (hT : PkgI1.ThetaModularity) (hG : HSyn.G0Split.FibreQM.PeriodGlue.GammaStarGen)
    (hV : ValenceBoundGammaStar) (h : QMHauptmodulBase3) : QMHauptmodulBase2 := by
  classical
  obtain ⟨f, hc, hform, hfib, hsurj, h24⟩ := h
  refine ⟨f, hc, hform, hfib, hsurj, fun γ hγ τ hτ => ?_, h24⟩
  obtain rfl := fixed_x3 hγ hτ
  have h3U : (tau3 : ℂ) ∈ U := tau3.im_pos
  have h4U : (tau4 : ℂ) ∈ U := tau4.im_pos
  have hW := HSyn.G0Split.FibreQM.PeriodGlue.s8WeightExact_of hT hG
  -- `ord Σθ⁸∘Ω ≥ 2` at `i√3`
  have hS3 : 2 ≤ analyticOrderAt Sf (tau3 : ℂ) := by
    rw [ord_Sf_eq h3U]; exact s8OrderCM3_of thetaOmegaAnalytic_proof hW
  -- `G8(i√3) = 0`, `G8(√2+i) ≠ 0`
  have hG8_3 : G8 (tau3 : ℂ) = 0 := by
    apply apply_eq_zero_of_analyticOrderAt_ne_zero
    rw [← ord_Sf_eq h3U]; intro h0; rw [h0] at hS3; norm_num at hS3
  have hG8_4 : G8 (tau4 : ℂ) ≠ 0 := by
    rw [G8_eq]; exact div_ne_zero Sf_tau4 (pow_ne_zero _ (Zf_ne tau4.im_pos))
  -- `i√3` and `√2 + i` are inequivalent
  have hne34 : tau3 ≠ tau4 := by
    intro h0
    have := congrArg (fun w : UpperHalfPlane => (w : ℂ).re) h0
    simp [tau3_coe, tau4_coe] at this
    have h2 : (0 : ℝ) < √2 := Real.sqrt_pos.2 (by norm_num)
    linarith
  have hpair : ((({tau3, tau4} : Finset UpperHalfPlane)) : Set UpperHalfPlane).Pairwise
      (fun z w => ∀ γ ∈ PkgI1.GammaStar, γ • z ≠ w) := by
    intro z hz w hw hzw γ hγ' hγz
    have hdet : (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ≠ 0 := by
      obtain ⟨_, _, _, hd⟩ := hγ'; exact_mod_cast hd.ne'
    have e := hW γ hγ' z
    rw [hγz] at e
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz hw
    rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
    · exact hzw rfl
    · rw [hG8_3, mul_zero] at e
      exact hG8_4 ((mul_eq_zero.1 e).resolve_right (pow_ne_zero _ hdet))
    · rw [hG8_3, zero_mul] at e
      exact hG8_4 ((mul_eq_zero.1 e.symm).resolve_left (pow_ne_zero _ (denom_ne_zero γ _)))
    · exact hzw rfl
  -- `G20 ≢ 0` (else `f ≡ 0`, against surjectivity)
  have hG20ne : ∃ z ∈ U, HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20 z ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hf0 : ∀ τ0 : UpperHalfPlane, f τ0 = ((0 : ℂ) : OnePoint ℂ) := by
      intro τ0
      refine value_of_eventually hc τ0 _ ?_
      filter_upwards [eventually_jDen_ne_H τ0] with τ hτ
      rw [hform τ hτ]
      have hP : Pf (τ : ℂ) = 0 := by
        have := hall τ τ.im_pos
        rw [G20_eq] at this
        exact (div_eq_zero_iff.1 this).resolve_right (pow_ne_zero _ (Zf_ne τ.im_pos))
      rw [jNumO_eq, hP]; simp
    obtain ⟨τ, hτ⟩ := hsurj OnePoint.infty
    rw [hf0 τ] at hτ
    exact OnePoint.coe_ne_infty _ hτ
  -- automorphy in absolute value
  have hW20 : ∀ γ ∈ PkgI1.GammaStar, ∀ z : UpperHalfPlane,
      ‖HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20 ((γ • z : UpperHalfPlane) : ℂ)‖ *
        ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ 10 =
      ‖denom γ z‖ ^ (2 * 10) * ‖HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20 (z : ℂ)‖ := by
    intro γ hγ' z
    have ⟨_, _, _, hdet⟩ := hγ'
    have e := congrArg norm (HSyn.G0Split.FibreQM.PeriodGlue.LQ20.s20WeightExact_of hT hG γ hγ' z)
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg hdet.le] at e
    simpa using e
  have hval := hV 10 HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20 (fun z hz => G20_analytic hz)
    hG20ne hW20 {tau3, tau4} hpair
  rw [Finset.sum_pair hne34] at hval
  -- `ord_{√2+i} G20 ≥ 1`
  have h4 : 1 ≤ analyticOrderAt HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20 (tau4 : ℂ) := by
    rw [ENat.one_le_iff_ne_zero, (G20_analytic h4U).analyticOrderAt_ne_zero, G20_eq, Pf_tau4,
      zero_div]
  -- `ord_{i√3} G20 ≤ 4`
  have h3 : analyticOrderAt HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20 (tau3 : ℂ) ≤ 4 := by
    exact enat_aux hval h4
  -- orders of `jNum ∘ Ω` and `jDen ∘ Ω`
  have hNan : AnalyticAt ℂ (fun z => PkgI1.jNum (PkgI1.Omega z)) (tau3 : ℂ) :=
    analyticAt_const.mul ((Pf_analytic _ h3U).pow 2)
  have hDan : AnalyticAt ℂ (fun z => PkgI1.jDen (PkgI1.Omega z)) (tau3 : ℂ) := jDenO_analytic _ h3U
  have hN : analyticOrderAt (fun z => PkgI1.jNum (PkgI1.Omega z)) (tau3 : ℂ) ≤ 8 := by
    have e : (fun z => PkgI1.jNum (PkgI1.Omega z)) = (fun _ => (3779136 : ℂ)) * Pf ^ 2 := by
      funext z; rfl
    rw [e, analyticOrderAt_mul analyticAt_const ((Pf_analytic _ h3U).pow 2),
      analyticOrderAt_eq_zero.2 (Or.inr (by norm_num)), zero_add,
      analyticOrderAt_pow (Pf_analytic _ h3U), ord_Pf_eq h3U]
    calc (2 : ℕ) • analyticOrderAt HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20 (tau3 : ℂ)
        ≤ (2 : ℕ) • (4 : ℕ∞) := by gcongr
      _ = 8 := by norm_num
  have hD : 10 ≤ analyticOrderAt (fun z => PkgI1.jDen (PkgI1.Omega z)) (tau3 : ℂ) := by
    have e : (fun z => PkgI1.jDen (PkgI1.Omega z)) = Sf ^ 5 := by funext z; rfl
    rw [e, analyticOrderAt_pow (Sf_analytic _ h3U)]
    calc (10 : ℕ∞) = (5 : ℕ) • (2 : ℕ∞) := by norm_num
      _ ≤ (5 : ℕ) • analyticOrderAt Sf (tau3 : ℂ) := by gcongr
  have hDtop := jDenO_order_ne_top h3U
  -- `jNum/jDen → ∞`
  have hmo : meromorphicOrderAt (fun z => PkgI1.jNum (PkgI1.Omega z) / PkgI1.jDen (PkgI1.Omega z))
      (tau3 : ℂ) < 0 := by
    exact mero_neg_aux hNan hDan hN hD hDtop
  refine value_infty_of_tendsto hc tau3 (h := fun z => PkgI1.jNum (PkgI1.Omega z) /
    PkgI1.jDen (PkgI1.Omega z)) ?_ (tendsto_cobounded_of_meromorphicOrderAt_neg hmo)
  filter_upwards [eventually_jDen_ne_H tau3] with τ hτ
  exact hform τ hτ

end HDec.LeafQCheck.HM

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# qm-split: `QMHauptmodulBase3` from the valence formula (published) and three small glue Props

For `c ∈ ℂ` put `H_c = 3779136·G20² − c·G8⁵` (weight 40 for `Γ*`; `jNum∘Ω − c·jDen∘Ω` divided by `dF²⁰`).
The valence formula gives `Σ_{Γ*\ℍ} ord/e = 40·(π/6)/(4π) = 5/3` for `H_c` and `1/3` for `G8`, `5/6` for
`G20`. At `i√3`: `ord G8 ≥ 2` (period-map) and the bound for `G8` force `e = 6`, `ord G8 = 2` and that `G8`
has no other zeros; `ord G20 = a ≤ 4`; so `ord H_c = 2a` there, contributing `a/3`. At every other zero `Q`
of `H_c`, `H_c/G8⁵ = j_θ − c` is `Γ*`-invariant and holomorphic, so `e_Q ∣ ord_Q` (glue
`EllipticOrderDvd`): those contributions are integers. `a/3 + n = 5/3` forces `a = 2`, `n = 1`: the fibre of
`j_θ` over `c` is exactly one orbit. The value `−16/27` is the glue `ThetaQuotientValue24`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

namespace HDec.LeafQCheck.HM.QMSplit

open PkgI1
open HSyn.G0Split.FibreQM.PeriodMap (G8 U tau3 tau4 thetaOmegaAnalytic_proof s8OrderCM3_of
  isOpen_U isPreconnected_U gammaStar_inv)
open UpperHalfPlane (denom denom_ne_zero)
open scoped ENNReal
open Filter Topology

noncomputable section

/-- `G20 = ∏θ²∘Ω/dF¹⁰`. -/
abbrev G20 : ℂ → ℂ := HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20

/-! ## Genuine definitions (as in `Valence.lean`) -/

/-- `e_P` for a general `Γ`: the number of distinct Möbius maps of elements of `Γ` fixing `P`. -/
noncomputable def ellOrderOf (Γ : Set (GL (Fin 2) ℝ)) (P : UpperHalfPlane) : ℕ :=
  Nat.card {f : UpperHalfPlane → UpperHalfPlane // ∃ γ ∈ Γ, γ • P = P ∧ f = fun z => γ • z}

/-- `Γ` acts on `ℍ` as a cocompact Fuchsian group (see `Valence.lean`). -/
structure IsCocompactFuchsian (Γ : Set (GL (Fin 2) ℝ)) : Prop where
  one_mem : 1 ∈ Γ
  mul_mem : ∀ a ∈ Γ, ∀ b ∈ Γ, a * b ∈ Γ
  inv_mem : ∀ a ∈ Γ, a⁻¹ ∈ Γ
  det_pos : ∀ a ∈ Γ, 0 < (a : Matrix (Fin 2) (Fin 2) ℝ).det
  properlyDiscontinuous : ∀ K : Set UpperHalfPlane, IsCompact K →
    {f : UpperHalfPlane → UpperHalfPlane | ∃ γ ∈ Γ, f = (fun z => γ • z) ∧ (f '' K ∩ K).Nonempty}.Finite
  cocompact : ∃ C : Set UpperHalfPlane, IsCompact C ∧ ∀ z, ∃ γ ∈ Γ, γ • z ∈ C

/-- A fundamental domain of `Γ` on `ℍ` (see `Valence.lean`). -/
def IsFundDomain (Γ : Set (GL (Fin 2) ℝ)) (s : Set UpperHalfPlane) : Prop :=
  MeasurableSet s ∧ (∀ z, ∃ γ ∈ Γ, γ • z ∈ s) ∧
    ∀ γ ∈ Γ, (fun z : UpperHalfPlane => γ • z) ≠ id →
      MeasureTheory.volume (s ∩ (fun z : UpperHalfPlane => γ • z) ⁻¹' s) = 0

/-- Every zero of `F` in `ℍ` is `Γ`-equivalent to a point of `T`. -/
def Covers (Γ : Set (GL (Fin 2) ℝ)) (T : Finset UpperHalfPlane) (F : ℂ → ℂ) : Prop :=
  ∀ z : UpperHalfPlane, F (z : ℂ) = 0 → ∃ t ∈ T, ∃ γ ∈ Γ, γ • t = z

/-- **LEAF (the valence formula for a cocompact Fuchsian group, equality form).** For `Γ` a cocompact
Fuchsian group with fundamental domain `s` and `F` a nonzero holomorphic automorphic form of weight
`k = 2m` (unitary multiplier): the zeros of `F` lie in finitely many `Γ`-orbits, and for a set `T` of
representatives (pairwise inequivalent, covering the zeros) `Σ_{P ∈ T} ord_P(F)/e_P = k·vol(s)/(4π)`; the
same sum over any finite set of pairwise inequivalent points is `≤ k·vol(s)/(4π)`.

Published form: Shimura, *Introduction to the arithmetic theory of automorphic functions*, 1971, Prop. 2.16
and Thm. 2.20 (`Σ_{P ∈ Γ\ℍ} ν_P(F)/e_P = k·vol(Γ\ℍ)/(4π)` for `Γ` of the first kind without cusps; the zeros
are finitely many orbits since `Γ\ℍ` is compact); Rankin, *Modular forms and functions*, 1977, Thm. 4.1.4
(unitary multipliers); numbers UNVERIFIED. The third clause drops nonnegative terms. -/
def ValenceFormulaCocompactEq : Prop :=
  ∀ (Γ : Set (GL (Fin 2) ℝ)), IsCocompactFuchsian Γ → ∀ s, IsFundDomain Γ s →
  ∀ (m : ℕ) (F : ℂ → ℂ), AnalyticOnNhd ℂ F U → (∃ z ∈ U, F z ≠ 0) →
    (∀ γ ∈ Γ, ∀ z : UpperHalfPlane,
      ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖) →
    (∃ T : Finset UpperHalfPlane, (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γ, γ • z ≠ w) ∧
        Covers Γ T F) ∧
    (∀ T : Finset UpperHalfPlane, (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γ, γ • z ≠ w) →
      Covers Γ T F →
      ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (ellOrderOf Γ z : ℝ≥0∞) =
        (2 * m : ℝ≥0∞) * MeasureTheory.volume s / ENNReal.ofReal (4 * Real.pi)) ∧
    (∀ T : Finset UpperHalfPlane, (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γ, γ • z ≠ w) →
      ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (ellOrderOf Γ z : ℝ≥0∞) ≤
        (2 * m : ℝ≥0∞) * MeasureTheory.volume s / ENNReal.ofReal (4 * Real.pi))

/-- **GLUE (`Γ*` is a cocompact Fuchsian group with covolume `π/6`)**, as in `Valence.lean` (row H-87). -/
def GammaStarCocompactArea : Prop :=
  IsCocompactFuchsian PkgI1.GammaStar ∧
    ∃ s, IsFundDomain PkgI1.GammaStar s ∧ MeasureTheory.volume s = ENNReal.ofReal (Real.pi / 6)

/-- **GLUE (textbook: orders at elliptic points).** If `F₁, F₂` are holomorphic automorphic forms of the same
weight `2m` for `Γ*` (exact automorphy) and `F₂(P) ≠ 0`, then `e_P` divides `ord_P F₁`: `F₁/F₂` is
`Γ*`-invariant and holomorphic at `P`, the stabilizer of `P` acts on a local coordinate `w = (z − P)/(z − P̄)`
by the rotations `w ↦ ζw`, `ζ^{e_P} = 1` (`ζ` primitive), so only powers `w^n` with `e_P ∣ n` occur.
(Shimura 1971, §2.4, the local expansion at elliptic points; Miyake, *Modular forms*, §2.3; UNVERIFIED.) -/
def EllipticOrderDvd : Prop :=
  ∀ (m : ℕ) (F₁ F₂ : ℂ → ℂ), AnalyticOnNhd ℂ F₁ U → AnalyticOnNhd ℂ F₂ U →
    (∀ γ ∈ PkgI1.GammaStar, ∀ z : UpperHalfPlane,
      F₁ ((γ • z : UpperHalfPlane) : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ^ m =
        denom γ z ^ (2 * m) * F₁ (z : ℂ)) →
    (∀ γ ∈ PkgI1.GammaStar, ∀ z : UpperHalfPlane,
      F₂ ((γ • z : UpperHalfPlane) : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ^ m =
        denom γ z ^ (2 * m) * F₂ (z : ℂ)) →
    ∀ P : UpperHalfPlane, F₂ (P : ℂ) ≠ 0 → analyticOrderAt F₁ (P : ℂ) ≠ ⊤ →
      HDec.LeafQCheck.VB.ellOrder P ∣ (analyticOrderAt F₁ (P : ℂ)).toNat

/-- **GLUE (the value of the theta quotient at the CM point of discriminant `−24`).** At the fixed point
`τ = i√(9 + 6√2)` of `ι(μ)`, `μ = 2j + ij`: `jDen(Ω(τ)) ≠ 0` and `jNum(Ω(τ))/jDen(Ω(τ)) = −16/27`.
Numerically VERIFIED by leaf-review-a (`py/hauptmodul_check.py`: `−0.592592592592593`). Sources for a proof:
Baba–Granath, Canad. J. Math. 60 (2008) (Igusa invariants of the QM family as functions of the Hauptmodul of
`X₆/W`, and its CM values) with Igusa's theta expressions of the Igusa invariants (Amer. J. Math. 89 (1967));
locators UNVERIFIED. -/
def ThetaQuotientValue24 : Prop :=
  ∀ γ : GL (Fin 2) ℝ, (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota mu → ∀ τ : UpperHalfPlane, γ • τ = τ →
    PkgI1.jDen (PkgI1.Omega τ) ≠ 0 ∧
      PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) = -16 / 27


/-! ## Proof -/

abbrev Γs : Set (GL (Fin 2) ℝ) := PkgI1.GammaStar

theorem ellOrderOf_eq : ellOrderOf Γs = HDec.LeafQCheck.VB.ellOrder := rfl

/-- Exact automorphy of weight `2m` for `Γ*`. -/
def Auto (m : ℕ) (F : ℂ → ℂ) : Prop :=
  ∀ γ ∈ Γs, ∀ z : UpperHalfPlane,
    F ((γ • z : UpperHalfPlane) : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ^ m =
      denom γ z ^ (2 * m) * F (z : ℂ)

theorem det_ne {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γs) :
    (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ≠ 0 := by
  obtain ⟨_, _, _, hd⟩ := hγ; exact_mod_cast hd.ne'

theorem zero_iff {m : ℕ} {F : ℂ → ℂ} (hF : Auto m F) {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γs)
    (z : UpperHalfPlane) : F ((γ • z : UpperHalfPlane) : ℂ) = 0 ↔ F (z : ℂ) = 0 := by
  have e := hF γ hγ z
  constructor
  · intro h
    rw [h, zero_mul] at e
    exact (mul_eq_zero.1 e.symm).resolve_left (pow_ne_zero _ (denom_ne_zero γ z))
  · intro h
    rw [h, mul_zero] at e
    exact (mul_eq_zero.1 e).resolve_right (pow_ne_zero _ (det_ne hγ))

theorem abs_auto {m : ℕ} {F : ℂ → ℂ} (hF : Auto m F) :
    ∀ γ ∈ Γs, ∀ z : UpperHalfPlane,
      ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖ := by
  intro γ hγ z
  have ⟨_, _, _, hdet⟩ := hγ
  have e := congrArg norm (hF γ hγ z)
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg hdet.le] at e
  simpa using e

theorem auto8 (hT : PkgI1.ThetaModularity) : Auto 4 G8 :=
  HSyn.G0Split.FibreQM.PeriodGlue.s8WeightExact_of hT HDec.LeafQCheck.gammaStarGen_proof

theorem auto20 (hT : PkgI1.ThetaModularity) : Auto 10 G20 :=
  HSyn.G0Split.FibreQM.PeriodGlue.LQ20.s20WeightExact_of hT HDec.LeafQCheck.gammaStarGen_proof

/-- `H_c = 3779136·G20² − c·G8⁵`. -/
def Hc (c : ℂ) (z : ℂ) : ℂ := 3779136 * G20 z ^ 2 - c * G8 z ^ 5

/-- `G8⁵`. -/
def G85 (z : ℂ) : ℂ := G8 z ^ 5

theorem autoHc (hT : PkgI1.ThetaModularity) (c : ℂ) : Auto 20 (Hc c) := by
  intro γ hγ z
  have e1 := auto20 hT γ hγ z
  have e2 := auto8 hT γ hγ z
  simp only [Hc]
  set X := G20 ((γ • z : UpperHalfPlane) : ℂ)
  set Y := G8 ((γ • z : UpperHalfPlane) : ℂ)
  set d := (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ)
  set j := denom γ z
  linear_combination 3779136 * (X * d ^ 10 + j ^ 20 * G20 (z : ℂ)) * e1 -
    c * ((Y * d ^ 4) ^ 4 + (Y * d ^ 4) ^ 3 * (j ^ 8 * G8 (z : ℂ)) +
      (Y * d ^ 4) ^ 2 * (j ^ 8 * G8 (z : ℂ)) ^ 2 + (Y * d ^ 4) * (j ^ 8 * G8 (z : ℂ)) ^ 3 +
      (j ^ 8 * G8 (z : ℂ)) ^ 4) * e2

theorem autoG85 (hT : PkgI1.ThetaModularity) : Auto 20 G85 := by
  intro γ hγ z
  have e2 := auto8 hT γ hγ z
  simp only [G85]
  set Y := G8 ((γ • z : UpperHalfPlane) : ℂ)
  set d := (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ)
  set j := denom γ z
  linear_combination ((Y * d ^ 4) ^ 4 + (Y * d ^ 4) ^ 3 * (j ^ 8 * G8 (z : ℂ)) +
      (Y * d ^ 4) ^ 2 * (j ^ 8 * G8 (z : ℂ)) ^ 2 + (Y * d ^ 4) * (j ^ 8 * G8 (z : ℂ)) ^ 3 +
      (j ^ 8 * G8 (z : ℂ)) ^ 4) * e2

theorem Hc_analytic (c : ℂ) : AnalyticOnNhd ℂ (Hc c) U := fun z hz => by
  unfold Hc
  exact (analyticAt_const.mul ((G20_analytic hz).pow 2)).sub (analyticAt_const.mul ((G8_analytic hz).pow 5))

theorem G85_analytic : AnalyticOnNhd ℂ G85 U := fun z hz => by
  unfold G85; exact (G8_analytic hz).pow 5

/-! ### The equivalence relation of `Γ*` on `ℍ` -/

theorem eqv_symm {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γs) {z w : UpperHalfPlane} (h : γ • z = w) :
    γ⁻¹ • w = z := by rw [← h, inv_smul_smul]

theorem eqv_trans {γ γ' : GL (Fin 2) ℝ} (hγ : γ ∈ Γs) (hγ' : γ' ∈ Γs) {z w v : UpperHalfPlane}
    (h : γ • z = w) (h' : γ' • w = v) : ∃ δ ∈ Γs, δ • z = v :=
  ⟨γ' * γ, HDec.LeafQCheck.VB.gammaStar_mul hγ' hγ, by rw [mul_smul, h, h']⟩

/-! ### Arithmetic -/

theorem arith (m : ℕ) :
    (2 * m : ℝ≥0∞) * ENNReal.ofReal (Real.pi / 6) / ENNReal.ofReal (4 * Real.pi) = (m : ℝ≥0∞) / 12 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have e1 : (2 * m : ℝ≥0∞) = ENNReal.ofReal (2 * m) := by
    rw [ENNReal.ofReal_mul (by norm_num)]; simp
  rw [e1, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_div_of_pos (by positivity)]
  have e2 : (2 * (m : ℝ) * (Real.pi / 6)) / (4 * Real.pi) = (m : ℝ) / 12 := by
    field_simp; ring
  rw [e2, ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

theorem enn_div (x y : ℕ) (hy : 0 < y) : (x : ℝ≥0∞) / y = ENNReal.ofReal ((x : ℝ) / y) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hy)]; simp

/-! ### The valence formula for `Γ*` -/

/-- **The valence statements for `Γ*` used below** (existence of a finite set of representatives of the zeros,
the sum over it, and the bound over any finite set of inequivalent points; weight `2m`, exact automorphy). -/
def GammaStarValence : Prop :=
  ∀ (m : ℕ) (F : ℂ → ℂ), AnalyticOnNhd ℂ F U → (∃ z ∈ U, F z ≠ 0) → Auto m F →
    (∃ T : Finset UpperHalfPlane, (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γs, γ • z ≠ w) ∧
      Covers Γs T F) ∧
    (∀ T : Finset UpperHalfPlane, (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γs, γ • z ≠ w) →
      Covers Γs T F →
      ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (HDec.LeafQCheck.VB.ellOrder z : ℝ≥0∞) =
        (m : ℝ≥0∞) / 12) ∧
    (∀ T : Finset UpperHalfPlane, (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γs, γ • z ≠ w) →
      ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (HDec.LeafQCheck.VB.ellOrder z : ℝ≥0∞) ≤
        (m : ℝ≥0∞) / 12)

/-- `GammaStarValence` from the valence formula and the covolume glue. -/
theorem gammaStarValence_of_area (hV : ValenceFormulaCocompactEq) (hA : GammaStarCocompactArea) :
    GammaStarValence := by
  intro m F hF hne hau
  obtain ⟨hFuchs, s, hs, hvol⟩ := hA
  obtain ⟨h1, h2, h3⟩ := hV Γs hFuchs s hs m F hF hne (abs_auto hau)
  refine ⟨h1, fun T hT hc => ?_, fun T hT => ?_⟩
  · have := h2 T hT hc; rwa [hvol, arith] at this
  · have := h3 T hT; rwa [hvol, arith] at this

section Val

variable (hG : GammaStarValence)
include hG

theorem val_le (m : ℕ) (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F U) (hne : ∃ z ∈ U, F z ≠ 0)
    (hau : Auto m F) (T : Finset UpperHalfPlane)
    (hT : (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γs, γ • z ≠ w)) :
    ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (HDec.LeafQCheck.VB.ellOrder z : ℝ≥0∞) ≤
      (m : ℝ≥0∞) / 12 :=
  (hG m F hF hne hau).2.2 T hT

theorem val_eq (m : ℕ) (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F U) (hne : ∃ z ∈ U, F z ≠ 0)
    (hau : Auto m F) (T : Finset UpperHalfPlane)
    (hT : (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γs, γ • z ≠ w)) (hc : Covers Γs T F) :
    ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (HDec.LeafQCheck.VB.ellOrder z : ℝ≥0∞) =
      (m : ℝ≥0∞) / 12 :=
  (hG m F hF hne hau).2.1 T hT hc

theorem val_ex (m : ℕ) (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F U) (hne : ∃ z ∈ U, F z ≠ 0)
    (hau : Auto m F) :
    ∃ T : Finset UpperHalfPlane, (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γs, γ • z ≠ w) ∧
      Covers Γs T F :=
  (hG m F hF hne hau).1

end Val

/-! ### Facts at `i√3`, `√2 + i`, `τ₂₄` -/

open scoped Classical

theorem pair_ineq {x y : UpperHalfPlane} (h : ∀ γ ∈ Γs, γ • x ≠ y) :
    ((({x, y} : Finset UpperHalfPlane)) : Set UpperHalfPlane).Pairwise
      (fun z w => ∀ γ ∈ Γs, γ • z ≠ w) := by
  intro z hz w hw hzw γ hγ h'
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hz hw
  rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
  · exact hzw rfl
  · exact h γ hγ h'
  · exact h γ⁻¹ (gammaStar_inv hγ) (eqv_symm hγ h')
  · exact hzw rfl

theorem G8_tau4_ne : G8 (tau4 : ℂ) ≠ 0 := by
  rw [G8_eq]; exact div_ne_zero Sf_tau4 (pow_ne_zero _ (Zf_ne tau4.im_pos))

theorem G8_ne : ∃ z ∈ U, G8 z ≠ 0 := ⟨tau4, tau4.im_pos, G8_tau4_ne⟩

theorem ord_ne_top_of {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U) {w : ℂ} (hw : w ∈ U) (hFw : F w ≠ 0)
    (z : UpperHalfPlane) : analyticOrderAt F (z : ℂ) ≠ ⊤ :=
  hF.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_U hw z.im_pos
    (by rw [analyticOrderAt_eq_zero.2 (Or.inr hFw)]; simp)

theorem enn_coe_toNat {o : ℕ∞} (h : o ≠ ⊤) : ((o : ℕ∞) : ℝ≥0∞) = ((o.toNat : ℕ) : ℝ≥0∞) := by
  conv_lhs => rw [← ENat.coe_toNat h]
  simp

variable (hT : PkgI1.ThetaModularity) (hG : GammaStarValence)

include hT in
theorem G8_tau3_ge : 2 ≤ analyticOrderAt G8 (tau3 : ℂ) :=
  s8OrderCM3_of thetaOmegaAnalytic_proof (auto8 hT)

include hT hG in
/-- `e_{i√3} = 6` and `ord_{i√3} G8 = 2`. -/
theorem tau3_facts : HDec.LeafQCheck.VB.ellOrder tau3 = 6 ∧ analyticOrderAt G8 (tau3 : ℂ) = 2 := by
  have hb2 := G8_tau3_ge hT
  have hbt := ord_ne_top_of (fun z hz => G8_analytic hz) tau4.im_pos G8_tau4_ne tau3
  obtain ⟨he0, he6⟩ := HDec.LeafQCheck.VB.ellipticOrderLe6_proof tau3
  have hle := val_le hG 4 G8 (fun z hz => G8_analytic hz) G8_ne (auto8 hT) {tau3}
    (by simp)
  rw [Finset.sum_singleton, enn_coe_toNat hbt, enn_div _ _ he0,
    show ((4 : ℕ) : ℝ≥0∞) / 12 = ((4 : ℕ) : ℝ≥0∞) / ((12 : ℕ) : ℝ≥0∞) by norm_num,
    enn_div 4 12 (by norm_num), ENNReal.ofReal_le_ofReal_iff (by positivity),
    div_le_div_iff₀ (by exact_mod_cast he0) (by norm_num)] at hle
  have hle' : (analyticOrderAt G8 (tau3 : ℂ)).toNat * 12 ≤ 4 * HDec.LeafQCheck.VB.ellOrder tau3 := by
    exact_mod_cast hle
  have hb2' : 2 ≤ (analyticOrderAt G8 (tau3 : ℂ)).toNat := by
    have := ENat.coe_toNat hbt
    rw [← this] at hb2; exact_mod_cast hb2
  refine ⟨by omega, ?_⟩
  rw [← ENat.coe_toNat hbt]
  have : (analyticOrderAt G8 (tau3 : ℂ)).toNat = 2 := by omega
  rw [this]; rfl

include hT in
theorem G8_tau3_zero : G8 (tau3 : ℂ) = 0 := by
  apply apply_eq_zero_of_analyticOrderAt_ne_zero
  intro h0; have := G8_tau3_ge hT; rw [h0] at this; norm_num at this

include hT hG in
/-- **`G8` vanishes only on the orbit of `i√3`.** -/
theorem G8_zero_orbit (z : UpperHalfPlane) (hz : G8 (z : ℂ) = 0) : ∃ γ ∈ Γs, γ • tau3 = z := by
  by_contra hno
  push Not at hno
  have hne : tau3 ≠ z := fun h => hno 1 HDec.LeafQCheck.VB.one_mem_gammaStar' (by rw [one_smul, h])
  have hle := val_le hG 4 G8 (fun w hw => G8_analytic hw) G8_ne (auto8 hT) {tau3, z}
    (pair_ineq hno)
  rw [Finset.sum_pair hne] at hle
  obtain ⟨he3, hb⟩ := tau3_facts hT hG
  have hzt := ord_ne_top_of (fun w hw => G8_analytic hw) tau4.im_pos G8_tau4_ne z
  obtain ⟨hez0, -⟩ := HDec.LeafQCheck.VB.ellipticOrderLe6_proof z
  have ho1 : 1 ≤ (analyticOrderAt G8 (z : ℂ)).toNat := by
    have h1 : analyticOrderAt G8 (z : ℂ) ≠ 0 := by
      rw [Ne, analyticOrderAt_eq_zero]; push Not; exact ⟨G8_analytic z.im_pos, hz⟩
    have h2 : (analyticOrderAt G8 (z : ℂ)).toNat ≠ 0 := by
      rw [Ne, ENat.toNat_eq_zero]; push Not; exact ⟨h1, hzt⟩
    omega
  rw [hb, he3, enn_coe_toNat hzt, enn_div _ _ hez0,
    show ((2 : ℕ∞) : ℝ≥0∞) / ((6 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℕ) / (6 : ℕ)) by
      rw [← enn_div 2 6 (by norm_num)]; simp,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    show ((4 : ℕ) : ℝ≥0∞) / 12 = ((4 : ℕ) : ℝ≥0∞) / ((12 : ℕ) : ℝ≥0∞) by norm_num,
    enn_div 4 12 (by norm_num), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  have hpos : (0 : ℝ) < ((analyticOrderAt G8 (z : ℂ)).toNat : ℝ) / (HDec.LeafQCheck.VB.ellOrder z : ℝ) := by
    apply div_pos <;> exact_mod_cast (by omega)
  push_cast at hle
  linarith

/-! ### The CM point of discriminant `−24` -/

theorem s9 : (0 : ℝ) < 9 + 6 * √2 := by positivity

/-- `τ₂₄ = i√(9 + 6√2)`. -/
def tau24 : UpperHalfPlane := ⟨(√(9 + 6 * √2) : ℂ) * Complex.I, by simp; positivity⟩

theorem nrd_mu : HDec.LeafQCheck.HM.nrd mu ≠ 0 := by simp [HDec.LeafQCheck.HM.nrd, mu]; norm_num

/-- `ι(μ)` as an element of `GL₂(ℝ)`. -/
def gam24 : GL (Fin 2) ℝ := HDec.LeafQCheck.HM.glOf mu nrd_mu

theorem gam24_coe : (gam24 : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota mu := HDec.LeafQCheck.HM.coe_glOf mu nrd_mu

theorem tau24_fixed : gam24 • tau24 = tau24 := by
  have hM : (gam24 : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -6 - 3 * √2; 2 - √2, 0] := by
    rw [gam24_coe, iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp [mu] <;> ring
  have s2 : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have h2 : √2 < (2 : ℝ) := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hdet : 0 < gam24.det.val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hM, Matrix.det_fin_two_of]
    nlinarith
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet, div_eq_iff (UpperHalfPlane.denom_ne_zero _ _)]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hM, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons]
  have e9 : ((√(9 + 6 * √2) : ℝ) : ℂ) * ((√(9 + 6 * √2) : ℝ) : ℂ) = 9 + 6 * (√2 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt s9.le]; push_cast; ring
  have s2c : (√2 : ℂ) * √2 = 2 := by rw [← Complex.ofReal_mul, s2]; norm_num
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  change _ = ((√(9 + 6 * √2) : ℝ) : ℂ) * Complex.I *
    (((2 - √2 : ℝ) : ℂ) * (((√(9 + 6 * √2) : ℝ) : ℂ) * Complex.I) + ((0 : ℝ) : ℂ))
  push_cast
  linear_combination (-(2 - (√2 : ℂ)) * Complex.I * Complex.I) * e9 +
    (-(2 - (√2 : ℂ)) * (9 + 6 * √2)) * hI + (-6) * s2c

variable (hC : ThetaQuotientValue24)

include hC in
theorem G20_tau24_ne : G20 (tau24 : ℂ) ≠ 0 := by
  obtain ⟨hD, hv⟩ := hC gam24 gam24_coe tau24 tau24_fixed
  have hN : PkgI1.jNum (PkgI1.Omega tau24) ≠ 0 := by
    intro h0; rw [h0, zero_div] at hv; norm_num at hv
  change HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20 _ ≠ 0
  rw [G20_eq]
  refine div_ne_zero ?_ (pow_ne_zero _ (Zf_ne tau24.im_pos))
  intro hP; apply hN; rw [jNumO_eq, hP]; ring

include hT hG hC in
/-- `ord_{i√3} G20 ≤ 4`. -/
theorem G20_tau3_le : (analyticOrderAt G20 (tau3 : ℂ)).toNat ≤ 4 ∧ analyticOrderAt G20 (tau3 : ℂ) ≠ ⊤ := by
  have hG20 : AnalyticOnNhd ℂ G20 U := fun z hz => G20_analytic hz
  have htop := ord_ne_top_of hG20 tau24.im_pos (G20_tau24_ne hC) tau3
  have h4top := ord_ne_top_of hG20 tau24.im_pos (G20_tau24_ne hC) tau4
  refine ⟨?_, htop⟩
  have hineq : ∀ γ ∈ Γs, γ • tau3 ≠ tau4 := by
    intro γ hγ h
    have := (zero_iff (auto8 hT) hγ tau3).2 (G8_tau3_zero hT)
    rw [h] at this; exact G8_tau4_ne this
  have hne : tau3 ≠ tau4 := fun h => hineq 1 HDec.LeafQCheck.VB.one_mem_gammaStar' (by rw [one_smul, h])
  have hle := val_le hG 10 G20 hG20 ⟨tau24, tau24.im_pos, G20_tau24_ne hC⟩ (auto20 hT) {tau3, tau4}
    (pair_ineq hineq)
  rw [Finset.sum_pair hne] at hle
  obtain ⟨he3, -⟩ := tau3_facts hT hG
  obtain ⟨he40, he46⟩ := HDec.LeafQCheck.VB.ellipticOrderLe6_proof tau4
  have ho1 : 1 ≤ (analyticOrderAt G20 (tau4 : ℂ)).toNat := by
    have h1 : analyticOrderAt G20 (tau4 : ℂ) ≠ 0 := by
      rw [Ne, analyticOrderAt_eq_zero]; push Not
      exact ⟨G20_analytic tau4.im_pos, by
        change HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20 _ = 0; rw [G20_eq, Pf_tau4, zero_div]⟩
    have h2 : (analyticOrderAt G20 (tau4 : ℂ)).toNat ≠ 0 := by
      rw [Ne, ENat.toNat_eq_zero]; push Not; exact ⟨h1, h4top⟩
    omega
  rw [he3, enn_coe_toNat htop, enn_coe_toNat h4top, enn_div _ 6 (by norm_num), enn_div _ _ he40,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    show ((10 : ℕ) : ℝ≥0∞) / 12 = ((10 : ℕ) : ℝ≥0∞) / ((12 : ℕ) : ℝ≥0∞) by norm_num,
    enn_div 10 12 (by norm_num), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  have h16 : (1 : ℝ) / 6 ≤ ((analyticOrderAt G20 (tau4 : ℂ)).toNat : ℝ) / (HDec.LeafQCheck.VB.ellOrder tau4 : ℝ) := by
    rw [div_le_div_iff₀ (by norm_num) (by exact_mod_cast he40)]
    have : (HDec.LeafQCheck.VB.ellOrder tau4 : ℝ) ≤ 6 := by exact_mod_cast he46
    have : (1 : ℝ) ≤ ((analyticOrderAt G20 (tau4 : ℂ)).toNat : ℝ) := by exact_mod_cast ho1
    nlinarith
  have : ((analyticOrderAt G20 (tau3 : ℂ)).toNat : ℝ) ≤ 4 := by
    push_cast at hle h16 ⊢
    linarith
  exact_mod_cast this

/-! ### The fibres over `c ∈ ℂ` -/

theorem Hc_split (c : ℂ) :
    Hc c = (fun z => 3779136 * G20 z ^ 2) + (fun z => -c * G8 z ^ 5) := by
  funext z; simp only [Hc, Pi.add_apply]; ring

include hT hG hC in
theorem ord_Hc_tau3 (c : ℂ) :
    analyticOrderAt (Hc c) (tau3 : ℂ) = ((2 * (analyticOrderAt G20 (tau3 : ℂ)).toNat : ℕ) : ℕ∞) := by
  obtain ⟨he3, hb⟩ := tau3_facts hT hG
  obtain ⟨ha4, hatop⟩ := G20_tau3_le hT hG hC
  have h3U : (tau3 : ℂ) ∈ U := tau3.im_pos
  have hF : analyticOrderAt (fun z => 3779136 * G20 z ^ 2) (tau3 : ℂ) =
      ((2 * (analyticOrderAt G20 (tau3 : ℂ)).toNat : ℕ) : ℕ∞) := by
    have e : (fun z => 3779136 * G20 z ^ 2) = (fun _ => (3779136 : ℂ)) * G20 ^ 2 := by
      funext z; rfl
    rw [e, analyticOrderAt_mul analyticAt_const ((G20_analytic h3U).pow 2),
      analyticOrderAt_eq_zero.2 (Or.inr (by norm_num)), zero_add,
      analyticOrderAt_pow (G20_analytic h3U), nsmul_eq_mul]
    conv_lhs => rw [← ENat.coe_toNat hatop]
    push_cast; ring
  have hG : (10 : ℕ∞) ≤ analyticOrderAt (fun z => -c * G8 z ^ 5) (tau3 : ℂ) := by
    by_cases hc : c = 0
    · have e : (fun z => -c * G8 z ^ 5) = 0 := by funext z; simp [hc]
      have h0 : analyticOrderAt (0 : ℂ → ℂ) (tau3 : ℂ) = ⊤ :=
        analyticOrderAt_eq_top.2 (Filter.Eventually.of_forall fun _ => rfl)
      rw [e, h0]; exact le_top
    · have e : (fun z => -c * G8 z ^ 5) = (fun _ => -c) * G8 ^ 5 := by funext z; rfl
      rw [e, analyticOrderAt_mul analyticAt_const ((G8_analytic h3U).pow 5),
        analyticOrderAt_eq_zero.2 (Or.inr (by simpa using hc)), zero_add,
        analyticOrderAt_pow (G8_analytic h3U), hb]
      norm_num
  rw [Hc_split, analyticOrderAt_add_eq_left_of_lt, hF]
  rw [hF]
  refine lt_of_lt_of_le ?_ hG
  have : 2 * (analyticOrderAt G20 (tau3 : ℂ)).toNat < 10 := by omega
  exact_mod_cast this

variable (hD : EllipticOrderDvd)

include hT hG hC hD in
/-- **The fibre of `j_θ` over `c ∈ ℂ` is one `Γ*`-orbit.** -/
theorem fibre_c (c : ℂ) : ∃ t₁ : UpperHalfPlane, ∀ z : UpperHalfPlane,
    (G8 (z : ℂ) ≠ 0 ∧ Hc c (z : ℂ) = 0) ↔ ∃ γ ∈ Γs, γ • t₁ = z := by
  obtain ⟨he3, hb⟩ := tau3_facts hT hG
  obtain ⟨ha4, hatop⟩ := G20_tau3_le hT hG hC
  set a := (analyticOrderAt G20 (tau3 : ℂ)).toNat with ha
  have hord := ord_Hc_tau3 hT hG hC c
  rw [← ha] at hord
  have hHtop3 : analyticOrderAt (Hc c) (tau3 : ℂ) ≠ ⊤ := by rw [hord]; exact ENat.coe_ne_top _
  have hHtop : ∀ z : UpperHalfPlane, analyticOrderAt (Hc c) (z : ℂ) ≠ ⊤ := fun z =>
    (Hc_analytic c).analyticOrderAt_ne_top_of_isPreconnected isPreconnected_U tau3.im_pos z.im_pos hHtop3
  have hHne : ∃ z ∈ U, Hc c z ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hHtop3
    rw [analyticOrderAt_eq_top]
    filter_upwards [isOpen_U.mem_nhds tau3.im_pos] with z hz using hall z hz
  obtain ⟨T₀, hT₀p, hT₀c⟩ := val_ex hG 20 (Hc c) (Hc_analytic c) hHne (autoHc hT c)
  set T₁ := T₀.filter (fun t => ¬ ∃ γ ∈ Γs, γ • t = tau3) with hT₁
  set T' := insert tau3 T₁ with hT'
  have hnot : tau3 ∉ T₁ := by
    rw [hT₁, Finset.mem_filter]; push Not
    intro _; exact ⟨1, HDec.LeafQCheck.VB.one_mem_gammaStar', one_smul _ _⟩
  have hT'p : (T' : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γs, γ • z ≠ w) := by
    rw [hT', Finset.coe_insert]
    refine (hT₀p.mono (by intro x hx; exact (Finset.mem_filter.1 hx).1)).insert ?_
    intro w hw hne
    have hw' := (Finset.mem_filter.1 hw).2
    refine ⟨fun γ hγ h => hw' ⟨γ⁻¹, gammaStar_inv hγ, eqv_symm hγ h⟩, fun γ hγ h => hw' ⟨γ, hγ, h⟩⟩
  have hT'c : Covers Γs T' (Hc c) := by
    intro z hz
    obtain ⟨t, ht, γ, hγ, rfl⟩ := hT₀c z hz
    by_cases hR : ∃ δ ∈ Γs, δ • t = tau3
    · obtain ⟨δ, hδ, hδt⟩ := hR
      obtain ⟨ε, hε, hεz⟩ := eqv_trans (gammaStar_inv hδ) hγ (eqv_symm hδ hδt) rfl
      exact ⟨tau3, Finset.mem_insert_self _ _, ε, hε, hεz⟩
    · exact ⟨t, Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨ht, hR⟩), γ, hγ, rfl⟩
  have hsum := val_eq hG 20 (Hc c) (Hc_analytic c) hHne (autoHc hT c) T' hT'p hT'c
  rw [hT', Finset.sum_insert hnot] at hsum
  -- the points of `T₁`: `G8 ≠ 0`, and `e_t ∣ ord_t H_c`
  have hG8t : ∀ t ∈ T₁, G8 (t : ℂ) ≠ 0 := by
    intro t ht h0
    obtain ⟨γ, hγ, hγt⟩ := G8_zero_orbit hT hG t h0
    exact (Finset.mem_filter.1 ht).2 ⟨γ⁻¹, gammaStar_inv hγ, eqv_symm hγ hγt⟩
  have hdvd : ∀ t ∈ T₁, HDec.LeafQCheck.VB.ellOrder t ∣ (analyticOrderAt (Hc c) (t : ℂ)).toNat :=
    fun t ht => hD 20 (Hc c) G85 (Hc_analytic c) G85_analytic (autoHc hT c) (autoG85 hT) t
      (pow_ne_zero 5 (hG8t t ht)) (hHtop t)
  set n : UpperHalfPlane → ℕ := fun t =>
    (analyticOrderAt (Hc c) (t : ℂ)).toNat / HDec.LeafQCheck.VB.ellOrder t with hn
  have hterm : ∀ t ∈ T₁, ((analyticOrderAt (Hc c) (t : ℂ) : ℕ∞) : ℝ≥0∞) /
      (HDec.LeafQCheck.VB.ellOrder t : ℝ≥0∞) = (n t : ℝ≥0∞) := by
    intro t ht
    obtain ⟨he0, -⟩ := HDec.LeafQCheck.VB.ellipticOrderLe6_proof t
    rw [enn_coe_toNat (hHtop t), ← Nat.div_mul_cancel (hdvd t ht)]
    push_cast
    rw [ENNReal.mul_div_cancel_right (by exact_mod_cast he0.ne') (by simp)]
  rw [Finset.sum_congr rfl hterm, hord, he3, ← Nat.cast_sum] at hsum
  set N := ∑ t ∈ T₁, n t
  have key : 2 * a + 6 * N = 10 := by
    have h1 : ((((2 * a : ℕ) : ℕ∞)) : ℝ≥0∞) = ((2 * a : ℕ) : ℝ≥0∞) := by simp
    rw [h1, enn_div _ 6 (by norm_num),
      show ((N : ℕ) : ℝ≥0∞) = ENNReal.ofReal (N : ℝ) by simp,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      show ((20 : ℕ) : ℝ≥0∞) / 12 = ((20 : ℕ) : ℝ≥0∞) / ((12 : ℕ) : ℝ≥0∞) by norm_num,
      enn_div 20 12 (by norm_num), ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at hsum
    push_cast at hsum
    have : (2 * (a : ℝ) + 6 * N) = 10 := by linarith
    exact_mod_cast this
  have hN1 : N = 1 := by omega
  -- the unique point `t₁`
  obtain ⟨t₁, ht₁, hn₁⟩ : ∃ t₁ ∈ T₁, n t₁ ≠ 0 := by
    by_contra h; push Not at h
    have : N = 0 := Finset.sum_eq_zero h
    omega
  have hrest : ∀ t ∈ T₁, t ≠ t₁ → n t = 0 := by
    have hs := Finset.add_sum_erase T₁ n ht₁
    rw [show ∑ x ∈ T₁, n x = N from rfl, hN1] at hs
    have h0 : ∑ x ∈ T₁.erase t₁, n x = 0 := by omega
    intro t ht hne
    exact (Finset.sum_eq_zero_iff.1 h0) t (Finset.mem_erase.2 ⟨hne, ht⟩)
  have hpos : ∀ t ∈ T₁, (Hc c (t : ℂ) = 0 ↔ n t ≠ 0) := by
    intro t ht
    obtain ⟨he0, -⟩ := HDec.LeafQCheck.VB.ellipticOrderLe6_proof t
    have hm := Nat.div_mul_cancel (hdvd t ht)
    constructor
    · intro h0 hn0
      have h1 : analyticOrderAt (Hc c) (t : ℂ) ≠ 0 := by
        rw [Ne, analyticOrderAt_eq_zero]; push Not; exact ⟨Hc_analytic c _ t.im_pos, h0⟩
      have h2 : (analyticOrderAt (Hc c) (t : ℂ)).toNat ≠ 0 := by
        rw [Ne, ENat.toNat_eq_zero]; push Not; exact ⟨h1, hHtop t⟩
      apply h2; rw [← hm]; simp only [n] at hn0; rw [hn0, zero_mul]
    · intro hn0
      apply apply_eq_zero_of_analyticOrderAt_ne_zero
      intro h0
      apply hn0
      simp only [n]; rw [h0]; simp
  refine ⟨t₁, fun z => ⟨fun ⟨hz8, hzH⟩ => ?_, fun ⟨γ, hγ, hγz⟩ => ?_⟩⟩
  · obtain ⟨t, ht, δ, hδ, rfl⟩ := hT'c z hzH
    rw [hT', Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · exact absurd ((zero_iff (auto8 hT) hδ tau3).2 (G8_tau3_zero hT)) hz8
    · have hHt : Hc c (t : ℂ) = 0 := (zero_iff (autoHc hT c) hδ t).1 hzH
      by_cases htt : t = t₁
      · exact ⟨δ, hδ, by rw [← htt]⟩
      · exact absurd ((hpos t ht).1 hHt) (by rw [hrest t ht htt]; simp)
  · subst hγz
    exact ⟨fun h => hG8t t₁ ht₁ ((zero_iff (auto8 hT) hγ t₁).1 h),
      (zero_iff (autoHc hT c) hγ t₁).2 ((hpos t₁ ht₁).2 hn₁)⟩

/-! ### `j_θ` as a map `ℍ → P¹(ℂ)` -/

/-- `j_θ = jNum/jDen ∘ Ω`, with value `∞` where `jDen ∘ Ω = 0`. -/
def jth (τ : UpperHalfPlane) : OnePoint ℂ :=
  if PkgI1.jDen (PkgI1.Omega τ) = 0 then OnePoint.infty
  else ((PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) : ℂ) : OnePoint ℂ)

theorem Sf_eq (z : UpperHalfPlane) : Sf (z : ℂ) = G8 (z : ℂ) * Zf (z : ℂ) ^ 4 := by
  rw [G8_eq, div_mul_cancel₀ _ (pow_ne_zero 4 (Zf_ne z.im_pos))]

theorem Pf_eq (z : UpperHalfPlane) : Pf (z : ℂ) = G20 (z : ℂ) * Zf (z : ℂ) ^ 10 := by
  change Pf (z : ℂ) = HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20 (z : ℂ) * Zf (z : ℂ) ^ 10
  rw [G20_eq, div_mul_cancel₀ _ (pow_ne_zero 10 (Zf_ne z.im_pos))]

theorem jDen_zero_iff (z : UpperHalfPlane) : PkgI1.jDen (PkgI1.Omega z) = 0 ↔ G8 (z : ℂ) = 0 := by
  rw [jDenO_eq, Sf_eq]
  constructor
  · intro h
    have := pow_eq_zero_iff (n := 5) (by norm_num) |>.1 h
    exact (mul_eq_zero.1 this).resolve_right (pow_ne_zero _ (Zf_ne z.im_pos))
  · intro h; rw [h]; ring

theorem jth_infty_iff (z : UpperHalfPlane) : jth z = OnePoint.infty ↔ G8 (z : ℂ) = 0 := by
  rw [← jDen_zero_iff]
  unfold jth
  split_ifs with h
  · simp [h]
  · simp [h]

theorem jth_coe_iff (z : UpperHalfPlane) (c : ℂ) : jth z = (c : OnePoint ℂ) ↔
    G8 (z : ℂ) ≠ 0 ∧ Hc c (z : ℂ) = 0 := by
  have hiff := jDen_zero_iff z
  unfold jth
  have hZ := pow_ne_zero 20 (Zf_ne z.im_pos)
  split_ifs with h
  · simp [hiff.1 h]
  · have h8 : G8 (z : ℂ) ≠ 0 := fun h' => h (hiff.2 h')
    simp only [OnePoint.coe_eq_coe, ne_eq, h8, not_false_eq_true, true_and]
    rw [div_eq_iff h, jNumO_eq, jDenO_eq, Sf_eq, Pf_eq]
    constructor
    · intro e
      have : Hc c (z : ℂ) * Zf (z : ℂ) ^ 20 = 0 := by simp only [Hc]; linear_combination e
      exact (mul_eq_zero.1 this).resolve_right hZ
    · intro e
      simp only [Hc] at e
      linear_combination Zf (z : ℂ) ^ 20 * e

include hT hG hC hD in
/-- **Every fibre of `j_θ` is one `Γ*`-orbit.** -/
theorem jth_fibre (v : OnePoint ℂ) : ∃ b : UpperHalfPlane, ∀ z : UpperHalfPlane,
    jth z = v ↔ ∃ γ ∈ Γs, γ • b = z := by
  induction v using OnePoint.rec with
  | infty =>
    refine ⟨tau3, fun z => ?_⟩
    rw [jth_infty_iff]
    constructor
    · exact G8_zero_orbit hT hG z
    · rintro ⟨γ, hγ, rfl⟩
      exact (zero_iff (auto8 hT) hγ tau3).2 (G8_tau3_zero hT)
  | coe c =>
    obtain ⟨t₁, ht₁⟩ := fibre_c hT hG hC hD c
    exact ⟨t₁, fun z => by rw [jth_coe_iff]; exact ht₁ z⟩

include hT in
/-- `j_θ` is `Γ*`-invariant on the finite part (as a function to `ℂ`). -/
theorem g_inv {δ : GL (Fin 2) ℝ} (hδ : δ ∈ Γs) (τ : UpperHalfPlane) :
    PkgI1.jNum (PkgI1.Omega ((δ • τ : UpperHalfPlane) : ℂ)) / PkgI1.jDen (PkgI1.Omega ((δ • τ : UpperHalfPlane) : ℂ)) =
      PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) := by
  have key : ∀ w : UpperHalfPlane, PkgI1.jNum (PkgI1.Omega w) / PkgI1.jDen (PkgI1.Omega w) =
      3779136 * G20 (w : ℂ) ^ 2 / G8 (w : ℂ) ^ 5 := by
    intro w
    rw [jNumO_eq, jDenO_eq, Sf_eq, Pf_eq]
    have hZ := Zf_ne w.im_pos
    by_cases h8 : G8 (w : ℂ) = 0
    · simp [h8]
    · field_simp
  rw [key, key]
  have e1 := auto20 hT δ hδ τ
  have e2 := auto8 hT δ hδ τ
  have hd := det_ne hδ
  have hj := denom_ne_zero δ τ
  by_cases h8 : G8 (τ : ℂ) = 0
  · have h8' : G8 ((δ • τ : UpperHalfPlane) : ℂ) = 0 := (zero_iff (auto8 hT) hδ τ).2 h8
    simp [h8, h8']
  · have h8' : G8 ((δ • τ : UpperHalfPlane) : ℂ) ≠ 0 := fun h => h8 ((zero_iff (auto8 hT) hδ τ).1 h)
    rw [div_eq_div_iff (pow_ne_zero _ h8') (pow_ne_zero _ h8)]
    set X := G20 ((δ • τ : UpperHalfPlane) : ℂ)
    set Y := G8 ((δ • τ : UpperHalfPlane) : ℂ)
    set d := (((δ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ)
    set j := denom δ τ
    have hd20 : d ^ 20 ≠ 0 := pow_ne_zero _ hd
    apply mul_right_cancel₀ hd20
    linear_combination 3779136 * (X * d ^ 10 + j ^ 20 * G20 (τ : ℂ)) * G8 (τ : ℂ) ^ 5 * e1 -
      3779136 * G20 (τ : ℂ) ^ 2 * ((Y * d ^ 4) ^ 4 + (Y * d ^ 4) ^ 3 * (j ^ 8 * G8 (τ : ℂ)) +
        (Y * d ^ 4) ^ 2 * (j ^ 8 * G8 (τ : ℂ)) ^ 2 + (Y * d ^ 4) * (j ^ 8 * G8 (τ : ℂ)) ^ 3 +
        (j ^ 8 * G8 (τ : ℂ)) ^ 4) * e2

theorem jNumO_analytic : AnalyticOnNhd ℂ (fun z => PkgI1.jNum (PkgI1.Omega z)) U :=
  fun z hz => analyticAt_const.mul ((Pf_analytic _ hz).pow 2)

include hT hG hC in
/-- `jNum/jDen ∘ Ω → ∞` at `i√3`. -/
theorem pole_tau3 : Tendsto (fun z => PkgI1.jNum (PkgI1.Omega z) / PkgI1.jDen (PkgI1.Omega z))
    (𝓝[≠] (tau3 : ℂ)) (Bornology.cobounded ℂ) := by
  obtain ⟨he3, hb⟩ := tau3_facts hT hG
  obtain ⟨ha4, hatop⟩ := G20_tau3_le hT hG hC
  have h3U : (tau3 : ℂ) ∈ U := tau3.im_pos
  have hNan := jNumO_analytic _ h3U
  have hDan := jDenO_analytic _ h3U
  have hN : analyticOrderAt (fun z => PkgI1.jNum (PkgI1.Omega z)) (tau3 : ℂ) ≤ 8 := by
    have e : (fun z => PkgI1.jNum (PkgI1.Omega z)) = (fun _ => (3779136 : ℂ)) * Pf ^ 2 := by
      funext z; rfl
    rw [e, analyticOrderAt_mul analyticAt_const ((Pf_analytic _ h3U).pow 2),
      analyticOrderAt_eq_zero.2 (Or.inr (by norm_num)), zero_add,
      analyticOrderAt_pow (Pf_analytic _ h3U), ord_Pf_eq h3U, nsmul_eq_mul]
    change 2 * analyticOrderAt G20 (tau3 : ℂ) ≤ 8
    rw [← ENat.coe_toNat hatop]
    have : 2 * (analyticOrderAt G20 (tau3 : ℂ)).toNat ≤ 8 := by omega
    exact_mod_cast this
  have hD : 10 ≤ analyticOrderAt (fun z => PkgI1.jDen (PkgI1.Omega z)) (tau3 : ℂ) := by
    have e : (fun z => PkgI1.jDen (PkgI1.Omega z)) = Sf ^ 5 := by funext z; rfl
    rw [e, analyticOrderAt_pow (Sf_analytic _ h3U), ord_Sf_eq h3U, hb]
    norm_num
  exact tendsto_cobounded_of_meromorphicOrderAt_neg
    (mero_neg_aux hNan hDan hN hD (jDenO_order_ne_top h3U))

include hT hG hC in
theorem jth_continuous : Continuous jth := by
  rw [continuous_iff_continuousAt]
  intro τ₀
  set g : ℂ → ℂ := fun z => PkgI1.jNum (PkgI1.Omega z) / PkgI1.jDen (PkgI1.Omega z) with hg
  by_cases hD0 : PkgI1.jDen (PkgI1.Omega τ₀) = 0
  · have hval : jth τ₀ = OnePoint.infty := by simp [jth, hD0]
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hval]
    obtain ⟨γ, hγ, hγτ⟩ := G8_zero_orbit hT hG τ₀ ((jDen_zero_iff τ₀).1 hD0)
    have hpoleH : Tendsto (fun τ : UpperHalfPlane => g τ) (𝓝[≠] tau3) (Bornology.cobounded ℂ) :=
      (pole_tau3 hT hG hC).comp (le_of_eq (map_coe_punctured tau3))
    have hback : γ⁻¹ • τ₀ = tau3 := eqv_symm hγ hγτ
    have hmap : Tendsto (fun τ : UpperHalfPlane => γ⁻¹ • τ) (𝓝[≠] τ₀) (𝓝[≠] tau3) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have := (continuous_const_smul γ⁻¹).tendsto τ₀
        rw [hback] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with τ hτ
        intro h
        apply hτ
        simp only [Set.mem_singleton_iff] at h ⊢
        rw [← hγτ, ← h, smul_inv_smul]
    have hG : Tendsto (fun τ : UpperHalfPlane => g τ) (𝓝[≠] τ₀) (Bornology.cobounded ℂ) := by
      refine (hpoleH.comp hmap).congr (fun τ => ?_)
      simp only [Function.comp, hg]
      have := g_inv hT (gammaStar_inv hγ) τ
      exact this
    have hev : ∀ᶠ τ in 𝓝[≠] τ₀, jth τ = ((g τ : ℂ) : OnePoint ℂ) := by
      filter_upwards [eventually_jDen_ne_H τ₀] with τ hτ
      simp [jth, hτ, hg]
    have hcoe : Tendsto (fun z : ℂ => (z : OnePoint ℂ)) (Bornology.cobounded ℂ) (𝓝 OnePoint.infty) := by
      rw [Metric.cobounded_eq_cocompact, ← Filter.coclosedCompact_eq_cocompact]
      exact OnePoint.tendsto_coe_infty
    exact (hcoe.comp hG).congr' (hev.mono fun τ hτ => hτ.symm)
  · have hcont : ContinuousAt (fun τ : UpperHalfPlane => PkgI1.jDen (PkgI1.Omega τ)) τ₀ :=
      (jDenO_analytic _ τ₀.im_pos).continuousAt.comp UpperHalfPlane.continuous_coe.continuousAt
    have hev : jth =ᶠ[𝓝 τ₀] fun τ => ((g τ : ℂ) : OnePoint ℂ) := by
      filter_upwards [hcont.eventually_ne hD0] with τ hτ
      simp [jth, hτ, hg]
    refine ContinuousAt.congr ?_ hev.symm
    refine OnePoint.continuous_coe.continuousAt.comp ?_
    exact ((jNumO_analytic _ τ₀.im_pos).div (jDenO_analytic _ τ₀.im_pos) hD0).continuousAt.comp
      UpperHalfPlane.continuous_coe.continuousAt

include hT hG hC hD in
/-- **Row H-88 from the published valence formula and three glue Props.** -/
theorem qmHauptmodulBase3_of : QMHauptmodulBase3 := by
  refine ⟨jth, jth_continuous hT hG hC, fun τ hτ => by simp [jth, hτ], fun τ τ' => ?_,
    fun v => ?_, fun γ hγ τ hτ => ?_⟩
  · obtain ⟨b, hb⟩ := jth_fibre hT hG hC hD (jth τ)
    obtain ⟨γ₀, hγ₀, hγ₀b⟩ := (hb τ).1 rfl
    constructor
    · intro h
      obtain ⟨γ₁, hγ₁, hγ₁b⟩ := (hb τ').1 h.symm
      exact eqv_trans (gammaStar_inv hγ₀) hγ₁ (eqv_symm hγ₀ hγ₀b) hγ₁b
    · rintro ⟨γ, hγ, rfl⟩
      obtain ⟨δ, hδ, hδb⟩ := eqv_trans hγ₀ hγ hγ₀b rfl
      exact ((hb _).2 ⟨δ, hδ, hδb⟩).symm
  · obtain ⟨b, hb⟩ := jth_fibre hT hG hC hD v
    exact ⟨b, (hb b).2 ⟨1, HDec.LeafQCheck.VB.one_mem_gammaStar', one_smul _ _⟩⟩
  · obtain ⟨hD0, hv⟩ := hC γ hγ τ hτ
    simp only [jth, hD0, if_false, hv]

/-! ### `EllipticOrderDvd` proved (local expansion at an elliptic fixed point) -/

section EllDvd

open HDec.LeafQCheck.VB (zeta zeta_mul zeta_inj zeta_normSq gammaStar_mul one_mem_gammaStar')

/-- `cz + d` on `ℂ`. -/
def dC (γ : GL (Fin 2) ℝ) (z : ℂ) : ℂ :=
  ((γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * z + ((γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ)

/-- The Möbius map on `ℂ`. -/
def Mb (γ : GL (Fin 2) ℝ) (z : ℂ) : ℂ :=
  (((γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * z + ((γ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ)) / dC γ z

theorem dC_coe (γ : GL (Fin 2) ℝ) (z : UpperHalfPlane) : dC γ (z : ℂ) = denom γ z := by
  simp [dC, UpperHalfPlane.denom]

theorem Mb_coe {γ : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det) (z : UpperHalfPlane) :
    Mb γ (z : ℂ) = ((γ • z : UpperHalfPlane) : ℂ) := by
  have hd' : 0 < γ.det.val := by rwa [Matrix.GeneralLinearGroup.val_det_apply]
  rw [UpperHalfPlane.coe_smul_of_det_pos hd', Mb, dC_coe]
  simp [UpperHalfPlane.num]

theorem Mb_sub (γ : GL (Fin 2) ℝ) {z w : ℂ} (hz : dC γ z ≠ 0) (hw : dC γ w ≠ 0) :
    Mb γ z - Mb γ w = (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) * (z - w) / (dC γ z * dC γ w) := by
  rw [Mb, Mb, div_sub_div _ _ hz hw, Matrix.det_fin_two]
  congr 1
  simp only [dC]; push_cast; ring

/-- `det/((cz + d)(cP + d))`, the difference quotient of the Möbius map at `P`. -/
def Rq (γ : GL (Fin 2) ℝ) (P : UpperHalfPlane) (z : ℂ) : ℂ :=
  (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) / (dC γ z * denom γ P)

theorem Rq_P (γ : GL (Fin 2) ℝ) (P : UpperHalfPlane) : Rq γ P (P : ℂ) = zeta γ P := by
  rw [Rq, dC_coe, zeta, sq]

theorem dC_cont (γ : GL (Fin 2) ℝ) : Continuous (dC γ) := by unfold dC; fun_prop

theorem Rq_cont (γ : GL (Fin 2) ℝ) (P : UpperHalfPlane) : ContinuousAt (Rq γ P) (P : ℂ) := by
  unfold Rq
  apply ContinuousAt.div continuousAt_const ((dC_cont γ).continuousAt.mul continuousAt_const)
  show dC γ (P : ℂ) * denom γ P ≠ 0
  rw [dC_coe]; exact mul_ne_zero (denom_ne_zero γ P) (denom_ne_zero γ P)

theorem Mb_cont (γ : GL (Fin 2) ℝ) (P : UpperHalfPlane) : ContinuousAt (Mb γ) (P : ℂ) := by
  unfold Mb
  apply ContinuousAt.div (by fun_prop) (dC_cont γ).continuousAt
  rw [dC_coe]; exact denom_ne_zero γ P

/-- `Mb γ z − P = Rq(z)·(z − P)` near `P`, for `γ` fixing `P`. -/
theorem Mb_sub_P {γ : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det) {P : UpperHalfPlane}
    (hP : γ • P = P) {z : ℂ} (hz : dC γ z ≠ 0) : Mb γ z - (P : ℂ) = Rq γ P z * (z - P) := by
  have hP' : Mb γ (P : ℂ) = (P : ℂ) := by rw [Mb_coe hd, hP]
  have hdP : dC γ (P : ℂ) ≠ 0 := by rw [dC_coe]; exact denom_ne_zero γ P
  conv_lhs => rw [← hP']
  rw [Mb_sub γ hz hdP, Rq, dC_coe]
  field_simp [denom_ne_zero γ P]

theorem eq_at_of_punctured {f g : ℂ → ℂ} {P : ℂ} (hf : ContinuousAt f P) (hg : ContinuousAt g P)
    (h : f =ᶠ[𝓝[≠] P] g) : f P = g P :=
  tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)

/-- **The multiplier depends only on the Möbius map.** -/
theorem zeta_congr {γ γ' : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    (hd' : 0 < (γ' : Matrix (Fin 2) (Fin 2) ℝ).det) {P : UpperHalfPlane} (hP : γ • P = P)
    (hP' : γ' • P = P) (h : ∀ z : UpperHalfPlane, γ • z = γ' • z) : zeta γ P = zeta γ' P := by
  rw [← Rq_P, ← Rq_P]
  apply eq_at_of_punctured (Rq_cont γ P) (Rq_cont γ' P)
  have hU : ∀ᶠ z in 𝓝[≠] (P : ℂ), z ∈ U ∧ z ≠ (P : ℂ) ∧ dC γ z ≠ 0 ∧ dC γ' z ≠ 0 := by
    have h1 : ∀ᶠ z in 𝓝 (P : ℂ), z ∈ U := isOpen_U.mem_nhds P.im_pos
    have h2 : ∀ᶠ z in 𝓝 (P : ℂ), dC γ z ≠ 0 :=
      (dC_cont γ).continuousAt.eventually_ne (by rw [dC_coe]; exact denom_ne_zero γ P)
    have h3 : ∀ᶠ z in 𝓝 (P : ℂ), dC γ' z ≠ 0 :=
      (dC_cont γ').continuousAt.eventually_ne (by rw [dC_coe]; exact denom_ne_zero γ' P)
    filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, nhdsWithin_le_nhds h3,
      self_mem_nhdsWithin] with z a b c d
    exact ⟨a, d, b, c⟩
  filter_upwards [hU] with z ⟨hzU, hzP, h1, h2⟩
  have e1 := Mb_sub_P hd hP h1
  have e2 := Mb_sub_P hd' hP' h2
  have e3 : Mb γ z = Mb γ' z := by
    have k1 := Mb_coe hd ⟨z, hzU⟩
    have k2 := Mb_coe hd' ⟨z, hzU⟩
    have k3 := congrArg (fun w : UpperHalfPlane => (w : ℂ)) (h ⟨z, hzU⟩)
    exact k1.trans (k3.trans k2.symm)
  rw [e3, e2] at e1
  exact (mul_right_cancel₀ (sub_ne_zero.2 hzP) e1).symm

/-- **The multiplier is an `n`-th root of unity, `n = ord_P F₁`.** -/
theorem zeta_pow_ord {m : ℕ} {F₁ F₂ : ℂ → ℂ} (hF₁ : AnalyticOnNhd ℂ F₁ U) (hF₂ : AnalyticOnNhd ℂ F₂ U)
    (h₁ : Auto m F₁) (h₂ : Auto m F₂) {P : UpperHalfPlane} (hF₂P : F₂ (P : ℂ) ≠ 0) {n : ℕ}
    (hn : analyticOrderAt F₁ (P : ℂ) = n) {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γs) (hP : γ • P = P) :
    zeta γ P ^ n = 1 := by
  have hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det := by obtain ⟨_, _, _, hd⟩ := hγ; exact hd
  obtain ⟨g, hg, hg0, hfact⟩ := ((hF₁ _ P.im_pos).analyticOrderAt_eq_natCast).1 hn
  have hP' : Mb γ (P : ℂ) = (P : ℂ) := by rw [Mb_coe hd, hP]
  have hMt : Tendsto (Mb γ) (𝓝 (P : ℂ)) (𝓝 (P : ℂ)) := by
    have := (Mb_cont γ P).tendsto; rwa [hP'] at this
  -- the cross relation `F₁(γz) F₂(z) = F₁(z) F₂(γz)`
  have hcross : ∀ z : UpperHalfPlane, F₁ (Mb γ z) * F₂ z = F₁ z * F₂ (Mb γ z) := by
    intro z
    have e1 := h₁ γ hγ z
    have e2 := h₂ γ hγ z
    rw [← Mb_coe hd] at e1 e2
    have hdm := pow_ne_zero m (det_ne hγ)
    apply mul_right_cancel₀ hdm
    linear_combination F₂ (z : ℂ) * e1 - F₁ (z : ℂ) * e2
  have hev : ∀ᶠ z in 𝓝[≠] (P : ℂ),
      Rq γ P z ^ n * (g (Mb γ z) * F₂ z) = g z * F₂ (Mb γ z) := by
    have h1 : ∀ᶠ z in 𝓝 (P : ℂ), z ∈ U := isOpen_U.mem_nhds P.im_pos
    have h2 : ∀ᶠ z in 𝓝 (P : ℂ), dC γ z ≠ 0 :=
      (dC_cont γ).continuousAt.eventually_ne (by rw [dC_coe]; exact denom_ne_zero γ P)
    have h3 : ∀ᶠ z in 𝓝 (P : ℂ), F₁ (Mb γ z) = (Mb γ z - P) ^ n • g (Mb γ z) := hMt.eventually hfact
    filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, nhdsWithin_le_nhds h3,
      nhdsWithin_le_nhds hfact, self_mem_nhdsWithin] with z hzU hdz h3z hfz hzP
    have hc := hcross ⟨z, hzU⟩
    simp only at hc
    rw [h3z, hfz, Mb_sub_P hd hP hdz, smul_eq_mul, smul_eq_mul, mul_pow] at hc
    have hzP' : (z - P) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hzP)
    apply mul_left_cancel₀ hzP'
    linear_combination hc
  have hL : ContinuousAt (fun z => Rq γ P z ^ n * (g (Mb γ z) * F₂ z)) (P : ℂ) := by
    refine ((Rq_cont γ P).pow n).mul (ContinuousAt.mul ?_ (hF₂ _ P.im_pos).continuousAt)
    exact ContinuousAt.comp (by rw [hP']; exact hg.continuousAt) (Mb_cont γ P)
  have hR : ContinuousAt (fun z => g z * F₂ (Mb γ z)) (P : ℂ) := by
    refine hg.continuousAt.mul ?_
    exact ContinuousAt.comp (by rw [hP']; exact (hF₂ _ P.im_pos).continuousAt) (Mb_cont γ P)
  have heq := eq_at_of_punctured hL hR hev
  simp only [hP', Rq_P] at heq
  have hne : g (P : ℂ) * F₂ (P : ℂ) ≠ 0 := mul_ne_zero hg0 hF₂P
  have : (zeta γ P ^ n - 1) * (g (P : ℂ) * F₂ (P : ℂ)) = 0 := by linear_combination heq
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)

theorem zeta_one (P : UpperHalfPlane) : zeta 1 P = 1 := by
  simp [zeta, UpperHalfPlane.denom]

theorem zeta_ne_zero {γ : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    {P : UpperHalfPlane} (hP : γ • P = P) : zeta γ P ≠ 0 := by
  intro h; have := zeta_normSq hd hP; rw [h] at this; simp at this

/-- **`EllipticOrderDvd` is a theorem.** -/
theorem ellipticOrderDvd_proof : EllipticOrderDvd := by
  intro m F₁ F₂ hF₁ hF₂ h₁ h₂ P hF₂P htop
  set n := (analyticOrderAt F₁ (P : ℂ)).toNat
  have hn : analyticOrderAt F₁ (P : ℂ) = n := (ENat.coe_toNat htop).symm
  have hdet : ∀ γ ∈ Γs, 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det := fun γ ⟨_, _, _, hd⟩ => hd
  -- the multiplier group
  let H : Subgroup ℂˣ :=
    { carrier := {u | ∃ γ ∈ Γs, γ • P = P ∧ (u : ℂ) = zeta γ P}
      one_mem' := ⟨1, one_mem_gammaStar', one_smul _ _, by simp [zeta_one]⟩
      mul_mem' := by
        rintro u v ⟨γ, hγ, hP, hu⟩ ⟨γ', hγ', hP', hv⟩
        refine ⟨γ * γ', gammaStar_mul hγ hγ', by rw [mul_smul, hP', hP], ?_⟩
        rw [Units.val_mul, hu, hv, zeta_mul (hdet _ hγ) (hdet _ hγ') hP']
      inv_mem' := by
        rintro u ⟨γ, hγ, hP, hu⟩
        refine ⟨γ⁻¹, gammaStar_inv hγ, by rw [inv_smul_eq_iff, hP], ?_⟩
        have hm := zeta_mul (hdet _ (gammaStar_inv hγ)) (hdet _ hγ) hP
        rw [inv_mul_cancel, zeta_one] at hm
        have hz := zeta_ne_zero (hdet _ hγ) hP
        rw [Units.val_inv_eq_inv_val, hu]
        field_simp
        linear_combination hm }
  set S := {f : UpperHalfPlane → UpperHalfPlane //
    ∃ γ ∈ PkgI1.GammaStar, γ • P = P ∧ f = fun z => γ • z}
  -- `S ≃ H`
  let Ψ : S → H := fun f =>
    ⟨Units.mk0 (zeta (Classical.choose f.2) P)
      (zeta_ne_zero (hdet _ (Classical.choose_spec f.2).1) (Classical.choose_spec f.2).2.1),
      ⟨_, (Classical.choose_spec f.2).1, (Classical.choose_spec f.2).2.1, rfl⟩⟩
  have hΨ : Function.Bijective Ψ := by
    constructor
    · intro f f' hff
      have h := congrArg (fun u : H => ((u : ℂˣ) : ℂ)) hff
      simp only [Ψ, Units.val_mk0] at h
      obtain ⟨hγ, hP, hf⟩ := Classical.choose_spec f.2
      obtain ⟨hγ', hP', hf'⟩ := Classical.choose_spec f'.2
      apply Subtype.ext
      rw [hf, hf']
      funext z
      exact zeta_inj (hdet _ hγ) (hdet _ hγ') hP hP' h z
    · rintro ⟨u, γ, hγ, hP, hu⟩
      refine ⟨⟨fun z => γ • z, γ, hγ, hP, rfl⟩, ?_⟩
      apply Subtype.ext; apply Units.ext
      simp only [Ψ, Units.val_mk0]
      obtain ⟨hγ', hP', hf'⟩ := Classical.choose_spec
        (⟨fun z => γ • z, γ, hγ, hP, rfl⟩ : S).2
      rw [hu]
      exact zeta_congr (hdet _ hγ') (hdet _ hγ) hP' hP (fun z => (congrFun hf' z).symm)
  have hcard : Nat.card H = HDec.LeafQCheck.VB.ellOrder P :=
    (Nat.card_congr (Equiv.ofBijective Ψ hΨ)).symm
  obtain ⟨he0, -⟩ := HDec.LeafQCheck.VB.ellipticOrderLe6_proof P
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  rw [← hcard, ← IsCyclic.exponent_eq_card]
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  rintro ⟨u, γ, hγ, hP, hu⟩
  apply Subtype.ext; apply Units.ext
  simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one]
  rw [hu]
  exact zeta_pow_ord hF₁ hF₂ h₁ h₂ hF₂P hn hγ hP

end EllDvd

include hT hG hC in
/-- **Row H-88 with `EllipticOrderDvd` discharged**: from the valence formula (LEAF), the covolume glue and
the CM-value glue (and the bundle leaf `r4`). -/
theorem qmHauptmodulBase3_of' : QMHauptmodulBase3 :=
  qmHauptmodulBase3_of hT hG hC ellipticOrderDvd_proof

/-- **Row H-87 from the same leaf and glue** (the inequality clause of the valence formula; the chain-level
copy `HDec.LeafQCheck.VB.ValenceFormulaGammaStar` of leafq-check's row). -/
theorem valenceFormulaGammaStar_of_eq (hV : ValenceFormulaCocompactEq) (hA : GammaStarCocompactArea) :
    HDec.LeafQCheck.VB.ValenceFormulaGammaStar := by
  intro m F hF hne haut T hT
  obtain ⟨hFuchs, s, hs, hvol⟩ := hA
  have := (hV Γs hFuchs s hs m F hF hne haut).2.2 T hT
  rwa [hvol, arith] at this


/-! ### The covolume glue split: Shimizu's formula for `𝒪¹` (LEAF) and the passage to `Γ*` (GLUE) -/

/-- `Γ¹ = ι(𝒪¹)`: the images of the norm-one units of `𝒪` (`det ι(x) = nrd(x)`). -/
def Gamma1 : Set (GL (Fin 2) ℝ) :=
  {γ | ∃ x : PkgI1.B, PkgI1.InO x ∧ (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x ∧
    (γ : Matrix (Fin 2) (Fin 2) ℝ).det = 1}

/-- **LEAF (Shimura; Shimizu's volume formula).** `Γ¹ = ι(𝒪¹)`, for the maximal order `𝒪` of the indefinite
division algebra `B` of discriminant `6`, is a cocompact Fuchsian group, with a fundamental domain of
hyperbolic area `(π/3) ∏_{p | 6} (p − 1) = 2π/3`. Shimura, *Introduction to the arithmetic theory of
automorphic functions*, 1971, Prop. 9.2 (cocompactness); H. Shimizu, *On zeta functions of quaternion
algebras*, Ann. of Math. 81 (1965) (volume); Vignéras, *Arithmétique des algèbres de quaternions*, LNM 800,
IV §1; Voight, *Quaternion algebras*, Thm 39.1.13; locators UNVERIFIED. -/
def ShimizuCovolumeO1 : Prop :=
  IsCocompactFuchsian Gamma1 ∧
    ∃ s, IsFundDomain Gamma1 s ∧ MeasureTheory.volume s = ENNReal.ofReal (2 * Real.pi / 3)

/-- **GLUE (from `𝒪¹` to `Γ*`).** Shimizu's statement for `Γ¹` gives `GammaStarCocompactArea`. What it needs:
`Γ¹ ⊆ Γ*`, the index `[Γ* : ℚ^×Γ¹] = 4` of the Möbius groups (`N_B(𝒪)⁺/ℚ^×𝒪^×₊ ≅ W`, representatives
`1, x₄, x₆, x₄x₆` up to `𝒪¹`; `GammaStarGen` and the chain's `tt` representatives), proper discontinuity and
cocompactness of a finite-index supergroup, and the comparison of fundamental domains (area divided by the
index). Project glue (measure theory and an index computation). -/
def GammaStarFromO1 : Prop := ShimizuCovolumeO1 → GammaStarCocompactArea

/-! ### `GammaStarFromO1` bypassed for H-87: the valence formula for `Γ¹` and an index argument

For `z` and the four coset representatives `g_i = ι(1), ι(a4), ι(a6), ι(a4 a6)` of `Γ¹` in `Γ*` (reduced norms
`1, 2, 3, 6`, pairwise in distinct cosets), the points `g_i z` fall into `r_z` classes of `Γ¹`-equivalence with
`4 e¹_z ≤ r_z e*_z`; the valence bound for `Γ¹` (Shimizu: total `m/3`) over these points gives
`4 Σ ord/e* ≤ m/3`. -/

section Index

open HDec.LeafQCheck.VB (gammaStar_mul one_mem_gammaStar')

theorem inO_ofInt (x : PkgI1.B) : PkgI1.InO x ↔ ∃ n : Fin 4 → ℤ, x = LeafQM.ofInt n := by
  rw [inO_iff]
  constructor
  · rintro ⟨n0, n1, n2, n3, rfl⟩
    exact ⟨![n0, n1, n2, n3], by ext <;> simp [LeafQM.ofInt]⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n 0, n 1, n 2, n 3, by ext <;> simp [LeafQM.ofInt]⟩

theorem inO_mul {x y : PkgI1.B} (hx : PkgI1.InO x) (hy : PkgI1.InO y) : PkgI1.InO (x * y) := by
  obtain ⟨n, rfl⟩ := (inO_ofInt x).1 hx
  obtain ⟨m, rfl⟩ := (inO_ofInt y).1 hy
  exact (inO_ofInt _).2 ⟨_, LeafQM.ofInt_mul n m⟩

theorem inO_one : PkgI1.InO (1 : PkgI1.B) :=
  (inO_ofInt _).2 ⟨![1, 0, 0, 0], by ext <;> simp [LeafQM.ofInt]⟩

theorem inO_star {x : PkgI1.B} (hx : PkgI1.InO x) : PkgI1.InO (star x) := by
  obtain ⟨n, rfl⟩ := (inO_ofInt x).1 hx
  exact (inO_ofInt _).2 ⟨![n 0 + n 2, -n 1, -n 2, -n 3], by ext <;> simp [LeafQM.ofInt] <;> ring⟩

theorem mul_star_nrd (x : PkgI1.B) : x * star x = ((nrd x : ℚ) : PkgI1.B) := by
  rw [QuaternionAlgebra.mul_star_eq_coe]; congr 1; simp [nrd]; ring

theorem star_mul_nrd (x : PkgI1.B) : star x * x = ((nrd x : ℚ) : PkgI1.B) := by
  rw [QuaternionAlgebra.star_mul_eq_coe]; congr 1; simp [nrd]; ring

/-- `Γ¹` as a subgroup of `GL₂(ℝ)`. -/
def G1 : Subgroup (GL (Fin 2) ℝ) where
  carrier := Gamma1
  one_mem' := ⟨1, inO_one, by rw [iota_one]; rfl, by simp⟩
  mul_mem' := by
    rintro a b ⟨x, hx, hax, hda⟩ ⟨y, hy, hby, hdb⟩
    exact ⟨x * y, inO_mul hx hy, by rw [Units.val_mul, hax, hby, iota_mul],
      by rw [Units.val_mul, Matrix.det_mul, hda, hdb, one_mul]⟩
  inv_mem' := by
    rintro a ⟨x, hx, hax, hda⟩
    have hn : nrd x = 1 := by
      have := hda; rw [hax, det_iota_eq] at this; exact_mod_cast this
    refine ⟨star x, inO_star hx, ?_, ?_⟩
    · have h1 : (a : Matrix (Fin 2) (Fin 2) ℝ) * PkgI1.iota (star x) = 1 := by
        rw [hax, ← iota_mul, mul_star_nrd, hn]; simpa using iota_one
      have := congrArg (fun M => (((a⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) * M) h1
      simp only [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul, mul_one] at this
      exact this.symm
    · rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.det_nonsing_inv, hda, Ring.inverse_one]

/-- `Γ*` as a subgroup of `GL₂(ℝ)`. -/
def Gs : Subgroup (GL (Fin 2) ℝ) where
  carrier := Γs
  one_mem' := one_mem_gammaStar'
  mul_mem' := fun ha hb => gammaStar_mul ha hb
  inv_mem' := fun ha => gammaStar_inv ha

theorem G1_le : G1 ≤ Gs := by
  rintro a ⟨x, hx, hax, hda⟩
  have hn : nrd x = 1 := by
    have := hda; rw [hax, det_iota_eq] at this; exact_mod_cast this
  refine ⟨x, ⟨star x, by rw [mul_star_nrd, hn]; simp, by rw [star_mul_nrd, hn]; simp,
    fun z hz => ⟨inO_mul (inO_mul hx hz) (inO_star hx), inO_mul (inO_mul (inO_star hx) hz) hx⟩⟩,
    hax, by rw [hda]; norm_num⟩

theorem G1_normal {γ h : GL (Fin 2) ℝ} (hγ : γ ∈ Gs) (hh : h ∈ G1) : γ * h * γ⁻¹ ∈ G1 := by
  obtain ⟨x, ⟨y, hxy, hyx, hN⟩, hγx, hd⟩ := hγ
  obtain ⟨w, hw, hhw, hdw⟩ := hh
  have hinv : ((γ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota y := by
    have h1 : (γ : Matrix (Fin 2) (Fin 2) ℝ) * PkgI1.iota y = 1 := by
      rw [hγx, ← iota_mul, hxy, iota_one]
    have := congrArg (fun M => (((γ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) * M) h1
    simp only [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul, mul_one] at this
    exact this.symm
  refine ⟨x * w * y, (hN w hw).1, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, hγx, hhw, hinv, iota_mul, iota_mul]
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdw, mul_one, ← Matrix.det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

/-- The Möbius action as permutations. -/
abbrev mob : GL (Fin 2) ℝ →* Equiv.Perm UpperHalfPlane := MulAction.toPermHom _ _

def Mstar : Subgroup (Equiv.Perm UpperHalfPlane) := Gs.map mob
def Mone : Subgroup (Equiv.Perm UpperHalfPlane) := G1.map mob

theorem Mone_normal {σ τ : Equiv.Perm UpperHalfPlane} (hσ : σ ∈ Mstar) (hτ : τ ∈ Mone) :
    σ * τ * σ⁻¹ ∈ Mone := by
  obtain ⟨γ, hγ, rfl⟩ := hσ
  obtain ⟨h, hh, rfl⟩ := hτ
  exact ⟨γ * h * γ⁻¹, G1_normal hγ hh, by simp [map_mul, map_inv]⟩

/-- Stabilizers. -/
def Sstar (z : UpperHalfPlane) : Subgroup (Equiv.Perm UpperHalfPlane) :=
  Mstar ⊓ MulAction.stabilizer (Equiv.Perm UpperHalfPlane) z
def Sone (z : UpperHalfPlane) : Subgroup (Equiv.Perm UpperHalfPlane) :=
  Mone ⊓ MulAction.stabilizer (Equiv.Perm UpperHalfPlane) z

theorem card_Sstar (z : UpperHalfPlane) : Nat.card (Sstar z) = HDec.LeafQCheck.VB.ellOrder z := by
  unfold HDec.LeafQCheck.VB.ellOrder
  refine Nat.card_congr (Equiv.ofBijective (fun σ => ⟨⇑(σ : Equiv.Perm UpperHalfPlane), ?_⟩) ⟨?_, ?_⟩)
  · obtain ⟨⟨γ, hγ, hσ⟩, hz⟩ := σ.2
    refine ⟨γ, hγ, ?_, ?_⟩
    · have : (σ : Equiv.Perm UpperHalfPlane) z = z := hz
      rw [← hσ] at this; exact this
    · rw [← hσ]; rfl
  · intro σ τ h
    apply Subtype.ext; apply Equiv.ext; intro w
    exact congrFun (congrArg Subtype.val h) w
  · rintro ⟨f, γ, hγ, hz, rfl⟩
    exact ⟨⟨mob γ, ⟨γ, hγ, rfl⟩, hz⟩, rfl⟩

theorem card_Sone (z : UpperHalfPlane) : Nat.card (Sone z) = ellOrderOf Gamma1 z := by
  unfold ellOrderOf
  refine Nat.card_congr (Equiv.ofBijective (fun σ => ⟨⇑(σ : Equiv.Perm UpperHalfPlane), ?_⟩) ⟨?_, ?_⟩)
  · obtain ⟨⟨γ, hγ, hσ⟩, hz⟩ := σ.2
    refine ⟨γ, hγ, ?_, ?_⟩
    · have : (σ : Equiv.Perm UpperHalfPlane) z = z := hz
      rw [← hσ] at this; exact this
    · rw [← hσ]; rfl
  · intro σ τ h
    apply Subtype.ext; apply Equiv.ext; intro w
    exact congrFun (congrArg Subtype.val h) w
  · rintro ⟨f, γ, hγ, hz, rfl⟩
    exact ⟨⟨mob γ, ⟨γ, hγ, rfl⟩, hz⟩, rfl⟩

theorem Sone_le (z : UpperHalfPlane) : Sone z ≤ Sstar z :=
  inf_le_inf_right _ (Subgroup.map_mono G1_le)

/-- `e¹` is constant along `Γ*`-orbits (`Γ¹` is normal in `Γ*`). -/
theorem card_Sone_smul {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Gs) (z : UpperHalfPlane) :
    Nat.card (Sone (γ • z)) = Nat.card (Sone z) := by
  have hσ : mob γ ∈ Mstar := ⟨γ, hγ, rfl⟩
  have hσi : (mob γ)⁻¹ ∈ Mstar := Mstar.inv_mem hσ
  refine Nat.card_congr ⟨fun τ => ⟨(mob γ)⁻¹ * τ * mob γ, ?_, ?_⟩,
    fun τ => ⟨mob γ * τ * (mob γ)⁻¹, ?_, ?_⟩, ?_, ?_⟩
  · have := Mone_normal hσi τ.2.1; rwa [inv_inv] at this
  · change ((mob γ)⁻¹ * τ * mob γ) z = z
    have hτ : (τ : Equiv.Perm UpperHalfPlane) (γ • z) = γ • z := τ.2.2
    simp only [Equiv.Perm.coe_mul, Function.comp]
    change (mob γ)⁻¹ ((τ : Equiv.Perm UpperHalfPlane) (γ • z)) = z
    rw [hτ]; simp
  · exact Mone_normal hσ τ.2.1
  · change (mob γ * τ * (mob γ)⁻¹) (γ • z) = γ • z
    have hτ : (τ : Equiv.Perm UpperHalfPlane) z = z := τ.2.2
    simp only [Equiv.Perm.coe_mul, Function.comp]
    have e : (mob γ)⁻¹ (γ • z) = z := by simp
    rw [e, hτ]; rfl
  · intro τ; apply Subtype.ext; simp [mul_assoc]
  · intro τ; apply Subtype.ext; simp [mul_assoc]

/-- The four coset representatives `1, a4, a6, a4 a6` (reduced norms `1, 2, 3, 6`) and their inverses. -/
def rep4 : Fin 4 → PkgI1.B := ![1, a4, a6, a4 * a6]
def rep4i : Fin 4 → PkgI1.B := ![1, a4i, a6i, a6i * a4i]

theorem nd_rep (i : Fin 4) : NormData (rep4 i) (rep4i i) := by
  fin_cases i
  · exact NormData.one
  · exact nd_a4
  · exact nd_a6
  · exact nd_a4.mul nd_a6

def g4 (i : Fin 4) : GL (Fin 2) ℝ := glOf (rep4 i) (nd_rep i).2.2.2.ne'

theorem g4_mem (i : Fin 4) : g4 i ∈ Gs := glOf_mem (nd_rep i)

theorem nrd_rep (i : Fin 4) : nrd (rep4 i) = ((![1, 2, 3, 6] : Fin 4 → ℤ) i : ℚ) := by
  fin_cases i <;> simp [rep4, nrd_mul, nrd, a4, a6] <;> norm_num

theorem g4_inv_coe (i : Fin 4) :
    (((g4 i)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota (rep4i i) := by
  have h1 : ((g4 i : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * PkgI1.iota (rep4i i) = 1 := by
    rw [g4, coe_glOf, ← iota_mul, (nd_rep i).1, iota_one]
  have := congrArg (fun M => ((((g4 i)⁻¹ : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) * M) h1
  simp only [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul, mul_one] at this
  exact this.symm

/-- A matrix of positive determinant acting trivially on `ℍ` is scalar. -/
theorem scalar_of_trivial {γ : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    (h : ∀ z : UpperHalfPlane, γ • z = z) :
    (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
  have hd' : 0 < γ.det.val := by rwa [Matrix.GeneralLinearGroup.val_det_apply]
  have key : ∀ z : UpperHalfPlane,
      ((γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * z + ((γ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) =
        (z : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * z + ((γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ)) := by
    intro z
    have e : ((γ • z : UpperHalfPlane) : ℂ) = (z : ℂ) := congrArg (fun w : UpperHalfPlane => (w : ℂ)) (h z)
    rw [UpperHalfPlane.coe_smul_of_det_pos hd', div_eq_iff (denom_ne_zero γ z)] at e
    simpa [UpperHalfPlane.num, UpperHalfPlane.denom, mul_comm] using e
  have k1 := key UpperHalfPlane.I
  have k2 := key ⟨2 * Complex.I, by simp⟩
  simp only [UpperHalfPlane.coe_I] at k1
  simp only [UpperHalfPlane.coe_mk] at k2
  have r1 := congrArg Complex.re k1; have i1 := congrArg Complex.im k1
  have r2 := congrArg Complex.re k2
  simp at r1 i1 r2
  refine ⟨by linarith, by linarith, by linarith⟩

theorem rat_of_scalar {u : PkgI1.B} (h10 : PkgI1.iota u 1 0 = 0) (h01 : PkgI1.iota u 0 1 = 0)
    (h00 : PkgI1.iota u 0 0 = PkgI1.iota u 1 1) : u.imI = 0 ∧ u.imJ = 0 ∧ u.imK = 0 := by
  rw [iota_apply] at h10 h01 h00
  simp at h10 h01 h00
  have hs : (0 : ℝ) < √2 := Real.sqrt_pos.2 (by norm_num)
  have hK : (u.imK : ℝ) = 0 := by
    have : (u.imK : ℝ) * √2 = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hs.ne'
  have hJ : (u.imJ : ℝ) = 0 := by rw [hK] at h10; linarith
  have hI : (u.imI : ℝ) = 0 := by
    have : (u.imI : ℝ) * √2 = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hs.ne'
  exact ⟨by exact_mod_cast hI, by exact_mod_cast hJ, by exact_mod_cast hK⟩

theorem not_sq_q (q : ℚ) (c : ℤ) (hc : ¬ IsSquare c) (h : q * q = c) : False := by
  have h1 : IsSquare (c : ℚ) := ⟨q, by rw [← h]⟩
  rw [Rat.isSquare_iff] at h1
  simp at h1
  exact hc h1

/-- **The four representatives lie in distinct cosets of `Γ¹`** (norms `1, 2, 3, 6` are distinct modulo
squares). -/
theorem coset_distinct {i j : Fin 4} (hij : i ≠ j) : (mob (g4 i))⁻¹ * mob (g4 j) ∉ Mone := by
  rintro ⟨h, ⟨w, hw, hhw, hdw⟩, hmob⟩
  set γ := (g4 i)⁻¹ * g4 j * h⁻¹ with hγ
  have hone : mob γ = 1 := by
    rw [hγ, map_mul, map_mul, map_inv, map_inv, hmob]; group
  have htriv : ∀ z : UpperHalfPlane, γ • z = z := fun z => by
    have := congrArg (fun σ : Equiv.Perm UpperHalfPlane => σ z) hone
    simpa using this
  have hn : nrd w = 1 := by
    have := hdw; rw [hhw, det_iota_eq] at this; exact_mod_cast this
  have hhinv : ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota (star w) := by
    have h1 : ((h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * PkgI1.iota (star w) = 1 := by
      rw [hhw, ← iota_mul, mul_star_nrd, hn]; simpa using iota_one
    have := congrArg (fun M => (((h⁻¹ : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) * M) h1
    simp only [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul, mul_one] at this
    exact this.symm
  set u := rep4i i * rep4 j * star w with hu
  have hγu : (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota u := by
    rw [hγ, Units.val_mul, Units.val_mul, g4_inv_coe, hhinv, g4, coe_glOf, hu, iota_mul, iota_mul]
  have hdγ : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [hγu, det_iota_eq, hu, nrd_mul, nrd_mul]
    have h1 := (nd_rep j).2.2.2
    have h2 := (nd_rep i)
    have hni : nrd (rep4i i) * nrd (rep4 i) = 1 := by rw [← nrd_mul, h2.2.1]; simp [nrd]
    have hpos : 0 < nrd (rep4i i) := by
      by_contra hneg; push Not at hneg; nlinarith [h2.2.2.2]
    have hs : nrd (star w) = 1 := by simp [nrd] at hn ⊢; linarith
    rw [hs]; exact_mod_cast mul_pos (mul_pos hpos h1) one_pos
  obtain ⟨s10, s01, s00⟩ := scalar_of_trivial hdγ htriv
  rw [hγu] at s10 s01 s00
  obtain ⟨hI, hJ, hK⟩ := rat_of_scalar s10 s01 s00
  -- `nrd u = u.re²`
  have hnu : nrd u = u.re * u.re := by simp [nrd, hI, hJ, hK]; ring
  have hni : nrd (rep4i i) * nrd (rep4 i) = 1 := by rw [← nrd_mul, (nd_rep i).2.1]; simp [nrd]
  have hs : nrd (star w) = 1 := by simp [nrd] at hn ⊢; linarith
  have hprod : nrd (rep4 i) * nrd (rep4 j) = (u.re * nrd (rep4 i)) * (u.re * nrd (rep4 i)) := by
    have : nrd u = nrd (rep4i i) * nrd (rep4 j) := by rw [hu, nrd_mul, nrd_mul, hs, mul_one]
    rw [hnu] at this
    have e : nrd (rep4 j) = nrd (rep4 i) * (nrd (rep4i i) * nrd (rep4 j)) := by
      rw [← mul_assoc, mul_comm (nrd (rep4 i)), hni, one_mul]
    rw [e, ← this]; ring
  rw [nrd_rep i, nrd_rep j] at hprod
  have hsq : ∀ a b : Fin 4, a ≠ b →
      ¬ IsSquare ((![1, 2, 3, 6] : Fin 4 → ℤ) a * (![1, 2, 3, 6] : Fin 4 → ℤ) b) := by decide +kernel
  exact not_sq_q (u.re * ((![1, 2, 3, 6] : Fin 4 → ℤ) i : ℚ)) _ (hsq i j hij)
    (by push_cast; linarith)

/-- `Γ¹`-equivalence. -/
def Eq1 (a b : UpperHalfPlane) : Prop := ∃ h ∈ G1, h • a = b

theorem mob_apply (γ : GL (Fin 2) ℝ) (w : UpperHalfPlane) : mob γ w = γ • w := rfl

theorem finite_Sstar (z : UpperHalfPlane) : Finite (Sstar z) := by
  obtain ⟨h0, -⟩ := HDec.LeafQCheck.VB.ellipticOrderLe6_proof z
  exact Nat.finite_of_card_ne_zero (by rw [card_Sstar]; omega)

/-- **The class bound**: the representatives `i` with `g_i z` `Γ¹`-equivalent to `g_{i₀} z` inject into
`Stab*(z)/Stab¹(z)`. -/
theorem class_bound (z : UpperHalfPlane) (i₀ : Fin 4) :
    (Finset.univ.filter (fun i => Eq1 (g4 i • z) (g4 i₀ • z))).card * Nat.card (Sone z) ≤
      Nat.card (Sstar z) := by
  classical
  haveI := finite_Sstar z
  set C := Finset.univ.filter (fun i => Eq1 (g4 i • z) (g4 i₀ • z)) with hC
  have hmem : ∀ i ∈ C, ∃ h ∈ G1, h • (g4 i • z) = g4 i₀ • z := fun i hi => (Finset.mem_filter.1 hi).2
  choose hh hhG hhz using hmem
  let σ : C → Sstar z := fun i =>
    ⟨(mob (g4 i₀))⁻¹ * mob (hh i.1 i.2) * mob (g4 i.1),
      Mstar.mul_mem (Mstar.mul_mem (Mstar.inv_mem ⟨_, g4_mem i₀, rfl⟩) ⟨_, G1_le (hhG i.1 i.2), rfl⟩)
        ⟨_, g4_mem i.1, rfl⟩, by
        change ((mob (g4 i₀))⁻¹ * mob (hh i.1 i.2) * mob (g4 i.1)) z = z
        simp only [Equiv.Perm.coe_mul, Function.comp, mob_apply]
        rw [hhz i.1 i.2]
        simp⟩
  let q : Sstar z → Sstar z ⧸ (Sone z).subgroupOf (Sstar z) := QuotientGroup.mk
  have hinj : Function.Injective (q ∘ σ) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simp only [Function.comp, q] at hij
    rw [QuotientGroup.eq] at hij
    have hk : ((σ ⟨i, hi⟩)⁻¹ * σ ⟨j, hj⟩ : Sstar z).1 ∈ Mone := (Subgroup.mem_subgroupOf.1 hij).1
    simp only [σ, Subgroup.coe_mul, Subgroup.coe_inv] at hk
    set k := (mob (hh i hi))⁻¹ * mob (hh j hj)
    have hkM : k ∈ Mone := Mone.mul_mem (Mone.inv_mem ⟨_, hhG i hi, rfl⟩) ⟨_, hhG j hj, rfl⟩
    have e1 : ((mob (g4 i₀))⁻¹ * mob (hh i hi) * mob (g4 i))⁻¹ *
        ((mob (g4 i₀))⁻¹ * mob (hh j hj) * mob (g4 j)) = (mob (g4 i))⁻¹ * k * mob (g4 j) := by
      simp only [k]; group
    rw [e1] at hk
    have hi' : (mob (g4 i))⁻¹ ∈ Mstar := Mstar.inv_mem ⟨_, g4_mem i, rfl⟩
    have h2 := Mone_normal hi' (Mone.inv_mem hkM)
    have e2 : (mob (g4 i))⁻¹ * mob (g4 j) =
        ((mob (g4 i))⁻¹ * k⁻¹ * (mob (g4 i))⁻¹⁻¹) * ((mob (g4 i))⁻¹ * k * mob (g4 j)) := by group
    have h3 : (mob (g4 i))⁻¹ * mob (g4 j) ∈ Mone := by rw [e2]; exact Mone.mul_mem h2 hk
    by_contra hne
    exact coset_distinct (fun h => hne (Subtype.ext h)) h3
  have hc1 : C.card ≤ Nat.card (Sstar z ⧸ (Sone z).subgroupOf (Sstar z)) := by
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  have hL := Subgroup.card_mul_index ((Sone z).subgroupOf (Sstar z))
  have hS : Nat.card ((Sone z).subgroupOf (Sstar z)) = Nat.card (Sone z) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Sone_le z)).toEquiv
  rw [hS] at hL
  rw [← hL, Subgroup.index, mul_comm (Nat.card (Sone z))]
  exact Nat.mul_le_mul_right _ hc1

/-! #### Orders along orbits -/

theorem eq_at_of_punctured_real {f g : ℂ → ℝ} {P : ℂ} (hf : ContinuousAt f P) (hg : ContinuousAt g P)
    (h : f =ᶠ[𝓝[≠] P] g) : f P = g P :=
  tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)

/-- Orders agree when the moduli differ by a continuous positive factor. -/
theorem ord_eq_of_norm {F G : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F z) (hG : AnalyticAt ℂ G z)
    {c : ℂ → ℝ} (hc : ContinuousAt c z) (hc0 : 0 < c z) (h : ∀ᶠ w in 𝓝 z, ‖G w‖ = c w * ‖F w‖) :
    analyticOrderAt G z = analyticOrderAt F z := by
  have hcpos : ∀ᶠ w in 𝓝 z, 0 < c w := hc.eventually (lt_mem_nhds hc0)
  by_cases hFt : analyticOrderAt F z = ⊤
  · rw [hFt, analyticOrderAt_eq_top]
    rw [analyticOrderAt_eq_top] at hFt
    filter_upwards [hFt, h] with w h1 h2
    rw [h1, norm_zero, mul_zero] at h2
    exact norm_eq_zero.1 h2
  by_cases hGt : analyticOrderAt G z = ⊤
  · exfalso; apply hFt
    rw [analyticOrderAt_eq_top] at hGt ⊢
    filter_upwards [hGt, h, hcpos] with w h1 h2 h3
    rw [h1, norm_zero] at h2
    have := (mul_eq_zero.1 h2.symm).resolve_left h3.ne'
    exact norm_eq_zero.1 this
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 hFt
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 hGt
  rw [← ha, ← hb]
  obtain ⟨f, hf, hf0, hfF⟩ := hF.analyticOrderAt_eq_natCast.1 hb.symm
  obtain ⟨g, hg, hg0, hgG⟩ := hG.analyticOrderAt_eq_natCast.1 ha.symm
  have key : ∀ᶠ w in 𝓝 z, ‖w - z‖ ^ a * ‖g w‖ = c w * (‖w - z‖ ^ b * ‖f w‖) := by
    filter_upwards [h, hfF, hgG] with w h1 h2 h3
    rw [h3, h2, norm_smul, norm_smul, norm_pow, norm_pow] at h1
    exact h1
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso
    have hev : (fun w => ‖g w‖) =ᶠ[𝓝[≠] z] (fun w => c w * (‖w - z‖ ^ (b - a) * ‖f w‖)) := by
      filter_upwards [nhdsWithin_le_nhds key, self_mem_nhdsWithin] with w h1 h2
      have hw : 0 < ‖w - z‖ ^ a := pow_pos (norm_pos_iff.2 (sub_ne_zero.2 h2)) a
      have e : ‖w - z‖ ^ b = ‖w - z‖ ^ a * ‖w - z‖ ^ (b - a) := by
        rw [← pow_add]; congr 1; omega
      rw [e] at h1
      apply mul_left_cancel₀ hw.ne'
      linear_combination h1
    have := eq_at_of_punctured_real (hg.continuousAt.norm)
      (hc.mul ((((continuous_id.sub continuous_const).norm.pow _).continuousAt).mul hf.continuousAt.norm)) hev
    have this' : ‖g z‖ = c z * (‖z - z‖ ^ (b - a) * ‖f z‖) := this
    rw [sub_self, norm_zero, zero_pow (by omega), zero_mul, mul_zero] at this'
    have this := this'
    exact hg0 (norm_eq_zero.1 this)
  · rw [hab]
  · exfalso
    have hev : (fun w => ‖w - z‖ ^ (a - b) * ‖g w‖) =ᶠ[𝓝[≠] z] (fun w => c w * ‖f w‖) := by
      filter_upwards [nhdsWithin_le_nhds key, self_mem_nhdsWithin] with w h1 h2
      have hw : 0 < ‖w - z‖ ^ b := pow_pos (norm_pos_iff.2 (sub_ne_zero.2 h2)) b
      have e : ‖w - z‖ ^ a = ‖w - z‖ ^ b * ‖w - z‖ ^ (a - b) := by
        rw [← pow_add]; congr 1; omega
      rw [e] at h1
      apply mul_left_cancel₀ hw.ne'
      linear_combination h1
    have := eq_at_of_punctured_real
      ((((continuous_id.sub continuous_const).norm.pow _).continuousAt).mul hg.continuousAt.norm)
      (hc.mul hf.continuousAt.norm) hev
    have this' : ‖z - z‖ ^ (a - b) * ‖g z‖ = c z * ‖f z‖ := this
    rw [sub_self, norm_zero, zero_pow (by omega), zero_mul] at this'
    have this := this'
    have := (mul_eq_zero.1 this.symm).resolve_left hc0.ne'
    exact hf0 (norm_eq_zero.1 this)

theorem Mb_analytic (γ : GL (Fin 2) ℝ) (z : UpperHalfPlane) : AnalyticAt ℂ (Mb γ) (z : ℂ) := by
  unfold Mb
  apply AnalyticAt.div (by fun_prop) (by unfold dC; fun_prop)
  rw [dC_coe]; exact denom_ne_zero γ z

theorem ord_comp_Mb {F : ℂ → ℂ} {γ : GL (Fin 2) ℝ} (z : UpperHalfPlane)
    (hF : AnalyticAt ℂ F (Mb γ z)) :
    analyticOrderAt (fun w => F (Mb γ w)) (z : ℂ) = analyticOrderAt F (Mb γ z) := by
  have hMb := Mb_analytic γ z
  have hcomp : AnalyticAt ℂ (fun w => F (Mb γ w)) z := hF.comp hMb
  have hdz : dC γ z ≠ 0 := by rw [dC_coe]; exact denom_ne_zero γ z
  have hMt : Tendsto (Mb γ) (𝓝 (z : ℂ)) (𝓝 (Mb γ z)) := hMb.continuousAt.tendsto
  by_cases ht : analyticOrderAt F (Mb γ z) = ⊤
  · rw [ht, analyticOrderAt_eq_top]
    rw [analyticOrderAt_eq_top] at ht
    exact hMt.eventually ht
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 ht
    rw [← hn]
    obtain ⟨f, hf, hf0, hfF⟩ := hF.analyticOrderAt_eq_natCast.1 hn.symm
    rw [hcomp.analyticOrderAt_eq_natCast]
    have hdet : (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast γ.isUnit.map (Matrix.detMonoidHom) |>.ne_zero
    refine ⟨fun w => ((((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) / (dC γ w * dC γ z)) ^ n *
      f (Mb γ w), ?_, ?_, ?_⟩
    · exact ((analyticAt_const.div ((by unfold dC; fun_prop : AnalyticAt ℂ (dC γ) (z : ℂ)).mul
        analyticAt_const) (mul_ne_zero hdz hdz)).pow n).mul (hf.comp hMb)
    · exact mul_ne_zero (pow_ne_zero _ (div_ne_zero hdet (mul_ne_zero hdz hdz))) hf0
    · filter_upwards [hMt.eventually hfF, (dC_cont γ).continuousAt.eventually_ne hdz] with w h1 h2
      rw [h1, Mb_sub γ h2 hdz, smul_eq_mul, smul_eq_mul,
        show (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) * (w - (z : ℂ)) / (dC γ w * dC γ (z : ℂ)) =
          (w - (z : ℂ)) * ((((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) / (dC γ w * dC γ (z : ℂ))) by ring,
        mul_pow]
      ring

/-- **Orders are constant along `Γ*`-orbits** (from the automorphy in absolute value). -/
theorem ord_smul_eq {m : ℕ} {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U)
    (haut : ∀ γ ∈ Γs, ∀ w : UpperHalfPlane,
      ‖F ((γ • w : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖denom γ w‖ ^ (2 * m) * ‖F (w : ℂ)‖) {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γs) (z : UpperHalfPlane) :
    analyticOrderAt F ((γ • z : UpperHalfPlane) : ℂ) = analyticOrderAt F (z : ℂ) := by
  have hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det := by obtain ⟨_, _, _, hd⟩ := hγ; exact hd
  have hFγ : AnalyticAt ℂ F (Mb γ z) := by rw [Mb_coe hd]; exact hF _ (γ • z).im_pos
  rw [← Mb_coe hd z, ← ord_comp_Mb z hFγ]
  have hdz : dC γ z ≠ 0 := by rw [dC_coe]; exact denom_ne_zero γ z
  refine ord_eq_of_norm (hF _ z.im_pos) (hFγ.comp (Mb_analytic γ z))
    (c := fun w => ‖dC γ w‖ ^ (2 * m) / ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m) ?_ ?_ ?_
  · exact (((dC_cont γ).continuousAt.norm.pow _).div continuousAt_const (pow_pos hd m).ne')
  · exact div_pos (pow_pos (norm_pos_iff.2 hdz) _) (pow_pos hd m)
  · filter_upwards [isOpen_U.mem_nhds z.im_pos] with w hw
    have e := haut γ hγ ⟨w, hw⟩
    rw [← Mb_coe hd, ← dC_coe] at e
    simp only [UpperHalfPlane.coe_mk] at e ⊢
    field_simp
    linarith

theorem eq1_refl (a : UpperHalfPlane) : Eq1 a a := ⟨1, G1.one_mem, one_smul _ _⟩

theorem eq1_symm {a b : UpperHalfPlane} (h : Eq1 a b) : Eq1 b a := by
  obtain ⟨g, hg, rfl⟩ := h
  exact ⟨g⁻¹, G1.inv_mem hg, inv_smul_smul g a⟩

theorem eq1_trans {a b c : UpperHalfPlane} (h : Eq1 a b) (h' : Eq1 b c) : Eq1 a c := by
  obtain ⟨g, hg, rfl⟩ := h
  obtain ⟨g', hg', rfl⟩ := h'
  exact ⟨g' * g, G1.mul_mem hg' hg, mul_smul _ _ _⟩

theorem arith3 (m : ℕ) :
    (2 * m : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi / 3) / ENNReal.ofReal (4 * Real.pi) = (m : ℝ≥0∞) / 3 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have e1 : (2 * m : ℝ≥0∞) = ENNReal.ofReal (2 * m) := by
    rw [ENNReal.ofReal_mul (by norm_num)]; simp
  rw [e1, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_div_of_pos (by positivity)]
  have e2 : (2 * (m : ℝ) * (2 * Real.pi / 3)) / (4 * Real.pi) = (m : ℝ) / 3 := by
    field_simp; ring
  rw [e2, ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

/-- `4 e¹ ≤ r e*` for the kept representatives. -/
theorem kept_bound (z : UpperHalfPlane) :
    4 * Nat.card (Sone z) ≤
      (Finset.univ.filter (fun i : Fin 4 => ∀ j < i, ¬ Eq1 (g4 j • z) (g4 i • z))).card *
        Nat.card (Sstar z) := by
  classical
  set K := Finset.univ.filter (fun i : Fin 4 => ∀ j < i, ¬ Eq1 (g4 j • z) (g4 i • z))
  set C : Fin 4 → Finset (Fin 4) := fun i₀ => Finset.univ.filter (fun i => Eq1 (g4 i • z) (g4 i₀ • z))
  have hcover : (Finset.univ : Finset (Fin 4)) ⊆ K.biUnion C := by
    intro j _
    rw [Finset.mem_biUnion]
    set S := Finset.univ.filter (fun i : Fin 4 => Eq1 (g4 i • z) (g4 j • z))
    have hS : S.Nonempty := ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, eq1_refl _⟩⟩
    refine ⟨S.min' hS, ?_, ?_⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun k hk hEq => ?_⟩
      have h1 := (Finset.mem_filter.1 (S.min'_mem hS)).2
      have hkS : k ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, eq1_trans hEq h1⟩
      exact absurd (S.min'_le k hkS) (not_le.2 hk)
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, eq1_symm (Finset.mem_filter.1 (S.min'_mem hS)).2⟩
  have h4 : 4 ≤ ∑ i₀ ∈ K, (C i₀).card := by
    have := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    simpa using this
  calc 4 * Nat.card (Sone z) ≤ (∑ i₀ ∈ K, (C i₀).card) * Nat.card (Sone z) := Nat.mul_le_mul_right _ h4
    _ = ∑ i₀ ∈ K, (C i₀).card * Nat.card (Sone z) := Finset.sum_mul _ _ _
    _ ≤ ∑ _i₀ ∈ K, Nat.card (Sstar z) := Finset.sum_le_sum fun i₀ _ => class_bound z i₀
    _ = K.card * Nat.card (Sstar z) := by rw [Finset.sum_const, smul_eq_mul]

theorem enn_ineq (o : ℝ≥0∞) (es e1 k : ℕ) (hes : 0 < es) (he1 : 0 < e1) (h : 4 * e1 ≤ k * es) :
    4 * (o / es) ≤ k * (o / e1) := by
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ← mul_assoc, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have e1' : (4 : ℝ≥0∞) * (es : ℝ≥0∞)⁻¹ = ((4 : ℕ) : ℝ≥0∞) / (es : ℝ≥0∞) := by
    rw [ENNReal.div_eq_inv_mul, mul_comm]; norm_cast
  have e2' : (k : ℝ≥0∞) * (e1 : ℝ≥0∞)⁻¹ = (k : ℝ≥0∞) / (e1 : ℝ≥0∞) := by
    rw [ENNReal.div_eq_inv_mul, mul_comm]
  rw [e1', e2', enn_div _ _ hes, enn_div _ _ he1, ENNReal.ofReal_le_ofReal_iff (by positivity),
    div_le_div_iff₀ (by exact_mod_cast hes) (by exact_mod_cast he1)]
  exact_mod_cast (by linarith : 4 * e1 ≤ k * es)

theorem card_Sone_pos (z : UpperHalfPlane) : 0 < Nat.card (Sone z) := by
  haveI := finite_Sstar z
  haveI : Finite (Sone z) := Finite.of_injective (Subgroup.inclusion (Sone_le z)) (Subgroup.inclusion_injective _)
  exact Nat.card_pos

/-! #### The four cosets cover `Γ*` -/

open HDec.LeafQM.AV.Pin.NormO in
/-- The chain's `normalizerFinite` with its explicit set of representatives `T = {1, i, j, ij}` (the proof is
the chain's, `TailC.lean` l.2365-2380, with `T` kept). -/
theorem normalizer_explicit (u : HDec.LeafQM.Bˣ)
    (hu : ∀ a : HDec.LeafQM.B, a ∈ HDec.LeafQM.O ↔ (u : HDec.LeafQM.B) * a * ((u⁻¹ : HDec.LeafQM.Bˣ) : HDec.LeafQM.B) ∈ HDec.LeafQM.O) :
    ∃ t ∈ T, ∃ v : HDec.LeafQM.Oˣ, ∃ q : ℚ, q ≠ 0 ∧
      (u : HDec.LeafQM.B) = algebraMap ℚ HDec.LeafQM.B q * ((v : HDec.LeafQM.O) : HDec.LeafQM.B) * t := by
  obtain ⟨m, hm, ⟨n, hn⟩⟩ := HDec.LeafQM.AV.Pin.AutOExt.exists_nat_smul_mem (u : HDec.LeafQM.B)
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hu0 : ((sc _ hm0 * u : HDec.LeafQM.Bˣ) : HDec.LeafQM.B) = HDec.LeafQM.ofInt n := by
    change algebraMap ℚ HDec.LeafQM.B m * u = _
    rw [← Algebra.smul_def]; exact hn
  have hN : IsNorm u := by
    intro a ha
    refine ⟨(hu a).1 ha, (hu _).2 ?_⟩
    simpa [mul_assoc] using ha
  obtain ⟨q, hq, v, t, ht, he⟩ := HDec.LeafQM.AV.Pin.NormO.descent _ (sc _ hm0 * u) n hu0 rfl ((isNorm_sc _ hm0).mul hN)
  refine ⟨t, ht, v, (m : ℚ)⁻¹ * q, mul_ne_zero (inv_ne_zero hm0) hq, ?_⟩
  have : (u : HDec.LeafQM.B) = algebraMap ℚ HDec.LeafQM.B ((m : ℚ)⁻¹) * ((sc _ hm0 * u : HDec.LeafQM.Bˣ) : HDec.LeafQM.B) := by
    change _ = _ * (algebraMap ℚ HDec.LeafQM.B m * u)
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hm0, map_one, one_mul]
  rw [this, he, ← mul_assoc, ← mul_assoc, ← map_mul]

theorem smul_eq_of_scalar {γ δ : GL (Fin 2) ℝ} (hγ : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    (hδ : 0 < (δ : Matrix (Fin 2) (Fin 2) ℝ).det) {c : ℝ} (hc : c ≠ 0)
    (h : (γ : Matrix (Fin 2) (Fin 2) ℝ) = c • (δ : Matrix (Fin 2) (Fin 2) ℝ)) (z : UpperHalfPlane) :
    γ • z = δ • z := by
  have hγ' : 0 < γ.det.val := by rwa [Matrix.GeneralLinearGroup.val_det_apply]
  have hδ' : 0 < δ.det.val := by rwa [Matrix.GeneralLinearGroup.val_det_apply]
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos hγ', UpperHalfPlane.coe_smul_of_det_pos hδ']
  have hz1 := denom_ne_zero γ z
  have hz2 := denom_ne_zero δ z
  rw [div_eq_div_iff hz1 hz2]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, h, Matrix.smul_apply, smul_eq_mul]
  push_cast; ring

/-- `i`, `j`. -/
def eI : PkgI1.B := ⟨0, 1, 0, 0⟩
def eJ : PkgI1.B := ⟨0, 0, 1, 0⟩

theorem inO_i_a4i : PkgI1.InO (eI * a4i) :=
  (inO_iff _).2 ⟨-1, 1, 0, -1, by ext <;> simp [eI, a4i] <;> norm_num⟩
theorem inO_j_a6i : PkgI1.InO (eJ * a6i) :=
  (inO_iff _).2 ⟨1, 0, -1, 0, by ext <;> simp [eJ, a6i] <;> norm_num⟩
theorem inO_k_a6i_a4i : PkgI1.InO (eI * eJ * a6i * a4i) :=
  (inO_iff _).2 ⟨0, 0, -1, -1, by ext <;> simp [eI, eJ, a4i, a6i] <;> norm_num⟩
theorem nrd_eI : nrd eI = -2 := by simp [nrd, eI]
theorem nrd_eJ : nrd eJ = 3 := by simp [nrd, eJ]

open HDec.LeafQM.AV.Pin.NormO in
/-- **The four cosets cover `Γ*`** (from the chain's normalizer computation). -/
theorem coset_cover {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Gs) :
    ∃ i : Fin 4, ∃ h ∈ G1, mob γ = mob h * mob (g4 i) := by
  obtain ⟨x, ⟨y, hxy, hyx, hN⟩, hγx, hd⟩ := hγ
  have hnx : 0 < nrd x := by rw [hγx, det_iota_eq] at hd; exact_mod_cast hd
  let u : HDec.LeafQM.Bˣ := ⟨x, y, hxy, hyx⟩
  have hO : ∀ a : PkgI1.B, a ∈ HDec.LeafQM.O ↔ PkgI1.InO a := fun a => (inO_ofInt a).symm
  have hiff : ∀ a : HDec.LeafQM.B, a ∈ HDec.LeafQM.O ↔
      (u : HDec.LeafQM.B) * a * ((u⁻¹ : HDec.LeafQM.Bˣ) : HDec.LeafQM.B) ∈ HDec.LeafQM.O := by
    intro a
    change a ∈ HDec.LeafQM.O ↔ x * a * y ∈ HDec.LeafQM.O
    rw [hO, hO]
    refine ⟨fun ha => (hN a ha).1, fun ha => ?_⟩
    have := (hN _ ha).2
    simpa [mul_assoc, hyx, ← mul_assoc y x, hyx] using this
  obtain ⟨t, ht, v, q, hq, hu⟩ := normalizer_explicit u hiff
  change x = _ at hu
  set vv : PkgI1.B := ((v : HDec.LeafQM.O) : HDec.LeafQM.B)
  have hvO : PkgI1.InO vv := (hO vv).1 (v : HDec.LeafQM.O).2
  have hvn : nrd vv = 1 ∨ nrd vv = -1 := by
    have := HDec.LeafQM.AV.Pin.Exact.nrd_unit v
    simpa [HDec.LeafQM.AV.Pin.Exact.nrd, nrd] using this
  -- the representative and the norm-one factor
  have hqa : ∀ z : PkgI1.B, nrd (algebraMap ℚ PkgI1.B q * z) = q ^ 2 * nrd z := by
    intro z; rw [nrd_mul]; congr 1; simp [nrd]
  have hnq : 0 < q ^ 2 := by positivity
  have hui : ((ui : HDec.LeafQM.Bˣ) : PkgI1.B) = eI := by
    show HDec.LeafQM.ofInt ei = _; ext <;> simp [HDec.LeafQM.ofInt, ei, eI]
  have huj : ((uj : HDec.LeafQM.Bˣ) : PkgI1.B) = eJ := by
    show HDec.LeafQM.ofInt ej = _; ext <;> simp [HDec.LeafQM.ofInt, ej, eJ]
  have na4i : nrd a4i = 1 / 2 := by simp [nrd, a4i]; norm_num
  have na6i : nrd a6i = 1 / 3 := by simp [nrd, a6i]; norm_num
  have h44 : a4i * a4 = 1 := nd_a4.2.1
  have h66 : a6i * a6 = 1 := nd_a6.2.1
  have hA : ∀ z : PkgI1.B, a4i * (a4 * z) = z := fun z => by rw [← mul_assoc, h44, one_mul]
  have hB : ∀ z : PkgI1.B, a6i * (a6 * z) = z := fun z => by rw [← mul_assoc, h66, one_mul]
  have key : ∃ (i : Fin 4) (w : PkgI1.B), PkgI1.InO w ∧ nrd w = 1 ∧
      x = algebraMap ℚ PkgI1.B q * (w * rep4 i) := by
    rw [T_mem_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · have hv1 : nrd vv = 1 := by
        rcases hvn with h | h
        · exact h
        · exfalso; rw [hu, Units.val_one, mul_one, hqa, h] at hnx; nlinarith
      exact ⟨0, vv, hvO, hv1, by rw [hu]; simp [rep4]⟩
    · rw [hui] at hu
      have hv1 : nrd vv = -1 := by
        rcases hvn with h | h
        · exfalso; rw [hu, mul_assoc, hqa, nrd_mul, h, nrd_eI] at hnx; nlinarith
        · exact h
      refine ⟨1, vv * (eI * a4i), inO_mul hvO inO_i_a4i, ?_, ?_⟩
      · rw [nrd_mul, nrd_mul, hv1, na4i, nrd_eI]; norm_num
      · rw [hu, show rep4 1 = a4 from rfl]; simp only [mul_assoc, hA, h44, mul_one]
    · rw [huj] at hu
      have hv1 : nrd vv = 1 := by
        rcases hvn with h | h
        · exact h
        · exfalso; rw [hu, mul_assoc, hqa, nrd_mul, h, nrd_eJ] at hnx; nlinarith
      refine ⟨2, vv * (eJ * a6i), inO_mul hvO inO_j_a6i, ?_, ?_⟩
      · rw [nrd_mul, nrd_mul, hv1, na6i, nrd_eJ]; norm_num
      · rw [hu, show rep4 2 = a6 from rfl]; simp only [mul_assoc, hB, h66, mul_one]
    · rw [Units.val_mul, hui, huj] at hu
      have hv1 : nrd vv = -1 := by
        rcases hvn with h | h
        · exfalso; rw [hu, mul_assoc, hqa, nrd_mul, nrd_mul, h, nrd_eI, nrd_eJ] at hnx; nlinarith
        · exact h
      refine ⟨3, vv * (eI * eJ * a6i * a4i), inO_mul hvO inO_k_a6i_a4i, ?_, ?_⟩
      · simp only [nrd_mul, hv1, na6i, na4i, nrd_eI, nrd_eJ]; norm_num
      · rw [hu, show rep4 3 = a4 * a6 from rfl]; simp only [mul_assoc, hA, h66, mul_one]
  obtain ⟨i, w, hwO, hwn, hxw⟩ := key
  have hw0 : nrd w ≠ 0 := by rw [hwn]; norm_num
  let h : GL (Fin 2) ℝ := glOf w hw0
  have hh : h ∈ G1 := ⟨w, hwO, coe_glOf w hw0, by rw [coe_glOf, det_iota_eq, hwn]; norm_num⟩
  refine ⟨i, h, hh, ?_⟩
  rw [← map_mul]
  have hdet2 : 0 < ((h * g4 i : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [Units.val_mul, Matrix.det_mul, coe_glOf, det_iota_eq, hwn, g4, coe_glOf, det_iota_eq]
    have := (nd_rep i).2.2.2
    simp only [Rat.cast_one, one_mul]; exact_mod_cast this
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hmat : (γ : Matrix (Fin 2) (Fin 2) ℝ) = (q : ℝ) • ((h * g4 i : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    have hia : PkgI1.iota (algebraMap ℚ PkgI1.B q) = (q : ℝ) • 1 := by
      rw [iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [hγx, hxw, Units.val_mul, coe_glOf, g4, coe_glOf, iota_mul, iota_mul, hia, smul_one_mul]
  exact Equiv.ext fun z => smul_eq_of_scalar hd hdet2 hq0 hmat z

/-- **The reverse class bound**: `e* ≤ |C_{i₀}| e¹` (from the covering by the four cosets). -/
theorem class_bound_rev (z : UpperHalfPlane) (i₀ : Fin 4) :
    Nat.card (Sstar z) ≤
      (Finset.univ.filter (fun i => Eq1 (g4 i • z) (g4 i₀ • z))).card * Nat.card (Sone z) := by
  classical
  haveI := finite_Sstar z
  haveI : Finite (Sone z) := Finite.of_injective (Subgroup.inclusion (Sone_le z)) (Subgroup.inclusion_injective _)
  set C := Finset.univ.filter (fun i => Eq1 (g4 i • z) (g4 i₀ • z))
  -- the fibre predicate
  let Fib : Fin 4 → (Sstar z) → Prop := fun i σ =>
    ∃ h ∈ G1, mob (g4 i₀) * (σ : Equiv.Perm UpperHalfPlane) = mob h * mob (g4 i)
  have hex : ∀ σ : Sstar z, ∃ i, Fib i σ := by
    intro σ
    obtain ⟨δ, hδ, hσ⟩ := σ.2.1
    obtain ⟨i, h, hh, he⟩ := coset_cover (Gs.mul_mem (g4_mem i₀) hδ)
    exact ⟨i, h, hh, by rw [← hσ, ← map_mul, he]⟩
  choose idx hidx using hex
  have hC : ∀ σ, idx σ ∈ C := by
    intro σ
    obtain ⟨h, hh, he⟩ := hidx σ
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, h, hh, ?_⟩
    have := congrArg (fun π : Equiv.Perm UpperHalfPlane => π z) he
    simp only [Equiv.Perm.coe_mul, Function.comp, mob_apply] at this
    have hz : (σ : Equiv.Perm UpperHalfPlane) z = z := σ.2.2
    rw [hz] at this
    exact this.symm
  let ρ : Fin 4 → Sstar z := fun i => if hi : ∃ σ, idx σ = i then hi.choose else 1
  have hρ : ∀ σ, idx (ρ (idx σ)) = idx σ := by
    intro σ
    have hi : ∃ τ, idx τ = idx σ := ⟨σ, rfl⟩
    simp only [ρ, dif_pos hi]
    exact hi.choose_spec
  have hmemS : ∀ σ : Sstar z, ((ρ (idx σ))⁻¹ * σ : Sstar z).1 ∈ Sone z := by
    intro σ
    obtain ⟨h₁, hh₁, he₁⟩ := hidx (ρ (idx σ))
    obtain ⟨h₂, hh₂, he₂⟩ := hidx σ
    rw [hρ σ] at he₁
    refine ⟨?_, ((ρ (idx σ))⁻¹ * σ).2.2⟩
    have e : (((ρ (idx σ))⁻¹ * σ : Sstar z) : Equiv.Perm UpperHalfPlane) =
        (mob (g4 (idx σ)))⁻¹ * ((mob h₁)⁻¹ * mob h₂) * (mob (g4 (idx σ)))⁻¹⁻¹ := by
      have k1 : ((ρ (idx σ)) : Equiv.Perm UpperHalfPlane) = (mob (g4 i₀))⁻¹ * (mob h₁ * mob (g4 (idx σ))) := by
        rw [← he₁]; group
      have k2 : (σ : Equiv.Perm UpperHalfPlane) = (mob (g4 i₀))⁻¹ * (mob h₂ * mob (g4 (idx σ))) := by
        rw [← he₂]; group
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, k1, k2]; group
    rw [e]
    exact Mone_normal (Mstar.inv_mem ⟨_, g4_mem _, rfl⟩)
      (Mone.mul_mem (Mone.inv_mem ⟨_, hh₁, rfl⟩) ⟨_, hh₂, rfl⟩)
  let Ψ : Sstar z → C × Sone z := fun σ =>
    (⟨idx σ, hC σ⟩, ⟨((ρ (idx σ))⁻¹ * σ : Sstar z).1, hmemS σ⟩)
  have hΨ : Function.Injective Ψ := by
    intro σ σ' h
    simp only [Ψ, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hi : idx σ = idx σ' := congrArg Subtype.val h1
    have h2' := congrArg Subtype.val h2
    simp only at h2'
    rw [hi] at h2'
    apply Subtype.ext
    have := mul_left_cancel h2'
    exact this
  have := Nat.card_le_card_of_injective Ψ hΨ
  rw [Nat.card_prod] at this
  simpa using this

/-- **Exact count**: `r_z e*_z = 4 e¹_z`. -/
theorem kept_eq (z : UpperHalfPlane) :
    (Finset.univ.filter (fun i : Fin 4 => ∀ j < i, ¬ Eq1 (g4 j • z) (g4 i • z))).card *
        Nat.card (Sstar z) = 4 * Nat.card (Sone z) := by
  classical
  refine le_antisymm ?_ (kept_bound z)
  set K := Finset.univ.filter (fun i : Fin 4 => ∀ j < i, ¬ Eq1 (g4 j • z) (g4 i • z))
  set C : Fin 4 → Finset (Fin 4) := fun i₀ => Finset.univ.filter (fun i => Eq1 (g4 i • z) (g4 i₀ • z))
  have hdisj : (K : Set (Fin 4)).PairwiseDisjoint C := by
    intro a ha b hb hab
    rw [Function.onFun, Finset.disjoint_left]
    intro j hja hjb
    have e1 := (Finset.mem_filter.1 hja).2
    have e2 := (Finset.mem_filter.1 hjb).2
    have hab' : Eq1 (g4 a • z) (g4 b • z) := eq1_trans (eq1_symm e1) e2
    rcases lt_or_gt_of_ne hab with h | h
    · exact (Finset.mem_filter.1 hb).2 a h hab'
    · exact (Finset.mem_filter.1 ha).2 b h (eq1_symm hab')
  have hsum : ∑ i₀ ∈ K, (C i₀).card ≤ 4 := by
    rw [← Finset.card_biUnion hdisj]
    exact (Finset.card_le_univ _).trans (by simp)
  calc K.card * Nat.card (Sstar z) = ∑ _i₀ ∈ K, Nat.card (Sstar z) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ i₀ ∈ K, (C i₀).card * Nat.card (Sone z) := Finset.sum_le_sum fun i₀ _ => class_bound_rev z i₀
    _ = (∑ i₀ ∈ K, (C i₀).card) * Nat.card (Sone z) := (Finset.sum_mul _ _ _).symm
    _ ≤ 4 * Nat.card (Sone z) := Nat.mul_le_mul_right _ hsum

/-- **Row H-87 from the published leaves only**: the valence formula applied to `Γ¹ = ι(𝒪¹)` with
Shimizu's covolume `2π/3`, and the index argument above. -/
theorem valenceFormulaGammaStar_of_O1 (hV : ValenceFormulaCocompactEq) (hS : ShimizuCovolumeO1) :
    HDec.LeafQCheck.VB.ValenceFormulaGammaStar := by
  classical
  intro m F hF hne haut T hT
  obtain ⟨hF1, s, hs, hvol⟩ := hS
  have haut1 : ∀ γ ∈ Gamma1, ∀ z : UpperHalfPlane,
      ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖ := fun γ hγ z => haut γ (G1_le hγ) z
  set K : UpperHalfPlane → Finset (Fin 4) := fun z =>
    Finset.univ.filter (fun i : Fin 4 => ∀ j < i, ¬ Eq1 (g4 j • z) (g4 i • z)) with hK
  set p : UpperHalfPlane → Fin 4 → UpperHalfPlane := fun z i => g4 i • z with hp
  set T' := T.biUnion (fun z => (K z).image (p z)) with hT'
  have hcross : ∀ z ∈ T, ∀ z' ∈ T, ∀ i j, Eq1 (p z i) (p z' j) → z = z' := by
    intro z hz z' hz' i j ⟨h, hh, hhz⟩
    by_contra hne'
    apply hT hz hz' hne' ((g4 j)⁻¹ * h * g4 i)
      (Gs.mul_mem (Gs.mul_mem (Gs.inv_mem (g4_mem j)) (G1_le hh)) (g4_mem i))
    simp only [hp] at hhz
    rw [mul_smul, mul_smul, hhz, inv_smul_smul]
  have hkeep : ∀ z, ∀ i ∈ K z, ∀ j ∈ K z, i ≠ j → ¬ Eq1 (p z i) (p z j) := by
    intro z i hi j hj hij hE
    rcases lt_or_gt_of_ne hij with h | h
    · exact (Finset.mem_filter.1 hj).2 i h hE
    · exact (Finset.mem_filter.1 hi).2 j h (eq1_symm hE)
  have hpair : (T' : Set UpperHalfPlane).Pairwise (fun a b => ∀ γ ∈ Gamma1, γ • a ≠ b) := by
    intro a ha b hb hab γ hγ hγab
    simp only [hT', Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Finset.mem_image] at ha hb
    obtain ⟨z, hz, i, hi, rfl⟩ := ha
    obtain ⟨z', hz', j, hj, rfl⟩ := hb
    have hE : Eq1 (p z i) (p z' j) := ⟨γ, hγ, hγab⟩
    obtain rfl := hcross z hz z' hz' i j hE
    have hij : i ≠ j := fun h => hab (by rw [h])
    exact hkeep z i hi j hj hij hE
  have hval := (hV Gamma1 hF1 s hs m F hF hne haut1).2.2 T' hpair
  rw [hvol, arith3] at hval
  have hdisj : (T : Set UpperHalfPlane).PairwiseDisjoint (fun z => (K z).image (p z)) := by
    intro z hz z' hz' hne'
    rw [Function.onFun, Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_image] at ha ha'
    obtain ⟨i, -, rfl⟩ := ha
    obtain ⟨j, -, hj⟩ := ha'
    exact hne' (hcross z hz z' hz' i j (by rw [← hj]; exact eq1_refl _))
  rw [hT', Finset.sum_biUnion hdisj] at hval
  have hinner : ∀ z ∈ T, ∑ a ∈ (K z).image (p z),
      ((analyticOrderAt F (a : ℂ) : ℕ∞) : ℝ≥0∞) / (ellOrderOf Gamma1 a : ℝ≥0∞) =
      ((K z).card : ℝ≥0∞) * (((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (Nat.card (Sone z) : ℝ≥0∞)) := by
    intro z hz
    rw [Finset.sum_image (fun i hi j hj hij => by
      by_contra hne'
      exact hkeep z i hi j hj hne' (by rw [hij]; exact eq1_refl _))]
    rw [Finset.sum_congr rfl (fun i _ => by
      rw [ord_smul_eq hF haut (g4_mem i) z, ← card_Sone, card_Sone_smul (g4_mem i) z]),
      Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hinner] at hval
  have hper : ∀ z ∈ T, 4 * (((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) /
      (HDec.LeafQCheck.VB.ellOrder z : ℝ≥0∞)) ≤
      ((K z).card : ℝ≥0∞) * (((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (Nat.card (Sone z) : ℝ≥0∞)) := by
    intro z hz
    have hb := kept_bound z
    rw [card_Sstar] at hb
    obtain ⟨he0, -⟩ := HDec.LeafQCheck.VB.ellipticOrderLe6_proof z
    exact enn_ineq _ _ _ _ he0 (card_Sone_pos z) hb
  have hsum := (Finset.sum_le_sum hper).trans hval
  rw [← Finset.mul_sum] at hsum
  set X := ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (HDec.LeafQCheck.VB.ellOrder z : ℝ≥0∞)
  have h12 : (m : ℝ≥0∞) / 12 = ((m : ℝ≥0∞) / 3) / 4 := by
    rw [show ((m : ℝ≥0∞) / 3) = ((m : ℕ) : ℝ≥0∞) / ((3 : ℕ) : ℝ≥0∞) by norm_num,
      show ((m : ℝ≥0∞) / 12) = ((m : ℕ) : ℝ≥0∞) / ((12 : ℕ) : ℝ≥0∞) by norm_num,
      enn_div _ _ (by norm_num), enn_div _ _ (by norm_num),
      show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_div_of_pos (by norm_num)]
    congr 1; push_cast; ring
  rw [h12, ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num)), mul_comm]
  exact hsum

theorem enn_eq (o : ℝ≥0∞) (es e1 k : ℕ) (hes : 0 < es) (he1 : 0 < e1) (h : k * es = 4 * e1) :
    (k : ℝ≥0∞) * (o / e1) = 4 * (o / es) := by
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ← mul_assoc, ← mul_assoc]
  congr 1
  have e1' : (4 : ℝ≥0∞) * (es : ℝ≥0∞)⁻¹ = ((4 : ℕ) : ℝ≥0∞) / (es : ℝ≥0∞) := by
    rw [ENNReal.div_eq_inv_mul, mul_comm]; norm_cast
  have e2' : (k : ℝ≥0∞) * (e1 : ℝ≥0∞)⁻¹ = (k : ℝ≥0∞) / (e1 : ℝ≥0∞) := by
    rw [ENNReal.div_eq_inv_mul, mul_comm]
  rw [e1', e2', enn_div _ _ hes, enn_div _ _ he1]
  congr 1
  rw [div_eq_div_iff (by exact_mod_cast he1.ne') (by exact_mod_cast hes.ne')]
  exact_mod_cast (by linarith : k * es = 4 * e1)

/-- Every finite set has a subset of pairwise `Γ*`-inequivalent points meeting each of its `Γ*`-classes. -/
theorem exists_reps (S : Finset UpperHalfPlane) :
    ∃ T ⊆ S, (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γs, γ • z ≠ w) ∧
      ∀ s ∈ S, ∃ t ∈ T, ∃ γ ∈ Γs, γ • t = s := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, subset_refl _, by simp, by simp⟩
  | insert a S ha ih =>
    obtain ⟨T, hTS, hTp, hTc⟩ := ih
    by_cases hc : ∃ t ∈ T, ∃ γ ∈ Γs, γ • t = a
    · refine ⟨T, hTS.trans (Finset.subset_insert _ _), hTp, fun s hs => ?_⟩
      rcases Finset.mem_insert.1 hs with rfl | hs
      · exact hc
      · exact hTc s hs
    · push Not at hc
      refine ⟨insert a T, Finset.insert_subset_insert _ hTS, ?_, fun s hs => ?_⟩
      · rw [Finset.coe_insert]
        refine hTp.insert fun t ht hne => ⟨fun γ hγ h => ?_, fun γ hγ h => hc t ht γ hγ h⟩
        exact hc t ht γ⁻¹ (gammaStar_inv hγ) (by rw [← h, inv_smul_smul])
      · rcases Finset.mem_insert.1 hs with rfl | hs
        · exact ⟨s, Finset.mem_insert_self _ _, 1, one_mem_gammaStar', one_smul _ _⟩
        · obtain ⟨t, ht, γ, hγ, h⟩ := hTc s hs
          exact ⟨t, Finset.mem_insert_of_mem ht, γ, hγ, h⟩

/-- **`GammaStarValence` from the published leaves only** (valence formula for `Γ¹`, Shimizu's covolume), by the
index argument with the exact count `r e* = 4 e¹` and the covering by the four cosets. -/
theorem gammaStarValence_of_O1 (hV : ValenceFormulaCocompactEq) (hS : ShimizuCovolumeO1) :
    GammaStarValence := by
  classical
  intro m F hF hne hau
  obtain ⟨hF1, s, hs, hvol⟩ := hS
  have haut := abs_auto hau
  have haut1 : ∀ γ ∈ Gamma1, ∀ z : UpperHalfPlane,
      ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖ := fun γ hγ z => haut γ (G1_le hγ) z
  obtain ⟨h1, h2, -⟩ := hV Gamma1 hF1 s hs m F hF hne haut1
  refine ⟨?_, fun T hT hcov => ?_, fun T hT => valenceFormulaGammaStar_of_O1 hV ⟨hF1, s, hs, hvol⟩ m F hF hne haut T hT⟩
  · -- representatives for `Γ*` from representatives for `Γ¹`
    obtain ⟨T₁, -, hT₁c⟩ := h1
    obtain ⟨T, -, hTp, hTc⟩ := exists_reps T₁
    refine ⟨T, hTp, fun w hw => ?_⟩
    obtain ⟨t₁, ht₁, h, hh, rfl⟩ := hT₁c w hw
    obtain ⟨t, ht, γ, hγ, rfl⟩ := hTc t₁ ht₁
    exact ⟨t, ht, h * γ, Gs.mul_mem (G1_le hh) hγ, mul_smul _ _ _⟩
  · set K : UpperHalfPlane → Finset (Fin 4) := fun z =>
      Finset.univ.filter (fun i : Fin 4 => ∀ j < i, ¬ Eq1 (g4 j • z) (g4 i • z)) with hK
    set p : UpperHalfPlane → Fin 4 → UpperHalfPlane := fun z i => g4 i • z with hp
    set T' := T.biUnion (fun z => (K z).image (p z)) with hT'
    have hcross : ∀ z ∈ T, ∀ z' ∈ T, ∀ i j, Eq1 (p z i) (p z' j) → z = z' := by
      intro z hz z' hz' i j ⟨h, hh, hhz⟩
      by_contra hne'
      apply hT hz hz' hne' ((g4 j)⁻¹ * h * g4 i)
        (Gs.mul_mem (Gs.mul_mem (Gs.inv_mem (g4_mem j)) (G1_le hh)) (g4_mem i))
      simp only [hp] at hhz
      rw [mul_smul, mul_smul, hhz, inv_smul_smul]
    have hkeep : ∀ z, ∀ i ∈ K z, ∀ j ∈ K z, i ≠ j → ¬ Eq1 (p z i) (p z j) := by
      intro z i hi j hj hij hE
      rcases lt_or_gt_of_ne hij with h | h
      · exact (Finset.mem_filter.1 hj).2 i h hE
      · exact (Finset.mem_filter.1 hi).2 j h (eq1_symm hE)
    have hpair : (T' : Set UpperHalfPlane).Pairwise (fun a b => ∀ γ ∈ Gamma1, γ • a ≠ b) := by
      intro a ha b hb hab γ hγ hγab
      simp only [hT', Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Finset.mem_image] at ha hb
      obtain ⟨z, hz, i, hi, rfl⟩ := ha
      obtain ⟨z', hz', j, hj, rfl⟩ := hb
      have hE : Eq1 (p z i) (p z' j) := ⟨γ, hγ, hγab⟩
      obtain rfl := hcross z hz z' hz' i j hE
      have hij : i ≠ j := fun h => hab (by rw [h])
      exact hkeep z i hi j hj hij hE
    -- covering of the zeros by `T'` (the four cosets cover `Γ*`)
    have hcov1 : Covers Gamma1 T' F := by
      intro w hw
      obtain ⟨t, ht, γ, hγ, rfl⟩ := hcov w hw
      obtain ⟨i, h, hh, he⟩ := coset_cover hγ
      have hw' : γ • t = h • (g4 i • t) := by
        have := congrArg (fun π : Equiv.Perm UpperHalfPlane => π t) he
        simpa [mob_apply, mul_smul] using this
      set Sx := Finset.univ.filter (fun j : Fin 4 => Eq1 (g4 j • t) (g4 i • t))
      have hS : Sx.Nonempty := ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, eq1_refl _⟩⟩
      set i' := Sx.min' hS
      have hi'K : i' ∈ K t := by
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun k hk hEq => ?_⟩
        have h1 := (Finset.mem_filter.1 (Sx.min'_mem hS)).2
        have hkS : k ∈ Sx := Finset.mem_filter.2 ⟨Finset.mem_univ _, eq1_trans hEq h1⟩
        exact absurd (Sx.min'_le k hkS) (not_le.2 hk)
      have hE : Eq1 (g4 i' • t) (γ • t) := by
        rw [hw']
        exact eq1_trans (Finset.mem_filter.1 (Sx.min'_mem hS)).2 ⟨h, hh, rfl⟩
      obtain ⟨h', hh', he'⟩ := hE
      refine ⟨g4 i' • t, ?_, h', hh', he'⟩
      simp only [hT', Finset.mem_biUnion, Finset.mem_image]
      exact ⟨t, ht, i', hi'K, rfl⟩
    have hval := h2 T' hpair hcov1
    rw [hvol, arith3] at hval
    have hdisj : (T : Set UpperHalfPlane).PairwiseDisjoint (fun z => (K z).image (p z)) := by
      intro z hz z' hz' hne'
      rw [Function.onFun, Finset.disjoint_left]
      intro a ha ha'
      simp only [Finset.mem_image] at ha ha'
      obtain ⟨i, -, rfl⟩ := ha
      obtain ⟨j, -, hj⟩ := ha'
      exact hne' (hcross z hz z' hz' i j (by rw [← hj]; exact eq1_refl _))
    rw [hT', Finset.sum_biUnion hdisj] at hval
    have hinner : ∀ z ∈ T, ∑ a ∈ (K z).image (p z),
        ((analyticOrderAt F (a : ℂ) : ℕ∞) : ℝ≥0∞) / (ellOrderOf Gamma1 a : ℝ≥0∞) =
        4 * (((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (HDec.LeafQCheck.VB.ellOrder z : ℝ≥0∞)) := by
      intro z hz
      rw [Finset.sum_image (fun i hi j hj hij => by
        by_contra hne'
        exact hkeep z i hi j hj hne' (by rw [hij]; exact eq1_refl _))]
      rw [Finset.sum_congr rfl (fun i _ => by
        rw [ord_smul_eq hF haut (g4_mem i) z, ← card_Sone, card_Sone_smul (g4_mem i) z]),
        Finset.sum_const, nsmul_eq_mul]
      have hk := kept_eq z
      rw [card_Sstar] at hk
      obtain ⟨he0, -⟩ := HDec.LeafQCheck.VB.ellipticOrderLe6_proof z
      exact enn_eq _ _ _ _ he0 (card_Sone_pos z) hk
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum] at hval
    have h12 : (m : ℝ≥0∞) / 12 = ((m : ℝ≥0∞) / 3) / 4 := by
      rw [show ((m : ℝ≥0∞) / 3) = ((m : ℕ) : ℝ≥0∞) / ((3 : ℕ) : ℝ≥0∞) by norm_num,
        show ((m : ℝ≥0∞) / 12) = ((m : ℕ) : ℝ≥0∞) / ((12 : ℕ) : ℝ≥0∞) by norm_num,
        enn_div _ _ (by norm_num), enn_div _ _ (by norm_num),
        show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_div_of_pos (by norm_num)]
      congr 1; push_cast; ring
    rw [h12, ENNReal.eq_div_iff (by norm_num) (by norm_num)]
    exact hval

end Index

include hT hC in
/-- **Row H-88 from published leaves and one number**: the valence formula (for `Γ¹`), Shimizu's covolume,
the CM value `ThetaQuotientValue24` (and the bundle leaf `r4`). -/
theorem qmHauptmodulBase3_of_O1 (hV : ValenceFormulaCocompactEq) (hS : ShimizuCovolumeO1) :
    QMHauptmodulBase3 :=
  qmHauptmodulBase3_of' hT (gammaStarValence_of_O1 hV hS) hC

include hT hC in
/-- **Row H-88 from published leaves and project glue**: the valence formula, Shimizu's volume formula, the
glue from `𝒪¹` to `Γ*`, the CM value (and the bundle leaf `r4`). -/
theorem qmHauptmodulBase3_of_shimizu (hV : ValenceFormulaCocompactEq) (hS : ShimizuCovolumeO1)
    (hGF : GammaStarFromO1) : QMHauptmodulBase3 :=
  qmHauptmodulBase3_of' hT (gammaStarValence_of_area hV (hGF hS)) hC

end

end HDec.LeafQCheck.HM.QMSplit

#print axioms HDec.LeafQCheck.HM.QMSplit.qmHauptmodulBase3_of
#print axioms HDec.LeafQCheck.HM.QMSplit.valenceFormulaGammaStar_of_eq
#print axioms HDec.LeafQCheck.HM.QMSplit.ellipticOrderDvd_proof
#print axioms HDec.LeafQCheck.HM.QMSplit.qmHauptmodulBase3_of'
#print axioms HDec.LeafQCheck.HM.QMSplit.qmHauptmodulBase3_of_shimizu
#print axioms HDec.LeafQCheck.HM.QMSplit.valenceFormulaGammaStar_of_O1
#print axioms HDec.LeafQCheck.HM.QMSplit.gammaStarValence_of_O1
#print axioms HDec.LeafQCheck.HM.QMSplit.qmHauptmodulBase3_of_O1
