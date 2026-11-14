import TailK

/-!
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


end HDec.LeafQCheck

namespace HDec.HSyn

/-- leaf-fold4's `OpenAddedLeaves4` without `gammaStarGen` (proved: `LeafQCheck.gammaStarGen_proof`). -/
structure OpenAddedLeaves5 : Prop where
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  qmHauptmodul : PkgI1.QMHauptmodul
  qmClassNumberOne : G0Split.FibreQM.QMClassNumberOne
  senTwist : G0Galois.SenTwist
  finiteImageHT : G0Galois.FiniteImageHT
  t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists
  isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse
  x6ConicModel : X6Kummer.X6ConicModel
  y3Connected : TSHecke.Y3Connected
  qmAutCard : HeckeRest.QMAutCard
  serreRigidity3 : HeckeRest.SerreRigidity3
  alFixedPoints : HeckeRest.ALFixedPoints
  zariskiConnectedness : _root_.ZariskiConn.ZariskiConnectedness.{0}
  cmDescends : G0Split.FibreQM.PeriodMapH.CMDescends
  valenceBoundGammaStar : G0Split.FibreQM.PeriodMap.ValenceBoundGammaStar
  egaIV_8_8_2_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  egaIV_17_7_8_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii

theorem openAddedLeaves4_of_5 (l : OpenAddedLeaves5) : OpenAddedLeaves4 :=
  ⟨l.cmOptimalEmbedding, l.thetaRatiosAlgebraic, l.qmHauptmodul, l.qmClassNumberOne, l.senTwist,
    l.finiteImageHT, l.t09SymmIsogenyExists, l.isogenyQuasiInverse, l.x6ConicModel, l.y3Connected,
    l.qmAutCard, l.serreRigidity3, l.alFixedPoints, l.zariskiConnectedness, l.cmDescends,
    LeafQCheck.gammaStarGen_proof, l.valenceBoundGammaStar, l.egaIV_8_8_2_ii, l.egaIV_8_10_5_xii,
    l.egaIV_17_7_8_ii⟩

/-- **`SixContactMin` from 26 + 19 + 19 leaves and one glue Prop** (leaf-fold4's 66 fields minus
`gammaStarGen`). -/
theorem sixContactMin_of_open5 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4)
    (l : OpenAddedLeaves5) (g : OpenGlue4) : ZInQ.SixContactMin :=
  sixContactMin_of_open4 r t (openAddedLeaves4_of_5 l) g

end HDec.HSyn

example : ∀ (_ : HDec.HSyn.OpenResearchLeaves2) (_ : HDec.HSyn.OpenTextbookLeaves4)
    (_ : HDec.HSyn.OpenAddedLeaves5) (_ : HDec.HSyn.OpenGlue4), _root_.ZInQ.SixContactMin :=
  HDec.HSyn.sixContactMin_of_open5

#print axioms HDec.LeafQCheck.gammaStarGen_proof
#print axioms HDec.HSyn.sixContactMin_of_open5
