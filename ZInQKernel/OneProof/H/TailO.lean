import ZInQKernel.OneProof.H.TailN

/-! ## leaf-fold6, part f10: leafq-check's `Fold.lean`, ported after leaf-fold5's chain (made by `mk_f10.py`:
`import TailK` dropped; leafq-check's `OpenAddedLeaves5`-`10`, `sixContactMin_of_open5`-`10`,
`openAddedLeaves4_of_5`, `openAddedLeaves5_of_6` renamed with a `Q`; nothing else changed). -/

/-!
# leafq-check: the fold (check over leaf-fold4's olean chain)

`scratch/leafq-check/GammaStarGen.lean`'s proof, run over leaf-fold4's chain (`import TailK`, so the
statement is the chain's own constant `HDec.HSyn.G0Split.FibreQM.PeriodGlue.GammaStarGen`), and
`sixContactMin_of_openQ5`: `sixContactMin_of_open4` without the field `gammaStarGen`.
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

/-! ## `CMDescends` (copied from `CMDescendsGlue.lean`) -/


namespace HDec.HSyn.G0Split.FibreQM.PeriodMapH
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open HSyn.G0Split.FibreQM

namespace LeafQCheck

/-- `A₀ ×_{ℚ̄, ιe} ℂ`. -/
noncomputable abbrev bcC (ιe : Qbar →+* ℂ) (A₀ : PkgI3.AbVar Qbar) : PkgI3.AbVar ℂ :=
  @PkgI3.AbVar.baseChange Qbar _ A₀ ℂ _ ιe.toAlgebra

/-- **LEAF (Shimura–Taniyama, QM form).** A QM abelian surface over `ℂ` with CM by `ℤ[i]`, `ℤ[ζ₃]` or
`ℤ[√−6]` (an endomorphism `φ` commuting with `ι(𝒪)` with `φ² = −1`, `φ² − φ + 1 = 0` or `φ² = −6`) is
isomorphic, as an abelian variety, to `A₀ ×_{ℚ̄,ιe} ℂ` for some abelian variety `A₀/ℚ̄` and some
`ιe : ℚ̄ → ℂ`.

Published: an abelian variety over `ℂ` of CM type is isomorphic to the base change of an abelian variety
over a number field (Shimura–Taniyama, *Complex multiplication of abelian varieties*, 1961, §12.4;
Shimura, *Abelian varieties with complex multiplication and modular functions*, 1998, §12.4, Prop. 26;
UNVERIFIED numbers). It applies: `ι(i)` and `φ` commute, `ι(i)² = 2`, so `End⁰(A) ⊇ ℚ(√2, φ)`, a CM
field of degree `4 = 2 dim A`. A consequence of the published statement. -/
def STQM : Prop :=
  ∀ (A : PkgI3.AbVar ℂ) (q : QMStr A), A.dim = 2 → (HasCM4 q ∨ HasCM3 q ∨ HasCM24 q) →
    ∃ (ιe : Qbar →+* ℂ) (A₀ : PkgI3.AbVar Qbar) (e : PkgI3.AbVar.Hom (bcC ιe A₀) A)
      (e' : PkgI3.AbVar.Hom A (bcC ιe A₀)), e.hom ≫ e'.hom = 𝟙 _ ∧ e'.hom ≫ e.hom = 𝟙 _

/-- **LEAF (textbook: torsion points over an algebraically closed field are rational).** For an
abelian variety `A₀` over `ℚ̄` and `ιe : ℚ̄ → ℂ`, every torsion point `v ∈ A₀(ℂ)` (as a `ℂ`-point of the
base change) is the image of a unique point `v₀ ∈ A₀(ℚ̄)`.

Published: `A₀[n]` is a finite étale group scheme of order `n^{2g}` over `ℚ̄` (Mumford, *Abelian
varieties*, §4 (iv) and §6 Application 2; Milne, *Abelian varieties*, §8; UNVERIFIED numbers), hence
constant, so `A₀[n](ℚ̄) = A₀[n](ℂ)`; uniqueness is `A₀(ℚ̄) ↪ A₀(ℂ)`. (Also a consequence of the kernel's
T5 `TorsionStructure` and the injectivity of `A₀(ℚ̄) → A₀(ℂ)`, by counting.) -/
def TorsionDescends : Prop :=
  ∀ (ιe : Qbar →+* ℂ) (A₀ : PkgI3.AbVar Qbar) (v : (bcC ιe A₀).Pt ℂ) (n : ℕ), 0 < n → v ^ n = 1 →
    ∃! v₀ : A₀.Pt Qbar,
      v.left ≫ (pullback.fst A₀.X.hom (Spec.map (CommRingCat.ofHom ιe)) : _ ⟶ A₀.X.left) =
        Spec.map (CommRingCat.ofHom ιe) ≫ v₀.left

section Glue

variable (ιe : Qbar →+* ℂ) (A₀ : PkgI3.AbVar Qbar)

/-- `endBC` along `ιe`. -/
noncomputable abbrev endBCe : PkgI3.AbVar.End A₀ →+* PkgI3.AbVar.End (bcC ιe A₀) :=
  @G0ModField.KernelField.endBC Qbar _ A₀ ℂ _ ιe.toAlgebra

theorem endBCe_bijective (hR : ZInQ.LeafPush2.T11b_Rigidity) : Function.Bijective (endBCe ιe A₀) := by
  letI : Algebra Qbar ℂ := ιe.toAlgebra
  refine ⟨G0ModField.KernelField.endBC_injective A₀ ℂ, fun g => ?_⟩
  obtain ⟨φ, ⟨hφ, hφe⟩, -⟩ := hR Qbar ℂ A₀ A₀ g.hom inferInstance
  refine ⟨PkgI3.AbVar.Hom.mk' φ, PkgI3.AbVar.Hom.ext' ?_⟩
  exact hφe


section Conj

variable {A B : PkgI3.AbVar ℂ} (e : PkgI3.AbVar.Hom B A) (e' : PkgI3.AbVar.Hom A B)
  (h1 : e.hom ≫ e'.hom = 𝟙 _) (h2 : e'.hom ≫ e.hom = 𝟙 _)

/-- Conjugation `End A → End B`, `f ↦ e ≫ f ≫ e'`. -/
noncomputable def conjE : PkgI3.AbVar.End A →+* PkgI3.AbVar.End B where
  toFun f := PkgI3.AbVar.Hom.mk' (e.hom ≫ f.hom ≫ e'.hom)
  map_one' := by
    apply PkgI3.AbVar.Hom.ext'
    change e.hom ≫ 𝟙 _ ≫ e'.hom = 𝟙 _
    rw [Category.id_comp, h1]
  map_mul' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change e.hom ≫ (g.hom ≫ f.hom) ≫ e'.hom =
      (e.hom ≫ g.hom ≫ e'.hom) ≫ (e.hom ≫ f.hom ≫ e'.hom)
    simp only [Category.assoc]
    rw [reassoc_of% h2]
  map_zero' := by
    apply PkgI3.AbVar.Hom.ext'
    change e.hom ≫ (1 : A.X ⟶ A.X) ≫ e'.hom = 1
    rw [MonObj.one_comp, MonObj.comp_one]
  map_add' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change e.hom ≫ (f.hom * g.hom) ≫ e'.hom = (e.hom ≫ f.hom ≫ e'.hom) * (e.hom ≫ g.hom ≫ e'.hom)
    rw [MonObj.mul_comp, MonObj.comp_mul]

theorem conjE_hom (f : PkgI3.AbVar.End A) :
    (conjE e e' h1 h2 f).hom = e.hom ≫ f.hom ≫ e'.hom := rfl

theorem conjE_injective : Function.Injective (conjE e e' h1 h2) := by
  intro f g hfg
  apply PkgI3.AbVar.Hom.ext'
  have := congrArg PkgI3.AbVar.Hom.hom hfg
  rw [conjE_hom, conjE_hom] at this
  have h' := congrArg (fun t => e'.hom ≫ t ≫ e.hom) this
  simp only [Category.assoc] at h'
  simpa only [reassoc_of% h2, h2, Category.comp_id] using h'

end Conj


/-- The projection of the base change. -/
noncomputable abbrev fstC : (bcC ιe A₀).X.left ⟶ A₀.X.left :=
  pullback.fst A₀.X.hom (Spec.map (CommRingCat.ofHom ιe))

theorem bc_map_fst (φ : A₀.X ⟶ A₀.X) :
    (@Over.pullback _ _ _ _ (Spec.map (CommRingCat.ofHom (@algebraMap Qbar ℂ _ _ ιe.toAlgebra))) _
      |>.map φ).left ≫ fstC ιe A₀ = fstC ιe A₀ ≫ φ.left := by
  exact pullback.lift_fst _ _ _

theorem pb_map_fst {X Y : Over (Spec (CommRingCat.of Qbar))} (k : X ⟶ Y) :
    ((Over.pullback (Spec.map (CommRingCat.ofHom ιe))).map k).left ≫
      pullback.fst Y.hom (Spec.map (CommRingCat.ofHom ιe)) =
      pullback.fst X.hom (Spec.map (CommRingCat.ofHom ιe)) ≫ k.left :=
  pullback.lift_fst _ _ _

theorem endBCe_fst (f : PkgI3.AbVar.End A₀) :
    (endBCe ιe A₀ f).hom.left ≫ fstC ιe A₀ = fstC ιe A₀ ≫ f.hom.left :=
  bc_map_fst ιe A₀ f.hom

theorem bc_isPullback :
    IsPullback (fstC ιe A₀) (bcC ιe A₀).X.hom A₀.X.hom (Spec.map (CommRingCat.ofHom ιe)) :=
  IsPullback.of_hasPullback _ _

theorem eta_bc_fst : η[(bcC ιe A₀).X].left ≫ fstC ιe A₀ =
    Spec.map (CommRingCat.ofHom ιe) ≫ η[A₀.X].left := by
  letI : Algebra Qbar ℂ := ιe.toAlgebra
  change (Functor.LaxMonoidal.ε (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))) ≫
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))).map η[A₀.X]).left ≫
      fstC ιe A₀ = _
  rw [Over.comp_left, Category.assoc]
  erw [pb_map_fst ιe η[A₀.X]]
  rw [← Category.assoc]
  congr 1
  have hc : pullback.fst (𝟙_ (Over (Spec (CommRingCat.of Qbar)))).hom
      (Spec.map (CommRingCat.ofHom ιe)) ≫ (𝟙_ (Over (Spec (CommRingCat.of Qbar)))).hom =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ιe) := pullback.condition
  have hw := Over.w (Functor.LaxMonoidal.ε
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))))
  have h1 : (𝟙_ (Over (Spec (CommRingCat.of Qbar)))).hom = 𝟙 _ := rfl
  rw [h1, Category.comp_id] at hc
  erw [hc, ← Category.assoc]
  erw [hw]
  exact Category.id_comp _


/-- `ℂ`-points of the base change are determined by their projection to `A₀`. -/
theorem ptC_ext {u u' : (bcC ιe A₀).Pt ℂ} (h : u.left ≫ fstC ιe A₀ = u'.left ≫ fstC ιe A₀) :
    u = u' := by
  ext1
  exact (bc_isPullback ιe A₀).hom_ext h (by rw [Over.w u, Over.w u'])

/-- The identity points correspond. -/
theorem one_corr : (1 : (bcC ιe A₀).Pt ℂ).left ≫ fstC ιe A₀ =
    Spec.map (CommRingCat.ofHom ιe) ≫ (1 : A₀.Pt Qbar).left := by
  rw [Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left,
    PeriodGlue.ptObj_hom_self, PeriodGlue.ptObj_hom_self']
  erw [Category.id_comp, Category.id_comp]
  exact eta_bc_fst ιe A₀

/-- Endomorphisms act compatibly on corresponding points. -/
theorem endBCe_corr (f : PkgI3.AbVar.End A₀) {w : (bcC ιe A₀).Pt ℂ} {w₀ : A₀.Pt Qbar}
    (hw : w.left ≫ fstC ιe A₀ = Spec.map (CommRingCat.ofHom ιe) ≫ w₀.left) :
    (w ≫ (endBCe ιe A₀ f).hom).left ≫ fstC ιe A₀ =
      Spec.map (CommRingCat.ofHom ιe) ≫ (w₀ ≫ f.hom).left := by
  rw [Over.comp_left, Category.assoc, endBCe_fst, ← Category.assoc, hw, Over.comp_left]
  exact Category.assoc _ _ _

end Glue

/-- Isomorphic abelian varieties have the same dimension. -/
theorem dim_eq_of_iso {B A : PkgI3.AbVar ℂ} (e : PkgI3.AbVar.Hom B A) (e' : PkgI3.AbVar.Hom A B)
    (h1 : e.hom ≫ e'.hom = 𝟙 _) (h2 : e'.hom ≫ e.hom = 𝟙 _) : B.dim = A.dim := by
  obtain ⟨i⟩ : Nonempty (B.X.left ≅ A.X.left) := ⟨
    { hom := e.hom.left
      inv := e'.hom.left
      hom_inv_id := by rw [← Over.comp_left, h1, Over.id_left]
      inv_hom_id := by rw [← Over.comp_left, h2, Over.id_left] }⟩
  exact IsHomeomorph.topologicalKrullDim_eq _ i.hom.homeomorph.isHomeomorph

section Glue2



/-- `#A(k)[n] = n^{2g}` over an algebraically closed field of characteristic 0, from T5. -/
theorem card_torsion_algClosed (hT : PkgI2.TorsionStructure.{0}) {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] (A : PkgI3.AbVar k) (g : ℕ) (hg : A.dim = g) (n : ℕ) (hn : 0 < n) :
    Nat.card {x : A.Pt k // x ^ n = 1} = n ^ (2 * g) := by
  obtain ⟨e, -⟩ := hT k (ObjBridge.toGrp A) g n hg hn (by exact_mod_cast hn.ne')
  let φ : AlgebraicClosure k ≃ₐ[k] k :=
    (AlgEquiv.ofBijective (Algebra.ofId k (AlgebraicClosure k))
      IsAlgClosed.algebraMap_bijective_of_isIntegral).symm
  have h1 : Nat.card {x : A.Pt (AlgebraicClosure k) // x ^ n = 1} = n ^ (2 * g) := by
    have : Nat.card {x : A.Pt (AlgebraicClosure k) // x ^ n = 1} =
        Nat.card (PkgI2.torsion (ObjBridge.toGrp A) (AlgebraicClosure k) n) := rfl
    rw [this, Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  rw [← h1]
  exact Nat.card_congr ((UnramTate.trPt A φ).toEquiv.subtypeEquiv (fun x => by
    change x ^ n = 1 ↔ (UnramTate.trPt A φ x) ^ n = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff])).symm

/-- **`TorsionDescends` from T5 (proved).** `A₀(ℚ̄)[n] → A₀,ℂ(ℂ)[n]` is injective between sets of
`n^{2g}` elements. -/
theorem torsionDescends_of_t5 (hT : PkgI2.TorsionStructure.{0}) : TorsionDescends := by
  intro ιe A₀ v n hn hv
  letI : Algebra Qbar ℂ := ιe.toAlgebra
  obtain ⟨g, hg⟩ := PkgI3.AbVar.dim_finite A₀
  let κ : Qbar →ₐ[Qbar] ℂ := Algebra.ofId Qbar ℂ
  let ψ : A₀.Pt Qbar →* (bcC ιe A₀).Pt ℂ :=
    (E1Sub.bcPt ℂ A₀ ℂ).comp (ZInQ.Contrib.AbVarBC.extPt A₀ κ)
  have hψfst : ∀ p, (ψ p).left ≫ fstC ιe A₀ = Spec.map (CommRingCat.ofHom ιe) ≫ p.left := by
    intro p
    change (E1Sub.bcPt ℂ A₀ ℂ (ZInQ.Contrib.AbVarBC.extPt A₀ κ p)).left ≫ _ = _
    erw [E1Sub.bcPt_fst]
    rw [ZInQ.Contrib.AbVarBC.extPt_apply, Over.comp_left, ZInQ.Contrib.AbVarBC.extHom_left]
    rfl
  have hψinj : Function.Injective ψ :=
    (E1Sub.bcPt_injective A₀ ℂ).comp (ZInQ.Contrib.AbVarBC.extPt_injective A₀ κ)
  let ψn : {x : A₀.Pt Qbar // x ^ n = 1} → {x : (bcC ιe A₀).Pt ℂ // x ^ n = 1} :=
    fun x => ⟨ψ x.1, by rw [← map_pow, x.2, map_one]⟩
  have hinj : Function.Injective ψn := fun x y h => Subtype.ext (hψinj (congrArg Subtype.val h))
  have c0 := card_torsion_algClosed hT A₀ g hg n hn
  have c1 := card_torsion_algClosed hT (bcC ιe A₀) g
    ((@PkgI3.AbVar.dim_baseChange Qbar _ A₀ ℂ _ ιe.toAlgebra).trans hg) n hn
  haveI : Finite {x : (bcC ιe A₀).Pt ℂ // x ^ n = 1} :=
    Nat.finite_of_card_ne_zero (by rw [c1]; positivity)
  have hbij : Function.Bijective ψn := hinj.bijective_of_nat_card_le (by rw [c0, c1])
  obtain ⟨⟨v₀, hv₀⟩, hψv⟩ := hbij.2 ⟨v, hv⟩
  have hψv' : ψ v₀ = v := congrArg Subtype.val hψv
  refine ⟨v₀, by rw [← hψv']; exact hψfst v₀, fun v₀' hv₀' => hψinj ?_⟩
  rw [hψv']
  apply ptC_ext ιe A₀
  rw [hψfst]
  exact hv₀'.symm

/-- **The descended data** (glue, proved). -/
theorem descend_main (hST : STQM) (hR : ZInQ.LeafPush2.T11b_Rigidity) (hTD : TorsionDescends)
    (hRep : LeafAdopt.R1R2fpRep) (Q : QML3 ℂ) (hcm : HasCM4 Q.q ∨ HasCM3 Q.q ∨ HasCM24 Q.q) :
    ∃ (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q' : QML3 ℂ)
      (κ : PkgI3.AbVar.End Q.A →+* PkgI3.AbVar.End P.A),
      IsBaseChangeOf ιe P Q' ∧ Nonempty (QMIso Q.q Q'.q) ∧ ∀ a, κ (Q.q.iota a) = P.q.iota a := by
  obtain ⟨ιe, A₀, e, e', h1, h2⟩ := hST Q.A Q.q Q.surface hcm
  let β := RingEquiv.ofBijective (endBCe ιe A₀) (endBCe_bijective ιe A₀ hR)
  let κ : PkgI3.AbVar.End Q.A →+* PkgI3.AbVar.End A₀ := β.symm.toRingHom.comp (conjE e e' h1 h2)
  have hβκ : ∀ f, endBCe ιe A₀ (κ f) = conjE e e' h1 h2 f := fun f => β.apply_symm_apply _
  have κinj : Function.Injective κ := β.symm.injective.comp (conjE_injective e e' h1 h2)
  let q₀ : QMStr A₀ := ⟨κ.comp Q.q.iota, κinj.comp Q.q.injective⟩
  have hdim : A₀.dim = 2 := by
    have := dim_eq_of_iso e e' h1 h2
    rw [← Q.surface, ← this]
    exact (@PkgI3.AbVar.dim_baseChange Qbar _ A₀ ℂ _ ιe.toAlgebra).symm
  -- the level structure
  let v : (bcC ιe A₀).Pt ℂ := Additive.toMul (Q.e.eta 1) ≫ e'.hom
  have hv3 : v ^ 3 = 1 := by
    have h30 : Q.e.eta 3 = 0 := (Q.e.ker 3).2 ⟨1, by rw [_root_.mul_one]⟩
    have h3 : (Additive.toMul (Q.e.eta 1)) ^ 3 = 1 := by
      rw [← toMul_nsmul, ← map_nsmul, nsmul_eq_mul, _root_.mul_one]
      push_cast
      rw [h30]; rfl
    change (IsMonHom.monoidHom e'.hom _ (Additive.toMul (Q.e.eta 1))) ^ 3 = 1
    rw [← map_pow, h3, map_one]
  obtain ⟨v₀, hv₀, huniq⟩ := hTD ιe A₀ v 3 (by norm_num) hv3
  let η₀ : LeafQM.O →+ Additive (A₀.Pt Qbar) :=
    { toFun := fun a => qmAct q₀ Qbar a (Additive.ofMul v₀)
      map_zero' := by rw [map_zero]; rfl
      map_add' := fun a b => by rw [map_add]; rfl }
  have hη₀ : ∀ a, Additive.toMul (η₀ a) = v₀ ≫ (q₀.iota a).hom := fun a => rfl
  have lin : ∀ a b : LeafQM.O, η₀ (a * b) = qmAct q₀ Qbar a (η₀ b) := fun a b => by
    change qmAct q₀ Qbar (a * b) _ = _
    rw [map_mul]; rfl
  have ker : ∀ a : LeafQM.O, η₀ a = 0 ↔ ∃ b : LeafQM.O, a = 3 * b := by
    intro a
    have hw : v ≫ (endBCe ιe A₀ (q₀.iota a)).hom = Additive.toMul (Q.e.eta a) ≫ e'.hom := by
      rw [show q₀.iota a = κ (Q.q.iota a) from rfl, hβκ, conjE_hom]
      have hl := Q.e.linear a 1
      rw [_root_.mul_one] at hl
      have : Additive.toMul (Q.e.eta a) = Additive.toMul (Q.e.eta 1) ≫ (Q.q.iota a).hom := by
        rw [hl]; rfl
      rw [this]
      simp only [v, Category.assoc]
      rw [reassoc_of% h2]
    have hcorr := endBCe_corr ιe A₀ (q₀.iota a) hv₀
    constructor
    · intro h0
      have h0' : v₀ ≫ (q₀.iota a).hom = 1 := by rw [← hη₀, h0]; rfl
      have h1' : v ≫ (endBCe ιe A₀ (q₀.iota a)).hom = 1 :=
        ptC_ext ιe A₀ (by rw [hcorr, h0', one_corr])
      rw [hw] at h1'
      have h3 : Additive.toMul (Q.e.eta a) = 1 := by
        have := congrArg (· ≫ e.hom) h1'
        simp only [Category.assoc, h2, Category.comp_id] at this
        rw [this, MonObj.one_comp]
      exact (Q.e.ker a).1 h3
    · intro hb
      have h3 : Q.e.eta a = 0 := (Q.e.ker a).2 hb
      have h1' : v ≫ (endBCe ιe A₀ (q₀.iota a)).hom = 1 := by
        rw [hw, show Additive.toMul (Q.e.eta a) = 1 from congrArg Additive.toMul h3, MonObj.one_comp]
      obtain ⟨_, _, hu1⟩ := hTD ιe A₀ 1 1 one_pos (one_pow _)
      have e1 := hu1 (v₀ ≫ (q₀.iota a).hom) (by rw [← h1']; exact hcorr)
      have e2 := hu1 1 (one_corr ιe A₀)
      have : Additive.toMul (η₀ a) = 1 := by rw [hη₀, e1, ← e2]
      exact congrArg Additive.ofMul this
  let P : QML3 Qbar := ⟨A₀, hdim, q₀, ⟨η₀, lin, ker⟩⟩
  -- the base change from R1fp's naturality
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, hR1, -⟩ := hRep
  obtain ⟨Q', -, hBC⟩ := hR1.2.2.2.1 Qbar ℂ ιe.toRatAlgHom ((Φ Qbar).symm (M3.mk P)) P (by simp)
  have hBC' : IsBaseChangeOf ιe P Q' := hBC
  refine ⟨ιe, P, Q', κ, hBC', ?_, fun a => rfl⟩
  obtain ⟨g', hg', hι', hl'⟩ := hBC'
  -- comparison `Q'.A ≅ A₀ ×_{ℚ̄} ℂ`
  let θ : Q'.A.X ⟶ (bcC ιe A₀).X :=
    Over.homMk ((bc_isPullback ιe A₀).lift g' Q'.A.X.hom hg'.w) ((bc_isPullback ιe A₀).lift_snd _ _ _)
  let θ' : (bcC ιe A₀).X ⟶ Q'.A.X :=
    Over.homMk (hg'.lift (fstC ιe A₀) (bcC ιe A₀).X.hom (bc_isPullback ιe A₀).w) (hg'.lift_snd _ _ _)
  have hθ : θ.left ≫ fstC ιe A₀ = g' := (bc_isPullback ιe A₀).lift_fst _ _ _
  have hθ' : θ'.left ≫ g' = fstC ιe A₀ := hg'.lift_fst _ _ _
  have hθθ' : θ ≫ θ' = 𝟙 _ := by
    ext1
    exact hg'.hom_ext (by rw [Over.comp_left, Category.assoc, hθ', hθ]; simp)
      (by rw [Over.comp_left, Category.assoc, Over.w θ', Over.w θ]; simp)
  have hθ'θ : θ' ≫ θ = 𝟙 _ := by
    ext1
    exact (bc_isPullback ιe A₀).hom_ext (by rw [Over.comp_left, Category.assoc, hθ, hθ']; simp)
      (by rw [Over.comp_left, Category.assoc, Over.w θ, Over.w θ']; simp)
  have hη : η[Q'.A.X] ≫ θ = η[(bcC ιe A₀).X] := by
    ext1
    refine (bc_isPullback ιe A₀).hom_ext ?_ ?_
    · rw [Over.comp_left, Category.assoc, hθ, PeriodGlue.eta_comp hl', eta_bc_fst]
    · rw [Over.comp_left, Category.assoc, Over.w θ, Over.w η[Q'.A.X], Over.w η[(bcC ιe A₀).X]]
  have hη' : η[(bcC ιe A₀).X] ≫ θ' = η[Q'.A.X] := by
    rw [← hη, Category.assoc, hθθ', Category.comp_id]
  haveI : IsMonHom θ :=
    _root_.HDec.PeriodGlue.MulRigidity.isMonHom_of_geometricallyIntegral Q'.A.X (bcC ιe A₀).X θ hη
  haveI : IsMonHom θ' :=
    _root_.HDec.PeriodGlue.MulRigidity.isMonHom_of_geometricallyIntegral (bcC ιe A₀).X Q'.A.X θ' hη'
  let qC : QMStr (bcC ιe A₀) :=
    ⟨(endBCe ιe A₀).comp q₀.iota, (endBCe_bijective ιe A₀ hR).1.comp q₀.injective⟩
  let iso1 : QMIso Q.q qC :=
    { φ := e'
      ψ := e
      left := h2
      right := h1
      equivariant := fun a => by
        change _ = e'.hom ≫ (endBCe ιe A₀ (κ (Q.q.iota a))).hom
        rw [hβκ, conjE_hom, reassoc_of% h2] }
  let iso2 : QMIso Q'.q qC :=
    { φ := PkgI3.AbVar.Hom.mk' θ
      ψ := PkgI3.AbVar.Hom.mk' θ'
      left := by simpa using hθθ'
      right := by simpa using hθ'θ
      equivariant := fun a => by
        simp only [PkgI3.AbVar.Hom.hom_mk']
        ext1
        refine (bc_isPullback ιe A₀).hom_ext ?_ ?_
        · change ((Q'.q.iota a).hom.left ≫ θ.left) ≫ fstC ιe A₀ =
            (θ.left ≫ (endBCe ιe A₀ (q₀.iota a)).hom.left) ≫ fstC ιe A₀
          rw [Category.assoc, hθ, hι' a, Category.assoc, endBCe_fst, ← Category.assoc, hθ]
        · simp [Over.w] }
  exact ⟨iso1.trans iso2.symm⟩

/-- **`CMDescends` from `STQM`, `T11b_Rigidity`, `TorsionDescends` and `R1R2fpRep` (proved).** -/
theorem cmDescends_of (hST : STQM) (hR : ZInQ.LeafPush2.T11b_Rigidity) (hTD : TorsionDescends)
    (hRep : LeafAdopt.R1R2fpRep) : CMDescends := by
  intro Q
  have com_of : ∀ (P : QML3 Qbar) (κ : PkgI3.AbVar.End Q.A →+* PkgI3.AbVar.End P.A),
      (∀ a, κ (Q.q.iota a) = P.q.iota a) → ∀ φ ∈ com Q.q, κ φ ∈ com P.q := by
    intro P κ hκ φ hφ
    rw [com, Subring.mem_centralizer_iff] at hφ ⊢
    rintro _ ⟨a, rfl⟩
    rw [← hκ, ← map_mul, ← map_mul, hφ _ ⟨a, rfl⟩]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨ιe, P, Q', κ, hBC, hiso, hκ⟩ := descend_main hST hR hTD hRep Q (Or.inl h)
    obtain ⟨φ, hφ, hφ2⟩ := h
    exact ⟨ιe, P, Q', hBC, ⟨κ φ, com_of P κ hκ φ hφ, by rw [← map_mul, hφ2, map_neg, map_one]⟩, hiso⟩
  · obtain ⟨ιe, P, Q', κ, hBC, hiso, hκ⟩ := descend_main hST hR hTD hRep Q (Or.inr (Or.inl h))
    obtain ⟨φ, hφ, hφ2⟩ := h
    exact ⟨ιe, P, Q', hBC, ⟨κ φ, com_of P κ hκ φ hφ, by
      rw [← map_mul, ← map_sub, ← map_one κ, ← map_add, hφ2, map_zero]⟩, hiso⟩
  · obtain ⟨ιe, P, Q', κ, hBC, hiso, hκ⟩ := descend_main hST hR hTD hRep Q (Or.inr (Or.inr h))
    obtain ⟨φ, hφ, hφ2⟩ := h
    exact ⟨ιe, P, Q', hBC, ⟨κ φ, com_of P κ hκ φ hφ, by rw [← map_mul, hφ2, map_neg, map_ofNat]⟩,
      hiso⟩

end Glue2

end LeafQCheck

end HDec.HSyn.G0Split.FibreQM.PeriodMapH


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


namespace HDec.HSyn

/-- leaf-fold4's `OpenAddedLeaves4` without `gammaStarGen` (proved: `LeafQCheck.gammaStarGen_proof`). -/
structure OpenAddedLeavesQ5 : Prop where
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

theorem openAddedLeaves4_of_Q5 (l : OpenAddedLeavesQ5) : OpenAddedLeaves4 :=
  ⟨l.cmOptimalEmbedding, l.thetaRatiosAlgebraic, l.qmHauptmodul, l.qmClassNumberOne, l.senTwist,
    l.finiteImageHT, l.t09SymmIsogenyExists, l.isogenyQuasiInverse, l.x6ConicModel, l.y3Connected,
    l.qmAutCard, l.serreRigidity3, l.alFixedPoints, l.zariskiConnectedness, l.cmDescends,
    LeafQCheck.gammaStarGen_proof, l.valenceBoundGammaStar, l.egaIV_8_8_2_ii, l.egaIV_8_10_5_xii,
    l.egaIV_17_7_8_ii⟩

/-- **`SixContactMin` from 26 + 19 + 19 leaves and one glue Prop** (leaf-fold4's 66 fields minus
`gammaStarGen`). -/
theorem sixContactMin_of_openQ5 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4)
    (l : OpenAddedLeavesQ5) (g : OpenGlue4) : ZInQ.SixContactMin :=
  sixContactMin_of_open4 r t (openAddedLeaves4_of_Q5 l) g

/-- `OpenAddedLeavesQ5` with `valenceBoundGammaStar` (LEAF?) replaced by the published valence formula
`ValenceFormulaGammaStar` (LEAF; `e_P ≤ 6` is proved, `LeafQCheck.VB.ellipticOrderLe6_proof`). -/
structure OpenAddedLeavesQ6 : Prop where
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
  valenceFormulaGammaStar : LeafQCheck.VB.ValenceFormulaGammaStar
  egaIV_8_8_2_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  egaIV_17_7_8_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii

theorem openAddedLeavesQ5_of_Q6 (l : OpenAddedLeavesQ6) : OpenAddedLeavesQ5 :=
  ⟨l.cmOptimalEmbedding, l.thetaRatiosAlgebraic, l.qmHauptmodul, l.qmClassNumberOne, l.senTwist,
    l.finiteImageHT, l.t09SymmIsogenyExists, l.isogenyQuasiInverse, l.x6ConicModel, l.y3Connected,
    l.qmAutCard, l.serreRigidity3, l.alFixedPoints, l.zariskiConnectedness, l.cmDescends,
    LeafQCheck.VB.valenceBound_of_formula l.valenceFormulaGammaStar, l.egaIV_8_8_2_ii,
    l.egaIV_8_10_5_xii, l.egaIV_17_7_8_ii⟩

/-- **`SixContactMin` from 26 + 19 + 19 leaves and one glue Prop, with the valence formula in its
published form.** -/
theorem sixContactMin_of_openQ6 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4)
    (l : OpenAddedLeavesQ6) (g : OpenGlue4) : ZInQ.SixContactMin :=
  sixContactMin_of_openQ5 r t (openAddedLeavesQ5_of_Q6 l) g


/-- `OpenAddedLeavesQ6` with `cmDescends` (LEAF?) replaced by `STQM` (LEAF, Shimura–Taniyama);
the glue uses the bundle leaves `r1r2`, `t11b`, `t5` (`PeriodMapH.LeafQCheck.cmDescends_of`,
`torsionDescends_of_t5`). -/
structure OpenAddedLeavesQ7 : Prop where
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
  stQM : G0Split.FibreQM.PeriodMapH.LeafQCheck.STQM
  valenceFormulaGammaStar : LeafQCheck.VB.ValenceFormulaGammaStar
  egaIV_8_8_2_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  egaIV_17_7_8_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii

/-- **`SixContactMin` from 26 + 19 + 19 leaves and one glue Prop, with `CMDescends` replaced by the
published Shimura–Taniyama statement `STQM`.** -/
theorem sixContactMin_of_openQ7 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4)
    (l : OpenAddedLeavesQ7) (g : OpenGlue4) : ZInQ.SixContactMin :=
  sixContactMin_of_openQ6 r t
    ⟨l.cmOptimalEmbedding, l.thetaRatiosAlgebraic, l.qmHauptmodul, l.qmClassNumberOne, l.senTwist,
      l.finiteImageHT, l.t09SymmIsogenyExists, l.isogenyQuasiInverse, l.x6ConicModel, l.y3Connected,
      l.qmAutCard, l.serreRigidity3, l.alFixedPoints, l.zariskiConnectedness,
      G0Split.FibreQM.PeriodMapH.LeafQCheck.cmDescends_of l.stQM t.t11b
        (G0Split.FibreQM.PeriodMapH.LeafQCheck.torsionDescends_of_t5 t.t5) r.r1r2,
      l.valenceFormulaGammaStar, l.egaIV_8_8_2_ii, l.egaIV_8_10_5_xii, l.egaIV_17_7_8_ii⟩ g


/-- `OpenAddedLeavesQ7` with `qmHauptmodul` (LEAF?) replaced by the narrowed `QMHauptmodulBase` (its CM
clauses at one point each; `LeafQCheck.HM.qmHauptmodul_of_base`). -/
structure OpenAddedLeavesQ8 : Prop where
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  qmHauptmodulBase : LeafQCheck.HM.QMHauptmodulBase
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
  stQM : G0Split.FibreQM.PeriodMapH.LeafQCheck.STQM
  valenceFormulaGammaStar : LeafQCheck.VB.ValenceFormulaGammaStar
  egaIV_8_8_2_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  egaIV_17_7_8_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii

/-- **`SixContactMin` from 26 + 19 + 19 leaves and one glue Prop** (leafq-check's final form: no
`gammaStarGen`; the valence formula, Shimura–Taniyama and the narrowed Hauptmodul in place of three
LEAF? fields). -/
theorem sixContactMin_of_openQ8 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4)
    (l : OpenAddedLeavesQ8) (g : OpenGlue4) : ZInQ.SixContactMin :=
  sixContactMin_of_openQ7 r t
    ⟨l.cmOptimalEmbedding, l.thetaRatiosAlgebraic,
      LeafQCheck.HM.qmHauptmodul_of_base l.qmHauptmodulBase, l.qmClassNumberOne, l.senTwist,
      l.finiteImageHT, l.t09SymmIsogenyExists, l.isogenyQuasiInverse, l.x6ConicModel, l.y3Connected,
      l.qmAutCard, l.serreRigidity3, l.alFixedPoints, l.zariskiConnectedness, l.stQM,
      l.valenceFormulaGammaStar, l.egaIV_8_8_2_ii, l.egaIV_8_10_5_xii, l.egaIV_17_7_8_ii⟩ g


/-- `OpenAddedLeavesQ8` with `qmHauptmodulBase` replaced by `QMHauptmodulBase2` (no disc −4 clause:
`j_θ(√2+i) = 0` is a computation, `LeafQCheck.HM.base_of_base2`). -/
structure OpenAddedLeavesQ9 : Prop where
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  qmHauptmodulBase2 : LeafQCheck.HM.QMHauptmodulBase2
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
  stQM : G0Split.FibreQM.PeriodMapH.LeafQCheck.STQM
  valenceFormulaGammaStar : LeafQCheck.VB.ValenceFormulaGammaStar
  egaIV_8_8_2_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  egaIV_17_7_8_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii

/-- **`SixContactMin` from 26 + 19 + 19 leaves and one glue Prop** (leafq-check's final form). -/
theorem sixContactMin_of_openQ9 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4)
    (l : OpenAddedLeavesQ9) (g : OpenGlue4) : ZInQ.SixContactMin :=
  sixContactMin_of_openQ8 r t
    ⟨l.cmOptimalEmbedding, l.thetaRatiosAlgebraic,
      LeafQCheck.HM.base_of_base2 l.qmHauptmodulBase2, l.qmClassNumberOne, l.senTwist,
      l.finiteImageHT, l.t09SymmIsogenyExists, l.isogenyQuasiInverse, l.x6ConicModel, l.y3Connected,
      l.qmAutCard, l.serreRigidity3, l.alFixedPoints, l.zariskiConnectedness, l.stQM,
      l.valenceFormulaGammaStar, l.egaIV_8_8_2_ii, l.egaIV_8_10_5_xii, l.egaIV_17_7_8_ii⟩ g


/-- `OpenAddedLeavesQ9` with `qmHauptmodulBase2` replaced by `QMHauptmodulBase3` (no disc −3 clause: the
pole at `i√3` follows from R4, `GammaStarGen` and the valence bound, `LeafQCheck.HM.base2_of_base3`). -/
structure OpenAddedLeavesQ10 : Prop where
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  qmHauptmodulBase3 : LeafQCheck.HM.QMHauptmodulBase3
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
  stQM : G0Split.FibreQM.PeriodMapH.LeafQCheck.STQM
  valenceFormulaGammaStar : LeafQCheck.VB.ValenceFormulaGammaStar
  egaIV_8_8_2_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  egaIV_17_7_8_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii

/-- **`SixContactMin` from 26 + 19 + 19 leaves and one glue Prop** (leafq-check's final form). -/
theorem sixContactMin_of_openQ10 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4)
    (l : OpenAddedLeavesQ10) (g : OpenGlue4) : ZInQ.SixContactMin :=
  sixContactMin_of_openQ9 r t
    ⟨l.cmOptimalEmbedding, l.thetaRatiosAlgebraic,
      LeafQCheck.HM.base2_of_base3 r.r4 LeafQCheck.gammaStarGen_proof
        (LeafQCheck.VB.valenceBound_of_formula l.valenceFormulaGammaStar) l.qmHauptmodulBase3,
      l.qmClassNumberOne, l.senTwist,
      l.finiteImageHT, l.t09SymmIsogenyExists, l.isogenyQuasiInverse, l.x6ConicModel, l.y3Connected,
      l.qmAutCard, l.serreRigidity3, l.alFixedPoints, l.zariskiConnectedness, l.stQM,
      l.valenceFormulaGammaStar, l.egaIV_8_8_2_ii, l.egaIV_8_10_5_xii, l.egaIV_17_7_8_ii⟩ g

end HDec.HSyn

example : ∀ (_ : HDec.HSyn.OpenResearchLeaves2) (_ : HDec.HSyn.OpenTextbookLeaves4)
    (_ : HDec.HSyn.OpenAddedLeavesQ5) (_ : HDec.HSyn.OpenGlue4), _root_.ZInQ.SixContactMin :=
  HDec.HSyn.sixContactMin_of_openQ5

example : ∀ (_ : HDec.HSyn.OpenResearchLeaves2) (_ : HDec.HSyn.OpenTextbookLeaves4)
    (_ : HDec.HSyn.OpenAddedLeavesQ7) (_ : HDec.HSyn.OpenGlue4), _root_.ZInQ.SixContactMin :=
  HDec.HSyn.sixContactMin_of_openQ7

example : ∀ (_ : HDec.HSyn.OpenResearchLeaves2) (_ : HDec.HSyn.OpenTextbookLeaves4)
    (_ : HDec.HSyn.OpenAddedLeavesQ8) (_ : HDec.HSyn.OpenGlue4), _root_.ZInQ.SixContactMin :=
  HDec.HSyn.sixContactMin_of_openQ8

example : ∀ (_ : HDec.HSyn.OpenResearchLeaves2) (_ : HDec.HSyn.OpenTextbookLeaves4)
    (_ : HDec.HSyn.OpenAddedLeavesQ9) (_ : HDec.HSyn.OpenGlue4), _root_.ZInQ.SixContactMin :=
  HDec.HSyn.sixContactMin_of_openQ9

example : ∀ (_ : HDec.HSyn.OpenResearchLeaves2) (_ : HDec.HSyn.OpenTextbookLeaves4)
    (_ : HDec.HSyn.OpenAddedLeavesQ10) (_ : HDec.HSyn.OpenGlue4), _root_.ZInQ.SixContactMin :=
  HDec.HSyn.sixContactMin_of_openQ10

#print axioms HDec.LeafQCheck.gammaStarGen_proof
#print axioms HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.cmDescends_of
#print axioms HDec.HSyn.sixContactMin_of_openQ5
#print axioms HDec.LeafQCheck.VB.ellipticOrderLe6_proof
#print axioms HDec.HSyn.sixContactMin_of_openQ6
#print axioms HDec.HSyn.sixContactMin_of_openQ7
#print axioms HDec.LeafQCheck.HM.qmHauptmodul_of_base
#print axioms HDec.HSyn.sixContactMin_of_openQ8
#print axioms HDec.HSyn.sixContactMin_of_openQ9
#print axioms HDec.LeafQCheck.HM.base2_of_base3
#print axioms HDec.HSyn.sixContactMin_of_openQ10

/-! ## leaf-fold6, part f20: leaf-fold5's statement with leafq-check's four reductions, T8 kept as a leaf

Task leaf-fold6, 2026-11-14. Everything above is leaf-fold5's chain (leaf-fold4's `Leaves4.lean` as the olean chain
LPrefix ... TailK, then leaf-fold5's TailL, TailM, TailN) and part f10 (leafq-check's `Fold.lean`, with its own
bundle names suffixed `Q`).

`sixContactMin_of_open6` is leaf-fold4's `sixContactMin_of_open4` applied to leaf-fold4's four bundles, each built
here from leaf-fold6's (as leaf-fold5's `sixContactMin_of_open5` does): every field of leaf-fold4 that changed is a
theorem whose type is the chain's own Prop, so Lean checks that the statements agree.

Changes against leaf-fold5's bundles:
* (a) leafq-check's four reductions of `OpenAddedLeaves5`:
  - `gammaStarGen` dropped: `LeafQCheck.gammaStarGen_proof`;
  - `valenceBoundGammaStar` → `valenceFormulaGammaStar`: `LeafQCheck.VB.valenceBound_of_formula`;
  - `cmDescends` → `stQM`: `PeriodMapH.LeafQCheck.cmDescends_of` with leaf-fold5's versions of its other inputs:
    `t11b := t11b_of_exists5 t.t11bExists` (leaf-fold5 weakened T11(b) to its existence half),
    `t5 := torsionStructure_ofK5 t.t5` (leaf-fold5 restated T5 over the kernel's Prop), `r1r2 := r.r1r2`;
  - `qmHauptmodul` → `qmHauptmodulBase3`: `LeafQCheck.HM.qmHauptmodul_of_base2 ∘ base2_of_base3` with `r.r4`,
    `gammaStarGen_proof` and the valence bound from `valenceFormulaGammaStar`.
* (b) T8 kept as a textbook leaf, over the kernel's own Prop `_root_.PkgI3.PoincareReducibility`
  (`ZInQKernel/HDecomp/Objects.lean`), transported to the chain's copy by `t8_ofK6`; leaf-fold5's
  `poincareComplement` (LEAF) and the glue `simpleImageIsogeny` are not fields. Glue: 1 (`ModelCoordinateResidue`).
  The other choice is `sixContactMin_of_open6_poincare` below (T8 from the kernel's
  `ZInQ.Contrib.AVB1.poincareReducibility_of_simpleImage`; glue 2).
* (c) Every field leaf-fold5 put on a kernel constant stays on it (`OpenResearchLeaves5` is reused unchanged). -/

noncomputable section

namespace HDec.HSyn

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **T8, the chain's copy, from the kernel's Prop** (same statement; the abelian varieties pass by leaf-fold4's
`toAbVarK4`/`ofAbVarK4`, as in leaf-fold5's `t8_of_simpleImage5`). -/
theorem t8_ofK6 (h : _root_.PkgI3.PoincareReducibility) : PkgI3.PoincareReducibility := by
  intro k _ _ A J hA f hf
  obtain ⟨Z, g, hg⟩ := h k (toAbVarK4 A) (toAbVarK4 J) hA f hf
  exact ⟨ofAbVarK4 Z, g, hg⟩

/-- **The textbook leaves still open** (leaf-fold6): leaf-fold5's `OpenTextbookLeaves5` with `poincareComplement`
replaced by T8 itself, `t8 : _root_.PkgI3.PoincareReducibility` (the kernel's Prop; goal (b): this keeps the glue
count at 1). The other 20 fields are leaf-fold5's, with the same types. -/
structure OpenTextbookLeaves6 : Prop where
  /-- neron-c, LEAF: every `K`-morphism of the generic fibres of two abelian schemes over a DVR extends
  (BLR §1.2 Prop. 8, surjective half). -/
  t3Surj : _root_.ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj.{0}
  /-- T4 = I2-Red, reduction is bijective on prime-to-`p` torsion. -/
  t4 : _root_.PkgI2.ReductionTorsionBijective.{0}
  t5 : _root_.PkgI2.TorsionStructure.{0}
  /-- av-b1, LEAF: Mumford §19 Thm 3 over an algebraically closed field. -/
  homFreeFiniteAlgClosed : _root_.ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed
  /-- av-b1, LEAF: Mumford §19 Thm 4 (consequence) over an algebraically closed field. -/
  charPolyIndepOfEllAlgClosed : _root_.ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed
  /-- T8 (I3.M3), Poincaré complete reducibility in the form used at E1, the kernel's Prop. -/
  t8 : _root_.PkgI3.PoincareReducibility
  t10 : _root_.T10Etale.T10_TateDuality
  homLatticeCorr : _root_.ZInQ.HomUnify.HomLatticeCorr
  /-- av-b2, LEAF: T11(b) without its uniqueness clause (Conrad 2006 §3; Milne 1986 §20). -/
  t11bExists : AVB2.T11bExists
  t23 : ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p
  t24 : _root_.PkgI4.EigenformTwist
  t27 : _root_.PkgI3.QMDichotomyYu
  t33 : _root_.LeafModCurves.JacobianExists ℚ
  /-- curves-g: `dim Jac X = genus` for curves over `ℚ` (Milne 1986 Prop. 2.1 with Serre duality). -/
  dimJacobianEqGenus : _root_.ZInQ.Contrib.CurvesG.DimJacobianEqGenus
  /-- curves-g: the genus of `K_N` is the genus of `Γ₁(N)` (Shimura 1971 §6.7 and Prop. 1.40). -/
  genusX1Field : _root_.ZInQ.Contrib.CurvesG.GenusX1Field
  t35 : _root_.ZInQ.LeafPush2.UniformizationExists
  /-- curves-g (A): a normal proper model of a function field over `ℚ(T)` (Stacks 0BXX). -/
  normalModelOfFunctionFieldQ : _root_.ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ
  /-- curves-g (B): a normal integral curve locally of finite type over `ℚ` is smooth. -/
  normalCurveSmoothQ : _root_.ZInQ.Contrib.CurvesG.NormalCurveSmoothQ
  /-- curves-g (C): constant field `ℚ` gives geometric connectedness (Stacks 0FD1). -/
  geomConnectedOfConstantFieldQ : _root_.ZInQ.Contrib.CurvesG.GeomConnectedOfConstantFieldQ
  x0Transitive : _root_.ZInQ.RLeaf.X0Transitive
  /-- neron-c, LEAF: a smooth separated quasi-compact `𝓞_L`-scheme with generic fibre `A_L` to which maps from
  smooth schemes extend (BLR §1.4 Thm 3, scheme level). -/
  neronSchemeExtensionExists : _root_.ZInQ.Contrib.NeronC.NeronSchemeExtensionExists

/-- **The added leaves still open** (leaf-fold6): leaf-fold5's `OpenAddedLeaves5` with leafq-check's reductions:
`gammaStarGen` dropped (proved), `valenceBoundGammaStar` → `valenceFormulaGammaStar`, `cmDescends` → `stQM`,
`qmHauptmodul` → `qmHauptmodulBase3`. 20 fields. -/
structure OpenAddedLeaves6 : Prop where
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  /-- leafq-check, LEAF?: the Hauptmodul property of the theta quotient on `Γ*` and its value `−16/27` at the
  order-2 point (the clauses at the discriminants `−4`, `−3` are proved). -/
  qmHauptmodulBase3 : LeafQCheck.HM.QMHauptmodulBase3
  qmClassNumberOne : G0Split.FibreQM.QMClassNumberOne
  senTwist : G0Galois.SenTwist
  finiteImageHT : G0Galois.FiniteImageHT
  t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists
  isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse
  x6ConicModel : X6Kummer.X6ConicModel
  y3Connected : TSHecke.Y3Connected
  qmAutCard : HeckeRest.QMAutCard
  alFixedPoints : HeckeRest.ALFixedPoints
  zariskiConnectedness : _root_.ZariskiConn.ZariskiConnectedness.{0}
  /-- leafq-check, LEAF: Shimura–Taniyama for QM surfaces with CM (`A ≅ A₀ ×_{ℚ̄} ℂ`). -/
  stQM : G0Split.FibreQM.PeriodMapH.LeafQCheck.STQM
  /-- leafq-check, LEAF: the valence formula on `Γ*` (signature `(0;2,4,6)`) on finite sets of inequivalent
  points. -/
  valenceFormulaGammaStar : LeafQCheck.VB.ValenceFormulaGammaStar
  egaIV_8_8_2_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  egaIV_17_7_8_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii
  /-- vert-witness, LEAF?: good reduction of the level-3 Shimura curve `Y₃` at `p > 324` with its universal
  family and Hecke automorphisms (Kottwitz 1992 §5; Morita 1981; Carayol 1986; Buzzard 1997). -/
  shimuraGoodReduction : VertWitness.ShimuraGoodReduction
  /-- model-glue, LEAF?: a morphism of proper smooth curves over `ℚ` bijective on `ℚ̄`-points is an
  isomorphism (Hartshorne II.6.7-6.9, III.10.7; EGA III 4.4.2). -/
  curveBijIso : ModelGlue.CurveBijIso

/-- **The glue still open** (leaf-fold6): model-glue's `ModelCoordinateResidue` only. -/
structure OpenGlue6 : Prop where
  /-- model-glue: a coordinate `ρ : 𝒴 → P¹` on the smooth model with transcendental residue at every point
  whose stalk is a DVR with maximal ideal `(p)` (the tame quotient `𝒴/Γ' ≅ P¹_{ℤ_(p)}`). -/
  modelCoordinateResidue : ModelGlue.ModelCoordinateResidue

/-- leaf-fold4's textbook bundle from leaf-fold6's (as leaf-fold5's `textbookLeaves4_of_open5`, with
`t8 := t8_ofK6 t.t8`). -/
theorem textbookLeaves4_of_open6 (t : OpenTextbookLeaves6) (l : OpenAddedLeaves6) : OpenTextbookLeaves4 where
  t3 := t3_of_surj5 t.t3Surj
  t4 := reductionTorsionBijective_ofK5 t.t4
  t5 := torsionStructure_ofK5 t.t5
  t6 := t6_of_algClosed5 t.homFreeFiniteAlgClosed
  t7 := t7_of_algClosed5 t.charPolyIndepOfEllAlgClosed
  t8 := t8_ofK6 t.t8
  t9 := t9_of_leaves5 l.t09SymmIsogenyExists l.isogenyQuasiInverse
  t10 := t10_ofK5 t.t10
  homLatticeCorr := homLatticeCorr_ofK5 t.homLatticeCorr
  t11b := t11b_of_exists5 t.t11bExists
  t23 := t.t23
  t24 := eigenformTwist_ofK5 t.t24
  t27 := qmDichotomyYu_ofK5 t.t27
  t33 := jacobianExists_ofK5 t.t33
  t34 := t34_of_split5 t.dimJacobianEqGenus t.genusX1Field
  t35 := uniformizationExists_ofK5 t.t35
  t38 := t38_of_split5 t.normalModelOfFunctionFieldQ t.normalCurveSmoothQ t.geomConnectedOfConstantFieldQ
  x0Transitive := t.x0Transitive
  t41 := t41_of_extension5 t.neronSchemeExtensionExists

/-- **`CMDescends` from Shimura–Taniyama** (leafq-check's `cmDescends_of`, with leaf-fold5's T11(b) and T5). -/
theorem cmDescends_of6 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves6) (l : OpenAddedLeaves6) :
    G0Split.FibreQM.PeriodMapH.CMDescends :=
  G0Split.FibreQM.PeriodMapH.LeafQCheck.cmDescends_of l.stQM (t11b_of_exists5 t.t11bExists)
    (G0Split.FibreQM.PeriodMapH.LeafQCheck.torsionDescends_of_t5 (torsionStructure_ofK5 t.t5)) r.r1r2

/-- **`QMHauptmodul` from `QMHauptmodulBase3`** (leafq-check's `base2_of_base3` and `qmHauptmodul_of_base2`:
R4, `GammaStarGen` (proved) and the valence bound (from the valence formula)). -/
theorem qmHauptmodul_of6 (r : OpenResearchLeaves5) (l : OpenAddedLeaves6) : PkgI1.QMHauptmodul :=
  LeafQCheck.HM.qmHauptmodul_of_base2
    (LeafQCheck.HM.base2_of_base3 r.r4 LeafQCheck.gammaStarGen_proof
      (LeafQCheck.VB.valenceBound_of_formula l.valenceFormulaGammaStar) l.qmHauptmodulBase3)

/-- leaf-fold4's added-leaves bundle from leaf-fold6's. -/
theorem addedLeaves4_of_open6 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves6) (l : OpenAddedLeaves6) :
    OpenAddedLeaves4 where
  cmOptimalEmbedding := l.cmOptimalEmbedding
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  qmHauptmodul := qmHauptmodul_of6 r l
  qmClassNumberOne := l.qmClassNumberOne
  senTwist := l.senTwist
  finiteImageHT := l.finiteImageHT
  t09SymmIsogenyExists := l.t09SymmIsogenyExists
  isogenyQuasiInverse := l.isogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  y3Connected := l.y3Connected
  qmAutCard := l.qmAutCard
  serreRigidity3 := serreRigidity3_of_T35_5 (uniformizationExists_ofK5 t.t35) (homLatticeCorr_ofK5 t.homLatticeCorr)
  alFixedPoints := l.alFixedPoints
  zariskiConnectedness := l.zariskiConnectedness
  cmDescends := cmDescends_of6 r t l
  gammaStarGen := LeafQCheck.gammaStarGen_proof
  valenceBoundGammaStar := LeafQCheck.VB.valenceBound_of_formula l.valenceFormulaGammaStar
  egaIV_8_8_2_ii := l.egaIV_8_8_2_ii
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  egaIV_17_7_8_ii := l.egaIV_17_7_8_ii

/-- leaf-fold4's glue bundle from leaf-fold6's: `HeckeVertWitness` from leaves and `ModelCoordinateResidue`
(leaf-fold5's `heckeVertWitness_of_leaves5`). -/
theorem glue4_of_open6 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves6) (l : OpenAddedLeaves6)
    (g : OpenGlue6) : OpenGlue4 where
  heckeVertWitness := heckeVertWitness_of_leaves5 l.shimuraGoodReduction r.r1r2 (torsionStructure_ofK5 t.t5)
    g.modelCoordinateResidue l.curveBijIso

/-- **G0 with only the open leaves and the open glue** (leaf-fold6; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from
* `OpenResearchLeaves5`: 26 research-level fields (leaf-fold5's bundle, unchanged; nine on the kernel's Props);
* `OpenTextbookLeaves6`: 21 textbook fields (T8 kept, on the kernel's Prop);
* `OpenAddedLeaves6`: 20 added leaves;
* `OpenGlue6`: 1 glue Prop (`ModelCoordinateResidue`).
The table of every field is `docs/research/leaf-fold6.md` §2. -/
theorem sixContactMin_of_open6 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves6)
    (l : OpenAddedLeaves6) (g : OpenGlue6) : ZInQ.SixContactMin :=
  sixContactMin_of_open4 (researchLeaves2_of_open5 r) (textbookLeaves4_of_open6 t l) (addedLeaves4_of_open6 r t l)
    (glue4_of_open6 r t l g)

/-- **The other choice for T8** (goal (b)): leaf-fold5's textbook bundle (with `poincareComplement`) and leaf-fold5's
glue bundle (with `simpleImageIsogeny`): 26 + 21 + 20 + 2 = 69 fields, glue 2. T8 is the kernel's
`ZInQ.Contrib.AVB1.poincareReducibility_of_simpleImage`. -/
theorem sixContactMin_of_open6_poincare (r : OpenResearchLeaves5) (t : OpenTextbookLeaves5)
    (l : OpenAddedLeaves6) (g : OpenGlue5) : ZInQ.SixContactMin :=
  sixContactMin_of_open6 r
    { t3Surj := t.t3Surj, t4 := t.t4, t5 := t.t5, homFreeFiniteAlgClosed := t.homFreeFiniteAlgClosed,
      charPolyIndepOfEllAlgClosed := t.charPolyIndepOfEllAlgClosed,
      t8 := _root_.ZInQ.Contrib.AVB1.poincareReducibility_of_simpleImage t.poincareComplement g.simpleImageIsogeny,
      t10 := t.t10, homLatticeCorr := t.homLatticeCorr, t11bExists := t.t11bExists, t23 := t.t23, t24 := t.t24,
      t27 := t.t27, t33 := t.t33, dimJacobianEqGenus := t.dimJacobianEqGenus, genusX1Field := t.genusX1Field,
      t35 := t.t35, normalModelOfFunctionFieldQ := t.normalModelOfFunctionFieldQ,
      normalCurveSmoothQ := t.normalCurveSmoothQ, geomConnectedOfConstantFieldQ := t.geomConnectedOfConstantFieldQ,
      x0Transitive := t.x0Transitive, neronSchemeExtensionExists := t.neronSchemeExtensionExists }
    l ⟨g.modelCoordinateResidue⟩

/-- leaf-fold5's added-leaves bundle from leaf-fold6's: the four fields leafq-check replaced are theorems from the
new fields (and `r4`, `r1r2`, T5, T11(b)); the other 17 are the same fields. -/
theorem addedLeaves5_of_open6 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves6) (l : OpenAddedLeaves6) :
    OpenAddedLeaves5 where
  cmOptimalEmbedding := l.cmOptimalEmbedding
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  qmHauptmodul := qmHauptmodul_of6 r l
  qmClassNumberOne := l.qmClassNumberOne
  senTwist := l.senTwist
  finiteImageHT := l.finiteImageHT
  t09SymmIsogenyExists := l.t09SymmIsogenyExists
  isogenyQuasiInverse := l.isogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  y3Connected := l.y3Connected
  qmAutCard := l.qmAutCard
  alFixedPoints := l.alFixedPoints
  zariskiConnectedness := l.zariskiConnectedness
  cmDescends := cmDescends_of6 r t l
  gammaStarGen := LeafQCheck.gammaStarGen_proof
  valenceBoundGammaStar := LeafQCheck.VB.valenceBound_of_formula l.valenceFormulaGammaStar
  egaIV_8_8_2_ii := l.egaIV_8_8_2_ii
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  egaIV_17_7_8_ii := l.egaIV_17_7_8_ii
  shimuraGoodReduction := l.shimuraGoodReduction
  curveBijIso := l.curveBijIso

end HDec.HSyn

end

example : ∀ (_ : HDec.HSyn.OpenResearchLeaves5) (_ : HDec.HSyn.OpenTextbookLeaves6)
    (_ : HDec.HSyn.OpenAddedLeaves6) (_ : HDec.HSyn.OpenGlue6), _root_.ZInQ.SixContactMin :=
  HDec.HSyn.sixContactMin_of_open6

example : ∀ (_ : HDec.HSyn.OpenResearchLeaves5) (_ : HDec.HSyn.OpenTextbookLeaves5)
    (_ : HDec.HSyn.OpenAddedLeaves6) (_ : HDec.HSyn.OpenGlue5), _root_.ZInQ.SixContactMin :=
  HDec.HSyn.sixContactMin_of_open6_poincare

#print axioms HDec.HSyn.t8_ofK6
#print axioms HDec.HSyn.cmDescends_of6
#print axioms HDec.HSyn.qmHauptmodul_of6
#print axioms HDec.HSyn.textbookLeaves4_of_open6
#print axioms HDec.HSyn.addedLeaves4_of_open6
#print axioms HDec.HSyn.glue4_of_open6
#print axioms HDec.HSyn.addedLeaves5_of_open6
#print axioms HDec.HSyn.sixContactMin_of_open6
#print axioms HDec.HSyn.sixContactMin_of_open6_poincare
