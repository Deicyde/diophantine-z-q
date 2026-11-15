import ZInQKernel.Contrib.OneProof.QMLattice

set_option linter.all false

noncomputable section

namespace GapGlue.CMStab

open LeafQM LeafQM.AV

/-! ## §1 Arithmetic of `𝒪` modulo `3` -/

/-- The element `ofInt n` of `𝒪`. -/
def mkO (n : Fin 4 → ℤ) : O := ⟨ofInt n, ⟨n, rfl⟩⟩

/-- The coordinates of `x ∈ 𝒪` in the basis `1, i, (1+j)/2, (i+k)/2`. -/
def coords (x : O) : Fin 4 → ℤ := Classical.choose x.2

theorem coords_spec (x : O) : (x : B) = ofInt (coords x) := Classical.choose_spec x.2

theorem coords_eq {x : O} {n : Fin 4 → ℤ} (h : (x : B) = ofInt n) : coords x = n :=
  AV.ofInt_injective ((coords_spec x).symm.trans h)

theorem coords_mkO (n : Fin 4 → ℤ) : coords (mkO n) = n := coords_eq rfl

theorem coords_mul (x y : O) : coords (x * y) = mulCoord (coords x) (coords y) := by
  apply coords_eq
  rw [MulMemClass.coe_mul, coords_spec x, coords_spec y, ofInt_mul]

theorem coords_add (x y : O) : coords (x + y) = coords x + coords y := by
  apply coords_eq
  rw [AddMemClass.coe_add, coords_spec x, coords_spec y, ofInt_add]

theorem coords_neg (x : O) : coords (-x) = -coords x := by
  apply coords_eq
  rw [NegMemClass.coe_neg, coords_spec x, ofInt_neg]

theorem coords_sub (x y : O) : coords (x - y) = coords x - coords y := by
  apply coords_eq
  rw [AddSubgroupClass.coe_sub, coords_spec x, coords_spec y, AV.ofInt_sub]

theorem coords_one : coords 1 = ![1, 0, 0, 0] := by
  apply coords_eq
  rw [OneMemClass.coe_one, ofInt_one]

theorem coe_three : ((3 : O) : B) = 3 := map_ofNat O.subtype 3

theorem coords_three_mul (x : O) : coords (3 * x) = fun i => 3 * coords x i := by
  apply coords_eq
  rw [MulMemClass.coe_mul, coe_three, coords_spec x, AV.three_mul_ofInt]

/-- `𝔽₉ = 𝔽₃[i]` as pairs, with Gaussian multiplication. -/
abbrev F9 := ZMod 3 × ZMod 3

def gm (a b : F9) : F9 := (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

def cj (a : F9) : F9 := (a.1, -a.2)

def redC (n : Fin 4 → ℤ) : F9 := (((n 0 - n 2 : ℤ) : ZMod 3), ((n 1 - n 3 : ℤ) : ZMod 3))

/-- **Reduction `𝒪 → 𝒪/𝔓₃ = 𝔽₉`** (`𝔓₃ = j𝒪`, the prime over the ramified `3`):
`ofInt n ↦ (n₀ − n₂) + (n₁ − n₃) i`. -/
def red (x : O) : F9 := redC (coords x)

theorem z3 : (3 : ZMod 3) = 0 := rfl

theorem redC_mul (n m : Fin 4 → ℤ) : redC (mulCoord n m) = gm (redC n) (redC m) := by
  have h1 : mulCoord n m 0 - mulCoord n m 2 = ((n 0 - n 2) * (m 0 - m 2) - (n 1 - n 3) * (m 1 - m 3))
      + 3 * (m 1 * n 1 + m 1 * n 3 - m 2 * n 2 - m 3 * n 1 + m 3 * n 3) := by
    simp [mulCoord]; ring
  have h2 : mulCoord n m 1 - mulCoord n m 3 = ((n 0 - n 2) * (m 1 - m 3) + (n 1 - n 3) * (m 0 - m 2))
      + 3 * (m 1 * n 2 - m 2 * n 3) := by
    simp [mulCoord]; ring
  simp only [redC, gm, h1, h2]
  push_cast
  simp [z3]

theorem red_mul (x y : O) : red (x * y) = gm (red x) (red y) := by
  rw [red, coords_mul, redC_mul]; rfl

theorem red_add (x y : O) : red (x + y) = red x + red y := by
  simp only [red, coords_add, redC, Pi.add_apply]; push_cast; ext <;> simp <;> ring

theorem red_sub (x y : O) : red (x - y) = red x - red y := by
  simp only [red, coords_sub, redC, Pi.sub_apply]; push_cast; ext <;> simp <;> ring

theorem red_neg (x : O) : red (-x) = -red x := by
  simp only [red, coords_neg, redC, Pi.neg_apply]; push_cast; ext <;> simp <;> ring

theorem red_one : red 1 = (1, 0) := by
  simp [red, coords_one, redC]

theorem red_three_mul (x : O) : red (3 * x) = 0 := by
  simp only [red, coords_three_mul, redC]; push_cast; simp [z3]

theorem red_mkO (n : Fin 4 → ℤ) : red (mkO n) = redC n := by rw [red, coords_mkO]

/-! ### Congruences modulo `3𝒪` -/

/-- Congruence modulo the two-sided ideal `3𝒪`. -/
def r3 : RingCon O where
  r x y := ∃ c : O, x - y = 3 * c
  iseqv := ⟨fun x => ⟨0, by simp⟩, fun ⟨c, h⟩ => ⟨-c, by rw [mul_neg, ← h]; abel⟩,
    fun ⟨c, h⟩ ⟨d, h'⟩ => ⟨c + d, by rw [mul_add, ← h, ← h']; abel⟩⟩
  add' := fun ⟨c, h⟩ ⟨d, h'⟩ => ⟨c + d, by rw [mul_add, ← h, ← h']; abel⟩
  mul' := by
    rintro w x y z ⟨c, h⟩ ⟨d, h'⟩
    refine ⟨c * y + x * d, ?_⟩
    have e : w * y - x * z = (w - x) * y + x * (y - z) := by noncomm_ring
    rw [e, h, h']
    noncomm_ring

/-- `𝒪/3𝒪`. -/
abbrev Q3 := r3.Quotient

/-- The reduction `𝒪 → 𝒪/3𝒪`. -/
abbrev π3 : O →+* Q3 := r3.mk'

theorem π3_eq_iff {x y : O} : π3 x = π3 y ↔ ∃ c : O, x - y = 3 * c := RingCon.eq r3

theorem red_congr {x y : O} (h : π3 x = π3 y) : red x = red y := by
  obtain ⟨c, hc⟩ := π3_eq_iff.1 h
  have := congrArg red hc
  rw [red_sub, red_three_mul, sub_eq_zero] at this
  exact this


/-! ### Explicit elements, divisibility -/

/-- `k = ij ∈ 𝒪` (`k² = 6`). -/
def ok : O := mkO ![0, -1, 0, 2]

/-- `1 + i`, a unit of `𝒪` (`(1 + i)(i − 1) = 1`). -/
def w1 : O := mkO ![1, 1, 0, 0]
def w1inv : O := mkO ![-1, 1, 0, 0]

theorem w1_mul_inv : w1 * w1inv = 1 := by
  apply Subtype.ext; change ofInt _ * ofInt _ = (1 : B); ext <;> simp [ofInt] <;> norm_num
theorem w1_inv_mul : w1inv * w1 = 1 := by
  apply Subtype.ext; change ofInt _ * ofInt _ = (1 : B); ext <;> simp [ofInt] <;> norm_num

/-- `1 + i` as a unit. -/
def w1U : Oˣ := ⟨w1, w1inv, w1_mul_inv, w1_inv_mul⟩

theorem ok_mul_ok : ok * ok = 6 := by
  apply Subtype.ext
  change ofInt ![0, -1, 0, 2] * ofInt ![0, -1, 0, 2] = ((6 : O) : B)
  rw [show ((6 : O) : B) = 6 from map_ofNat O.subtype 6]
  ext <;> simp [ofInt, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num

theorem oj_eq : oj = mkO ![-1, 0, 2, 0] := rfl

theorem red_oj : red oj = 0 := by rw [oj_eq, red_mkO]; simp [redC]; decide
theorem red_ok : red ok = 0 := by rw [ok, red_mkO]; simp [redC]; decide
theorem red_w1 : red w1 = (1, 1) := by rw [w1, red_mkO]; simp [redC]

/-- `𝒪` has no `ℤ`-torsion. -/
theorem eq_zero_of_intCast_mul {N : ℤ} (hN : N ≠ 0) {w : O} (h : (N : O) * w = 0) : w = 0 := by
  apply Subtype.ext
  have h1 : ((N : O) : B) * (w : B) = 0 := by
    have := congrArg Subtype.val h; simpa using this
  have h2 : ((N : ℚ) • (w : B)) = 0 := by
    rw [Algebra.smul_def, map_intCast]
    simpa using h1
  exact (smul_eq_zero.1 h2).resolve_left (by exact_mod_cast hN)

theorem ofInt_intMul (N : ℤ) (e : Fin 4 → ℤ) : ofInt (fun i => N * e i) = (N : B) * ofInt e := by
  ext <;> simp [ofInt] <;> ring

/-- **Left division by `t`** when `t² = ±N` and `N` divides every coordinate of `t z`. -/
theorem left_div (t z : O) (N s : ℤ) (hs : s * s = 1) (htt : t * t = ((s * N : ℤ) : O))
    (hN : N ≠ 0) (hdiv : ∀ i, N ∣ coords (t * z) i) : ∃ d : O, z = t * d := by
  choose e he using hdiv
  have htz : t * z = (N : O) * mkO e := by
    apply Subtype.ext
    rw [coords_spec (t * z), MulMemClass.coe_mul, show ((N : O) : B) = (N : B) by simp]
    change ofInt (coords (t * z)) = (N : B) * ofInt e
    rw [← ofInt_intMul]
    congr 1
    funext i; exact he i
  refine ⟨(s : O) * mkO e, ?_⟩
  have h1 : t * (t * z) = ((s * N : ℤ) : O) * z := by rw [← _root_.mul_assoc, htt]
  rw [htz] at h1
  have h2 : (N : O) * ((s : O) * z - t * mkO e) = 0 := by
    have hc : t * ((N : O) * mkO e) = (N : O) * (t * mkO e) := by
      rw [← _root_.mul_assoc, ← _root_.mul_assoc, (Int.cast_commute N t).symm.eq]
    rw [hc] at h1
    rw [mul_sub, h1, ← _root_.mul_assoc, ← Int.cast_mul, mul_comm N s, sub_self]
  have h3 := eq_zero_of_intCast_mul hN h2
  have h4 : (s : O) * z = t * mkO e := sub_eq_zero.1 h3
  calc z = ((s * s : ℤ) : O) * z := by rw [hs]; simp
    _ = (s : O) * ((s : O) * z) := by push_cast; rw [_root_.mul_assoc]
    _ = (s : O) * (t * mkO e) := by rw [h4]
    _ = t * ((s : O) * mkO e) := by
      rw [← _root_.mul_assoc, ← _root_.mul_assoc, (Int.cast_commute s t).eq]

/-! ### Finite checks modulo 2 and 3 -/

/-- `mulCoord` over any commutative ring. -/
def mcp {R : Type} [CommRing R] (n m : Fin 4 → R) : Fin 4 → R :=
  ![m 0 * n 0 + 2 * m 1 * n 1 + 2 * m 1 * n 3 - m 2 * n 2 + 2 * m 3 * n 3,
    m 0 * n 1 + m 1 * n 0 + m 1 * n 2 - m 2 * n 3 + m 3 * n 2,
    m 0 * n 2 - 2 * m 1 * n 3 + m 2 * n 0 + m 2 * n 2 + 2 * m 3 * n 1,
    m 0 * n 3 - m 1 * n 2 + m 2 * n 1 + m 2 * n 3 + m 3 * n 0]

theorem cast_mulCoord {p : ℕ} (n m : Fin 4 → ℤ) (i : Fin 4) :
    ((mulCoord n m i : ℤ) : ZMod p) =
      mcp (fun i => ((n i : ℤ) : ZMod p)) (fun i => ((m i : ℤ) : ZMod p)) i := by
  fin_cases i <;> simp [mulCoord, mcp]

theorem fin_j3 : ∀ a b c d : ZMod 3,
    mcp ![a, b, c, d] ![a, b, c, d] = 0 → mcp ![2, 0, 2, 0] ![a, b, c, d] = 0 := by
  decide

theorem fin_k3 : ∀ a b c d : ZMod 3,
    mcp ![a, b, c, d] ![a, b, c, d] = 0 → mcp ![0, 2, 0, 2] ![a, b, c, d] = 0 := by
  decide

theorem fin_k2 : ∀ a b c d : ZMod 2,
    mcp ![a, b, c, d] ![a, b, c, d] = 0 → mcp ![0, 1, 0, 0] ![a, b, c, d] = 0 := by
  decide

theorem fin_red : ∀ a b c d : ZMod 3,
    a - c = 0 → b - d = 0 → mcp ![2, 0, 2, 0] ![a, b, c, d] = 0 := by
  decide


theorem vec4 {R : Type} (f : Fin 4 → R) : f = ![f 0, f 1, f 2, f 3] := by
  funext i; fin_cases i <;> rfl

theorem coords_intCast (N : ℤ) : coords (N : O) = ![N, 0, 0, 0] := by
  apply coords_eq
  rw [show ((N : O) : B) = (N : B) by simp]
  ext <;> simp [ofInt]

theorem dvd_of_cast {p : ℕ} [NeZero p] {x : ℤ} (h : ((x : ℤ) : ZMod p) = 0) : (p : ℤ) ∣ x :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd x p).1 h

/-- `mcp v v = 0` modulo `p` when `y * y` is an integer divisible by `p`. -/
theorem mcp_sq_zero {p : ℕ} (y : O) (N : ℤ) (hy : y * y = (N : O)) (hp : ((N : ℤ) : ZMod p) = 0) :
    mcp ![((coords y 0 : ℤ) : ZMod p), ↑(coords y 1), ↑(coords y 2), ↑(coords y 3)]
      ![((coords y 0 : ℤ) : ZMod p), ↑(coords y 1), ↑(coords y 2), ↑(coords y 3)] = 0 := by
  rw [← vec4 (fun i => ((coords y i : ℤ) : ZMod p))]
  funext i
  rw [← cast_mulCoord, ← coords_mul, hy, coords_intCast]
  fin_cases i <;> simp [hp]

/-- `y² = −3` gives `y ∈ j𝒪`. -/
theorem div_j (y : O) (hy : y * y = -3) : ∃ d : O, y = oj * d := by
  have hy' : y * y = ((-3 : ℤ) : O) := by rw [hy]; push_cast; rfl
  refine left_div oj y 3 (-1) (by norm_num) (by rw [AV.oj_mul_oj]; norm_num)
    (by norm_num) fun i => ?_
  have h2 := fin_j3 _ _ _ _ (mcp_sq_zero (p := 3) y (-3) hy' (by decide))
  have hj : (fun i => ((coords oj i : ℤ) : ZMod 3)) = ![2, 0, 2, 0] := by
    rw [oj_eq, coords_mkO]; funext i; fin_cases i <;> decide
  have := dvd_of_cast (p := 3) (x := coords (oj * y) i) (by
    rw [coords_mul, cast_mulCoord, hj, vec4 (fun i => ((coords y i : ℤ) : ZMod 3))]
    exact congrFun h2 i)
  exact_mod_cast this

/-- `y² = −6` gives `y ∈ k𝒪`. -/
theorem div_k (y : O) (hy : y * y = -6) : ∃ d : O, y = ok * d := by
  have hy' : y * y = ((-6 : ℤ) : O) := by rw [hy]; push_cast; rfl
  refine left_div ok y 6 1 (by norm_num) (by rw [ok_mul_ok]; norm_num)
    (by norm_num) fun i => ?_
  have h3 := fin_k3 _ _ _ _ (mcp_sq_zero (p := 3) y (-6) hy' (by decide))
  have h2 := fin_k2 _ _ _ _ (mcp_sq_zero (p := 2) y (-6) hy' (by decide))
  have hk3 : (fun i => ((coords ok i : ℤ) : ZMod 3)) = ![0, 2, 0, 2] := by
    rw [ok, coords_mkO]; funext i; fin_cases i <;> decide
  have hk2 : (fun i => ((coords ok i : ℤ) : ZMod 2)) = ![0, 1, 0, 0] := by
    rw [ok, coords_mkO]; funext i; fin_cases i <;> decide
  have d3 := dvd_of_cast (p := 3) (x := coords (ok * y) i) (by
    rw [coords_mul, cast_mulCoord, hk3, vec4 (fun i => ((coords y i : ℤ) : ZMod 3))]
    exact congrFun h3 i)
  have d2 := dvd_of_cast (p := 2) (x := coords (ok * y) i) (by
    rw [coords_mul, cast_mulCoord, hk2, vec4 (fun i => ((coords y i : ℤ) : ZMod 2))]
    exact congrFun h2 i)
  push_cast at d3 d2
  omega

/-- `red z = 0` gives `z ∈ j𝒪` (the kernel of `red` is `𝔓₃ = j𝒪`). -/
theorem div_j_of_red (z : O) (hz : red z = 0) : ∃ d : O, z = oj * d := by
  refine left_div oj z 3 (-1) (by norm_num) (by rw [AV.oj_mul_oj]; norm_num)
    (by norm_num) fun i => ?_
  have h0 : ((coords z 0 - coords z 2 : ℤ) : ZMod 3) = 0 := congrArg Prod.fst hz
  have h1 : ((coords z 1 - coords z 3 : ℤ) : ZMod 3) = 0 := congrArg Prod.snd hz
  push_cast at h0 h1
  have h2 := fin_red _ _ _ _ h0 h1
  have hj : (fun i => ((coords oj i : ℤ) : ZMod 3)) = ![2, 0, 2, 0] := by
    rw [oj_eq, coords_mkO]; funext i; fin_cases i <;> decide
  have := dvd_of_cast (p := 3) (x := coords (oj * z) i) (by
    rw [coords_mul, cast_mulCoord, hj, vec4 (fun i => ((coords z i : ℤ) : ZMod 3))]
    exact congrFun h2 i)
  exact_mod_cast this

theorem three_eq_intCast : (3 : O) = ((3 : ℤ) : O) := by push_cast; rfl

/-- `j z ≡ 0 (mod 3)` gives `red z = 0`. -/
theorem red_of_j_mul (z : O) (h : π3 (oj * z) = 0) : red z = 0 := by
  obtain ⟨c, hc⟩ := π3_eq_iff.1 (h.trans (map_zero π3).symm)
  rw [sub_zero] at hc
  have e : ((3 : ℤ) : O) * (z + oj * c) = 0 := by
    have h1 : oj * (oj * z) = oj * (3 * c) := by rw [hc]
    rw [← _root_.mul_assoc, AV.oj_mul_oj] at h1
    rw [← three_eq_intCast, mul_add]
    calc 3 * z + 3 * (oj * c) = 3 * z + oj * (3 * c) := by noncomm_ring
      _ = 3 * z + -3 * z := by rw [← h1]
      _ = 0 := by noncomm_ring
  have e2 := eq_zero_of_intCast_mul (by norm_num) e
  rw [show z = -(oj * c) from eq_neg_of_add_eq_zero_left e2, red_neg, red_mul, red_oj]
  simp [gm]

/-- `k z ≡ 0 (mod 3)` gives `red z = 0`. -/
theorem red_of_k_mul (z : O) (h : π3 (ok * z) = 0) : red z = 0 := by
  obtain ⟨c, hc⟩ := π3_eq_iff.1 (h.trans (map_zero π3).symm)
  rw [sub_zero] at hc
  have e : ((3 : ℤ) : O) * ((z + z) - ok * c) = 0 := by
    have h1 : ok * (ok * z) = ok * (3 * c) := by rw [hc]
    rw [← _root_.mul_assoc, ok_mul_ok] at h1
    rw [← three_eq_intCast]
    calc 3 * ((z + z) - ok * c) = 6 * z - ok * (3 * c) := by noncomm_ring
      _ = 0 := by rw [← h1]; noncomm_ring
  have e2 := sub_eq_zero.1 (eq_zero_of_intCast_mul (by norm_num) e)
  have e3 := congrArg red e2
  rw [red_add, red_mul, red_ok] at e3
  have e4 : red z + red z = 0 := by rw [e3]; simp [gm]
  revert e4
  generalize red z = r
  revert r
  decide


/-! ### The involutions `α_j` and `α_k` of `𝒪` (conjugation by `j` and by `k = ij`) -/

/-- Conjugation by `j` on `B`: `i ↦ −i`, `j ↦ j`. -/
def cJ : B →+* B where
  toFun x := ⟨x.re, -x.imI, x.imJ, -x.imK⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp <;> ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp <;> ring

/-- Conjugation by `k` on `B`: `i ↦ −i`, `j ↦ −j`. -/
def cK : B →+* B where
  toFun x := ⟨x.re, -x.imI, -x.imJ, x.imK⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp <;> ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp <;> ring

theorem cJ_ofInt (n : Fin 4 → ℤ) : cJ (ofInt n) = ofInt ![n 0, -n 1, n 2, -n 3] := by
  ext <;> simp [cJ, ofInt] <;> ring

theorem cK_ofInt (n : Fin 4 → ℤ) : cK (ofInt n) = ofInt ![n 0 + n 2, -n 1 - n 3, -n 2, n 3] := by
  ext <;> simp [cK, ofInt] <;> ring

theorem cJ_cJ (x : B) : cJ (cJ x) = x := by ext <;> simp [cJ]
theorem cK_cK (x : B) : cK (cK x) = x := by ext <;> simp [cK]

theorem cJ_mem {x : B} (hx : x ∈ O) : cJ x ∈ O := by
  obtain ⟨n, rfl⟩ := hx; exact ⟨_, cJ_ofInt n⟩
theorem cK_mem {x : B} (hx : x ∈ O) : cK x ∈ O := by
  obtain ⟨n, rfl⟩ := hx; exact ⟨_, cK_ofInt n⟩

/-- A ring involution of `B` preserving `𝒪`, as an automorphism of `𝒪`. -/
def invEquiv (f : B →+* B) (hf : ∀ x, f (f x) = x) (hO : ∀ x : B, x ∈ O → f x ∈ O) :
    O ≃+* O where
  toFun x := ⟨f x, hO x x.2⟩
  invFun x := ⟨f x, hO x x.2⟩
  left_inv x := Subtype.ext (hf x)
  right_inv x := Subtype.ext (hf x)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

def αJ : O ≃+* O := invEquiv cJ cJ_cJ (fun _ h => cJ_mem h)
def αK : O ≃+* O := invEquiv cK cK_cK (fun _ h => cK_mem h)

theorem αJ_coe (x : O) : ((αJ x : O) : B) = cJ x := rfl
theorem αK_coe (x : O) : ((αK x : O) : B) = cK x := rfl

theorem αJ_αJ (x : O) : αJ (αJ x) = x := Subtype.ext (cJ_cJ _)
theorem αK_αK (x : O) : αK (αK x) = x := Subtype.ext (cK_cK _)

/-- `j α_j(z) = z j`. -/
theorem oj_mul_αJ (z : O) : oj * αJ z = z * oj := by
  apply Subtype.ext
  rw [MulMemClass.coe_mul, MulMemClass.coe_mul, αJ_coe]
  change ofInt ![-1, 0, 2, 0] * cJ z = z * ofInt ![-1, 0, 2, 0]
  ext <;> simp [cJ, ofInt] <;> ring

/-- `k α_k(z) = z k`. -/
theorem ok_mul_αK (z : O) : ok * αK z = z * ok := by
  apply Subtype.ext
  rw [MulMemClass.coe_mul, MulMemClass.coe_mul, αK_coe]
  change ofInt ![0, -1, 0, 2] * cK z = z * ofInt ![0, -1, 0, 2]
  ext <;> simp [cK, ofInt] <;> ring

theorem red_αJ (x : O) : red (αJ x) = cj (red x) := by
  have : coords (αJ x) = ![coords x 0, -coords x 1, coords x 2, -coords x 3] := by
    apply coords_eq; rw [αJ_coe, coords_spec x, cJ_ofInt]
  rw [red, this, red]
  simp only [redC, cj]
  push_cast
  ext <;> simp <;> ring

theorem red_αK (x : O) : red (αK x) = cj (red x) := by
  have : coords (αK x) = ![coords x 0 + coords x 2, -coords x 1 - coords x 3, -coords x 2,
      coords x 3] := by
    apply coords_eq; rw [αK_coe, coords_spec x, cK_ofInt]
  rw [red, this, red]
  simp only [redC, cj]
  push_cast
  ext
  · simp only [Matrix.cons_val]
    linear_combination (coords x 2 : ZMod 3) * z3
  · simp only [Matrix.cons_val]
    linear_combination (-(coords x 3 : ZMod 3)) * z3


/-! ### Copied verbatim from `scratch/mcr-quot/MCRQuot.lean`, lines 4578-4747 (namespace `MCRQuot`):
`nrdZ`, `nrdZ_mul`, `unit_table`, `nrdZ_mod3`, `exists_unit_congr`. -/

/-! ## Units of `𝒪` modulo 3 (a finite computation) -/

/-- The reduced norm of `ofInt n` (an integer form). -/
def nrdZ (n : Fin 4 → ℤ) : ℤ :=
  n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 - 2 * n 3 ^ 2

theorem nrdZ_mul (n m : Fin 4 → ℤ) : nrdZ (mulCoord n m) = nrdZ n * nrdZ m := by
  simp [nrdZ, mulCoord]
  ring

/-- **The unit table** (computed by `py/units.py`): every class of `(ℤ/3)⁴` of nonzero norm mod 3
contains a unit `ofInt n` of `𝒪` (inverse `ofInt m`). -/
theorem unit_table : ∀ a b c d : ZMod 3,
    a ^ 2 + a * c + c ^ 2 - 2 * b ^ 2 - 2 * b * d - 2 * d ^ 2 ≠ 0 →
    ∃ n m : Fin 4 → ℤ, mulCoord n m = ![1, 0, 0, 0] ∧ mulCoord m n = ![1, 0, 0, 0] ∧
      ((n 0 : ℤ) : ZMod 3) = a ∧ ((n 1 : ℤ) : ZMod 3) = b ∧ ((n 2 : ℤ) : ZMod 3) = c ∧
      ((n 3 : ℤ) : ZMod 3) = d := by
  intro a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![-3, 0, 0, -2], ![-3, 0, 0, 2], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, 0, 0, 2], ![-3, 0, 0, -2], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, 1, 0], ![1, 0, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, 1, 1], ![-1, 0, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, 1, -1], ![-1, 0, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, -1, 0], ![-1, 0, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, -1, 1], ![1, 0, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, -1, -1], ![1, 0, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, -2, 0, 0], ![-3, 2, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![-3, -2, 0, 2], ![-3, 2, 0, -2], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 1, 1, 0], ![-1, 1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, 1, 1, 1], ![-2, -1, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 1, 1, -1], ![-1, 1, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 1, -1, 0], ![1, 1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![3, 1, -1, 1], ![2, -1, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 1, -1, -1], ![1, 1, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, 2, 0, 0], ![-3, -2, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, 2, 0, -2], ![-3, -2, 0, 2], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![0, -1, 1, 0], ![-1, -1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, -1, 1, 1], ![-1, -1, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, -1, 1, -1], ![-2, 1, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, -1, -1, 0], ![1, -1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, -1, -1, 1], ![1, -1, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![3, -1, -1, -1], ![2, 1, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, 0, 0], ![1, 0, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, 0, 1], ![-1, 0, 0, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, 0, -1], ![-1, 0, 0, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![1, 0, 1, 1], ![2, 0, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, 1, -1], ![2, 0, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, -1, 0], ![0, 0, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, -1, 1], ![0, 0, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, -1, -1], ![0, 0, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, 0, 0], ![-1, 1, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, -3, 1], ![-2, -1, 3, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, 0, -1], ![-1, 1, 0, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, 1, 0], ![2, -1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![1, 1, 1, -1], ![2, -1, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, -1, 0], ![0, 1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-2, 1, -1, 1], ![-3, -1, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, -1, -1], ![0, 1, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, 0, 0], ![-1, -1, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, 0, 1], ![-1, -1, 0, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, -3, -1], ![-2, 1, 3, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, 1, 0], ![2, 1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, 1, 1], ![2, 1, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![1, -1, -1, 0], ![0, -1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, -1, 1], ![0, -1, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-2, -1, -1, -1], ![-3, 1, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 0, 0], ![-1, 0, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 0, 1], ![1, 0, 0, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 0, -1], ![1, 0, 0, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 1, 0], ![0, 0, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 1, 1], ![0, 0, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 1, -1], ![0, 0, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![-1, 0, -1, 1], ![-2, 0, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, -1, -1], ![-2, 0, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, 0, 0], ![1, 1, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, 3, 1], ![2, -1, -3, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, 0, -1], ![1, 1, 0, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, 1, 0], ![0, 1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, -2, 1], ![-3, -1, 2, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, 1, -1], ![0, 1, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, -1, 0], ![-2, -1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![-1, 1, -1, -1], ![-2, -1, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, 0, 0], ![1, -1, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, 0, 1], ![1, -1, 0, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, 3, -1], ![2, 1, -3, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, 1, 0], ![0, -1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, 1, 1], ![0, -1, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, -2, -1], ![-3, 1, 2, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, -1, 0], ![-2, 1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, -1, 1], ![-2, 1, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim

theorem nrdZ_mod3 (nc : Fin 4 → ℤ) :
    ((nrdZ (fun i => (![1, 0, 0, 0] : Fin 4 → ℤ) i + 3 * nc i) : ℤ) : ZMod 3) = 1 := by
  have h3 : (3 : ZMod 3) = 0 := rfl
  simp [nrdZ, h3]

/-- **`𝒪^× ↠ (𝒪/3𝒪)^×`**: an element of `𝒪` invertible modulo `3𝒪` is congruent modulo `3𝒪` to a
unit of `𝒪` (the unit table). -/
theorem exists_unit_congr (u₀ v₀ : O) (h : ∃ c : O, v₀ * u₀ - 1 = 3 * c) :
    ∃ u : Oˣ, ∃ c : O, (u : O) - u₀ = 3 * c := by
  obtain ⟨nu, hnu⟩ := u₀.2
  obtain ⟨nv, hnv⟩ := v₀.2
  obtain ⟨c, hc⟩ := h
  obtain ⟨nc, hnc⟩ := c.2
  have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
  have hcB : (v₀ : B) * u₀ - 1 = 3 * c := by
    have := congrArg Subtype.val hc
    simpa [h33] using this
  have key : mulCoord nv nu = fun i => (![1, 0, 0, 0] : Fin 4 → ℤ) i + 3 * nc i := by
    have e : ofInt (mulCoord nv nu) - ofInt ![1, 0, 0, 0] = ofInt (fun i => 3 * nc i) := by
      rw [← ofInt_mul, ofInt_one, ← AV.three_mul_ofInt, ← hnu, ← hnv, ← hnc, hcB]
    rw [AV.ofInt_sub] at e
    have e2 := AV.ofInt_injective e
    funext i
    have := congrFun e2 i
    simp only [Pi.sub_apply] at this
    omega
  have hN : ((nrdZ nu : ℤ) : ZMod 3) ≠ 0 := by
    intro h0
    have e := nrdZ_mul nv nu
    rw [key] at e
    have e3 := congrArg (fun z : ℤ => (z : ZMod 3)) e
    simp only [nrdZ_mod3, Int.cast_mul, h0, mul_zero] at e3
    exact one_ne_zero e3
  have hN' : ((nu 0 : ℤ) : ZMod 3) ^ 2 + (nu 0 : ZMod 3) * (nu 2 : ZMod 3) +
      (nu 2 : ZMod 3) ^ 2 - 2 * (nu 1 : ZMod 3) ^ 2 - 2 * (nu 1 : ZMod 3) * (nu 3 : ZMod 3) -
      2 * (nu 3 : ZMod 3) ^ 2 ≠ 0 := by
    have : ((nrdZ nu : ℤ) : ZMod 3) = ((nu 0 : ℤ) : ZMod 3) ^ 2 + (nu 0 : ZMod 3) * (nu 2 : ZMod 3) +
      (nu 2 : ZMod 3) ^ 2 - 2 * (nu 1 : ZMod 3) ^ 2 - 2 * (nu 1 : ZMod 3) * (nu 3 : ZMod 3) -
      2 * (nu 3 : ZMod 3) ^ 2 := by simp [nrdZ]
    rwa [← this]
  obtain ⟨n, m, hnm, hmn, h0, h1, h2, h3⟩ := unit_table _ _ _ _ hN'
  have hdiv : ∀ i, (3 : ℤ) ∣ n i - nu i := by
    intro i
    have hi : ((nu i : ℤ) : ZMod 3) = ((n i : ℤ) : ZMod 3) := by
      fin_cases i
      · exact h0.symm
      · exact h1.symm
      · exact h2.symm
      · exact h3.symm
    exact_mod_cast (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 3).1 hi
  choose k hk using hdiv
  let u : Oˣ :=
    { val := ⟨ofInt n, ⟨n, rfl⟩⟩
      inv := ⟨ofInt m, ⟨m, rfl⟩⟩
      val_inv := by
        apply Subtype.ext
        change ofInt n * ofInt m = 1
        rw [ofInt_mul, hnm, ofInt_one]
      inv_val := by
        apply Subtype.ext
        change ofInt m * ofInt n = 1
        rw [ofInt_mul, hmn, ofInt_one] }
  refine ⟨u, ⟨ofInt k, ⟨k, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change ofInt n - (u₀ : B) = ((3 : O) : B) * ofInt k
  rw [hnu, h33, AV.ofInt_sub, AV.three_mul_ofInt]
  congr 1
  funext i
  simp [hk i]

theorem π3_map (α : O ≃+* O) {x y : O} (h : π3 x = π3 y) : π3 (α x) = π3 (α y) := by
  obtain ⟨c, hc⟩ := π3_eq_iff.1 h
  exact π3_eq_iff.2 ⟨α c, by rw [← map_sub, hc, map_mul, map_ofNat]⟩

/-! ## §2 Level structures: residues of endomorphisms, isomorphisms of objects -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

section Objects

variable {K : Type} [Field K]

theorem eta_eq_of_π3 {A : AbVar K} {q : QMStr A} (e : Level3 q) {x y : O} (h : π3 x = π3 y) :
    e.eta x = e.eta y := (e.eq_iff x y).2 (π3_eq_iff.1 h)

theorem π3_of_eta_eq {A : AbVar K} {q : QMStr A} (e : Level3 q) {x y : O} (h : e.eta x = e.eta y) :
    π3 x = π3 y := π3_eq_iff.2 ((e.eq_iff x y).1 h)

theorem endPt_iota {A : AbVar K} (q : QMStr A) (a : O) (y : Additive (A.Pt K)) :
    endPt A K (q.iota a) y = qmAct q K a y := rfl

/-- `3`-torsion `K`-points are level points (given `TorsionStructure`). -/
theorem torsion_eq_eta (hT : ObjBridge.TorsionStructure) [CharZero K] (P : QML3 K)
    (y : Additive (P.A.Pt K)) (hy : (3 : ℕ) • y = 0) : ∃ b : O, y = P.e.eta b := by
  have h1 : Additive.toMul y ^ 3 = 1 := by rw [← toMul_nsmul, hy]; rfl
  have hx : bcPt P.A (Additive.toMul y) ^ 3 = 1 := by
    rw [bcPt, ← MonObj.comp_pow, h1]; exact MonObj.comp_one _
  obtain ⟨a, ha⟩ := Level3.onto hT P _ hx
  exact ⟨a, (Additive.toMul.injective (bcPt_injective P.A ha)).symm⟩

/-- **Residue of a `β`-semilinear endomorphism on the level points**: if `g ι(β a) = ι(a) g`, then
`g(η(β x)) = η(x u₀)` for some `u₀ ∈ 𝒪` (`u₀` with `η(u₀) = g(η(1))`). -/
theorem residue (hT : ObjBridge.TorsionStructure) [CharZero K] (P : QML3 K) (β : O →+* O)
    (g : AbVar.End P.A) (hg : ∀ a, g * P.q.iota (β a) = P.q.iota a * g) :
    ∃ u₀ : O, ∀ x, endPt P.A K g (P.e.eta (β x)) = P.e.eta (x * u₀) := by
  have h3 : (3 : ℕ) • endPt P.A K g (P.e.eta 1) = 0 := by
    rw [← map_nsmul, ← map_nsmul, P.e.ker _ |>.2 ⟨1, by simp⟩, map_zero]
  obtain ⟨u₀, hu⟩ := torsion_eq_eta hT P _ h3
  refine ⟨u₀, fun x => ?_⟩
  have e1 : P.e.eta (β x) = qmAct P.q K (β x) (P.e.eta 1) := by
    rw [← P.e.linear, _root_.mul_one]
  rw [e1, ← endPt_iota]
  calc endPt P.A K g (endPt P.A K (P.q.iota (β x)) (P.e.eta 1))
      = endPt P.A K (g * P.q.iota (β x)) (P.e.eta 1) := by rw [map_mul]; rfl
    _ = endPt P.A K (P.q.iota x * g) (P.e.eta 1) := by rw [hg]
    _ = endPt P.A K (P.q.iota x) (endPt P.A K g (P.e.eta 1)) := by rw [map_mul]; rfl
    _ = P.e.eta (x * u₀) := by rw [hu, endPt_iota, ← P.e.linear]

/-- The same for an endomorphism commuting with `ι(𝒪)`. -/
theorem residue_com (hT : ObjBridge.TorsionStructure) [CharZero K] (P : QML3 K)
    (c : AbVar.End P.A) (hc : c ∈ com P.q) :
    ∃ c₀ : O, ∀ x, endPt P.A K c (P.e.eta x) = P.e.eta (x * c₀) := by
  have hg : ∀ a, c * P.q.iota (RingHom.id O a) = P.q.iota a * c := by
    intro a
    rw [com, Subring.mem_centralizer_iff] at hc
    exact (hc _ ⟨a, rfl⟩).symm
  exact residue hT P (RingHom.id O) c hg

/-- An isomorphism of objects on the same abelian variety from a unit of `End(A)`. -/
def isoMk (A : AbVar K) (s : A.dim = 2) {q q' : QMStr A} (e : Level3 q) (e' : Level3 q')
    (φ ψ : AbVar.End A) (h1 : ψ * φ = 1) (h2 : φ * ψ = 1)
    (heq : ∀ a, φ * q.iota a = q'.iota a * φ)
    (hl : ∀ a, endPt A K φ (e.eta a) = e'.eta a) :
    QML3.Iso (⟨A, s, q, e⟩ : QML3 K) ⟨A, s, q', e'⟩ where
  φ := φ
  ψ := ψ
  left := congrArg AbVar.Hom.hom h1
  right := congrArg AbVar.Hom.hom h2
  equivariant a := congrArg AbVar.Hom.hom (heq a)
  level a := hl a

/-- The equivariance of an isomorphism, in `End(A)`. -/
theorem Iso.equiv_end {A : AbVar K} {s : A.dim = 2} {q q' : QMStr A} {e : Level3 q} {e' : Level3 q'}
    (f : QML3.Iso (⟨A, s, q, e⟩ : QML3 K) ⟨A, s, q', e'⟩) (a : O) :
    f.φ * q.iota a = q'.iota a * f.φ := AbVar.Hom.ext' (f.equivariant a)

theorem Iso.level_end {A : AbVar K} {s : A.dim = 2} {q q' : QMStr A} {e : Level3 q} {e' : Level3 q'}
    (f : QML3.Iso (⟨A, s, q, e⟩ : QML3 K) ⟨A, s, q', e'⟩) (a : O) :
    endPt A K f.φ (e.eta a) = e'.eta a := f.level a

theorem Iso.left_end {A : AbVar K} {s : A.dim = 2} {q q' : QMStr A} {e : Level3 q} {e' : Level3 q'}
    (f : QML3.Iso (⟨A, s, q, e⟩ : QML3 K) ⟨A, s, q', e'⟩) : f.ψ * f.φ = 1 := AbVar.Hom.ext' f.left

theorem endPt_intCast (A : AbVar K) (n : ℤ) (y : Additive (A.Pt K)) :
    endPt A K (n : AbVar.End A) y = n • y := by
  rw [map_intCast, AddMonoid.End.intCast_apply]

theorem eta_zsmul {A : AbVar K} {q : QMStr A} (e : Level3 q) (n : ℤ) (x : O) :
    n • e.eta x = e.eta ((n : O) * x) := by
  rw [← map_zsmul, zsmul_eq_mul]

end Objects


/-! ## §3 The operation `T = twist α ∘ rightMul u` from a semilinear unit `g` with `g² = ±1` -/

theorem sign_cases {ε : ℤ} (hε : ε * ε = 1) : ε = 1 ∨ ε = -1 := by
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hε with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

theorem sgn1 {R : Type} [Ring R] {ε : ℤ} (hε : ε * ε = 1) (a p q : R) (h : p * q = ε) :
    a * ((ε : R) * p) * q = a := by
  rcases sign_cases hε with rfl | rfl <;> simp only [Int.cast_one, Int.cast_neg] at h ⊢
  · calc a * (1 * p) * q = a * (p * q) := by noncomm_ring
      _ = a := by rw [h, _root_.mul_one]
  · calc a * (-1 * p) * q = -(a * (p * q)) := by noncomm_ring
      _ = a := by rw [h]; noncomm_ring

theorem sgn2 {R : Type} [Ring R] {ε : ℤ} (hε : ε * ε = 1) (a p q : R) (h : p * q = ε) :
    (ε : R) * (a * ((ε : R) * p) * ((ε : R) * q)) = a := by
  rcases sign_cases hε with rfl | rfl <;> simp only [Int.cast_one, Int.cast_neg] at h ⊢
  · calc 1 * (a * (1 * p) * (1 * q)) = a * (p * q) := by noncomm_ring
      _ = a := by rw [h, _root_.mul_one]
  · calc -1 * (a * (-1 * p) * (-1 * q)) = -(a * (p * q)) := by noncomm_ring
      _ = a := by rw [h]; noncomm_ring

section Stab

variable {K : Type} [Field K]

/-- **The stabilizing involution.** Let `α` be an involution of `𝒪` and `g ∈ End(A)` with
`g ι(α a) = ι(a) g` and `g² = ε = ±1`. Then `g(η(α x)) = η(x u₀)` with `α(u₀) u₀ ≡ ε (mod 3)`, and for a
unit `u ≡ ε u₀ (mod 3)` the operation `T = twist α ∘ rightMul u` fixes the class of `P` (by `g`) and
`T² = id` on all classes (`T² = rightMul(α(u) u)`, `α(u) u ≡ ε`, and `−1` acts trivially). -/
theorem stab_core (hT : ObjBridge.TorsionStructure) [CharZero K] (P : QML3 K) (α : O ≃+* O)
    (hα : ∀ a, α (α a) = a) (g : AbVar.End P.A) (ε : ℤ) (hε : ε * ε = 1)
    (hgg : g * g = (ε : AbVar.End P.A)) (hg : ∀ a, g * P.q.iota (α a) = P.q.iota a * g) :
    ∃ u₀ : O, (∀ x, endPt P.A K g (P.e.eta (α x)) = P.e.eta (x * u₀)) ∧
      π3 (α u₀) * π3 u₀ = (ε : Q3) ∧
      ∃ u : Oˣ, π3 (u : O) = (ε : Q3) * π3 u₀ ∧
        M3.twist α (M3.rightMul u (M3.mk P)) = M3.mk P ∧
        ∀ m : M3 K, M3.twist α (M3.rightMul u (M3.twist α (M3.rightMul u m))) = m := by
  obtain ⟨u₀, hu₀⟩ := residue hT P α.toRingHom g (fun a => hg a)
  have hu₀' : ∀ x, endPt P.A K g (P.e.eta (α x)) = P.e.eta (x * u₀) := hu₀
  have hgy : ∀ y, endPt P.A K g (P.e.eta y) = P.e.eta (α y * u₀) := by
    intro y; have := hu₀' (α y); rwa [hα] at this
  have hsq : π3 (α u₀) * π3 u₀ = (ε : Q3) := by
    have e1 : endPt P.A K (g * g) (P.e.eta 1) = P.e.eta (α u₀ * u₀) := by
      rw [map_mul]
      change endPt P.A K g (endPt P.A K g (P.e.eta 1)) = _
      rw [hgy 1, map_one, _root_.one_mul, hgy]
    have e2 : endPt P.A K (g * g) (P.e.eta 1) = P.e.eta (ε : O) := by
      rw [hgg, endPt_intCast, eta_zsmul, _root_.mul_one]
    have := π3_of_eta_eq P.e (e1.symm.trans e2)
    rwa [map_mul, map_intCast] at this
  have hinv : π3 (α u₀ * ((ε : O) * u₀)) = π3 1 := by
    rw [map_mul, map_mul, map_intCast, map_one, ← _root_.mul_assoc, ← (Int.cast_commute ε _).eq,
      _root_.mul_assoc, hsq, ← Int.cast_mul, hε, Int.cast_one]
  obtain ⟨u, c, hc⟩ := exists_unit_congr ((ε : O) * u₀) (α u₀) (π3_eq_iff.1 hinv)
  have hu : π3 (u : O) = (ε : Q3) * π3 u₀ := by
    rw [π3_eq_iff.2 ⟨c, hc⟩, map_mul, map_intCast]
  have hαu : π3 (α u) = (ε : Q3) * π3 (α u₀) := by
    have := π3_map α (π3_eq_iff.2 ⟨c, hc⟩)
    rw [this, map_mul, map_intCast, map_mul, map_intCast]
  refine ⟨u₀, hu₀', hsq, u, hu, ?_, ?_⟩
  · show M3.mk ((P.rightMul u).twist α) = M3.mk P
    have h1 : ((ε : AbVar.End P.A) * g) * g = 1 := by
      rw [_root_.mul_assoc, hgg, ← Int.cast_mul, hε, Int.cast_one]
    have h2 : g * ((ε : AbVar.End P.A) * g) = 1 := by
      rw [← _root_.mul_assoc, ← (Int.cast_commute ε g).eq, h1]
    refine Quotient.sound ⟨isoMk P.A P.surface _ _ g ((ε : AbVar.End P.A) * g) h1 h2
      (fun a => hg a) (fun a => ?_)⟩
    change endPt P.A K g (P.e.eta (α a * u)) = P.e.eta a
    rw [show α a * (u : O) = α (a * α u) by rw [map_mul, hα], hu₀']
    apply eta_eq_of_π3
    rw [map_mul, map_mul, hαu]
    exact sgn1 hε _ _ _ hsq
  · intro m
    induction m using Quotient.inductionOn with
    | h Q =>
      show M3.mk ((((Q.rightMul u).twist α).rightMul u).twist α) = M3.mk Q
      have h1 : (ε : AbVar.End Q.A) * (ε : AbVar.End Q.A) = 1 := by
        rw [← Int.cast_mul, hε, Int.cast_one]
      refine Quotient.sound ⟨isoMk Q.A Q.surface _ _ (ε : AbVar.End Q.A) (ε : AbVar.End Q.A) h1 h1
        (fun a => ?_) (fun a => ?_)⟩
      · change (ε : AbVar.End Q.A) * Q.q.iota (α (α a)) = Q.q.iota a * ε
        rw [hα, (Int.cast_commute ε _).eq]
      · change endPt Q.A K (ε : AbVar.End Q.A) (Q.e.eta (α (α a * u) * u)) = Q.e.eta a
        rw [endPt_intCast, eta_zsmul, map_mul α, hα]
        apply eta_eq_of_π3
        rw [map_mul, map_mul, map_mul, map_intCast, hαu, hu]
        exact sgn2 hε _ _ _ hsq

end Stab


/-! ## §4 The lattice model of `End(A)` over `ℚ̄` (gt-qm's `unif_conj`, transported as in `yuB6Emb_of`) -/

open HDec.QMSplit.CNO (act act_mul act_one act_smul mem_qmOrbit_iff)

/-- **`End(A)` for an abelian surface with QM over `ℚ̄`, as the ring of `ℂ`-linear maps preserving the
lattice `ι(𝒪)(τ, 1)ᵀ`**: `ρ` is injective, `ρ(ι(a)) = ι(a)`, and its image is exactly the maps preserving
the lattice. (gt-qm's `unif_conj` over `ℂ`, composed with `End(A) ≅ End(A_ℂ)` from T11(b), which the
chain proves, along an embedding `ℚ̄ → ℂ`.) -/
theorem lat_model (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed)
    (A : AbVar Qbar) (hA : A.dim = 2) (q : QMStr A) :
    ∃ (τ : ℂ) (_ : 0 < τ.im) (ρ : AbVar.End A →+* Module.End ℂ (Fin 2 → ℂ)),
      Function.Injective ρ ∧ (∀ a z, ρ (q.iota a) z = act (a : B) z) ∧
      ∀ N : Module.End ℂ (Fin 2 → ℂ),
        (∀ z ∈ HDec.FibreQMNorm.qmOrbit ![τ, 1], N z ∈ HDec.FibreQMNorm.qmOrbit ![τ, 1]) ↔
          ∃ e, ρ e = N := by
  have hR : ZInQ.LeafPush2.T11b_Rigidity := HDec.AVB2.t11b_of_exists HDec.HSyn.t11bExists_lf8
  let σ : AlgebraicClosure ℚ →+* ℂ := (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ).toRingHom
  letI : Algebra (AlgebraicClosure ℚ) ℂ := σ.toAlgebra
  let e := HDec.G0ModField.KernelField.endBC A ℂ
  have he : Function.Bijective e := by
    refine ⟨HDec.G0ModField.KernelField.endBC_injective A ℂ, fun g => ?_⟩
    obtain ⟨φ, ⟨hφ, hφe⟩, -⟩ := hR (AlgebraicClosure ℚ) ℂ A A g.hom inferInstance
    exact ⟨AbVar.Hom.mk' φ, AbVar.Hom.ext' hφe⟩
  let qC : QMStr (A.baseChange ℂ) := ⟨e.comp q.iota, he.1.comp q.injective⟩
  have hdim : (A.baseChange ℂ).dim = 2 := by rw [AbVar.dim_baseChange]; exact hA
  obtain ⟨τ, hτ, ρ, hρinj, hρι, hρrange⟩ := HDec.QMLattice.unif_conj hU hG hM (A.baseChange ℂ) hdim qC
  refine ⟨τ, hτ, ρ.comp e, hρinj.comp he.1, fun a z => hρι a z, fun N => ?_⟩
  rw [hρrange N]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨m, hm⟩ := he.2 g
    exact ⟨m, by rw [RingHom.comp_apply, hm, hg]⟩
  · rintro ⟨m, hm⟩
    exact ⟨e m, hm⟩

theorem act_intCast (n : ℤ) (z : Fin 2 → ℂ) : act (n : B) z = n • z := by
  rw [show ((n : B)) = ((n : ℚ) • (1 : B)) by rw [Algebra.smul_def, _root_.mul_one]; simp,
    act_smul, act_one, Rat.cast_intCast]
  exact Int.cast_smul_eq_zsmul ℂ n z

section Lattice

variable {A : AbVar Qbar} {q : QMStr A} {τ : ℂ}
  {ρ : AbVar.End A →+* Module.End ℂ (Fin 2 → ℂ)}

theorem rho_comm_act (hρι : ∀ a z, ρ (q.iota a) z = act (a : B) z) {s : AbVar.End A}
    (hs : s ∈ com q) (x : O) (z : Fin 2 → ℂ) : ρ s (act (x : B) z) = act (x : B) (ρ s z) := by
  have hc : s * q.iota x = q.iota x * s := by
    rw [com, Subring.mem_centralizer_iff] at hs
    exact (hs _ ⟨x, rfl⟩).symm
  rw [← hρι, ← hρι, ← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]


/-- **`End_𝒪(A)` is commutative** (its elements act on `ℂ²` by scalars, gt-qm's `commutant`). -/
theorem com_comm (hρinj : Function.Injective ρ) (hρι : ∀ a z, ρ (q.iota a) z = act (a : B) z)
    {c s : AbVar.End A} (hc : c ∈ com q) (hs : s ∈ com q) : c * s = s * c := by
  obtain ⟨c1, hc1⟩ := HDec.QMLattice.commutant (ρ c) (fun x hx z => rho_comm_act hρι hc ⟨x, hx⟩ z)
  obtain ⟨c2, hc2⟩ := HDec.QMLattice.commutant (ρ s) (fun x hx z => rho_comm_act hρι hs ⟨x, hx⟩ z)
  apply hρinj
  refine LinearMap.ext fun z => ?_
  simp only [map_mul, Module.End.mul_apply, hc1, hc2, map_smul, smul_smul, mul_comm]

/-- **An Atkin–Lehner-type semilinear unit.** Let `t ∈ 𝒪` with inverse `t' = r t` in `B`, `α(x) = t' x t`
an automorphism of `𝒪` with `t' α(a) = a t'`, and `s ∈ End_𝒪(A)` with `s² = d`, such that every
`y ∈ 𝒪` with `y² = d` lies in `t𝒪`. Then `g = ι(t)⁻¹ s ∈ End(A)`: `ι(t) g = s`, `g² = t'² d = ε`, and
`g ι(α a) = ι(a) g`. (In the lattice model `g` is `ι(t') ∘ ρ(s)`, which preserves `ι(𝒪)(τ, 1)ᵀ`.) -/
theorem semilinear_unit (hρinj : Function.Injective ρ)
    (hρι : ∀ a z, ρ (q.iota a) z = act (a : B) z)
    (hρrange : ∀ N : Module.End ℂ (Fin 2 → ℂ),
        (∀ z ∈ HDec.FibreQMNorm.qmOrbit ![τ, 1], N z ∈ HDec.FibreQMNorm.qmOrbit ![τ, 1]) ↔
          ∃ e, ρ e = N) (hτ : 0 < τ.im)
    (t : O) (r : ℚ) (α : O ≃+* O) (d ε : ℤ)
    (h1 : ∀ x : O, (r • (t : B)) * x * t = (α x : B))
    (h2 : ∀ a : O, (r • (t : B)) * (α a : B) = (a : B) * (r • (t : B)))
    (h3 : (t : B) * (r • (t : B)) = 1)
    (h4 : (r • (t : B)) * (r • (t : B)) * (d : B) = (ε : B))
    (hdiv : ∀ y : O, y * y = (d : O) → ∃ e : O, y = t * e)
    (s : AbVar.End A) (hs : s ∈ com q) (hss : s * s = (d : AbVar.End A)) :
    ∃ g : AbVar.End A, q.iota t * g = s ∧ g * g = (ε : AbVar.End A) ∧
      ∀ a, g * q.iota (α a) = q.iota a * g := by
  set v : Fin 2 → ℂ := ![τ, 1] with hvdef
  have hv : v ≠ 0 := fun h => by simpa [v] using congrFun h 1
  have hvorb : v ∈ HDec.FibreQMNorm.qmOrbit v := (mem_qmOrbit_iff _ _).2 ⟨1, O.one_mem, (act_one _).symm⟩
  let T := HDec.QMLattice.actHom (r • (t : B))
  have hT : ∀ z, T z = act (r • (t : B)) z := fun z => HDec.QMLattice.actHom_apply _ z
  let N : Module.End ℂ (Fin 2 → ℂ) := T * ρ s
  -- `ρ(s) v = ι(y) v` with `y² = d`
  obtain ⟨y, hyO, hy⟩ := (mem_qmOrbit_iff _ _).1 ((hρrange (ρ s)).2 ⟨s, rfl⟩ v hvorb)
  have hsx : ∀ x : O, ρ s (act (x : B) v) = act ((x : B) * y) v := by
    intro x; rw [rho_comm_act hρι hs, hy, act_mul]
  have hyy : (⟨y, hyO⟩ : O) * ⟨y, hyO⟩ = (d : O) := by
    apply Subtype.ext
    have e1 : ρ (s * s) v = act (y * y) v := by
      rw [map_mul, Module.End.mul_apply, hy]
      exact hsx ⟨y, hyO⟩
    have e2 : ρ (s * s) v = act (d : B) v := by
      rw [hss, map_intCast, Module.End.intCast_apply, act_intCast]
    have := HDec.QMLattice.act_inj hv (e1.symm.trans e2)
    simpa using this
  obtain ⟨e0, he0⟩ := hdiv _ hyy
  have hyB : y = (t : B) * e0 := congrArg Subtype.val he0
  have hN : ∀ z ∈ HDec.FibreQMNorm.qmOrbit v, N z ∈ HDec.FibreQMNorm.qmOrbit v := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (mem_qmOrbit_iff _ _).1 hz
    rw [mem_qmOrbit_iff]
    refine ⟨(α ⟨x, hx⟩ : B) * e0, O.mul_mem (α ⟨x, hx⟩).2 e0.2, ?_⟩
    change T (ρ s (act ((⟨x, hx⟩ : O) : B) v)) = _
    rw [hsx, hT, ← act_mul, hyB, ← h1 ⟨x, hx⟩]
    congr 1
    noncomm_ring
  obtain ⟨g, hg⟩ := (hρrange N).1 hN
  -- `ρ s` commutes with `T`
  have hsT : ρ s * T = T * ρ s := by
    refine LinearMap.ext fun z => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hT, hT, act_smul, act_smul, map_smul]
    congr 1
    exact rho_comm_act hρι hs t z
  refine ⟨g, ?_, ?_, fun a => ?_⟩
  · apply hρinj
    rw [map_mul, hg]
    refine LinearMap.ext fun z => ?_
    rw [Module.End.mul_apply, hρι]
    change act (t : B) (T (ρ s z)) = ρ s z
    rw [hT, ← act_mul, h3, act_one]
  · apply hρinj
    rw [map_mul, hg, map_intCast]
    calc T * ρ s * (T * ρ s) = T * T * (ρ s * ρ s) := by
          rw [_root_.mul_assoc, ← _root_.mul_assoc (ρ s), hsT]; noncomm_ring
      _ = (ε : Module.End ℂ (Fin 2 → ℂ)) := by
          rw [← map_mul ρ, hss, map_intCast]
          refine LinearMap.ext fun z => ?_
          rw [Module.End.mul_apply, Module.End.mul_apply, hT, hT, Module.End.intCast_apply,
            Module.End.intCast_apply, ← act_intCast, ← act_mul, ← act_mul, h4, act_intCast]
  · apply hρinj
    rw [map_mul, map_mul, hg]
    refine LinearMap.ext fun z => ?_
    simp only [Module.End.mul_apply]
    rw [hρι, hρι]
    change T (ρ s (act (α a : B) z)) = act (a : B) (T (ρ s z))
    rw [rho_comm_act hρι hs, hT, hT, ← act_mul, ← act_mul, h2]

end Lattice


/-! ## §5 `T` is not the identity -/

section NonId

variable {K : Type} [Field K]

theorem finA : ∀ U C : F9, ∀ e : ZMod 3, e * e = 1 → gm (cj U) U = (e, 0) →
    gm U C = gm (cj C) U → gm (gm (gm (cj (gm (e, 0) U)) (cj (1, 1))) U) C ≠ (1, 1) := by
  decide

theorem red_intCast (n : ℤ) : red (n : O) = ((n : ZMod 3), 0) := by
  rw [red, coords_intCast]; simp [redC]

/-- **An isomorphism `T(m) ≅ m` for `m = rightMul w P`** gives `c = h g⁻¹ ∈ End_𝒪(A)` with residue `c₀` and
`α(u) α(w) u₀ c₀ ≡ w (mod 3)`. -/
theorem nonid_core (hT : ObjBridge.TorsionStructure) [CharZero K] (P : QML3 K) (α : O ≃+* O)
    (hα : ∀ a, α (α a) = a) (g : AbVar.End P.A) (ε : ℤ) (hε : ε * ε = 1)
    (hgg : g * g = (ε : AbVar.End P.A)) (hg : ∀ a, g * P.q.iota (α a) = P.q.iota a * g)
    (u₀ : O) (hu₀ : ∀ x, endPt P.A K g (P.e.eta (α x)) = P.e.eta (x * u₀)) (u w : Oˣ)
    (hTm : M3.twist α (M3.rightMul u (M3.mk (P.rightMul w)))  = M3.mk (P.rightMul w)) :
    ∃ c ∈ com P.q, ∃ c₀ : O, (∀ x, endPt P.A K c (P.e.eta x) = P.e.eta (x * c₀)) ∧
      π3 (α u * α w * u₀ * c₀) = π3 (w : O) := by
  obtain ⟨h⟩ := Quotient.exact hTm
  have h' : QML3.Iso (⟨P.A, P.surface, P.q.twist α, ((P.e.rightMul w).rightMul u).twist α⟩ : QML3 K)
      ⟨P.A, P.surface, P.q, P.e.rightMul w⟩ := h
  set H := h'.φ with hHdef
  have heqH : ∀ a, H * P.q.iota (α a) = P.q.iota a * H := fun a => Iso.equiv_end h' a
  have hgα : ∀ a, g * P.q.iota a = P.q.iota (α a) * g := by
    intro a; have := hg (α a); rwa [hα] at this
  set c : AbVar.End P.A := H * g * (ε : AbVar.End P.A) with hcdef
  have hc : c ∈ com P.q := by
    rw [com, Subring.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    show P.q.iota a * c = c * P.q.iota a
    calc P.q.iota a * c = P.q.iota a * H * g * (ε : AbVar.End P.A) := by rw [hcdef]; noncomm_ring
      _ = H * P.q.iota (α a) * g * (ε : AbVar.End P.A) := by rw [heqH]
      _ = H * (g * P.q.iota a) * (ε : AbVar.End P.A) := by rw [hgα]; noncomm_ring
      _ = H * g * ((ε : AbVar.End P.A) * P.q.iota a) := by
          rw [(Int.cast_commute ε (P.q.iota a)).eq]; noncomm_ring
      _ = c * P.q.iota a := by rw [hcdef]; noncomm_ring
  have hcg : c * g = H := by
    calc c * g = H * g * ((ε : AbVar.End P.A) * g) := by rw [hcdef]; noncomm_ring
      _ = H * g * (g * (ε : AbVar.End P.A)) := by rw [(Int.cast_commute ε g).eq]
      _ = H * (g * g) * (ε : AbVar.End P.A) := by noncomm_ring
      _ = H := by rw [hgg, _root_.mul_assoc, ← Int.cast_mul, hε, Int.cast_one, _root_.mul_one]
  obtain ⟨c₀, hc₀⟩ := residue_com hT P c hc
  refine ⟨c, hc, c₀, hc₀, ?_⟩
  have hl : endPt P.A K H (P.e.eta ((α 1 * u) * w)) = P.e.eta (1 * w) := Iso.level_end h' 1
  rw [map_one, _root_.one_mul, _root_.one_mul,
    show (u : O) * w = α (α u * α w) by rw [map_mul, hα, hα], ← hcg, map_mul] at hl
  change endPt P.A K c (endPt P.A K g (P.e.eta (α (α u * α w)))) = _ at hl
  rw [hu₀, hc₀] at hl
  exact π3_of_eta_eq P.e hl

/-- **`T ≠ id` in the cases `ℤ[ζ₃]` and `ℤ[√−6]`** (`α` conjugation by `t = j` or `k`, `s = ι(t) g ∈ End_𝒪(A)`):
`T` moves the class of `rightMul (1 + i) P`. Modulo `𝔓₃`, `c₀` would be `(1+i)/(1−i) = i`, but commuting
with `s̄ = t u₀` forces `c̄₀ = c̄₀^σ ∈ 𝔽₃`. -/
theorem nonid_t (hT : ObjBridge.TorsionStructure) [CharZero K] (P : QML3 K) (α : O ≃+* O)
    (hα : ∀ a, α (α a) = a) (t : O) (ht : ∀ z, t * α z = z * t)
    (hredt : ∀ z, π3 (t * z) = 0 → red z = 0) (hredα : ∀ z, red (α z) = cj (red z))
    (g : AbVar.End P.A) (ε : ℤ) (hε : ε * ε = 1)
    (hgg : g * g = (ε : AbVar.End P.A)) (hg : ∀ a, g * P.q.iota (α a) = P.q.iota a * g)
    (hcomm : ∀ c ∈ com P.q, c * (P.q.iota t * g) = (P.q.iota t * g) * c)
    (u₀ : O) (hu₀ : ∀ x, endPt P.A K g (P.e.eta (α x)) = P.e.eta (x * u₀))
    (hsq : π3 (α u₀) * π3 u₀ = (ε : Q3)) (u : Oˣ) (hu : π3 (u : O) = (ε : Q3) * π3 u₀) :
    M3.twist α (M3.rightMul u (M3.mk (P.rightMul w1U))) ≠ M3.mk (P.rightMul w1U) := by
  intro hTm
  obtain ⟨c, hc, c₀, hc₀, heq⟩ := nonid_core hT P α hα g ε hε hgg hg u₀ hu₀ u w1U hTm
  have hgy : ∀ y, endPt P.A K g (P.e.eta y) = P.e.eta (α y * u₀) := by
    intro y; have := hu₀ (α y); rwa [hα] at this
  have hs : ∀ z, endPt P.A K (P.q.iota t * g) (P.e.eta z) = P.e.eta (z * (t * u₀)) := by
    intro z
    rw [map_mul]
    change endPt P.A K (P.q.iota t) (endPt P.A K g (P.e.eta z)) = _
    rw [hgy, endPt_iota, ← P.e.linear, ← _root_.mul_assoc, ht, _root_.mul_assoc]
  have hcs := hcomm c hc
  have e1 : P.e.eta (t * u₀ * c₀) = P.e.eta (c₀ * (t * u₀)) := by
    have := congrArg (fun f => endPt P.A K f (P.e.eta 1)) hcs
    simp only [map_mul] at this
    change endPt P.A K c (endPt P.A K (P.q.iota t * g) (P.e.eta 1)) =
      endPt P.A K (P.q.iota t * g) (endPt P.A K c (P.e.eta 1)) at this
    rwa [hs, hc₀, hc₀, hs, _root_.one_mul, _root_.one_mul] at this
  have e2 : π3 (t * (u₀ * c₀ - α c₀ * u₀)) = 0 := by
    have := π3_of_eta_eq P.e e1
    rw [← _root_.mul_assoc c₀, ← ht c₀] at this
    rw [mul_sub, map_sub, sub_eq_zero, ← _root_.mul_assoc, ← _root_.mul_assoc]
    exact this
  have hC := hredt _ e2
  rw [red_sub, red_mul, red_mul, hredα, sub_eq_zero] at hC
  have hW := red_congr heq
  rw [red_mul, red_mul, red_mul, hredα, hredα] at hW
  have hU : red (u : O) = gm ((ε : ZMod 3), 0) (red u₀) := by
    have : π3 (u : O) = π3 ((ε : O) * u₀) := by rw [hu, map_mul, map_intCast]
    rw [red_congr this, red_mul, red_intCast]
  have hS : gm (cj (red u₀)) (red u₀) = ((ε : ZMod 3), 0) := by
    have : π3 (α u₀ * u₀) = π3 (ε : O) := by rw [map_mul, hsq, map_intCast]
    have h2 := red_congr this
    rwa [red_mul, hredα, red_intCast] at h2
  have he : ((ε : ZMod 3)) * (ε : ZMod 3) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod 3) hε; push_cast at this; exact this
  rw [hU, show red ((w1U : Oˣ) : O) = (1, 1) from red_w1] at hW
  exact finA _ _ _ he hS hC hW


theorem gm_zero_left (x : F9) : gm 0 x = 0 := by ext <;> simp [gm]
theorem gm_zero_right (x : F9) : gm x 0 = 0 := by ext <;> simp [gm]

theorem finB : ∀ U D : F9, gm U U = (-1, 0) → gm (cj U) D = gm D U →
    D - gm (cj U) U - gm (gm (gm (cj U) U) 0) D - (1, 0) = 0 → False := by
  decide

/-- A unit `w ≡ 1 + j (mod 3)`. -/
theorem exists_w4 : ∃ w : Oˣ, π3 (w : O) = π3 (1 + oj) := by
  obtain ⟨w, c, hc⟩ := exists_unit_congr (1 + oj) (1 - oj) ⟨1, by
    calc (1 - oj) * (1 + oj) - 1 = -(oj * oj) := by noncomm_ring
      _ = 3 * 1 := by rw [AV.oj_mul_oj, neg_neg, _root_.mul_one]⟩
  exact ⟨w, π3_eq_iff.2 ⟨c, hc⟩⟩

/-- **`T ≠ id` in the case `ℤ[i]`** (`α = id`, `g = φ`, `φ² = −1`): `T = rightMul u` moves the class of
`rightMul w P` for a unit `w ≡ 1 + j`. Modulo `𝔓₃` the commutator equations force `c₀ = 1 + j d` with
`d̄ = −1` and `d̄ = 0` at once. -/
theorem nonid_4 (hT : ObjBridge.TorsionStructure) [CharZero K] (P : QML3 K)
    (g : AbVar.End P.A) (hgg : g * g = ((-1 : ℤ) : AbVar.End P.A))
    (hg : ∀ a, g * P.q.iota (RingEquiv.refl O a) = P.q.iota a * g)
    (hcomm : ∀ c ∈ com P.q, c * g = g * c)
    (u₀ : O) (hu₀ : ∀ x, endPt P.A K g (P.e.eta (RingEquiv.refl O x)) = P.e.eta (x * u₀))
    (hsq : π3 (RingEquiv.refl O u₀) * π3 u₀ = ((-1 : ℤ) : Q3)) (u : Oˣ)
    (hu : π3 (u : O) = ((-1 : ℤ) : Q3) * π3 u₀) (w : Oˣ) (hw : π3 (w : O) = π3 (1 + oj)) :
    M3.twist (RingEquiv.refl O) (M3.rightMul u (M3.mk (P.rightMul w))) ≠ M3.mk (P.rightMul w) := by
  intro hTm
  obtain ⟨c, hc, c₀, hc₀, heq⟩ :=
    nonid_core hT P (RingEquiv.refl O) (fun a => rfl) g (-1) (by norm_num) hgg hg u₀ hu₀ u w hTm
  change π3 ((u : O) * w * u₀ * c₀) = π3 (w : O) at heq
  have hgy : ∀ y, endPt P.A K g (P.e.eta y) = P.e.eta (y * u₀) := hu₀
  have hcm : π3 (u₀ * c₀) = π3 (c₀ * u₀) := by
    have := congrArg (fun f => endPt P.A K f (P.e.eta 1)) (hcomm c hc)
    simp only [map_mul] at this
    change endPt P.A K c (endPt P.A K g (P.e.eta 1)) =
      endPt P.A K g (endPt P.A K c (P.e.eta 1)) at this
    rw [hgy, hc₀, hc₀, hgy, _root_.one_mul, _root_.one_mul] at this
    exact π3_of_eta_eq P.e this
  set U := π3 u₀ with hUdef
  set C := π3 c₀ with hCdef
  set J := π3 oj with hJdef
  set A' := π3 (αJ u₀) with hAdef
  have hUJ : U * J = J * A' := by
    have := congrArg π3 (oj_mul_αJ u₀)
    rw [map_mul, map_mul] at this
    exact this.symm
  have hUU : U * U = -1 := by
    have := hsq; push_cast at this; exact this
  have hu' : π3 (u : O) = -U := by rw [hu]; push_cast; rw [neg_one_mul]
  have heq' : -U * (1 + J) * U * C = 1 + J := by
    have := heq
    rw [map_mul, map_mul, map_mul, hu', hw] at this
    rw [map_add, map_one] at this
    exact this
  have step1 : C - J * A' * U * C = 1 + J := by
    calc C - J * A' * U * C = -(U * U) * C - (U * J) * U * C := by rw [hUU, hUJ]; noncomm_ring
      _ = -U * (1 + J) * U * C := by noncomm_ring
      _ = 1 + J := heq'
  have hr1 : red c₀ = (1, 0) := by
    have h1 : π3 (c₀ - oj * αJ u₀ * u₀ * c₀) = π3 (1 + oj) := by
      simp only [map_sub, map_mul, map_add, map_one]; exact step1
    have h2 := red_congr h1
    simp only [red_sub, red_mul, red_add, red_one, red_oj, gm_zero_left, gm_zero_right, sub_zero,
      add_zero] at h2
    exact h2
  obtain ⟨d, hd⟩ := div_j_of_red (c₀ - 1) (by rw [red_sub, hr1, red_one, sub_self])
  set D := π3 d with hDdef
  have hC : C = 1 + J * D := by
    have := congrArg π3 hd
    rw [map_sub, map_one, map_mul] at this
    rw [← this]; abel
  have step2 : π3 (oj * (d - αJ u₀ * u₀ - αJ u₀ * u₀ * oj * d - 1)) = 0 := by
    simp only [map_sub, map_mul, map_one]
    calc J * (D - A' * U - A' * U * J * D - 1)
        = (1 + J * D) - J * A' * U * (1 + J * D) - (1 + J) := by noncomm_ring
      _ = 0 := by rw [← hC, step1, sub_self]
  have hr2 := red_of_j_mul _ step2
  simp only [red_sub, red_mul, red_αJ, red_oj, red_one] at hr2
  have step3 : π3 (oj * (αJ u₀ * d - d * u₀)) = 0 := by
    simp only [map_sub, map_mul]
    calc J * (A' * D - D * U) = U * (1 + J * D) - (1 + J * D) * U := by
          rw [mul_sub, ← _root_.mul_assoc J A' D, ← hUJ]; noncomm_ring
      _ = 0 := by rw [← hC]; simp only [map_mul] at hcm; rw [hcm, sub_self]
  have hr3 := red_of_j_mul _ step3
  simp only [red_sub, red_mul, red_αJ, sub_eq_zero] at hr3
  have hr4 : gm (red u₀) (red u₀) = (-1, 0) := by
    have : π3 (u₀ * u₀) = π3 ((-1 : ℤ) : O) := by rw [map_mul, map_intCast]; exact hsq
    have h2 := red_congr this
    rw [red_mul, red_intCast] at h2
    rw [h2]; rfl
  exact finB _ _ hr4 hr3 hr2

end NonId


/-! ## §6 The cases -/

theorem oj_coe : ((oj : O) : B) = ⟨0, 0, 1, 0⟩ := by ext <;> simp [oj, ofInt]
theorem ok_coe : ((ok : O) : B) = ⟨0, 0, 0, 1⟩ := by ext <;> simp [ok, mkO, ofInt]

theorem iota_comm_of_mem {A : AbVar Qbar} {q : QMStr A} {φ : AbVar.End A}
    (hφ : φ ∈ com q) (a : O) : φ * q.iota a = q.iota a * φ := by
  rw [com, Subring.mem_centralizer_iff] at hφ
  exact (hφ _ ⟨a, rfl⟩).symm

end GapGlue.CMStab

namespace GapGlue

open LeafQM LeafQM.AV CMStab PkgI3

/- Copied verbatim from `scratch/mcr-quot/MCRQuot.lean`, lines 7637-7653 (namespace `MCRQuot`, where
`Qbar` is `AlgebraicClosure ℚ`). -/

/-- **Glue (C1b-obj): a CM object is fixed by a Hecke operation of order exactly 2 on classes**
(QM with CM; the elliptic points of `Y₃ → P¹` have stabilizers of even order `4, 6, 2` in the
group of Hecke operations on classes, `CoverBranchData`/`nY3`, Baba–Granath §3.1 (locator
UNVERIFIED)). For a level-3 object `P` over `ℚ̄` with CM by `ℤ[i]`, `ℤ[ζ₃]` or `ℤ[√−6]`, some
operation `T = twist α ∘ rightMul u` on `M3 ℚ̄` fixes the class of `P`, is an involution, and is not
the identity. (Outline: for `ℤ[i]` take `α = id` and `u ≡ φ` on `A[3]` (`Level3.torsor`,
`exists_unit_congr`); then `u² ≡ −1`, and `−1` acts trivially on classes. For `ℤ[ζ₃]` and
`ℤ[√−6]` the involution is an Atkin–Lehner-type twist induced by an element of the normalizer of
`ι(𝒪)` in `End A` (for `ℤ[√−6]`: `ι(ij)⁻¹ φ`), which needs the structure of `End A` at CM points.) -/
def CMStabObj : Prop :=
  ∀ P : QML3 Qbar, (HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q) →
    ∃ (α : LeafQM.O ≃+* LeafQM.O) (u : (LeafQM.O)ˣ),
      M3.twist α (M3.rightMul u (M3.mk P)) = M3.mk P ∧
      (∀ m : M3 Qbar, M3.twist α (M3.rightMul u (M3.twist α (M3.rightMul u m))) = m) ∧
      ∃ m : M3 Qbar, M3.twist α (M3.rightMul u m) ≠ m

/-- **`CMStabObj` (mcr-quot's glue C1b-obj) from the textbook fields `uniformizationLeafAll`,
`gagaMorphism`, `mumfordTorsionAlgClosed` and the kernel's textbook leaf `TorsionStructure` (T5).**
* `ℤ[i]` (`φ² = −1`): `α = id`, `g = φ`, `T = rightMul u` with `u ≡ −u₀`, where `φ(η(x)) = η(x u₀)`;
  `T² = rightMul(u²)`, `u² ≡ −1`.
* `ℤ[ζ₃]` (`φ² − φ + 1 = 0`): `α` = conjugation by `j`, `g = ι(j)⁻¹(2φ − 1)`, `g² = 1`.
* `ℤ[√−6]` (`φ² = −6`): `α` = conjugation by `k = ij`, `g = ι(k)⁻¹ φ`, `g² = −1`.
`g ∈ End(A)` comes from the lattice model of `End(A)` (gt-qm), `T(P) ≅ P` through `g`, `T² = id` on every
class, and `T` moves the class of `rightMul w P` (`w = 1 + i`, resp. `w ≡ 1 + j`), by a computation in
`𝒪/3𝒪` and `𝒪/𝔓₃ = 𝔽₉` with the commutativity of `End_𝒪(A)`. -/
theorem cmStabObj_of (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hT : ObjBridge.TorsionStructure) :
    CMStabObj := by
  intro P hCM
  obtain ⟨τ, hτ, ρ, hρinj, hρι, hρrange⟩ := lat_model hU hG hM P.A P.surface P.q
  have hcommAll : ∀ c ∈ com P.q, ∀ s ∈ com P.q, c * s = s * c :=
    fun c hc s hs => com_comm hρinj hρι hc hs
  rcases hCM with ⟨φ, hφ, hφφ⟩ | ⟨φ, hφ, hφφ⟩ | ⟨φ, hφ, hφφ⟩
  · -- `ℤ[i]`
    have hg : ∀ a, φ * P.q.iota (RingEquiv.refl O a) = P.q.iota a * φ :=
      fun a => iota_comm_of_mem hφ a
    have hgg : φ * φ = ((-1 : ℤ) : AbVar.End P.A) := by rw [hφφ, Int.cast_neg, Int.cast_one]
    obtain ⟨u₀, hu₀, hsq, u, hu, hfix, hinv⟩ :=
      stab_core hT P (RingEquiv.refl O) (fun a => rfl) φ (-1) (by norm_num) hgg hg
    obtain ⟨w, hw⟩ := exists_w4
    exact ⟨RingEquiv.refl O, u, hfix, hinv, M3.mk (P.rightMul w),
      nonid_4 hT P φ hgg hg (fun c hc => hcommAll c hc φ hφ) u₀ hu₀ hsq u hu w hw⟩
  · -- `ℤ[ζ₃]`
    set s : AbVar.End P.A := φ + φ - 1 with hsdef
    have hs : s ∈ com P.q := (com P.q).sub_mem ((com P.q).add_mem hφ hφ) (com P.q).one_mem
    have hss : s * s = ((-3 : ℤ) : AbVar.End P.A) := by
      have h4 : s * s = (φ * φ - φ + 1) + (φ * φ - φ + 1) + (φ * φ - φ + 1) + (φ * φ - φ + 1)
          - 1 - 1 - 1 := by rw [hsdef]; noncomm_ring
      rw [h4, hφφ]; push_cast; norm_num
    obtain ⟨g, hgs, hgg, hg⟩ := semilinear_unit hρinj hρι hρrange hτ oj (-1 / 3) αJ (-3) 1
      (fun x => by
        rw [αJ_coe, oj_coe]; change _ = cJ (x : B)
        generalize (x : B) = y; ext <;> simp [cJ] <;> ring)
      (fun a => by
        rw [αJ_coe, oj_coe]; change _ * cJ (a : B) = _
        generalize (a : B) = y; ext <;> simp [cJ] <;> ring)
      (by rw [oj_coe]; ext <;> simp [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num)
      (by rw [oj_coe]; ext <;> simp [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num)
      (fun y hy => div_j y (by rw [hy]; norm_num)) s hs hss
    obtain ⟨u₀, hu₀, hsq, u, hu, hfix, hinv⟩ := stab_core hT P αJ αJ_αJ g 1 (by norm_num) hgg hg
    refine ⟨αJ, u, hfix, hinv, M3.mk (P.rightMul w1U), ?_⟩
    exact nonid_t hT P αJ αJ_αJ oj oj_mul_αJ red_of_j_mul red_αJ g 1 (by norm_num) hgg hg
      (fun c hc => by rw [hgs]; exact hcommAll c hc s hs) u₀ hu₀ hsq u hu
  · -- `ℤ[√−6]`
    have hss : φ * φ = ((-6 : ℤ) : AbVar.End P.A) := by rw [hφφ, Int.cast_neg, Int.cast_ofNat]
    have hdiv6 : ∀ y : O, y * y = ((-6 : ℤ) : O) → ∃ e : O, y = ok * e :=
      fun y hy => div_k y (by rw [hy, Int.cast_neg, Int.cast_ofNat])
    have k1 : ∀ x : O, ((1 / 6 : ℚ) • (ok : B)) * x * ok = (αK x : B) := fun x => by
      rw [αK_coe, ok_coe]; change _ = cK (x : B)
      generalize (x : B) = y; ext <;> simp [cK] <;> ring
    have k2 : ∀ a : O, ((1 / 6 : ℚ) • (ok : B)) * (αK a : B) = (a : B) * ((1 / 6 : ℚ) • (ok : B)) :=
      fun a => by
        rw [αK_coe, ok_coe]; change _ * cK (a : B) = _
        generalize (a : B) = y; ext <;> simp [cK] <;> ring
    have k3 : (ok : B) * ((1 / 6 : ℚ) • (ok : B)) = 1 := by
      rw [ok_coe]; ext <;> simp [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
        QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num
    have k4 : ((1 / 6 : ℚ) • (ok : B)) * ((1 / 6 : ℚ) • (ok : B)) * ((-6 : ℤ) : B) = ((-1 : ℤ) : B) := by
      rw [ok_coe]; ext <;> simp [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
        QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num
    obtain ⟨g, hgs, hgg, hg⟩ := semilinear_unit hρinj hρι hρrange hτ ok (1 / 6 : ℚ) αK _ _
      k1 k2 k3 k4 hdiv6 φ hφ hss
    have hε : ((-1 : ℤ)) * (-1) = 1 := by norm_num
    have hgg' : g * g = ((-1 : ℤ) : PkgI3.AbVar.End P.A) := hgg
    obtain ⟨u₀, hu₀, hsq, u, hu, hfix, hinv⟩ := stab_core hT P αK αK_αK g (-1 : ℤ) hε hgg' hg
    refine ⟨αK, u, hfix, hinv, M3.mk (P.rightMul w1U), ?_⟩
    exact nonid_t hT P αK αK_αK ok ok_mul_αK red_of_k_mul red_αK g (-1) (by norm_num) hgg hg
      (fun c hc => by rw [hgs]; exact hcommAll c hc φ hφ) u₀ hu₀ hsq u hu

end GapGlue
