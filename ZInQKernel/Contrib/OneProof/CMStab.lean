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

end GapGlue.CMStab
