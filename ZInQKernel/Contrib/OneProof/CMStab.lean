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

end GapGlue.CMStab
