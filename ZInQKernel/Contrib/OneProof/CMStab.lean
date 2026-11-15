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

end GapGlue.CMStab
