import ZInQKernel.OneProof.H.TailO

set_option linter.style.haveILetI false

namespace GapST
open _root_.LeafQM _root_.LeafQM.AV

/-! ## Part A: `𝒪` modulo `p` (finite checks) -/

/-- Multiplication of coordinate vectors modulo `p` (the formula of `mulCoord`). -/
def mulZ {p : ℕ} (n m : Fin 4 → ZMod p) : Fin 4 → ZMod p :=
  ![m 0 * n 0 + 2 * m 1 * n 1 + 2 * m 1 * n 3 - m 2 * n 2 + 2 * m 3 * n 3,
    m 0 * n 1 + m 1 * n 0 + m 1 * n 2 - m 2 * n 3 + m 3 * n 2,
    m 0 * n 2 - 2 * m 1 * n 3 + m 2 * n 0 + m 2 * n 2 + 2 * m 3 * n 1,
    m 0 * n 3 - m 1 * n 2 + m 2 * n 1 + m 2 * n 3 + m 3 * n 0]

/-- Reduction of integer coordinates modulo `p`. -/
def red (p : ℕ) (n : Fin 4 → ℤ) : Fin 4 → ZMod p := fun i => (n i : ZMod p)

theorem red_mul (p : ℕ) (n m : Fin 4 → ℤ) : red p (mulCoord n m) = mulZ (red p n) (red p m) := by
  funext i; fin_cases i <;> simp [red, mulZ, mulCoord]

/-- Coordinates of an element of `𝒪`. -/
noncomputable def crd (a : O) : Fin 4 → ℤ := a.2.choose

theorem crd_spec (a : O) : (a : B) = ofInt (crd a) := a.2.choose_spec

theorem crd_eq {a : O} {n : Fin 4 → ℤ} (h : (a : B) = ofInt n) : crd a = n :=
  ofInt_injective ((crd_spec a).symm.trans h)

theorem crd_mul (a b : O) : crd (a * b) = mulCoord (crd a) (crd b) := by
  apply crd_eq
  rw [MulMemClass.coe_mul, crd_spec a, crd_spec b, ofInt_mul]

theorem crd_sub (a b : O) : crd (a - b) = crd a - crd b := by
  apply crd_eq
  rw [AddSubgroupClass.coe_sub, crd_spec a, crd_spec b, ofInt_sub]

theorem crd_one : crd 1 = ![1, 0, 0, 0] := by
  apply crd_eq
  rw [OneMemClass.coe_one, ofInt_one]

theorem natCast_mul_ofInt (p : ℕ) (k : Fin 4 → ℤ) :
    (p : B) * ofInt k = ofInt (fun i => (p : ℤ) * k i) := by
  ext <;> simp [ofInt] <;> ring

/-- `a ∈ p𝒪` iff its coordinates vanish modulo `p`. -/
theorem mem_iff (p : ℕ) (a : O) : (∃ c : O, a = (p : O) * c) ↔ red p (crd a) = 0 := by
  have hp : ((p : O) : B) = (p : B) := map_natCast O.subtype p
  constructor
  · rintro ⟨c, rfl⟩
    have : crd ((p : O) * c) = fun i => (p : ℤ) * crd c i := by
      apply crd_eq
      rw [MulMemClass.coe_mul, hp, crd_spec c, natCast_mul_ofInt]
    funext i
    simp [red, this]
  · intro h
    have hd : ∀ i, (p : ℤ) ∣ crd a i := fun i =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (congrFun h i)
    choose k hk using hd
    refine ⟨⟨ofInt k, ⟨k, rfl⟩⟩, Subtype.ext ?_⟩
    rw [MulMemClass.coe_mul, hp, crd_spec a, natCast_mul_ofInt]
    change ofInt (crd a) = ofInt (fun i => (p : ℤ) * k i)
    congr 1; funext i; exact hk i

/-- The lift of a vector mod `p` with coordinates in `[0, p)`. -/
def liftP {p : ℕ} (c : Fin 4 → ZMod p) : O := ⟨ofInt (fun i => ((c i).val : ℤ)), ⟨_, rfl⟩⟩

theorem red_liftP {p : ℕ} [NeZero p] (c : Fin 4 → ZMod p) : red p (crd (liftP c)) = c := by
  rw [crd_eq (n := fun i => ((c i).val : ℤ)) rfl]
  funext i; simp [red]

theorem vec_eta {p : ℕ} (x : Fin 4 → ZMod p) : x = ![x 0, x 1, x 2, x 3] := by
  funext i; fin_cases i <;> rfl

/-! ### The finite checks -/

set_option maxRecDepth 100000 in
theorem d2_2i : ∀ x0 x1 x2 x3 a0 a1 a2 a3 : ZMod 2,
    mulZ ![x0, x1, x2, x3] ![x0, x1, x2, x3] = 0 →
    mulZ (mulZ ![0, 1, 0, 0] ![a0, a1, a2, a3]) ![x0, x1, x2, x3] = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem d2_3j : ∀ x0 x1 x2 x3 a0 a1 a2 a3 : ZMod 3,
    mulZ ![x0, x1, x2, x3] ![x0, x1, x2, x3] = 0 →
    mulZ (mulZ ![2, 0, 2, 0] ![a0, a1, a2, a3]) ![x0, x1, x2, x3] = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem d2_3ij : ∀ x0 x1 x2 x3 a0 a1 a2 a3 : ZMod 3,
    mulZ ![x0, x1, x2, x3] ![x0, x1, x2, x3] = 0 →
    mulZ (mulZ ![0, 2, 0, 2] ![a0, a1, a2, a3]) ![x0, x1, x2, x3] = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem d1_2i : ∀ x0 x1 x2 x3 : ZMod 2, ![x0, x1, x2, x3] ≠ 0 →
    ∃ b0 b1 b2 b3 : ZMod 2, mulZ ![b0, b1, b2, b3] ![x0, x1, x2, x3] = ![1, 0, 0, 0] ∨
      mulZ ![b0, b1, b2, b3] ![x0, x1, x2, x3] = ![0, 1, 0, 0] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem d1_3j : ∀ x0 x1 x2 x3 : ZMod 3, ![x0, x1, x2, x3] ≠ 0 →
    ∃ b0 b1 b2 b3 : ZMod 3, mulZ ![b0, b1, b2, b3] ![x0, x1, x2, x3] = ![1, 0, 0, 0] ∨
      mulZ ![b0, b1, b2, b3] ![x0, x1, x2, x3] = ![2, 0, 2, 0] := by
  decide +kernel

/-! ### Consequences in `𝒪` -/

/-- `i·j ∈ 𝒪`. -/
theorem crd_oi : crd oi = ![0, 1, 0, 0] := crd_eq rfl
theorem crd_oj : crd oj = ![-1, 0, 2, 0] := crd_eq rfl
theorem crd_oij : crd (oi * oj) = ![0, -1, 0, 2] := by
  rw [crd_mul, crd_oi, crd_oj]; funext i; fin_cases i <;> simp [mulCoord]

/-- **D2** in `𝒪`: if `x² ∈ p𝒪` then `w a x ∈ p𝒪` for all `a` (for the listed `(p, w)`). -/
theorem d2_of {p : ℕ} (w : O)
    (hc : ∀ x a : Fin 4 → ZMod p, mulZ x x = 0 → mulZ (mulZ (red p (crd w)) a) x = 0)
    (x : O) (hx : ∃ c : O, x * x = (p : O) * c) (a : O) : ∃ c : O, w * a * x = (p : O) * c := by
  rw [mem_iff] at hx ⊢
  rw [crd_mul, red_mul, crd_mul, red_mul]
  rw [crd_mul, red_mul] at hx
  exact hc _ _ hx

theorem hc2i : ∀ x a : Fin 4 → ZMod 2, mulZ x x = 0 → mulZ (mulZ (red 2 (crd oi)) a) x = 0 := by
  intro x a h
  rw [vec_eta x] at h ⊢; rw [vec_eta a]
  have : red 2 (crd oi) = ![0, 1, 0, 0] := by rw [crd_oi]; funext i; fin_cases i <;> rfl
  rw [this]; exact d2_2i _ _ _ _ _ _ _ _ h

end GapST
