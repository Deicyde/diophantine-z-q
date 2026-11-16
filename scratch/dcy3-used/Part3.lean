import ZInQKernel.Contrib.OneProof.RayClassShimura

set_option linter.all false

noncomputable section

namespace DCY3Used

open LeafQM ShimuraCFT RayClassCFT

def conjC (m : Fin 4 → ℤ) : Fin 4 → ℤ := ![m 0 + m 2, -m 1, -m 2, -m 3]
def red3 (m : Fin 4 → ℤ) : Fin 4 → ZMod 3 := fun i => (m i : ZMod 3)

/-! ## Integer coordinates -/

theorem mulCoordR_cast {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n m : Fin 4 → R) :
    (fun i => f (ShimuraGlue.mulCoordR n m i)) = ShimuraGlue.mulCoordR (fun i => f (n i)) (fun i => f (m i)) := by
  funext i; fin_cases i <;> simp [ShimuraGlue.mulCoordR]

theorem N4_mul {R : Type*} [CommRing R] (n m : Fin 4 → R) :
    ShimuraGlue.N4 (ShimuraGlue.mulCoordR n m) = ShimuraGlue.N4 n * ShimuraGlue.N4 m := by
  simp [ShimuraGlue.N4, ShimuraGlue.mulCoordR]; ring

theorem ofInt_mul (n m : Fin 4 → ℤ) : ofInt n * ofInt m = ofInt (ShimuraGlue.mulCoordR n m) := by
  rw [← ShimuraGlue.ofQ_eq_ofInt, ← ShimuraGlue.ofQ_eq_ofInt, ← ShimuraGlue.ofQ_eq_ofInt,
    ShimuraGlue.ofQ_mul]
  congr 1
  exact (mulCoordR_cast (Int.castRingHom ℚ) n m).symm

theorem ofInt_add (n m : Fin 4 → ℤ) : ofInt n + ofInt m = ofInt (n + m) := by
  rw [← ShimuraGlue.ofQ_eq_ofInt, ← ShimuraGlue.ofQ_eq_ofInt, ← ShimuraGlue.ofQ_eq_ofInt,
    ShimuraGlue.ofQ_add]
  congr 1; funext i; simp

theorem ofInt_injective : Function.Injective ofInt := by
  intro n m h
  have := congrArg cQ h
  rw [cQ_ofInt, cQ_ofInt] at this
  funext i
  exact_mod_cast congrFun this i

theorem ofInt_e1 : ofInt ![1, 0, 0, 0] = 1 := by ext <;> simp [ofInt]

theorem nrd_ofInt (n : Fin 4 → ℤ) : ShimuraGlue.nrdQ ℚ (ofInt n) = ((ShimuraGlue.N4 n : ℤ) : ℚ) := by
  rw [← ShimuraGlue.ofQ_eq_ofInt, ShimuraGlue.nrdQ_ofQ]
  exact (ShimuraGlue.map_N4 (Int.castRingHom ℚ) n).symm

theorem ofInt_mul_star {n : Fin 4 → ℤ} (h : ShimuraGlue.N4 n = 1) : ofInt n * star (ofInt n) = 1 := by
  rw [← nrd_coe_eq, nrd_ofInt, h]; simp

theorem star_ofInt' (n : Fin 4 → ℤ) : star (ofInt n) = ofInt (conjC n) := by
  rw [star_ofInt]; rfl

/-- Lift a congruence mod 3 from `ZMod 3` to `ℤ`. -/
theorem lift3 {z e : Fin 4 → ℤ} (h : red3 z = red3 e) : ∃ n : Fin 4 → ℤ, z = e + 3 • n := by
  have : ∀ i, (3 : ℤ) ∣ z i - e i := fun i => by
    have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd (z i - e i) 3).1 (by
      push_cast
      have := congrFun h i; simp only [red3] at this; rw [this, sub_self])
    exact_mod_cast h3
  choose n hn using this
  exact ⟨n, funext fun i => by simp; linarith [hn i]⟩

/-! ## Approximation mod `3𝒪̂` -/

theorem bEmb_ofInt_eq (m : Fin 4 → ℤ) : bEmb (ofInt m) = ShimuraGlue.ofQ (fun i => ((m i : ℤ) : AQ)) := by
  have h1 := ShimuraGlue.ofQ_coords (bEmb (ofInt m))
  have h2 : (![(bEmb (ofInt m)).re - (bEmb (ofInt m)).imJ,
      (bEmb (ofInt m)).imI - (bEmb (ofInt m)).imK,
      2 * (bEmb (ofInt m)).imJ, 2 * (bEmb (ofInt m)).imK] : Fin 4 → AQ) =
      fun i => ((m i : ℤ) : AQ) := by
    have := cQ_bEmb (ofInt m)
    rw [cQ_ofInt] at this
    rw [show (![(bEmb (ofInt m)).re - (bEmb (ofInt m)).imJ,
      (bEmb (ofInt m)).imI - (bEmb (ofInt m)).imK,
      2 * (bEmb (ofInt m)).imJ, 2 * (bEmb (ofInt m)).imK] : Fin 4 → AQ) = cQ (bEmb (ofInt m)) from rfl,
      this]
    funext i; simp
  rw [h2] at h1
  exact h1

theorem ofQ_smul3 (b : Fin 4 → AQ) : ShimuraGlue.ofQ (fun i => (3 : AQ) * b i) = 3 * ShimuraGlue.ofQ b := by
  have : (3 : BAQ) = algebraMap AQ BAQ 3 := (map_ofNat _ 3).symm
  rw [this]
  ext <;> simp [ShimuraGlue.ofQ, QuaternionAlgebra.algebraMap_eq] <;> ring

theorem approx3 {u : BAQ} (hu : u ∈ OhatQ) : ∃ m : Fin 4 → ℤ, ∃ y ∈ OhatQ, u = bEmb (ofInt m) + 3 * y := by
  obtain ⟨n, hn, rfl⟩ := hu
  choose m b hb hab using fun i => exists_int_approx (hn i) 3 (by norm_num)
  refine ⟨m, ShimuraGlue.ofQ b, ⟨b, hb, rfl⟩, ?_⟩
  rw [bEmb_ofInt_eq, ← ofQ_smul3, ShimuraGlue.ofQ_add]
  congr 1
  funext i
  rw [hab i]; simp

/-! ## Units mod 3 -/

theorem bEmb_smul (r : ℚ) (x : B) : bEmb (r • x) = algebraMap ℚ BAQ r * bEmb x := by
  rw [Algebra.smul_def, map_mul, AlgHom.commutes]

theorem inO_of_three_mul {x : B} {W : BAQ} (hW : W ∈ OhatQ) (h : bEmb x = 3 * W) :
    InO ((1 / 3 : ℚ) • x) := by
  apply inO_of_bEmb_mem
  rw [bEmb_smul, h, ← mul_assoc]
  have : algebraMap ℚ BAQ (1 / 3) * 3 = 1 := by
    rw [show (3 : BAQ) = algebraMap ℚ BAQ 3 from (map_ofNat _ 3).symm, ← map_mul]; norm_num
  rw [this, one_mul]; exact hW

/-- `x ∈ 𝒪` with `bEmb x ∈ 3𝒪̂` has coordinates divisible by 3. -/
theorem coords_of_three_mul {z : Fin 4 → ℤ} {W : BAQ} (hW : W ∈ OhatQ) (h : bEmb (ofInt z) = 3 * W) :
    ∃ n : Fin 4 → ℤ, z = 3 • n := by
  obtain ⟨n, hn⟩ := inO_of_three_mul hW h
  refine ⟨n, ofInt_injective ?_⟩
  have : ofInt z = (3 : ℚ) • ofInt n := by
    rw [← hn, smul_smul]; norm_num
  rw [this, ← ShimuraGlue.ofQ_eq_ofInt, ← ShimuraGlue.ofQ_eq_ofInt]
  ext <;> simp [ShimuraGlue.ofQ] <;> ring

theorem unit3 {u : BAQˣ} (hu : u ∈ OhatU) :
    ∃ m : Fin 4 → ℤ, ∃ y ∈ OhatQ, (u : BAQ) = bEmb (ofInt m) + 3 * y ∧
      ShimuraGlue.N4 (red3 m) ≠ 0 := by
  obtain ⟨m, y, hy, hu1⟩ := approx3 hu.1
  obtain ⟨m', y', hy', hu2⟩ := approx3 hu.2
  refine ⟨m, y, hy, hu1, ?_⟩
  set W : BAQ := bEmb (ofInt m) * y' + y * bEmb (ofInt m') + 3 * y * y'
  have hW : W ∈ OhatQ := OhatQ_add (OhatQ_add (OhatQ_mul (bEmb_mem_of_inO ⟨m, rfl⟩) hy')
    (OhatQ_mul hy (bEmb_mem_of_inO ⟨m', rfl⟩))) (OhatQ_mul (OhatQ_mul (OhatQ_natCast 3) hy) hy')
  have h1 : (1 : BAQ) = bEmb (ofInt (ShimuraGlue.mulCoordR m m')) + 3 * W := by
    have := u.mul_inv
    rw [← this, hu1, hu2, ← ofInt_mul, map_mul]
    have c3 : ∀ z : BAQ, z * 3 = 3 * z := fun z => (Commute.ofNat_right z 3).eq
    simp only [W, mul_add, add_mul, mul_assoc, c3]
    noncomm_ring
  have h2 : bEmb (ofInt (ShimuraGlue.mulCoordR m m' - ![1, 0, 0, 0])) = 3 * (-W) := by
    have e : ofInt (ShimuraGlue.mulCoordR m m' - ![1, 0, 0, 0]) =
        ofInt (ShimuraGlue.mulCoordR m m') - 1 := by
      rw [← ofInt_e1, eq_sub_iff_add_eq, ofInt_add]; congr 1; abel
    rw [e, map_sub, map_one]
    rw [mul_neg, eq_neg_iff_add_eq_zero]
    rw [h1]; abel
  obtain ⟨n, hn⟩ := coords_of_three_mul (OhatQ_neg hW) h2
  have hz : red3 (ShimuraGlue.mulCoordR m m') = red3 ![1, 0, 0, 0] := by
    funext i
    have := congrFun hn i
    simp only [red3]
    have e : ShimuraGlue.mulCoordR m m' i = ![1, 0, 0, 0] i + 3 * n i := by
      have := congrFun hn i; simp at this; linarith
    rw [e]; push_cast
    rw [show (3 : ZMod 3) = 0 from rfl]; ring
  have hN := congrArg ShimuraGlue.N4 hz
  rw [show red3 (ShimuraGlue.mulCoordR m m') = ShimuraGlue.mulCoordR (red3 m) (red3 m') from
    mulCoordR_cast (Int.castRingHom (ZMod 3)) m m', N4_mul] at hN
  intro h0
  rw [h0, zero_mul] at hN
  revert hN; decide

end DCY3Used
