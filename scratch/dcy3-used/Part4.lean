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


/-! ## The table -/

/-- 36 elements of `𝒪` of reduced norm 1, one in each class of `{x ∈ (𝒪/3𝒪)^× : nrd x = 1}`. -/
def L36 : List (Fin 4 → ℤ) :=
  [![0, 0, 1, 0], ![1, 0, 0, 0], ![-1, 0, 0, 0], ![0, 0, -1, 0], ![-1, 0, 1, 0], ![1, 0, -1, 0],
   ![1, -1, 1, 0], ![1, 0, 1, -1], ![1, 0, 1, 1], ![1, 1, 1, 0], ![-1, -1, -1, 0], ![-1, 0, -1, -1],
   ![-1, 0, -1, 1], ![-1, 1, -1, 0], ![1, -1, 1, 1], ![1, 1, 1, -1], ![-1, -1, -1, 1], ![-1, 1, -1, -1],
   ![-3, 2, 0, 0], ![-3, 0, 0, 2], ![-3, 0, 0, -2], ![-3, -2, 0, 0], ![-2, 1, -1, 1], ![-2, -1, -1, -1],
   ![-1, 1, -2, 1], ![-1, -1, -2, -1], ![-3, 1, 1, 1], ![3, 1, -1, 1], ![-3, -1, 1, -1], ![3, -1, -1, -1],
   ![1, 1, -3, 1], ![1, -1, -3, -1], ![-1, 1, 3, 1], ![-1, -1, 3, -1], ![-3, 2, 0, -2], ![-3, -2, 0, 2]]

theorem L36_norm : ∀ γ ∈ L36, ShimuraGlue.N4 γ = 1 := by decide


set_option maxRecDepth 100000 in
theorem table3 : ∀ a b c d : ZMod 3, ShimuraGlue.N4 ![a, b, c, d] ≠ 0 →
    ∃ γ ∈ L36, ShimuraGlue.mulCoordR (red3 (conjC γ)) ![a, b, c, d] = ![1, 0, 0, 0] ∨
      ShimuraGlue.mulCoordR (red3 (conjC γ)) ![a, b, c, d] = ![0, 1, 2, 0] := by
  decide


/-! ## Decomposition of `𝒪̂^×` modulo `K₃` -/

theorem ofInt_three_smul (n : Fin 4 → ℤ) : ofInt (3 • n) = 3 * ofInt n := by
  rw [← map_ofNat (algebraMap ℚ B) 3, ← Algebra.smul_def]
  ext <;> simp [ofInt] <;> ring

theorem red3_eta (m : Fin 4 → ℤ) : ![red3 m 0, red3 m 1, red3 m 2, red3 m 3] = red3 m := by
  funext i; fin_cases i <;> rfl

/-- The coordinates of `1 + i + j = q(1 + √−1)`. -/
def cc : Fin 4 → ℤ := ![0, 1, 2, 0]

theorem red3_e1 : red3 ![1, 0, 0, 0] = ![1, 0, 0, 0] := by funext i; fin_cases i <;> rfl
theorem red3_cc : red3 cc = ![0, 1, 2, 0] := by funext i; fin_cases i <;> rfl

/-- **Every `u ∈ 𝒪̂^×` is `γ k` or `γ h k`** with `γ ∈ 𝒪¹` and `k ∈ K₃`, for any `h ∈ 𝒪̂^×` congruent to
`1 + i + j` mod `3𝒪̂` (the table, through the approximation of `u` mod `3𝒪̂`). -/
theorem decomp3 {h : BAQˣ} (hh : h ∈ OhatU) {yh : BAQ} (hyh : yh ∈ OhatQ)
    (hhe : (h : BAQ) = bEmb (ofInt cc) + 3 * yh) {u : BAQˣ} (hu : u ∈ OhatU) :
    ∃ γ : B, ShimuraGlue.nrdQ ℚ γ = 1 ∧ ∃ k : BAQˣ, k ∈ K3Q ∧
      ((u : BAQ) = bEmb γ * k ∨ (u : BAQ) = bEmb γ * h * k) := by
  have c3 : ∀ z : BAQ, z * 3 = 3 * z := fun z => (Commute.ofNat_right z 3).eq
  obtain ⟨m, y, hy, hu1, hN⟩ := unit3 hu
  obtain ⟨γ, hγL, hcase⟩ := table3 (red3 m 0) (red3 m 1) (red3 m 2) (red3 m 3) (by rwa [red3_eta])
  rw [red3_eta] at hcase
  have hγN := L36_norm γ hγL
  set G : B := ofInt γ with hGdef
  have hGG : G * star G = 1 := ofInt_mul_star hγN
  have hGG' : star G * G = 1 := by rw [star_mul_eq]; exact hGG
  have hnrd : ShimuraGlue.nrdQ ℚ G = 1 := by rw [nrd_ofInt, hγN]; simp
  have hGO : bEmb G ∈ OhatQ := bEmb_mem_of_inO ⟨γ, rfl⟩
  have hGsO : bEmb (star G) ∈ OhatQ := bEmb_mem_of_inO (inO_star ⟨γ, rfl⟩)
  let Gu : BAQˣ := bUnit (star G) G hGG' hGG
  have hGu : (Gu : BAQ) = bEmb (star G) := rfl
  have hGui : ((Gu⁻¹ : BAQˣ) : BAQ) = bEmb G := rfl
  have hred : ∀ e : Fin 4 → ℤ, ShimuraGlue.mulCoordR (red3 (conjC γ)) (red3 m) = red3 e →
      ∃ n : Fin 4 → ℤ, star G * ofInt m = ofInt e + 3 * ofInt n := by
    intro e he
    have he' : red3 (ShimuraGlue.mulCoordR (conjC γ) m) = red3 e := by
      rw [show red3 (ShimuraGlue.mulCoordR (conjC γ) m) =
        ShimuraGlue.mulCoordR (red3 (conjC γ)) (red3 m) from
          mulCoordR_cast (Int.castRingHom (ZMod 3)) (conjC γ) m, he]
    obtain ⟨n, hn⟩ := lift3 he'
    refine ⟨n, ?_⟩
    rw [hGdef, star_ofInt', ofInt_mul, hn, ← ofInt_add, ofInt_three_smul]
  refine ⟨G, hnrd, ?_⟩
  rcases hcase with hA | hB
  · obtain ⟨n, hn⟩ := hred ![1, 0, 0, 0] (by rw [hA, red3_e1])
    rw [ofInt_e1] at hn
    refine ⟨Gu * u, ⟨?_, ?_, bEmb (ofInt n) + bEmb (star G) * y, ?_, ?_⟩, Or.inl ?_⟩
    · rw [Units.val_mul, hGu]; exact OhatQ_mul hGsO hu.1
    · rw [mul_inv_rev, Units.val_mul, hGui]; exact OhatQ_mul hu.2 hGO
    · exact OhatQ_add (bEmb_mem_of_inO ⟨n, rfl⟩) (OhatQ_mul hGsO hy)
    · rw [Units.val_mul, hGu, hu1, mul_add, ← map_mul, hn, map_add, map_one, map_mul, map_ofNat]
      rw [← mul_assoc (bEmb (star G)) 3 y, c3]; noncomm_ring
    · rw [Units.val_mul, hGu, ← mul_assoc, ← map_mul, hGG, map_one, one_mul]
  · obtain ⟨n, hn⟩ := hred cc (by rw [hB, red3_cc])
    have hhi : ((h⁻¹ : BAQˣ) : BAQ) * (h : BAQ) = 1 := by simp
    refine ⟨h⁻¹ * Gu * u, ⟨?_, ?_, ((h⁻¹ : BAQˣ) : BAQ) * (-yh + bEmb (ofInt n) + bEmb (star G) * y), ?_, ?_⟩,
      Or.inr ?_⟩
    · rw [Units.val_mul, Units.val_mul, hGu]; exact OhatQ_mul (OhatQ_mul hh.2 hGsO) hu.1
    · rw [mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, hGui]
      first | exact OhatQ_mul hu.2 (OhatQ_mul hGO hh.1) | exact OhatQ_mul (OhatQ_mul hu.2 hGO) hh.1
    · exact OhatQ_mul hh.2 (OhatQ_add (OhatQ_add (OhatQ_neg hyh) (bEmb_mem_of_inO ⟨n, rfl⟩))
        (OhatQ_mul hGsO hy))
    · rw [Units.val_mul, Units.val_mul, hGu, hu1, mul_assoc, mul_add, ← map_mul, hn, map_add, map_mul,
        map_ofNat]
      have e1 : bEmb (ofInt cc) = (h : BAQ) - 3 * yh := by rw [hhe]; abel
      rw [e1]
      rw [← mul_assoc (bEmb (star G)) 3 y, c3]
      have : ((h⁻¹ : BAQˣ) : BAQ) * ((h : BAQ) - 3 * yh + 3 * bEmb (ofInt n) + 3 * bEmb (star G) * y) =
          ((h⁻¹ : BAQˣ) : BAQ) * h + ((h⁻¹ : BAQˣ) : BAQ) * 3 * (-yh + bEmb (ofInt n) + bEmb (star G) * y) := by
        noncomm_ring
      rw [this, hhi, c3]; noncomm_ring
    · rw [Units.val_mul, Units.val_mul, hGu]
      have hh2 : (h : BAQ) * ((h⁻¹ : BAQˣ) : BAQ) = 1 := by simp
      calc (u : BAQ) = bEmb G * ((h : BAQ) * ((h⁻¹ : BAQˣ) : BAQ)) * bEmb (star G) * u := by
            rw [hh2, mul_one, ← map_mul, hGG, map_one, one_mul]
        _ = bEmb G * h * (((h⁻¹ : BAQˣ) : BAQ) * bEmb (star G) * u) := by
            noncomm_ring

end DCY3Used
