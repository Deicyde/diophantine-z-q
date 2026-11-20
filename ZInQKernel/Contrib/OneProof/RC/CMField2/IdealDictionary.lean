import ZInQKernel.Contrib.OneProof.RC.CMField2.Integrality

/-! Proper ideals of quadratic orders are invertible, and the lattice dictionary
once the multiplier order is known. The ports are identified at their declarations. -/

noncomputable section

open NumberField Module TauCeti.GlobalNumberFields FractionalIdeal
open scoped nonZeroDivisors

namespace ZInQ.Manuscript.RC.CMField2

variable {k : Type} [Field k] [NumberField k]

/-- A quadratic relation with nonzero leading coefficient normalizes to a primitive one with `a > 0`.
Port of `exists_prim` at dfc6804f30bb08ec33abefeca76cba33405b8984,
ZInQKernel/Contrib/OneProof/CMBranch/CoxProof.lean. -/
private theorem primitive_quadratic_equation {τ : ℂ} {q0 B C : ℤ} (hq0 : q0 ≠ 0) (h : (q0 : ℂ) * τ ^ 2 + B * τ + C = 0) :
    ∃ a b c : ℤ, 0 < a ∧ Int.gcd (Int.gcd a b) c = 1 ∧ (a : ℂ) * τ ^ 2 + b * τ + c = 0 := by
  set g : ℕ := Int.gcd (Int.gcd q0 B) C with hg
  have hg0 : g ≠ 0 := by
    intro h0
    rw [hg, Int.gcd_eq_zero_iff] at h0
    exact hq0 (Int.gcd_eq_zero_iff.mp (by exact_mod_cast h0.1)).1
  have dq : (g : ℤ) ∣ q0 := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
  have dB : (g : ℤ) ∣ B := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
  have dC : (g : ℤ) ∣ C := Int.gcd_dvd_right _ _
  obtain ⟨a1, ha1⟩ := dq
  obtain ⟨b1, hb1⟩ := dB
  obtain ⟨c1, hc1⟩ := dC
  have hprim1 : Int.gcd (Int.gcd a1 b1) c1 = 1 := by
    have : g = g * Int.gcd (Int.gcd a1 b1) c1 := by
      conv_lhs => rw [hg, ha1, hb1, hc1, Int.gcd_mul_left, Int.natAbs_natCast, Nat.cast_mul, Int.gcd_mul_left]
      simp
    have hg' : 0 < g := Nat.pos_of_ne_zero hg0
    nlinarith [Nat.le_of_eq this]
  have heq1 : (a1 : ℂ) * τ ^ 2 + b1 * τ + c1 = 0 := by
    have hgC : (g : ℂ) ≠ 0 := by exact_mod_cast hg0
    rw [ha1, hb1, hc1] at h
    push_cast at h
    have : (g : ℂ) * ((a1 : ℂ) * τ ^ 2 + b1 * τ + c1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hgC
    · exact h'
  have ha10 : a1 ≠ 0 := by rintro rfl; simp at ha1; exact hq0 ha1
  rcases lt_or_gt_of_ne ha10 with hneg | hpos
  · refine ⟨-a1, -b1, -c1, by linarith, ?_, ?_⟩
    · simpa [Int.gcd_neg] using hprim1
    · push_cast; linear_combination -heq1
  · exact ⟨a1, b1, c1, hpos, hprim1, heq1⟩

private theorem exists_noninteger (O : NumberFieldOrder k) (hk : finrank ℚ k = 2) :
    ∃ θ : O.toSubalgebra, ∀ n : ℤ, θ ≠ n := by
  classical
  obtain ⟨c, hc⟩ := exists_order_basis_one O hk
  refine ⟨c 1, fun n hn => ?_⟩
  have he : c 1 = n • c 0 := by simpa [hc] using hn
  have hr := congrArg (fun x => c.repr x 1) he
  change c.repr (c 1) 1 = c.repr (n • c 0) 1 at hr
  rw [map_smul, c.repr_self, c.repr_self] at hr
  simp at hr

private theorem mul_mem_of_mem_pair (O : NumberFieldOrder k)
    (J : FractionalIdeal O.toSubalgebra⁰ k) (τ x : k)
    (hgen : ∀ y : k, y ∈ J ↔ ∃ m n : ℤ, y = m + n * τ)
    (hx : x ∈ J) (hxt : x * τ ∈ J) :
    ∀ y ∈ J, x * y ∈ J := by
  intro y hy
  obtain ⟨m, n, rfl⟩ := (hgen y).mp hy
  have hmem : m • x + n • (x * τ) ∈ J :=
    J.val.add_mem (J.val.toAddSubgroup.zsmul_mem hx m) (J.val.toAddSubgroup.zsmul_mem hxt n)
  rw [show x * ((m : k) + n * τ) = m • x + n • (x * τ) by simp only [zsmul_eq_mul]; ring]
  exact hmem

/-- Proper fractional ideals of quadratic orders are exactly
the invertible fractional ideals. After scaling a basis to `(1, τ)`, write
`a τ² + b τ + c = 0` with coprime coefficients. Then `a` and `-b - aτ` are in the
inverse ideal, and the product contains `a, b, c`, hence contains `1`.
Port of `proper_iff_isUnit` at dfc6804f30bb08ec33abefeca76cba33405b8984,
ZInQKernel/Contrib/OneProof/FowlerBridgesIdeals.lean. -/
theorem proper_iff_isUnit (O : NumberFieldOrder k) (hk : finrank ℚ k = 2)
    (I : FractionalIdeal O.toSubalgebra⁰ k) :
    O.IsProperFractionalIdeal I ↔ IsUnit I := by
  classical
  refine ⟨fun hI => ?_, O.isProperFractionalIdeal_of_isUnit⟩
  obtain ⟨B⟩ := exists_ideal_basis O hk I hI.ne_zero
  let u : k := B 0
  let v : k := B 1
  have hu : u ≠ 0 := fun h => B.ne_zero 0 (Subtype.ext h)
  let τ := u⁻¹ * v
  let J := spanSingleton O.toSubalgebra⁰ u⁻¹ * I
  have hp : O.IsProperFractionalIdeal J := by
    rw [show J = I * spanSingleton _ u⁻¹ by exact mul_comm ..]
    exact (O.isProperFractionalIdeal_mul_spanSingleton I (inv_ne_zero hu)).mpr hI
  have hgenI : ∀ y : k, y ∈ I ↔ ∃ m n : ℤ, y = m * u + n * v := by
    intro y
    constructor
    · intro hy
      let z : I := ⟨y, hy⟩
      refine ⟨B.repr z 0, B.repr z 1, ?_⟩
      have hs := B.sum_repr z
      rw [Fin.sum_univ_two] at hs
      have he := congrArg (fun z : I => (z : k)) hs.symm
      simpa only [Submodule.coe_add, Submodule.coe_smul_of_tower, zsmul_eq_mul] using he
    · rintro ⟨m, n, rfl⟩
      simpa [zsmul_eq_mul] using I.val.add_mem (I.val.toAddSubgroup.zsmul_mem (B 0).property m)
        (I.val.toAddSubgroup.zsmul_mem (B 1).property n)
  have hgen : ∀ y : k, y ∈ J ↔ ∃ m n : ℤ, y = m + n * τ := by
    intro y
    rw [mem_singleton_mul]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨m, n, rfl⟩ := (hgenI z).mp hz
      exact ⟨m, n, by dsimp [τ]; field_simp⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨m * u + n * v, (hgenI _).mpr ⟨m, n, rfl⟩,
        by dsimp [τ]; field_simp⟩
  have h1 : (1 : k) ∈ J := (hgen _).mpr ⟨1, 0, by simp⟩
  have ht : τ ∈ J := (hgen _).mpr ⟨0, 1, by simp⟩
  obtain ⟨θ, hθ⟩ := exists_noninteger O hk
  have hmul (y : k) (hy : y ∈ J) : (θ : k) * y ∈ J :=
    (O.mem_multiplierRing_iff J θ).mp (O.order_le_multiplierRing J θ.property) y hy
  obtain ⟨m, n, hmn⟩ := (hgen _).mp (by simpa using hmul 1 h1)
  obtain ⟨p, q, hpq⟩ := (hgen _).mp (hmul τ ht)
  have hn : n ≠ 0 := by
    intro he
    apply hθ m
    apply Subtype.ext
    simpa [he] using hmn
  have hq0 : (n : k) * τ ^ 2 + ((m - q : ℤ) : k) * τ + ((-p : ℤ) : k) = 0 := by
    rw [hmn] at hpq
    push_cast
    linear_combination hpq
  let σ : k →+* ℂ := Classical.choice inferInstance
  have hqC := congrArg σ hq0
  simp only [map_add, map_mul, map_pow, map_intCast, map_zero] at hqC
  obtain ⟨a, b, c, _, hprim, hqC'⟩ := primitive_quadratic_equation hn hqC
  have hq : (a : k) * τ ^ 2 + b * τ + c = 0 := by
    apply σ.injective
    simpa only [map_add, map_mul, map_pow, map_intCast, map_zero] using hqC'
  have haτ : (a : k) * τ ∈ O.toSubalgebra := by
    change (a : k) * τ ∈ O.toSubalgebra.toSubring
    have hEq : O.multiplierRing J = O.toSubalgebra.toSubring := hp
    rw [← hEq, O.mem_multiplierRing_iff]
    apply mul_mem_of_mem_pair O J τ _ hgen ((hgen _).mpr ⟨0, a, by simp⟩)
    exact (hgen _).mpr ⟨-c, -b, by push_cast; linear_combination hq⟩
  have hy : -(b : k) - a * τ ∈ O.toSubalgebra :=
    O.toSubalgebra.sub_mem (by simpa only [Int.cast_neg] using O.toSubalgebra.intCast_mem (-b)) haτ
  have hyt : (-(b : k) - a * τ) * τ = (c : k) := by linear_combination -hq
  have hmem1 (x : k) : x ∈ (1 : FractionalIdeal O.toSubalgebra⁰ k) ↔ x ∈ O.toSubalgebra := by
    rw [mem_one_iff]
    exact ⟨by rintro ⟨x, rfl⟩; exact x.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hinv (x : k) (hx : x ∈ O.toSubalgebra) (hxt : x * τ ∈ O.toSubalgebra) :
      x ∈ 1 / J := by
    rw [mem_div_iff_of_ne_zero hp.ne_zero]
    intro y hy'
    obtain ⟨l, s, rfl⟩ := (hgen _).mp hy'
    apply (hmem1 _).mpr
    convert O.toSubalgebra.add_mem (O.toSubalgebra.mul_mem (O.toSubalgebra.intCast_mem l) hx)
      (O.toSubalgebra.mul_mem (O.toSubalgebra.intCast_mem s) hxt) using 1
    ring
  have haInv := hinv (a : k) (O.toSubalgebra.intCast_mem a) haτ
  have hyInv := hinv (-(b : k) - a * τ) hy (by rw [hyt]; exact O.toSubalgebra.intCast_mem c)
  let P := J * (1 / J)
  have haP : (a : k) ∈ P := by simpa only [one_mul] using FractionalIdeal.mul_mem_mul h1 haInv
  have hcP : (c : k) ∈ P := by
    simpa only [mul_comm τ, hyt] using FractionalIdeal.mul_mem_mul ht hyInv
  have hbP : (b : k) ∈ P := by
    have hsum := P.val.add_mem (FractionalIdeal.mul_mem_mul h1 hyInv)
      (FractionalIdeal.mul_mem_mul ht haInv)
    apply P.val.neg_mem at hsum
    change -(1 * (-(b : k) - a * τ) + τ * a) ∈ P at hsum
    rwa [show -(1 * (-(b : k) - a * τ) + τ * a) = b by ring] at hsum
  have gcd_mem (l s : ℤ) (hl : (l : k) ∈ P) (hs : (s : k) ∈ P) :
      ((Int.gcd l s : ℕ) : k) ∈ P := by
    have hsum : Int.gcdA l s • (l : k) + Int.gcdB l s • (s : k) ∈ P :=
      P.val.add_mem (P.val.toAddSubgroup.zsmul_mem hl (Int.gcdA l s))
        (P.val.toAddSubgroup.zsmul_mem hs (Int.gcdB l s))
    have he : ((Int.gcd l s : ℕ) : k) =
        Int.gcdA l s • (l : k) + Int.gcdB l s • (s : k) := by
      simp only [zsmul_eq_mul]
      have h := congrArg (fun t : ℤ => (t : k)) (Int.gcd_eq_gcd_ab l s)
      simpa only [Int.cast_natCast, Int.cast_add, Int.cast_mul, mul_comm] using h
    rw [he]
    exact hsum
  have h1P : (1 : k) ∈ P := by
    have h := gcd_mem (Int.gcd a b : ℕ) c (by simpa only [Int.cast_natCast] using gcd_mem a b haP hbP) hcP
    simpa only [hprim, Nat.cast_one] using h
  have hP : P = 1 := by
    apply le_antisymm
    · change J * (1 / J) ≤ 1
      rw [mul_comm, ← le_div_iff_mul_le hp.ne_zero]
    · simpa only [map_one] using (spanSingleton_le_iff_mem (x := (1 : k))).mpr h1P
  apply IsUnit.of_mul_eq_one (1 / J * spanSingleton _ u⁻¹)
  calc
    I * (1 / J * spanSingleton _ u⁻¹) = J * (1 / J) := by
      dsimp [J]
      ac_rfl
    _ = 1 := hP

/-- Exact multiplier order gives an ideal in the specified order. Scaling by the
first basis period gives the inverse image of the lattice inside the embedded field. -/
theorem exists_singularModulus_of_exact_multiplier (O : NumberFieldOrder k)
    (hk : finrank ℚ k = 2) (hc : IsTotallyComplex k) (κ : k →+* ℂ) (L : PeriodPair)
    (h : ∀ z : ℂ, (∀ x ∈ L.lattice, z * x ∈ L.lattice) ↔ z ∈ κ '' (O.toSubalgebra : Set k)) :
    ∃ I : O.invertibleProperFractionalIdeals, L.jLattice = singularModulus O hk hc κ I := by
  obtain ⟨b, hb⟩ := exists_order_basis_one O hk
  have hw := orderBasis_im_ne_zero O hc κ b hb
  let ω : k := b 1
  let u := Units.mk0 L.ω₁ (L.indep.ne_zero 0)
  have hu : L.ω₁ ≠ 0 := u.ne_zero
  let M := L.scale u⁻¹
  have hm₁ : M.ω₁ = 1 := inv_mul_cancel₀ hu
  have hmul (z : ℂ) : (∀ x ∈ M.lattice, z * x ∈ M.lattice) ↔
      z ∈ κ '' (O.toSubalgebra : Set k) := by
    rw [← h]
    simp only [M, ← SetLike.mem_coe, lattice_scale, Set.mem_image]
    constructor
    · intro hh x hx
      have h' := hh ((↑u⁻¹ : ℂ) * x) ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := h'
      exact (mul_left_cancel₀ ((u⁻¹).ne_zero) (by linear_combination hxy) : y = z * x) ▸ hy
    · rintro hh _ ⟨x, hx, rfl⟩
      exact ⟨z * x, hh x hx, by ring⟩
  have hω : κ ω * 1 ∈ M.lattice := (hmul (κ ω)).mpr ⟨ω, (b 1).property, rfl⟩ _
    (hm₁ ▸ (Submodule.subset_span (by simp) : M.ω₁ ∈ M.lattice))
  obtain ⟨a, c, hac⟩ : ∃ a c : ℤ, a • M.ω₁ + c • M.ω₂ = κ ω := by
    simpa only [mul_one, PeriodPair.lattice, Submodule.mem_span_pair] using hω
  have hc0 : c ≠ 0 := by
    intro he
    apply hw
    rw [he, hm₁, zero_smul, add_zero, zsmul_eq_mul, mul_one] at hac
    rw [← hac, Complex.intCast_im]
  let v : k := (ω - (a : k)) / (c : k)
  have hv : κ v = M.ω₂ := by
    rw [show κ v = (κ ω - (a : ℂ)) / (c : ℂ) by simp [v]]
    apply (div_eq_iff (by exact_mod_cast hc0)).mpr
    rw [← hac, hm₁, zsmul_eq_mul, zsmul_eq_mul, mul_one]
    ring
  let T : Submodule O.toSubalgebra k :=
    { carrier := {x | κ x ∈ M.lattice}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change κ (x + y) ∈ M.lattice
        rw [map_add]
        exact M.lattice.add_mem hx hy
      smul_mem' := fun r x hx =>
        show κ ((r : k) * x) ∈ M.lattice by
          rw [map_mul]
          exact (hmul _).mpr ⟨r, r.property, rfl⟩ _ hx }
  have hT : ∀ x : k, x ∈ T ↔ κ x ∈ M.lattice := fun _ => Iff.rfl
  have hspan : T = Submodule.span O.toSubalgebra ({(1 : k), v} : Set k) := by
    refine le_antisymm (fun x hx => ?_) (Submodule.span_le.mpr ?_)
    · obtain ⟨m, n, he⟩ := Submodule.mem_span_pair.mp ((hT x).mp hx :
        κ x ∈ Submodule.span ℤ ({M.ω₁, M.ω₂} : Set ℂ))
      refine Submodule.mem_span_pair.mpr ⟨(m : O.toSubalgebra), (n : O.toSubalgebra), ?_⟩
      apply κ.injective
      simpa only [Algebra.smul_def, map_add, map_mul, map_intCast, eq_intCast,
        map_one, zsmul_eq_mul, ← hv, hm₁] using he
    · change ∀ x ∈ ({(1 : k), v} : Set k), x ∈ T
      intro x hx
      rw [hT]
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · rw [map_one, ← hm₁]
        exact Submodule.subset_span (by simp)
      · rw [Set.mem_singleton_iff.mp hx, hv]
        exact Submodule.subset_span (by simp)
  let I : FractionalIdeal O.toSubalgebra⁰ k :=
    ⟨T, isFractional_of_fg (by rw [hspan]; exact Submodule.fg_span ((Set.finite_singleton _).insert _))⟩
  have hLI : κ '' (I : Set k) = (M.lattice : Set ℂ) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hT y).mp hy
    · intro hx
      obtain ⟨a, c, hrepr⟩ := Submodule.mem_span_pair.mp (hx :
        x ∈ Submodule.span ℤ ({M.ω₁, M.ω₂} : Set ℂ))
      let y : k := (a : k) + (c : k) * v
      have hy : κ y = x := by
        simpa [y, zsmul_eq_mul, hm₁, hv] using hrepr
      exact ⟨y, (hT y).mpr (hy.symm ▸ hx), hy⟩
  have hI : O.IsProperFractionalIdeal I := (O.isProperFractionalIdeal_iff I).mpr (by
    intro z hz
    have h' : κ z ∈ κ '' (O.toSubalgebra : Set k) := (hmul _).mp (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hLI ▸ (show x ∈ (M.lattice : Set ℂ) from hx)
      rw [← map_mul]
      exact (hT (z * y)).mp (hz y hy))
    obtain ⟨w, hw, he⟩ := h'
    rwa [κ.injective he] at hw)
  obtain ⟨J, hJ⟩ := (proper_iff_isUnit O hk I).mp hI
  have hlat : (idealPeriod O hk hc κ J).lattice = M.lattice := by
    apply SetLike.coe_injective
    rw [idealPeriod_lattice, hJ, hLI]
  exact ⟨J, (jLattice_scale L u⁻¹).symm.trans (jLattice_eq_of_lattice_eq hlat).symm⟩


end ZInQ.Manuscript.RC.CMField2
