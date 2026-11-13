import ZInQKernel.HDecomp.B3Unram.B3b

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt3 from
`scratch/glue-t32a/T32a.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

/-! The draft's first 1816 lines are a verbatim copy of glue-b3b's `B3b.lean`; here they are
imported from `ZInQKernel.HDecomp.B3Unram.B3b`. -/

/-!
# glue-t32a: proof of T32(a) (`LeafPush.T32a_TameQuadratic`)

For an odd prime `p` and `w` over `p`, every continuous `χ : I_w → ℤˣ` is `1` or `η_g`, the
character `τ ↦ τ(g)/g` of `g = √p`. Proof: a Kummer generator `β` of `χ`; `v(β)` is a rational
power of `v(p)`; glue-b3b's `exists_inertia_neg` (an inertia element negating `√p`) forces the
exponent of `v(β)` to have odd denominator over `v(g)`; then `β^n / g^k` is a unit and inertia acts
trivially on it modulo `w`, which pins `χ = η_g^k`.
-/

namespace GlueB3Unram

/-! `GQ`, `cyc`, `galChar`, `UnramifiedAt`, … are glue-descent's, as in `B3Unram.B3b`. -/
open GlueDescent.B2Q (GQ act toRingAut cyc galChar isLocallyConstant_of_openSubgroup
  cyc_eq_of_agree cyc_isLocallyConstant galChar_isLocallyConstant UnramifiedAt)

open scoped Pointwise

section T32a

variable {w : ValuationSubring Qbar} {p : ℕ}

/-- Inertia acts trivially modulo `w`: `v(τz - z) < 1` for `z ∈ w`. -/
theorem inertia_val_sub_lt_one (τ : Gal) (hτ : τ ∈ LeafPush.inertiaQ w) (z : Qbar) (hz : z ∈ w) :
    w.valuation (τ z - z) < 1 := by
  obtain ⟨y, hy, hres⟩ := residue_inertia w τ hτ ⟨z, hz⟩
  have h0 : IsLocalRing.residue w (y - ⟨z, hz⟩) = 0 := by rw [map_sub, hres, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at h0
  have : ((y - ⟨z, hz⟩ : w) : Qbar) = τ z - z := by
    show (y : Qbar) - z = τ z - z
    rw [hy]; rfl
  rwa [this] at h0

theorem not_dvd_two_of_odd (hp : p.Prime) (hp2 : p ≠ 2) : ¬ (p : ℤ) ∣ (-2 : ℤ) := by
  intro h
  rw [Int.dvd_neg] at h
  have h' : p ∣ 2 := by exact_mod_cast h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')

/-- **Sign lemma.** At an odd place no inertia element negates a unit. -/
theorem not_inertia_neg (hp : p.Prime) (hp2 : p ≠ 2) (hw : LiesOver w p) (τ : Gal)
    (hτ : τ ∈ LeafPush.inertiaQ w) (z : Qbar) (hz : w.valuation z = 1) (hτz : τ z = -z) : False :=
        by
  have hzw : z ∈ w := (w.valuation_le_one_iff z).mp hz.le
  have h := inertia_val_sub_lt_one τ hτ z hzw
  have e : τ z - z = ((-2 : ℤ) : Qbar) * z := by rw [hτz]; push_cast; ring
  rw [e, map_mul, hz, mul_one, val_intCast_eq_one hp hw (-2) (not_dvd_two_of_odd hp hp2)] at h
  exact lt_irrefl _ h

/-- Valuation of a nonzero integer: a power of `v(p)`. -/
theorem val_int_eq_pow (hp : p.Prime) (hw : LiesOver w p) (r : ℤ) (hr : r ≠ 0) :
    ∃ e : ℕ, w.valuation (r : Qbar) = w.valuation (p : Qbar) ^ e := by
  obtain ⟨e, n', hn', he⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hr) p hp.one_lt.ne'
  refine ⟨e, ?_⟩
  have hv : w.valuation (r : Qbar) = w.valuation ((r.natAbs : ℤ) : Qbar) := by
    rcases Int.natAbs_eq r with h | h
    · conv_lhs => rw [h]
    · conv_lhs => rw [h]
      rw [Int.cast_neg, Valuation.map_neg]
  rw [hv, he]
  push_cast
  rw [map_mul, map_pow]
  have h1 : w.valuation ((n' : ℤ) : Qbar) = 1 :=
    val_intCast_eq_one hp hw _ (by exact_mod_cast hn')
  push_cast at h1
  rw [h1, mul_one]

/-- Valuation of a nonzero rational: an integral power of `v(p)`. -/
theorem val_rat_eq_zpow (hp : p.Prime) (hw : LiesOver w p) (q : ℚ) (hq : q ≠ 0) :
    ∃ m : ℤ, w.valuation (algebraMap ℚ Qbar q) = w.valuation (p : Qbar) ^ m := by
  obtain ⟨a, ha⟩ := val_int_eq_pow hp hw q.num (Rat.num_ne_zero.mpr hq)
  obtain ⟨b, hb⟩ := val_int_eq_pow hp hw (q.den : ℤ) (by exact_mod_cast q.den_ne_zero)
  refine ⟨(a : ℤ) - b, ?_⟩
  have hvp : w.valuation (p : Qbar) ≠ 0 := val_natCast_ne_zero hp
  rw [eq_ratCast, Rat.cast_def, map_div₀]
  push_cast at ha hb
  rw [ha, hb, zpow_sub₀ hvp, zpow_natCast, zpow_natCast]

theorem pow_eq_zpow_aux {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (P X : Γ) (hP : P ≠ 0)
    (hX : X ≠ 0) (a b : ℤ) (i j : ℕ) (hij : i < j) (h : P ^ a * X ^ i = P ^ b * X ^ j) :
    X ^ (j - i) = P ^ (a - b) := by
  have hXi : X ^ i ≠ 0 := pow_ne_zero _ hX
  have h2 : P ^ a = P ^ b * X ^ (j - i) := by
    apply mul_right_cancel₀ hXi
    rw [h, mul_assoc, ← pow_add, Nat.sub_add_cancel hij.le]
  rw [zpow_sub₀ hP, h2, mul_div_cancel_left₀ _ (zpow_ne_zero _ hP)]

/-- **Values are rational powers of `v(p)`** (Newton polygon of the minimal polynomial): for
`x ≠ 0` in `ℚ̄`, `v(x)^n = v(p)^m` for some `n ≥ 1`, `m ∈ ℤ`. -/
theorem val_pow_eq_zpow (hp : p.Prime) (hw : LiesOver w p) (x : Qbar) (hx : x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, w.valuation x ^ n = w.valuation (p : Qbar) ^ m := by
  classical
  set f := minpoly ℚ x with hfdef
  have hmon : f.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  set d := f.natDegree
  let t : ℕ → Qbar := fun i => algebraMap ℚ Qbar (f.coeff i) * x ^ i
  have h0 : ∑ i ∈ Finset.range (d + 1), t i = 0 := by
    have := minpoly.aeval ℚ x
    rw [Polynomial.aeval_eq_sum_range] at this
    simpa [t, Algebra.smul_def] using this
  have hvt : ∀ i, w.valuation (t i) = w.valuation (algebraMap ℚ Qbar (f.coeff i)) *
      w.valuation x ^ i := fun i => by simp only [t, map_mul, map_pow]
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image (Finset.range (d + 1))
    (fun i => w.valuation (t i)) ⟨d, by simp⟩
  have hvx : w.valuation x ≠ 0 := by rwa [Ne, Valuation.zero_iff]
  have htd : w.valuation (t d) ≠ 0 := by
    rw [hvt, show f.coeff d = 1 from hmon.coeff_natDegree, map_one, map_one, one_mul]
    exact pow_ne_zero _ hvx
  have htj : w.valuation (t j) ≠ 0 := by
    intro h0'
    have := hjmax d (by simp)
    rw [h0'] at this
    exact htd (le_antisymm this zero_le')
  obtain ⟨i, hi, hij, heq⟩ : ∃ i ∈ Finset.range (d + 1), i ≠ j ∧
      w.valuation (t i) = w.valuation (t j) := by
    by_contra hcon
    push_neg at hcon
    have := Valuation.map_sum_eq_of_lt w.valuation hj (fun i hi => by
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
      exact lt_of_le_of_ne (hjmax i hi.1) (hcon i hi.1 hi.2))
    rw [h0, map_zero] at this
    exact htj this.symm
  have hcj : f.coeff j ≠ 0 := by
    intro hc; apply htj; rw [hvt, hc, map_zero, map_zero, zero_mul]
  have hci : f.coeff i ≠ 0 := by
    intro hc; apply htj; rw [← heq, hvt, hc, map_zero, map_zero, zero_mul]
  obtain ⟨a, ha⟩ := val_rat_eq_zpow hp hw _ hci
  obtain ⟨b, hb⟩ := val_rat_eq_zpow hp hw _ hcj
  rw [hvt, hvt, ha, hb] at heq
  have hvp : w.valuation (p : Qbar) ≠ 0 := val_natCast_ne_zero hp
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨j - i, Nat.sub_pos_of_lt h, a - b, pow_eq_zpow_aux _ _ hvp hvx a b i j h heq⟩
  · exact ⟨i - j, Nat.sub_pos_of_lt h, b - a, pow_eq_zpow_aux _ _ hvp hvx b a j i h heq.symm⟩

/-- **Kummer generator.** A continuous character `χ : I_w → ℤˣ` is `τ ↦ τ(β)/β` for some
`β ≠ 0` in `ℚ̄`. -/
theorem exists_kummer (w : ValuationSubring Qbar) (χ : LeafPush.inertiaQ w →* ℤˣ)
    (hχ : Continuous χ) : ∃ β : Qbar, β ≠ 0 ∧ ∀ (τ : Gal) (hτ : τ ∈ LeafPush.inertiaQ w),
      τ β = (((χ ⟨τ, hτ⟩ : ℤˣ) : ℤ) : Qbar) * β := by
  classical
  -- Step 1: an element `γ` whose stabilizer in `I` lies in `ker χ`
  have hopen : IsOpen ((χ ⁻¹' {1}) : Set (LeafPush.inertiaQ w)) := (isOpen_discrete _).preimage hχ
  rw [isOpen_induced_iff] at hopen
  obtain ⟨t, ht, hteq⟩ := hopen
  have h1t : (1 : Gal) ∈ t := by
    have : (1 : LeafPush.inertiaQ w) ∈ (χ ⁻¹' {1} : Set (LeafPush.inertiaQ w)) := by simp
    rw [← hteq] at this; exact this
  obtain ⟨E, hEfin, hEt⟩ := (krullTopology_mem_nhds_one_iff ℚ Qbar t).mp (ht.mem_nhds h1t)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  set γ : Qbar := (α : Qbar) with hγdef
  have hE : IntermediateField.adjoin ℚ {γ} = E := by
    rw [← IntermediateField.lift_adjoin_simple, hα, IntermediateField.lift_top]
  have hker : ∀ σ (hσ : σ ∈ LeafPush.inertiaQ w), σ γ = γ → χ ⟨σ, hσ⟩ = 1 := by
    intro σ hσ hσγ
    have hfix : σ ∈ E.fixingSubgroup := by
      rw [← hE]
      have hle : IntermediateField.adjoin ℚ {γ} ≤
          IntermediateField.fixedField (Subgroup.zpowers σ) := by
        rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
        intro g hg
        have : g ∈ MulAction.stabilizer Gal γ :=
          (Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hσγ)) hg
        exact this
      exact (IntermediateField.le_iff_le _ _).mp hle (Subgroup.mem_zpowers σ)
    have : (⟨σ, hσ⟩ : LeafPush.inertiaQ w) ∈ (Subtype.val ⁻¹' t : Set (LeafPush.inertiaQ w)) := hEt
        hfix
    rw [hteq] at this; exact this
  have hcons : ∀ σ (hσ : σ ∈ LeafPush.inertiaQ w) τ (hτ : τ ∈ LeafPush.inertiaQ w), σ γ = τ γ → χ
      ⟨σ, hσ⟩ = χ ⟨τ, hτ⟩ := by
    intro σ hσ τ hτ h
    have h' : (τ⁻¹ * σ) γ = γ := by
      rw [AlgEquiv.mul_apply, h, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have := hker (τ⁻¹ * σ) ((LeafPush.inertiaQ w).mul_mem ((LeafPush.inertiaQ w).inv_mem hτ) hσ) h'
    have e : (⟨τ⁻¹ * σ, (LeafPush.inertiaQ w).mul_mem ((LeafPush.inertiaQ w).inv_mem hτ) hσ⟩ :
        LeafPush.inertiaQ w) = (⟨τ, hτ⟩ : LeafPush.inertiaQ w)⁻¹ * ⟨σ, hσ⟩ := rfl
    rw [e, map_mul, map_inv, inv_mul_eq_one] at this
    exact this.symm
  -- Step 2: the class function `c` on the orbit of `γ`
  let c : Qbar → ℤ := fun y => if h : ∃ τ, ∃ hτ : τ ∈ LeafPush.inertiaQ w, τ γ = y then
    ((χ ⟨h.choose, h.choose_spec.choose⟩ : ℤˣ) : ℤ) else 0
  have hc : ∀ τ (hτ : τ ∈ LeafPush.inertiaQ w), c (τ γ) = χ ⟨τ, hτ⟩ := by
    intro τ hτ
    have h : ∃ τ', ∃ hτ' : τ' ∈ LeafPush.inertiaQ w, τ' γ = τ γ := ⟨τ, hτ, rfl⟩
    simp only [c, dif_pos h]
    rw [hcons _ h.choose_spec.choose _ hτ h.choose_spec.choose_spec]
  have hc0 : ∀ y, (¬ ∃ τ, ∃ hτ : τ ∈ LeafPush.inertiaQ w, τ γ = y) → c y = 0 := fun y h => by
    simp only [c, dif_neg h]
  have hcσ : ∀ σ (hσ : σ ∈ LeafPush.inertiaQ w) y, c (σ y) = ((χ ⟨σ, hσ⟩ : ℤˣ) : ℤ) * c y := by
    intro σ hσ y
    by_cases h : ∃ τ, ∃ hτ : τ ∈ LeafPush.inertiaQ w, τ γ = y
    · obtain ⟨τ, hτ, rfl⟩ := h
      rw [← AlgEquiv.mul_apply, hc _ ((LeafPush.inertiaQ w).mul_mem hσ hτ), hc τ hτ]
      have e : (⟨σ * τ, (LeafPush.inertiaQ w).mul_mem hσ hτ⟩ : LeafPush.inertiaQ w) = ⟨σ, hσ⟩ * ⟨τ,
          hτ⟩ := rfl
      rw [e, map_mul, Units.val_mul]
    · have h' : ¬ ∃ τ, ∃ hτ : τ ∈ LeafPush.inertiaQ w, τ γ = σ y := by
        rintro ⟨τ, hτ, hτy⟩
        apply h
        refine ⟨σ⁻¹ * τ, (LeafPush.inertiaQ w).mul_mem ((LeafPush.inertiaQ w).inv_mem hσ) hτ, ?_⟩
        rw [AlgEquiv.mul_apply, hτy, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
      rw [hc0 _ h, hc0 _ h', mul_zero]
  have hcσ' : ∀ σ (hσ : σ ∈ LeafPush.inertiaQ w) y, c y = ((χ ⟨σ, hσ⟩ : ℤˣ) : ℤ) * c (σ y) := by
    intro σ hσ y
    rw [hcσ σ hσ y, ← mul_assoc, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_mul]
  -- Step 3: the roots of the minimal polynomial of `γ`
  have hγint : IsIntegral ℚ γ := Algebra.IsIntegral.isIntegral γ
  set R : Finset Qbar := ((minpoly ℚ γ).aroots Qbar).toFinset with hRdef
  have hR : ∀ σ : Gal, ∀ y ∈ R, σ y ∈ R := by
    intro σ y hy
    simp only [hRdef, Multiset.mem_toFinset, Polynomial.mem_aroots] at hy ⊢
    refine ⟨hy.1, ?_⟩
    have := Polynomial.aeval_algHom_apply (σ : Qbar →ₐ[ℚ] Qbar) y (minpoly ℚ γ)
    rw [hy.2, map_zero] at this
    exact this
  have hγR : γ ∈ R := by
    simp only [hRdef, Multiset.mem_toFinset, Polynomial.mem_aroots]
    exact ⟨minpoly.ne_zero hγint, minpoly.aeval ℚ γ⟩
  have hγ1 : c γ = 1 := by
    have := hc 1 (LeafPush.inertiaQ w).one_mem
    rw [AlgEquiv.one_apply] at this
    rw [this]
    have e : (⟨1, (LeafPush.inertiaQ w).one_mem⟩ : LeafPush.inertiaQ w) = 1 := rfl
    rw [e, map_one, Units.val_one]
  -- Step 4: some power sum `∑ c(y) y^j` is nonzero (Vandermonde)
  let bsum : ℕ → Qbar := fun j => ∑ y ∈ R, (c y : Qbar) * y ^ j
  obtain ⟨j, hj⟩ : ∃ j, bsum j ≠ 0 := by
    by_contra hall
    push_neg at hall
    let e : Fin R.card ≃ R := R.equivFin.symm
    let v : Fin R.card → Qbar := fun i => (e i : Qbar)
    let cv : Fin R.card → Qbar := fun i => (c (e i) : Qbar)
    have hmul : (Matrix.vandermonde v).transpose.mulVec cv = 0 := by
      funext k
      have hk := hall k
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.vandermonde_apply,
        Pi.zero_apply]
      rw [← hk]
      simp only [bsum, v, cv]
      rw [← Finset.sum_coe_sort R, ← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hdet : (Matrix.vandermonde v).transpose.det ≠ 0 := by
      rw [Matrix.det_transpose]
      exact Matrix.det_vandermonde_ne_zero_iff.mpr fun a b h => e.injective (Subtype.ext h)
    have h0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
    have := congrFun h0 (e.symm ⟨γ, hγR⟩)
    simp only [cv, Equiv.apply_symm_apply, hγ1, Pi.zero_apply] at this
    norm_num at this
  -- Step 5: `β = ∑ c(y) y^j` transforms by `χ`
  refine ⟨bsum j, hj, fun σ hσ => ?_⟩
  simp only [bsum, map_sum, map_mul, map_intCast, map_pow]
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun y => σ y) (fun y => σ⁻¹ y) (fun y hy => hR σ y hy)
    (fun y hy => hR σ⁻¹ y hy) (fun y _ => by simp) (fun y _ => by simp) fun y _ => ?_
  rw [hcσ' σ hσ y]
  push_cast
  ring

theorem unit_cast_cases (u : ℤˣ) : ((u : ℤ) : Qbar) = 1 ∨ ((u : ℤ) : Qbar) = -1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

open Classical in
/-- The sign `δ_τ = τ(g)/g ∈ {±1}` of `g = √p` under `τ`. -/
noncomputable def sgnG (g : Qbar) (τ : Gal) : Qbar := if τ g = g then 1 else -1

theorem sgnG_spec {g : Qbar} {c : ℤ} (hg : g ^ 2 = (c : Qbar)) (τ : Gal) : τ g = sgnG g τ * g := by
  unfold sgnG
  split_ifs with h
  · rw [h, one_mul]
  · rw [(smul_sq_cases hg τ).resolve_left h, neg_one_mul]

/-- **The classification.** Every continuous `χ : I_w → ℤˣ` is a power of `τ ↦ τ(g)/g`. -/
theorem char_eq_sgn_zpow (hp : p.Prime) (hp2 : p ≠ 2) (hw : LiesOver w p) (g : Qbar)
    (hg : g ^ 2 = ((p : ℤ) : Qbar)) (τ₀ : Gal) (hτ₀ : τ₀ ∈ LeafPush.inertiaQ w) (hτ₀g : τ₀ g = -g)
    (χ : LeafPush.inertiaQ w →* ℤˣ) (hχ : Continuous χ) :
    ∃ k : ℤ, ∀ (τ : Gal) (hτ : τ ∈ LeafPush.inertiaQ w),
      (((χ ⟨τ, hτ⟩ : ℤˣ) : ℤ) : Qbar) = sgnG g τ ^ k := by
  classical
  obtain ⟨β, hβ0, hβ⟩ := exists_kummer w χ hχ
  have hp0 : ((p : ℤ) : Qbar) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hg0 : g ≠ 0 := by rintro rfl; rw [zero_pow two_ne_zero] at hg; exact hp0 hg.symm
  have hvg : w.valuation g ^ 2 = w.valuation (p : Qbar) := by
    rw [← map_pow, hg, Int.cast_natCast]
  have hvg0 : w.valuation g ≠ 0 := by rwa [Ne, Valuation.zero_iff]
  have hex : ∃ n, 0 < n ∧ ∃ k : ℤ, w.valuation β ^ n = w.valuation g ^ k := by
    obtain ⟨n, hn, m, hm⟩ := val_pow_eq_zpow hp hw β hβ0
    refine ⟨n, hn, 2 * m, ?_⟩
    rw [hm, ← hvg, ← zpow_natCast, ← zpow_mul]
    norm_num
  obtain ⟨hn₀, k, hk⟩ := Nat.find_spec hex
  set n₀ := Nat.find hex with hn₀def
  set z : Qbar := β ^ n₀ * g ^ (-k) with hzdef
  have hvz : w.valuation z = 1 := by
    rw [hzdef, map_mul, map_pow, map_zpow₀, hk, ← zpow_add₀ hvg0, add_neg_cancel, zpow_zero]
  have hτz : ∀ τ (hτ : τ ∈ LeafPush.inertiaQ w),
      τ z = (((χ ⟨τ, hτ⟩ : ℤˣ) : ℤ) : Qbar) ^ n₀ * sgnG g τ ^ (-k) * z := by
    intro τ hτ
    rw [hzdef, map_mul, map_pow, map_zpow₀, hβ τ hτ, sgnG_spec hg τ, mul_pow, mul_zpow]
    ring
  -- `n₀` is odd
  have hodd : Odd n₀ := by
    rcases Nat.even_or_odd n₀ with ⟨a, ha⟩ | h
    swap; · exact h
    exfalso
    rcases Int.even_or_odd k with ⟨b, hb⟩ | hk2
    · have ha0 : 0 < a := by omega
      have h2 : (w.valuation β ^ a) ^ 2 = (w.valuation g ^ b) ^ 2 := by
        rw [← pow_mul, mul_two, ← ha, hk, hb, ← zpow_natCast, ← zpow_mul]
        congr 1; push_cast; ring
      have h' : w.valuation β ^ a = w.valuation g ^ b := pow_left_injective two_ne_zero h2
      exact Nat.find_min hex (show a < n₀ by omega) ⟨ha0, b, h'⟩
    · have hτ₀z := hτz τ₀ hτ₀
      have hs : sgnG g τ₀ = -1 := by
        unfold sgnG; rw [if_neg]; rw [hτ₀g]; intro h
        exact hg0 (by linear_combination -h / 2)
      have hev : Even n₀ := ⟨a, ha⟩
      rw [hs, hk2.neg.neg_one_zpow] at hτ₀z
      rcases unit_cast_cases (χ ⟨τ₀, hτ₀⟩) with he | he
      · rw [he, one_pow] at hτ₀z
        exact not_inertia_neg hp hp2 hw τ₀ hτ₀ z hvz (by rw [hτ₀z]; ring)
      · rw [he, hev.neg_one_pow] at hτ₀z
        exact not_inertia_neg hp hp2 hw τ₀ hτ₀ z hvz (by rw [hτ₀z]; ring)
  refine ⟨k, fun τ hτ => ?_⟩
  have h := hτz τ hτ
  have hsg : sgnG g τ = 1 ∨ sgnG g τ = -1 := by unfold sgnG; split_ifs <;> simp
  rcases unit_cast_cases (χ ⟨τ, hτ⟩) with he | he <;> rcases hsg with hs | hs <;>
    rcases Int.even_or_odd k with hk2 | hk2 <;> rw [he, hs] at h ⊢ <;>
    simp only [one_pow, one_zpow, hodd.neg_one_pow, hk2.neg_one_zpow, hk2.neg.neg_one_zpow,
      one_mul, mul_one] at h ⊢ <;>
    first
    | rfl
    | exact (not_inertia_neg hp hp2 hw τ hτ z hvz (by rw [h]; ring)).elim

theorem neg_ne_self_of_ne_zero {g : Qbar} (hg0 : g ≠ 0) : -g ≠ g := fun h =>
  hg0 (by linear_combination (-1 / 2 : Qbar) * h)

open Classical in
/-- The quadratic character `η_g : τ ↦ τ(g)/g` of `I_w`, for `g² ∈ ℤ`, `g ≠ 0`, as a map to `ℤˣ`. -/
noncomputable def etaG (w : ValuationSubring Qbar) (g : Qbar) {c : ℤ} (hg : g ^ 2 = (c : Qbar))
    (hg0 : g ≠ 0) : LeafPush.inertiaQ w →* ℤˣ where
  toFun τ := if (τ : Gal) g = g then 1 else -1
  map_one' := by simp
  map_mul' σ τ := by
    have hne := neg_ne_self_of_ne_zero hg0
    rcases smul_sq_cases hg (σ : Gal) with h1 | h1 <;>
      rcases smul_sq_cases hg (τ : Gal) with h2 | h2 <;>
      simp [AlgEquiv.mul_apply, h1, h2, hne]

open Classical in
theorem etaG_apply (w : ValuationSubring Qbar) (g : Qbar) {c : ℤ} (hg : g ^ 2 = (c : Qbar))
    (hg0 : g ≠ 0) (τ : LeafPush.inertiaQ w) :
    etaG w g hg hg0 τ = if (τ : Gal) g = g then 1 else -1 := rfl

theorem etaG_continuous (w : ValuationSubring Qbar) (g : Qbar) {c : ℤ}
    (hg : g ^ 2 = (c : Qbar)) (hg0 : g ≠ 0) : Continuous (etaG w g hg hg0) := by
  let U : Subgroup (LeafPush.inertiaQ w) :=
    (MulAction.stabilizer Gal g).comap (LeafPush.inertiaQ w).subtype
  have hU : IsOpen (U : Set (LeafPush.inertiaQ w)) :=
    (stabilizer_isOpen_of_isIntegral (K := ℚ) (L := Qbar) g).preimage continuous_subtype_val
  refine IsLocallyConstant.continuous (isLocallyConstant_of_openSubgroup U hU _ ?_)
  intro σ k hk
  have hk' : (k : Gal) g = g := MulAction.mem_stabilizer_iff.mp hk
  rw [etaG_apply, etaG_apply, Subgroup.coe_mul, AlgEquiv.mul_apply, hk']

/-- **T32(a) is glue** (proved from Mathlib, via glue-b3b's `exists_inertia_neg`): for an odd
prime `p` and `w` over `ℤ_(p)`, the continuous characters `I_w → ℤˣ` number exactly two. -/
theorem t32a : LeafPush.T32a_TameQuadratic := by
  classical
  intro p hp hp2 O hO w hwO
  have hw : LiesOver w p := liesOver_of_isAtPrime O hO w hwO
  obtain ⟨g, hg'⟩ := IsAlgClosed.exists_pow_nat_eq (p : Qbar) two_pos
  have hg : g ^ 2 = ((p : ℤ) : Qbar) := by rw [hg']; simp
  have hp0 : ((p : ℤ) : Qbar) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hg0 : g ≠ 0 := by rintro rfl; rw [zero_pow two_ne_zero] at hg; exact hp0 hg.symm
  obtain ⟨σ, hσ⟩ := exists_neg_of_sq hg
    (not_isSquare_of_squarefree (Int.squarefree_natCast.mpr hp.squarefree) hp dvd_rfl)
  obtain ⟨τ₀, hτ₀, hτ₀g⟩ := exists_inertia_neg p hp w hw g p hg (by simp) σ hσ
  have hne := neg_ne_self_of_ne_zero hg0
  have hητ₀ : etaG w g hg hg0 ⟨τ₀, hτ₀⟩ = -1 := by
    rw [etaG_apply]
    show (if τ₀ g = g then (1 : ℤˣ) else -1) = -1
    rw [if_neg (by rw [hτ₀g]; exact hne)]
  have hZ : (-1 : ℤˣ) ≠ 1 := by decide
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, continuous_const⟩, ⟨etaG w g hg hg0, etaG_continuous w g hg hg0⟩, ?_, ?_⟩
  · intro h
    have := congrArg (fun x : {χ : LeafPush.inertiaQ w →* ℤˣ // Continuous χ} => x.1 ⟨τ₀, hτ₀⟩) h
    simp only [MonoidHom.one_apply] at this
    rw [hητ₀] at this
    exact hZ this.symm
  · ext ⟨χ, hχ⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    obtain ⟨k, hk⟩ := char_eq_sgn_zpow hp hp2 hw g hg τ₀ hτ₀ hτ₀g χ hχ
    rcases Int.even_or_odd k with hk2 | hk2
    · left
      apply Subtype.ext
      refine MonoidHom.ext fun x => ?_
      obtain ⟨τ, hτ⟩ := x
      have h := hk τ hτ
      have hs : sgnG g τ ^ k = 1 := by
        unfold sgnG; split_ifs
        · exact one_zpow k
        · exact hk2.neg_one_zpow
      rw [hs] at h
      show χ ⟨τ, hτ⟩ = 1
      have h' : ((χ ⟨τ, hτ⟩ : ℤˣ) : ℤ) = 1 := by exact_mod_cast h
      apply Units.val_injective
      rw [h', Units.val_one]
    · right
      apply Subtype.ext
      refine MonoidHom.ext fun x => ?_
      obtain ⟨τ, hτ⟩ := x
      have h := hk τ hτ
      show χ ⟨τ, hτ⟩ = etaG w g hg hg0 ⟨τ, hτ⟩
      rw [etaG_apply]
      unfold sgnG at h
      split_ifs at h ⊢ with hτg
      · rw [one_zpow] at h
        have h' : ((χ ⟨τ, hτ⟩ : ℤˣ) : ℤ) = 1 := by exact_mod_cast h
        apply Units.val_injective
        rw [h', Units.val_one]
      · rw [hk2.neg_one_zpow] at h
        have h' : ((χ ⟨τ, hτ⟩ : ℤˣ) : ℤ) = -1 := by exact_mod_cast h
        apply Units.val_injective
        rw [h', Units.val_neg, Units.val_one]

/-- **B3 (v) rests on no leaf** (glue-t32a): glue-b3b's `unramified_outside_t32a` with T32(a)
discharged by `t32a`. -/
theorem unramified_outside_noLeaf
    (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (T : Finset ℕ) (h2 : 2 ∈ T) (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p)
    (ε : GQ → GQ → ℂˣ)
    (hεN : ∀ σ τ, σ ∈ L.fixingSubgroup ∨ τ ∈ L.fixingSubgroup → ε σ τ = 1)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hN : ∀ q, q.Prime → q ∣ N → q ∈ T)
    (β : GQ → ℂˣ) (hβl : IsLocallyConstant β) (hβs : ∀ x, β x ^ 2 = galChar χ x)
    (hβe : ∀ x y, β x * β y = ε x y * β (x * y)) :
    ∃ Q : Finset ℕ, (∀ q ∈ Q, q.Prime ∧ q ∉ T) ∧
      (∀ x, (∏ q ∈ Q, etaP q) x ^ 2 = 1) ∧ IsLocallyConstant ⇑(∏ q ∈ Q, etaP q) ∧
      ∀ L' : IntermediateField ℚ Qbar,
        (∀ σ, σ ∈ L'.fixingSubgroup ↔
          σ ∈ L.fixingSubgroup ∧ β σ * (∏ q ∈ Q, etaP q) σ = 1) →
        GalUnramifiedOutside L' T :=
  unramified_outside_t32a t32a L T h2 hram ε hεN χ hN β hβl hβs hβe

/-- `LeafB3a` (glue-b3-unram's form of the unique quadratic character of tame inertia) is glue. -/
theorem leafB3a : LeafB3a := leafB3a_of_t32a t32a

end T32a

end GlueB3Unram
