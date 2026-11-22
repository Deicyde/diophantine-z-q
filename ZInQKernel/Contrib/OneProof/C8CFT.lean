import ZInQKernel.Contrib.OneProof.C8LocAlg

/-! # c8-conrad2: `FiniteOfLocAlgTrivialQ` ("class field theory over ℚ", diophantine_zq.tex L761-765) from two
dictionary statements

* `CFTFiniteQ` is proved from `MinkowskiInertiaQ` (Mathlib's Minkowski theorem read on the inertia groups of places
  of `ℚ̄`): `ψ^m` takes values in the torsion-free open subgroup `V = {‖u - 1‖ < ‖p‖}` of `ℚ̄_p^×`
  (`eq_one_of_pow_eq_one_small`), so it kills every inertia group with finite image, hence is trivial by Krull's
  Galois correspondence (`eq_one_of_inertia_trivial`); so `ψ` has values in the `m`-th roots of unity.
* `InertiaFiniteAwayFromP` (the on-the-spot step of N5, rv-h-c8 §4 item 3) is proved from the inertia dictionary
  `InertiaAtPDecomp` at `q` and Tau Ceti's local class field theory of `ℚ_q`: `u^{(q-1)q^n} → 1` in `ℤ_q^×` while
  `x ↦ x^{q^n}` is an isometry on `V` (`q ≠ p`).
* `finiteOfLocAlgTrivialQ_of_dicts : InertiaAtPDecomp → MinkowskiInertiaQ → FiniteOfLocAlgTrivialQ`. -/

set_option linter.style.longLine false
set_option linter.style.haveILetI false

noncomputable section

namespace HDec.G0Galois.C8Conrad

open _root_.PkgI4 (GaloisRep GaloisChar)

section Torsion

variable (p : ℕ) [Fact p.Prime]

local notation "K" => PadicAlgCl p

theorem norm_natCast_K (n : ℕ) : ‖(n : K)‖ = ‖(n : ℚ_[p])‖ := by
  rw [← PadicAlgCl.norm_extends p (n : ℚ_[p]), map_natCast]

theorem norm_p_K : ‖(p : K)‖ = (p : ℝ)⁻¹ := by rw [norm_natCast_K, Padic.norm_p]

theorem norm_p_K_pos : 0 < ‖(p : K)‖ := by
  rw [norm_p_K]; exact inv_pos.2 (by exact_mod_cast (Fact.out : p.Prime).pos)

theorem norm_p_K_lt_one : ‖(p : K)‖ < 1 := by
  rw [norm_p_K]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

theorem norm_le_one_of_norm_sub_one_lt {x : K} (h : ‖x - 1‖ < 1) : ‖x‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (x - 1) 1
  rw [sub_add_cancel, norm_one] at this
  exact this.trans (max_le h.le le_rfl)

theorem norm_pow_sub_one_le {x : K} (h : ‖x - 1‖ < 1) (i : ℕ) : ‖x ^ i - 1‖ ≤ ‖x - 1‖ := by
  rw [← geom_sum_mul, norm_mul]
  have hs : ‖∑ j ∈ Finset.range i, x ^ j‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_le_one_of_norm_sub_one_lt p h)
  calc ‖∑ j ∈ Finset.range i, x ^ j‖ * ‖x - 1‖ ≤ 1 * ‖x - 1‖ :=
        mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ = ‖x - 1‖ := one_mul _

/-- Prime-to-`p` torsion: `‖x - 1‖ < 1`, `x^n = 1`, `p ∤ n` force `x = 1`. -/
theorem eq_one_of_pow_eq_one_coprime {x : K} (h : ‖x - 1‖ < 1) {n : ℕ} (hn : p.Coprime n)
    (hx : x ^ n = 1) : x = 1 := by
  set S := ∑ j ∈ Finset.range n, x ^ j
  have hS : ‖S - n‖ < 1 := by
    have : S - n = ∑ j ∈ Finset.range n, (x ^ j - 1) := by
      simp [S, Finset.sum_sub_distrib]
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
      fun j _ => norm_pow_sub_one_le p h j) h
  have hn1 : ‖(n : K)‖ = 1 := by rw [norm_natCast_K]; exact Padic.norm_natCast_eq_one_iff.2 hn
  have hS1 : ‖S‖ = 1 := by
    have h2 : ‖S - n‖ ≠ ‖(n : K)‖ := by rw [hn1]; exact hS.ne
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2
    rw [sub_add_cancel, hn1] at this
    rw [this]; exact max_eq_right hS.le
  have h0 : S * (x - 1) = 0 := by rw [geom_sum_mul, hx, sub_self]
  rcases mul_eq_zero.1 h0 with h1 | h1
  · rw [h1, norm_zero] at hS1; exact absurd hS1 zero_ne_one
  · exact sub_eq_zero.1 h1

theorem binom_split {R : Type*} [CommRing R] (y : R) (n q : ℕ) (hq : n = q + 2) :
    (y + 1) ^ n = ∑ k ∈ Finset.range q, y ^ (k + 2) * (n.choose (k + 2) : R) + (n : R) * y + 1 + y ^ n := by
  subst hq
  rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [one_pow, mul_one, pow_zero, pow_one, Nat.choose_zero_right, Nat.choose_one_right,
    Nat.cast_one, Nat.choose_self, zero_add, Nat.sub_self]
  ring

/-- `p`-torsion: `‖x - 1‖ < ‖p‖` and `x^p = 1` force `x = 1`. -/
theorem eq_one_of_pow_p_eq_one {x : K} (h : ‖x - 1‖ < ‖(p : K)‖) (hx : x ^ p = 1) : x = 1 := by
  by_contra hne
  set y := x - 1 with hy_def
  have hy0 : y ≠ 0 := sub_ne_zero.2 hne
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hy1 : ‖y‖ < 1 := h.trans (norm_p_K_lt_one p)
  obtain ⟨q, hq⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := (Fact.out : p.Prime).two_le; omega⟩
  have hexp := binom_split y p q hq
  have hR : ‖∑ k ∈ Finset.range q, y ^ (k + 2) * (p.choose (k + 2) : K)‖ ≤ ‖(p : K)‖ * ‖y‖ ^ 2 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k hk => by
      have hk' : k + 2 < p := by rw [Finset.mem_range] at hk; omega
      obtain ⟨c, hc⟩ := (Fact.out : p.Prime).dvd_choose_self (by omega) hk'
      rw [hc, Nat.cast_mul, norm_mul, norm_mul, norm_pow]
      have hc1 : ‖(c : K)‖ ≤ 1 := by rw [norm_natCast_K]; simpa using Padic.norm_int_le_one (p := p) c
      have hpow : ‖y‖ ^ (k + 2) ≤ ‖y‖ ^ 2 := pow_le_pow_of_le_one (norm_nonneg _) hy1.le (by omega)
      calc ‖y‖ ^ (k + 2) * (‖(p : K)‖ * ‖(c : K)‖) ≤ ‖y‖ ^ 2 * (‖(p : K)‖ * 1) := by gcongr
        _ = ‖(p : K)‖ * ‖y‖ ^ 2 := by ring
  have hyp : ‖y ^ p‖ < ‖(p : K)‖ * ‖y‖ := by
    rw [norm_pow]
    calc ‖y‖ ^ p ≤ ‖y‖ ^ 2 := pow_le_pow_of_le_one (norm_nonneg _) hy1.le (Fact.out : p.Prime).two_le
      _ = ‖y‖ * ‖y‖ := pow_two _
      _ < ‖(p : K)‖ * ‖y‖ := mul_lt_mul_of_pos_right h hyn
  have hsum : ∑ k ∈ Finset.range q, y ^ (k + 2) * (p.choose (k + 2) : K) + (p : K) * y + y ^ p = 0 := by
    have : (y + 1) ^ p = 1 := by rw [hy_def, sub_add_cancel, hx]
    rw [hexp] at this
    linear_combination this
  have hmain : ‖(p : K) * y‖ = ‖(p : K)‖ * ‖y‖ := norm_mul _ _
  have hrest : ‖∑ k ∈ Finset.range q, y ^ (k + 2) * (p.choose (k + 2) : K) + y ^ p‖ < ‖(p : K) * y‖ := by
    rw [hmain]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hyp)
    calc _ ≤ ‖(p : K)‖ * ‖y‖ ^ 2 := hR
      _ < ‖(p : K)‖ * ‖y‖ := by
        rw [pow_two]
        exact mul_lt_mul_of_pos_left (mul_lt_of_lt_one_left hyn hy1) (norm_p_K_pos p)
  have : ‖(p : K) * y + (∑ k ∈ Finset.range q, y ^ (k + 2) * (p.choose (k + 2) : K) + y ^ p)‖ = ‖(p : K) * y‖ := by
    rw [add_comm]
    exact IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hrest.ne |>.trans (max_eq_right hrest.le)
  have h0 : (p : K) * y + (∑ k ∈ Finset.range q, y ^ (k + 2) * (p.choose (k + 2) : K) + y ^ p) = 0 := by
    linear_combination hsum
  rw [h0, norm_zero, hmain] at this
  exact (mul_pos (norm_p_K_pos p) hyn).ne' this.symm

/-- No nontrivial torsion within `‖x - 1‖ < ‖p‖`. -/
theorem eq_one_of_pow_eq_one_small {x : K} (h : ‖x - 1‖ < ‖(p : K)‖) {m : ℕ} (hm : 0 < m)
    (hx : x ^ m = 1) : x = 1 := by
  obtain ⟨a, b, hb, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p (Fact.out : p.Prime).ne_one
  have h1 : ‖x - 1‖ < 1 := h.trans (norm_p_K_lt_one p)
  have hy : x ^ p ^ a = 1 := by
    refine eq_one_of_pow_eq_one_coprime p (lt_of_le_of_lt (norm_pow_sub_one_le p h1 _) h1)
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hb) ?_
    rw [← pow_mul, hx]
  clear hx hm
  induction a with
  | zero => simpa using hy
  | succ a ih =>
    apply ih
    refine eq_one_of_pow_p_eq_one p (lt_of_le_of_lt (norm_pow_sub_one_le p h1 _) h) ?_
    rw [← pow_mul, ← pow_succ, hy]

/-- The open subgroup `V = {u : ‖u - 1‖ < ‖p‖}` of `ℚ̄_p^×`; it has no nontrivial torsion. -/
def smallUnits : Subgroup (PadicAlgCl p)ˣ where
  carrier := {u | ‖((u : K)) - 1‖ < ‖(p : K)‖}
  one_mem' := by simp [norm_p_K_pos p]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at ha hb ⊢
    have ha1 : ‖(a : K)‖ ≤ 1 := norm_le_one_of_norm_sub_one_lt p (ha.trans (norm_p_K_lt_one p))
    have : (a : K) * b - 1 = a * (b - 1) + (a - 1) := by ring
    rw [this]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ha)
    rw [norm_mul]
    calc ‖(a : K)‖ * ‖(b : K) - 1‖ ≤ 1 * ‖(b : K) - 1‖ := by gcongr
      _ < ‖(p : K)‖ := by rw [one_mul]; exact hb
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have ha1 : ‖(a : K) - 1‖ < 1 := ha.trans (norm_p_K_lt_one p)
    have hna : ‖(a : K)‖ = 1 := by
      have h2 : ‖(a : K) - 1‖ ≠ ‖(1 : K)‖ := by rw [norm_one]; exact ha1.ne
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2
      rw [sub_add_cancel, norm_one] at this
      rw [this]; exact max_eq_right ha1.le
    have : ((a⁻¹ : (PadicAlgCl p)ˣ) : K) - 1 = (a⁻¹ : (PadicAlgCl p)ˣ) * (1 - a) := by
      rw [mul_sub, mul_one, Units.inv_mul]
    rw [this, norm_mul, norm_sub_rev]
    have hinv : ‖((a⁻¹ : (PadicAlgCl p)ˣ) : K)‖ = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv, hna, inv_one]
    rw [hinv, one_mul]; exact ha

theorem isOpen_smallUnits : IsOpen ((smallUnits p : Subgroup (PadicAlgCl p)ˣ) : Set (PadicAlgCl p)ˣ) := by
  have : ((smallUnits p : Subgroup (PadicAlgCl p)ˣ) : Set (PadicAlgCl p)ˣ) =
      Units.val ⁻¹' Metric.ball (1 : K) ‖(p : K)‖ := by
    ext u; simp [smallUnits, Metric.mem_ball, dist_eq_norm]
  rw [this]
  exact Metric.isOpen_ball.preimage Units.continuous_val

end Torsion

/-! ## `CFTFiniteQ` from Minkowski's theorem -/

/-- **GLUE over Mathlib's Minkowski theorem (C8, "class field theory over ℚ", N5 L761-765).** An algebraic number
fixed by every inertia group of every place of `ℚ̄` is rational: `ℚ` has no nontrivial extension unramified at every
prime (Minkowski; in Mathlib `NumberField.exists_not_isUnramifiedIn`, `NumberField.finrank_eq_one_of_unramified`,
`Mathlib/NumberTheory/NumberField/ExistsRamified.lean`). The step from Mathlib's statement is a dictionary: if every
inertia group of `ℚ̄` fixes `x`, the Galois closure `L` of `ℚ(x)` has trivial inertia groups at every prime of `𝓞_L`
(the inertia groups of places of `ℚ̄` surject onto those of `L`), so `L/ℚ` is unramified (STANDARD; Neukirch,
*Algebraic Number Theory*, I §9 and III §2, UNVERIFIED locators). -/
def MinkowskiInertiaQ : Prop :=
  ∀ x : PkgI4.Qbar, (∀ q : ℕ, q.Prime → ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v q →
    ∀ τ : v.inertiaSubgroup ℚ, ((τ : v.decompositionSubgroup ℚ) : PkgI4.GQ) x = x) →
    x ∈ Set.range (algebraMap ℚ PkgI4.Qbar)

theorem finite_quot_open (H : OpenSubgroup PkgI4.GQ) : Finite (PkgI4.GQ ⧸ (H : Subgroup PkgI4.GQ)) :=
  inferInstance

/-- A continuous homomorphism out of `G_ℚ` into a `T₁` group that kills every inertia group is trivial (Krull's
Galois correspondence and `MinkowskiInertiaQ`). -/
theorem eq_one_of_inertia_trivial (hM : MinkowskiInertiaQ) {G' : Type*} [Group G'] [TopologicalSpace G']
    [T1Space G'] (φ : PkgI4.GQ →* G') (hφ : Continuous φ)
    (h : ∀ q : ℕ, q.Prime → ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v q →
      ∀ τ : v.inertiaSubgroup ℚ, φ ((τ : v.decompositionSubgroup ℚ) : PkgI4.GQ) = 1)
    (g : PkgI4.GQ) : φ g = 1 := by
  by_contra hg
  have hclosed : IsClosed (φ.ker : Set PkgI4.GQ) := by
    have : (φ.ker : Set PkgI4.GQ) = φ ⁻¹' {1} := by ext; simp
    rw [this]; exact isClosed_singleton.preimage hφ
  let N : ClosedSubgroup PkgI4.GQ := ⟨φ.ker, hclosed⟩
  have hK := InfiniteGalois.fixingSubgroup_fixedField (k := ℚ) (K := PkgI4.Qbar) N
  have hgN : g ∉ (IntermediateField.fixedField (N : Subgroup PkgI4.GQ)).fixingSubgroup := by
    rw [hK]; exact hg
  rw [IntermediateField.mem_fixingSubgroup_iff] at hgN
  push Not at hgN
  obtain ⟨x, hx, hgx⟩ := hgN
  have hfix : ∀ σ ∈ φ.ker, σ x = x := fun σ hσ =>
    (IntermediateField.mem_fixedField_iff (N : Subgroup PkgI4.GQ) x).1 hx σ hσ
  obtain ⟨c, rfl⟩ := hM x fun q hq v hv τ => hfix _ (h q hq v hv τ)
  exact hgx (AlgEquiv.commutes g c)

/-- **`CFTFiniteQ` from Minkowski's theorem** (`MinkowskiInertiaQ`): `ψ^m` (with `m` the index of `ψ⁻¹(V)`) takes
values in the torsion-free open subgroup `V = {‖u - 1‖ < ‖p‖}` of `ℚ̄_p^×`, so it kills every inertia group (finite
images), hence is trivial, so `ψ` takes values in the `m`-th roots of unity. The hypothesis "unramified outside a
finite set" is not needed. -/
theorem cftFiniteQNoRam_of_minkowski (hM : MinkowskiInertiaQ) (p : ℕ) [Fact p.Prime] (ψ : GaloisChar p)
    (hfin : ∀ q : ℕ, q.Prime → ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v q → CharInertiaFinite ψ v) :
    (Set.range ψ.toHom).Finite := by
  let H : Subgroup PkgI4.GQ := (smallUnits p).comap ψ.toHom
  have hHopen : IsOpen (H : Set PkgI4.GQ) := (isOpen_smallUnits p).preimage ψ.continuous_toHom
  haveI hHnormal : H.Normal := ⟨fun n hn g => by
    change ψ.toHom (g * n * g⁻¹) ∈ smallUnits p
    rw [map_mul, map_mul, mul_comm (ψ.toHom g), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    exact hn⟩
  haveI : Finite (PkgI4.GQ ⧸ H) := finite_quot_open ⟨H, hHopen⟩
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  set m := H.index with hm_def
  have hm : 0 < m := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hV : ∀ g, ψ.toHom g ^ m ∈ smallUnits p := fun g => by
    have := Subgroup.pow_index_mem H g
    change ψ.toHom (g ^ H.index) ∈ smallUnits p at this
    rwa [map_pow] at this
  let φ : PkgI4.GQ →* (PadicAlgCl p)ˣ := ψ.toHom ^ m
  have hφ : ∀ g, φ g = ψ.toHom g ^ m := fun g => rfl
  have hφc : Continuous φ := by
    have : (φ : PkgI4.GQ → (PadicAlgCl p)ˣ) = fun g => ψ.toHom g ^ m := funext hφ
    rw [this]; exact ψ.continuous_toHom.pow m
  have hinert : ∀ q : ℕ, q.Prime → ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v q →
      ∀ τ : v.inertiaSubgroup ℚ, φ ((τ : v.decompositionSubgroup ℚ) : PkgI4.GQ) = 1 := by
    intro q hq v hv τ
    -- `ψ(τ)` has finite order: its powers lie in the finite set `ψ(I_v)`
    have hS := hfin q hq v hv
    obtain ⟨i, j, hij, hEq⟩ : ∃ i j : ℕ, i ≠ j ∧ ψ.toHom ((τ : v.decompositionSubgroup ℚ) : PkgI4.GQ) ^ i =
        ψ.toHom ((τ : v.decompositionSubgroup ℚ) : PkgI4.GQ) ^ j := by
      have hmaps : ∀ n : ℕ, ψ.toHom ((τ : v.decompositionSubgroup ℚ) : PkgI4.GQ) ^ n ∈
          Set.range fun σ : v.inertiaSubgroup ℚ => ψ.toHom ((σ : v.decompositionSubgroup ℚ) : PkgI4.GQ) :=
        fun n => ⟨τ ^ n, by simp⟩
      haveI := hS.to_subtype
      obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite
        (fun n : ℕ => (⟨_, hmaps n⟩ : Set.range fun σ : v.inertiaSubgroup ℚ =>
          ψ.toHom ((σ : v.decompositionSubgroup ℚ) : PkgI4.GQ)))
      exact ⟨i, j, hij, congrArg Subtype.val h⟩
    set y := ψ.toHom ((τ : v.decompositionSubgroup ℚ) : PkgI4.GQ)
    have hy : ∃ n, 0 < n ∧ y ^ n = 1 := by
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · refine ⟨j - i, Nat.sub_pos_of_lt hlt, ?_⟩
        have := hEq; rw [← Nat.add_sub_cancel' hlt.le, pow_add] at this
        exact (mul_eq_left.1 this.symm)
      · refine ⟨i - j, Nat.sub_pos_of_lt hlt, ?_⟩
        have := hEq; rw [← Nat.add_sub_cancel' hlt.le, pow_add] at this
        exact (mul_eq_left.1 this)
    obtain ⟨n, hn, hyn⟩ := hy
    rw [hφ]
    apply Units.ext
    have hmem := hV ((τ : v.decompositionSubgroup ℚ) : PkgI4.GQ)
    refine eq_one_of_pow_eq_one_small p hmem hn ?_
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hyn, one_pow, Units.val_one]
  have htriv := eq_one_of_inertia_trivial hM φ hφc hinert
  have hfinR : (rootsOfUnity m (PadicAlgCl p) : Set (PadicAlgCl p)ˣ).Finite := by
    haveI : NeZero m := ⟨hm.ne'⟩
    exact Set.finite_coe_iff.mp (inferInstance : Finite (rootsOfUnity m (PadicAlgCl p)))
  refine hfinR.subset ?_
  rintro _ ⟨g, rfl⟩
  change _ ∈ rootsOfUnity m (PadicAlgCl p)
  rw [mem_rootsOfUnity, ← hφ]
  exact htriv g


/-- `CFTFiniteQ` (with its unused hypothesis "unramified outside a finite set"). -/
theorem cftFiniteQ_of_minkowski (hM : MinkowskiInertiaQ) : CFTFiniteQ :=
  fun p _ ψ hfin _ => cftFiniteQNoRam_of_minkowski hM p ψ hfin

/-! ## `InertiaFiniteAwayFromP` from the inertia dictionary and Tau Ceti's local class field theory at `q` -/

/-- `x ↦ x^n` is an isometry near `1` when `p ∤ n`. -/
theorem norm_pow_sub_one_eq_of_coprime (p : ℕ) [Fact p.Prime] {x : PadicAlgCl p} (h : ‖x - 1‖ < 1) {n : ℕ}
    (hn : p.Coprime n) : ‖x ^ n - 1‖ = ‖x - 1‖ := by
  set S := ∑ j ∈ Finset.range n, x ^ j
  have hS : ‖S - n‖ < 1 := by
    have : S - n = ∑ j ∈ Finset.range n, (x ^ j - 1) := by
      simp [S, Finset.sum_sub_distrib]
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
      fun j _ => norm_pow_sub_one_le p h j) h
  have hn1 : ‖(n : PadicAlgCl p)‖ = 1 := by
    rw [norm_natCast_K]; exact Padic.norm_natCast_eq_one_iff.2 hn
  have hS1 : ‖S‖ = 1 := by
    have h2 : ‖S - n‖ ≠ ‖(n : PadicAlgCl p)‖ := by rw [hn1]; exact hS.ne
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2
    rw [sub_add_cancel, hn1] at this
    rw [this]; exact max_eq_right hS.le
  rw [← geom_sum_mul, norm_mul, hS1, one_mul]

/-- Some power `ψ^m`, `m > 0`, takes values in `V = smallUnits p`. -/
theorem exists_pow_mem_smallUnits (p : ℕ) [Fact p.Prime] (ψ : GaloisChar p) :
    ∃ m : ℕ, 0 < m ∧ ∀ g, ψ.toHom g ^ m ∈ smallUnits p := by
  let H : Subgroup PkgI4.GQ := (smallUnits p).comap ψ.toHom
  have hHopen : IsOpen (H : Set PkgI4.GQ) := (isOpen_smallUnits p).preimage ψ.continuous_toHom
  haveI hHnormal : H.Normal := ⟨fun n hn g => by
    change ψ.toHom (g * n * g⁻¹) ∈ smallUnits p
    rw [map_mul, map_mul, mul_comm (ψ.toHom g), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    exact hn⟩
  haveI : Finite (PkgI4.GQ ⧸ H) := finite_quot_open ⟨H, hHopen⟩
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨H.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, fun g => ?_⟩
  have := Subgroup.pow_index_mem H g
  change ψ.toHom (g ^ H.index) ∈ smallUnits p at this
  rwa [map_pow] at this

/-- For a unit `u` of `ℤ_q`, `u^{(q-1) q^n} → 1`. -/
theorem tendsto_pow_units (q : ℕ) [Fact q.Prime] (u : ℤ_[q]ˣ) :
    Filter.Tendsto (fun n : ℕ => unitsQp q ((u ^ (q - 1)) ^ q ^ n)) Filter.atTop (nhds 1) := by
  rw [Units.isEmbedding_val₀.tendsto_nhds_iff]
  set w : ℤ_[q] := ((u ^ (q - 1) : ℤ_[q]ˣ) : ℤ_[q])
  have hw : (q : ℤ_[q]) ∣ w - 1 := by
    have h0 : PadicInt.toZMod (w - 1) = 0 := by
      have hu : PadicInt.toZMod (u : ℤ_[q]) ≠ 0 := by
        intro h0
        have := congrArg PadicInt.toZMod (u.mul_inv)
        rw [map_mul, h0, zero_mul, map_one] at this
        exact zero_ne_one this
      simp only [w, Units.val_pow_eq_pow_val, map_sub, map_pow, map_one]
      rw [ZMod.pow_card_sub_one_eq_one hu, sub_self]
    have : w - 1 ∈ IsLocalRing.maximalIdeal ℤ_[q] := by
      rw [← PadicInt.ker_toZMod]; exact h0
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
    exact this
  have hbound : ∀ n : ℕ, ‖((((u ^ (q - 1)) ^ q ^ n : ℤ_[q]ˣ) : ℤ_[q]) : ℚ_[q]) - 1‖ ≤ ((q : ℝ)⁻¹) ^ (n + 1) := by
    intro n
    have hd := dvd_sub_pow_of_dvd_sub hw n
    rw [one_pow] at hd
    have hmem : w ^ q ^ n - 1 ∈ (Ideal.span {(q : ℤ_[q]) ^ (n + 1)} : Ideal ℤ_[q]) :=
      Ideal.mem_span_singleton.2 hd
    have := (PadicInt.norm_le_pow_iff_mem_span_pow (w ^ q ^ n - 1) (n + 1)).2 hmem
    have e : ((((u ^ (q - 1)) ^ q ^ n : ℤ_[q]ˣ) : ℤ_[q]) : ℚ_[q]) - 1 = ((w ^ q ^ n - 1 : ℤ_[q]) : ℚ_[q]) := by
      simp [w, Units.val_pow_eq_pow_val]
    rw [e, PadicInt.norm_coe]
    refine this.trans (le_of_eq ?_)
    rw [zpow_neg, zpow_natCast, inv_pow]
  have hlim : Filter.Tendsto (fun n : ℕ => ((q : ℝ)⁻¹) ^ (n + 1)) Filter.atTop (nhds 0) := by
    have h1 : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : q.Prime).one_lt)
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) h1).comp (Filter.tendsto_add_atTop_nat 1)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _) hbound hlim

/-- **`InertiaFiniteAwayFromP` proved** from the inertia dictionary `InertiaAtPDecomp` (at the prime `q`) and Tau
Ceti's local class field theory of `ℚ_q`: on `I_{ℚ_q}`, `ψ^m` (values in `V`) factors through the Artin symbols of
`ℤ_q^×`; `u^{(q-1)q^n} → 1`, while `x ↦ x^{q^n}` is an isometry on `V` (`q ≠ p`), so `ψ^{m(q-1)} = 1` on inertia, and
`ψ^m = 1` there since `V` has no torsion. -/
theorem inertiaFiniteAwayFromP_of_decomp (hB : InertiaAtPDecomp) : InertiaFiniteAwayFromP := by
  intro p _ ψ q hq hqp v hv
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨m, hm, hV⟩ := exists_pow_mem_smallUnits p ψ
  have key : ∀ τ : v.inertiaSubgroup ℚ, ψ.toHom ((τ : v.decompositionSubgroup ℚ) : PkgI4.GQ) ^ m = 1 := by
    intro τ
    obtain ⟨σ, g, hσ, hτ⟩ := hB q v hv τ
    rw [hτ, map_mul, map_mul, mul_comm (ψ.toHom g), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    obtain ⟨u, hu⟩ := exists_unit_isArtinLift q σ hσ
    set y := ψ.toHom (PkgI4.decomp q σ) ^ m with hy_def
    let f : Field.absoluteGaloisGroup ℚ_[q] →ₜ* (PadicAlgCl p)ˣ :=
      { toMonoidHom := (ψ.toHom ^ m).comp (PkgI4.decomp q)
        continuous_toFun := by
          have hd : Continuous (PkgI4.decomp q) :=
            (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[q])).continuous
          exact (ψ.continuous_toHom.comp hd).pow m }
    let Φ := TopologicalAbelianization.lift f
    have hΦ : ∀ n : ℕ, Φ (TauCeti.ClassFieldTheory.artinMap ℚ_[q] (unitsQp q ((u ^ (q - 1)) ^ q ^ n))) =
        y ^ ((q - 1) * q ^ n) := by
      intro n
      have hl : IsArtinLift q (σ ^ ((q - 1) * q ^ n)) (unitsQp q ((u ^ (q - 1)) ^ q ^ n)) := by
        unfold IsArtinLift at hu ⊢
        have e1 : unitsQp q ((u ^ (q - 1)) ^ q ^ n) = unitsQp q u ^ ((q - 1) * q ^ n) := by
          simp only [unitsQp, map_pow, ← pow_mul]
        rw [e1, map_pow, ← hu]
        rfl
      unfold IsArtinLift at hl
      rw [← hl]
      change f (σ ^ ((q - 1) * q ^ n)) = _
      change (ψ.toHom ^ m) (PkgI4.decomp q (σ ^ ((q - 1) * q ^ n))) = _
      rw [map_pow, MonoidHom.pow_apply, map_pow, hy_def, ← pow_mul, ← pow_mul, Nat.mul_comm]
    have htend : Filter.Tendsto (fun n : ℕ => y ^ ((q - 1) * q ^ n)) Filter.atTop (nhds 1) := by
      have hc : Continuous (fun x : ℚ_[q]ˣ => Φ (TauCeti.ClassFieldTheory.artinMap ℚ_[q] x)) :=
        Φ.continuous.comp (TauCeti.ClassFieldTheory.continuous_artinMap (K := ℚ_[q]))
      have := (hc.tendsto 1).comp (tendsto_pow_units q u)
      simp only [map_one] at this
      refine this.congr fun n => ?_
      exact hΦ n
    -- `z = y^{q-1} ∈ V`, and `‖z^{q^n} - 1‖ = ‖z - 1‖` is constant and tends to `0`
    have hz : (y ^ (q - 1) : (PadicAlgCl p)ˣ) ∈ smallUnits p := (smallUnits p).pow_mem (hV _) _
    have hz1 : ‖((y ^ (q - 1) : (PadicAlgCl p)ˣ) : PadicAlgCl p) - 1‖ < 1 := hz.trans (norm_p_K_lt_one p)
    have hcop : ∀ n : ℕ, p.Coprime (q ^ n) := fun n =>
      Nat.Coprime.pow_right n ((Nat.coprime_primes Fact.out hq).2 (Ne.symm hqp))
    have hconst : ∀ n : ℕ, ‖((y ^ ((q - 1) * q ^ n) : (PadicAlgCl p)ˣ) : PadicAlgCl p) - 1‖ =
        ‖((y ^ (q - 1) : (PadicAlgCl p)ˣ) : PadicAlgCl p) - 1‖ := by
      intro n
      rw [pow_mul, Units.val_pow_eq_pow_val]
      exact norm_pow_sub_one_eq_of_coprime p hz1 (hcop n)
    have hval : Filter.Tendsto (fun n : ℕ => ((y ^ ((q - 1) * q ^ n) : (PadicAlgCl p)ˣ) : PadicAlgCl p))
        Filter.atTop (nhds 1) := by
      have := (Units.continuous_val.tendsto 1).comp htend
      rwa [Units.val_one] at this
    have h0 : ‖((y ^ (q - 1) : (PadicAlgCl p)ˣ) : PadicAlgCl p) - 1‖ = 0 := by
      have h2 := (tendsto_iff_norm_sub_tendsto_zero.1 hval)
      simp only [hconst] at h2
      exact tendsto_nhds_unique tendsto_const_nhds h2
    have hzq : y ^ (q - 1) = 1 := Units.ext (sub_eq_zero.1 (norm_eq_zero.1 h0))
    have hq1 : 0 < q - 1 := Nat.sub_pos_of_lt hq.one_lt
    exact Units.ext (eq_one_of_pow_eq_one_small p (hV _) hq1
      (by rw [← Units.val_pow_eq_pow_val, hzq, Units.val_one]))
  have hfinR : (rootsOfUnity m (PadicAlgCl p) : Set (PadicAlgCl p)ˣ).Finite := by
    haveI : NeZero m := ⟨hm.ne'⟩
    exact Set.finite_coe_iff.mp (inferInstance : Finite (rootsOfUnity m (PadicAlgCl p)))
  refine hfinR.subset ?_
  rintro _ ⟨τ, rfl⟩
  change _ ∈ rootsOfUnity m (PadicAlgCl p)
  rw [mem_rootsOfUnity]
  exact key τ

/-- **`FiniteOfLocAlgTrivialQ` from two dictionary statements**: the inertia dictionary `InertiaAtPDecomp` and
`MinkowskiInertiaQ` (Mathlib's Minkowski theorem read on inertia groups of places of `ℚ̄`). -/
theorem finiteOfLocAlgTrivialQ_of_dicts (hB : InertiaAtPDecomp) (hM : MinkowskiInertiaQ) :
    FiniteOfLocAlgTrivialQ :=
  finiteOfLocAlgTrivialQ_of_pieces (inertiaFiniteAwayFromP_of_decomp hB) hB (cftFiniteQ_of_minkowski hM)


/-! ## Step C8 without the "unramified almost everywhere" half of `TwistCharHT0` -/

/-- **`FiniteOfLocAlgTrivialQ` without its hypothesis "unramified outside a finite set"** (which the proof from the
dictionaries does not use). -/
def FiniteOfLocAlgTrivialQNoRam : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ψ : GaloisChar p),
    (∃ k : ℕ, ∀ u : ℤ_[p]ˣ, PadicInt.toZModPow k (u : ℤ_[p]) = 1 → ∀ σ : PkgI4.GQp p,
      IsArtinLift p σ (unitsQp p u) → ψ.toHom (PkgI4.decomp p σ) = 1) →
    (Set.range ψ.toHom).Finite

theorem finiteOfLocAlgTrivialQNoRam_of_dicts (hB : InertiaAtPDecomp) (hM : MinkowskiInertiaQ) :
    FiniteOfLocAlgTrivialQNoRam := by
  intro p _ ψ ⟨k, hk⟩
  refine cftFiniteQNoRam_of_minkowski hM p ψ fun q hq v hv => ?_
  by_cases hqp : q = p
  · subst hqp
    haveI : NeZero (q ^ k) := ⟨pow_ne_zero k hq.ne_zero⟩
    set N := (q ^ k).totient
    have hNpos : 0 < N := Nat.totient_pos.2 (pow_pos hq.pos k)
    haveI : NeZero N := ⟨hNpos.ne'⟩
    have hfin : (rootsOfUnity N (PadicAlgCl q) : Set (PadicAlgCl q)ˣ).Finite :=
      Set.finite_coe_iff.mp (inferInstance : Finite (rootsOfUnity N (PadicAlgCl q)))
    refine (hfin.image (fun x : (PadicAlgCl q)ˣ => x)).subset ?_
    rintro _ ⟨τ, rfl⟩
    obtain ⟨σ, g, hσ, hτ⟩ := hB q v hv τ
    refine ⟨ψ.toHom ((τ : v.decompositionSubgroup ℚ) : PkgI4.GQ), ?_, rfl⟩
    rw [hτ, map_mul, map_mul, mul_comm (ψ.toHom g), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    show _ ∈ rootsOfUnity N (PadicAlgCl q)
    rw [mem_rootsOfUnity]
    exact pow_card_eq_one_of_mem_inertia q ψ k hk σ hσ
  · exact inertiaFiniteAwayFromP_of_decomp hB p ψ q hq hqp v hv

/-- **GLUE (C8, N5 L758-760 and the weight comparison L765-766): the twisting character is Hodge–Tate of weight `0`
at 5.** The Hodge–Tate half of `TwistCharHT0` (whose other half, "unramified outside a finite set", the proof of C8
no longer needs). On-the-spot sketch, following N5: with `ρ_g` from R14 (`EigenformRepExists`), Chebotarev density
and continuity give `tr r = ψ · tr ρ_g` on `G_ℚ`, so `r^{ss} ≅ ψ ⊗ ρ_g` (Brauer–Nesbitt), i.e. `ψ` is a
subrepresentation of `Hom(ρ_g, r^{ss})` (N5: "a de Rham subrepresentation of the Hom representation"); Hodge–Tate
representations are stable under `Hom`, subquotients and semisimplification (Fontaine; Brinon–Conrad, CMI notes
§2.4, UNVERIFIED locators), so `ψ|_{G_{ℚ_5}}` is Hodge–Tate of some weight `s`, with values in a finite `E/ℚ_5`
(Baire); R13 (`EigenformHT`) gives `ρ_g` the weights `{0, -1}` at `k = 2`, so `{s, s - 1} = {0, -1}` and `s = 0`
(the tree's `SenTwist` machinery, `senTwist_of_tate`, proves the weight shift once `ψ` is Hodge–Tate). -/
def TwistCharHTWt0 : Prop :=
  HSyn.EigenformRepExists → PkgI4.EigenformHT →
  ∀ (r : GaloisRep 5 2) (N : ℕ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N 2) (ψ : GaloisChar 5)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5) (S : Finset ℕ),
    0 < N → PkgI4.IsNormalizedEigenform g χ →
    PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := r) 5 {0, -1} → r.AttachedUpToTwist ψ ιC ιL g S →
    ∃ (E : IntermediateField ℚ_[5] (PadicAlgCl 5)) (_ : FiniteDimensional ℚ_[5] E) (ψE : PkgI4.GQp 5 →* Eˣ),
      (∀ σ, (((ψE σ : Eˣ) : E) : PadicAlgCl 5) = ((ψ.toHom (PkgI4.decomp 5 σ) : (PadicAlgCl 5)ˣ) : PadicAlgCl 5)) ∧
      PkgI4.HasHTWeights 5 (charRep ψE) {0}

/-- `TwistCharHTWt0` is weaker than `TwistCharHT0`. -/
theorem twistCharHTWt0_of_twistCharHT0 (h : TwistCharHT0) : TwistCharHTWt0 :=
  fun hR hHT r N χ g ψ ιC ιL S hN hg hr hatt => (h hR hHT r N χ g ψ ιC ιL S hN hg hr hatt).2

/-- **C8 from Conrad's App. B, Tate's theorem over `\hat{K^{ur}}`, the two inertia dictionaries and
`TwistCharHTWt0`** (`c8TwistFinite_of_conrad` with `LocAlgExponentEqWeight` and `FiniteOfLocAlgTrivialQ` proved and the
unramified half dropped). -/
theorem c8TwistFinite_of_leaves (hR : HSyn.EigenformRepExists) (hHT : PkgI4.EigenformHT)
    (hC : ConradAppBQp) (hTT : TateTwistInvariantsInertia) (hT : TwistCharHTWt0)
    (hB : InertiaAtPDecomp) (hM : MinkowskiInertiaQ) : C8TwistFinite := by
  intro r N χ g ψ ιC ιL S hN hg hr hatt
  obtain ⟨E, hE, ψE, hlift, hwt⟩ := hT hR hHT r N χ g ψ ιC ιL S hN hg hr hatt
  have hcont : Continuous (fun σ => (((ψE σ : Eˣ) : E) : PadicAlgCl 5)) := by
    have h1 : Continuous (fun σ : PkgI4.GQp 5 => ((ψ.toHom (PkgI4.decomp 5 σ) : (PadicAlgCl 5)ˣ) : PadicAlgCl 5)) :=
      Units.continuous_val.comp (ψ.continuous_toHom.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[5])).continuous)
    exact (funext hlift : _) ▸ h1
  obtain ⟨n, hn⟩ := hC 5 E ψE hcont ⟨0, hwt⟩
  have hn0 : n = 0 := locAlgExponentEqWeight_of_tateInertia hTT 5 E ψE 0 n hcont hwt hn
  subst hn0
  obtain ⟨k, hk⟩ := hn
  refine finiteOfLocAlgTrivialQNoRam_of_dicts hB hM 5 ψ ⟨k, fun u hu σ hσ => ?_⟩
  have h := hk u hu σ hσ
  rw [zpow_zero] at h
  apply Units.ext
  rw [← hlift σ, h]
  simp

end HDec.G0Galois.C8Conrad
