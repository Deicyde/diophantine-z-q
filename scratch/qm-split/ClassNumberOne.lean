import TailK

/-!
# qm-split, row H-46: `QMClassNumberOne` proved (no leaf)

`HDec.HSyn.G0Split.FibreQM.QMClassNumberOne` (leaf-fold4 chain, `TailC.lean` l.10112, the row's Prop,
imported, not restated) is proved here outright:

* **Class number one, computed** (`principal_of_lattice`): the order
  `𝒪 = ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩ ⊂ B = (2, −3)` is left norm-Euclidean: for every `x ∈ B` there is
  `q ∈ 𝒪` with `|nrd(x − q)| ≤ 7/8 < 1` (`euclid`; in the basis, `nrd = N(α) − 2N(β)` with `N` the
  Eisenstein norm form, and rounding gives `N ≤ 7/16`). Hence every left `𝒪`-stable additive subgroup
  `I ⊆ B` with `dI ⊆ 𝒪` for some `d ≥ 1` is `𝒪α` (an element of minimal `|nrd|`). This replaces the
  citation of Eichler's theorem (Vignéras Cor. III.5.7) by a computation.
* **Lattice glue**: for a full `ι(𝒪)`-stable lattice `Λ ⊂ ℂ²` and `0 ≠ v ∈ Λ`, `I = {x : ι(x)v ∈ Λ}`
  satisfies the hypotheses (rank 4 against rank 4) and `Λ = ι(I)v`; so `Λ = ι(𝒪)w`, `w = ι(α)v`, and `w`
  is not a complex multiple of a real vector because `Λ` spans `ℂ²` over `ℝ`.

Check: `scratch/qm-split/chk.sh scratch/qm-split/ClassNumberOne.lean`.
-/

set_option linter.all false

noncomputable section

namespace HDec.QMSplit.CNO

open HDec HDec.HSyn.G0Split.FibreQM Matrix

abbrev B := LeafQM.B

/-- The reduced norm of `B = (2, −3)`. -/
def nrd (x : B) : ℚ := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2

theorem star_mul_self' (a : B) : star a * a = ((nrd a : ℚ) : B) := by
  rw [QuaternionAlgebra.star_mul_eq_coe]
  congr 1
  simp [nrd]; ring

theorem nrd_mul (x y : B) : nrd (x * y) = nrd x * nrd y := by
  simp [nrd]; ring

theorem nrd_ne_zero {x : B} (hx : x ≠ 0) : nrd x ≠ 0 := by
  have h := HDec.GlueRepo.A1.nrd_ne_zero hx
  rw [HDec.GlueRepo.A1.nrd_eq] at h
  exact h

theorem nrd_ofInt (n : Fin 4 → ℤ) :
    nrd (LeafQM.ofInt n) = ((n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2) : ℤ) : ℚ) := by
  simp [nrd, LeafQM.ofInt]; ring

theorem nrd_O_int {x : B} (hx : x ∈ LeafQM.O) : ∃ z : ℤ, nrd x = z := by
  obtain ⟨n, rfl⟩ := hx
  exact ⟨_, nrd_ofInt n⟩

/-- `x · ((nrd α)⁻¹ • star α) · α = x`-style division: `((nrd α)⁻¹ • (β * star α)) * α = β`. -/
theorem div_mul_cancel' (β α : B) (hα : α ≠ 0) : ((nrd α)⁻¹ • (β * star α)) * α = β := by
  rw [smul_mul_assoc, mul_assoc, star_mul_self', QuaternionAlgebra.mul_coe_eq_smul, smul_smul,
    inv_mul_cancel₀ (nrd_ne_zero hα), one_smul]

/-! ## The Euclidean step -/

theorem sq_le_of_abs_le {e c : ℚ} (h : |e| ≤ c) : e ^ 2 ≤ c ^ 2 := by
  have := abs_nonneg e
  rw [← sq_abs]; exact pow_le_pow_left₀ this h 2

/-- **`𝒪` is left norm-Euclidean**: every `x ∈ B` is within `|nrd| < 1` of `𝒪`. -/
theorem euclid (x : B) : ∃ q ∈ LeafQM.O, |nrd (x - q)| < 1 := by
  set c : ℤ := round (2 * x.imJ)
  set d : ℤ := round (2 * x.imK)
  set a : ℤ := round (x.re - c / 2)
  set b : ℤ := round (x.imI - d / 2)
  refine ⟨LeafQM.ofInt ![a, b, c, d], ⟨![a, b, c, d], rfl⟩, ?_⟩
  have hc := abs_sub_round (2 * x.imJ)
  have hd := abs_sub_round (2 * x.imK)
  have ha := abs_sub_round (x.re - c / 2)
  have hb := abs_sub_round (x.imI - d / 2)

  set e0 := x.re - c / 2 - a
  set e1 := x.imI - d / 2 - b
  set e2 := x.imJ - c / 2
  set e3 := x.imK - d / 2
  have h0 : e0 ^ 2 ≤ (1/2) ^ 2 := sq_le_of_abs_le ha
  have h1 : e1 ^ 2 ≤ (1/2) ^ 2 := sq_le_of_abs_le hb
  have h2' : (2 * e2) ^ 2 ≤ (1/2) ^ 2 := sq_le_of_abs_le (by
    have : 2 * e2 = 2 * x.imJ - c := by simp only [e2]; ring
    rw [this]; exact hc)
  have h3' : (2 * e3) ^ 2 ≤ (1/2) ^ 2 := sq_le_of_abs_le (by
    have : 2 * e3 = 2 * x.imK - d := by simp only [e3]; ring
    rw [this]; exact hd)
  have hn : nrd (x - LeafQM.ofInt ![a, b, c, d]) = e0 ^ 2 - 2 * e1 ^ 2 + 3 * e2 ^ 2 - 6 * e3 ^ 2 := by
    simp only [nrd, LeafQM.ofInt, e0, e1, e2, e3]
    simp; ring
  rw [hn, abs_lt]
  constructor <;> nlinarith [sq_nonneg e0, sq_nonneg e1, sq_nonneg e2, sq_nonneg e3]

/-! ## Principal ideals -/

/-- **Class number one of `𝒪` (computed, no leaf).** A left `𝒪`-stable additive subgroup `I ⊆ B` with
`d I ⊆ 𝒪` for some `d ≥ 1` is `𝒪 α` for some `α ∈ I`. (Every left `𝒪`-ideal of `B` has this form.) -/
theorem principal_of_lattice (I : AddSubgroup B) (hI : ∀ q ∈ LeafQM.O, ∀ x ∈ I, q * x ∈ I)
    (d : ℕ) (hd : 0 < d) (hdI : ∀ x ∈ I, (d : ℚ) • x ∈ LeafQM.O) :
    ∃ α ∈ I, ∀ β ∈ I, ∃ q ∈ LeafQM.O, β = q * α := by
  by_cases hI0 : ∀ x ∈ I, x = 0
  · exact ⟨0, I.zero_mem, fun β hβ => ⟨0, LeafQM.O.zero_mem, by simp [hI0 β hβ]⟩⟩
  push Not at hI0
  -- the integer `d² |nrd x|` for `x ∈ I`
  have hint : ∀ x ∈ I, ∃ n : ℕ, ((d : ℚ) ^ 2) * |nrd x| = n := by
    intro x hx
    obtain ⟨z, hz⟩ := nrd_O_int (hdI x hx)
    refine ⟨z.natAbs, ?_⟩
    have e : nrd ((d : ℚ) • x) = (d : ℚ) ^ 2 * nrd x := by simp [nrd]; ring
    rw [e] at hz
    have hd2 : (0 : ℚ) ≤ (d : ℚ) ^ 2 := by positivity
    rw [← abs_of_nonneg hd2, ← abs_mul, hz]
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hex : ∃ n : ℕ, ∃ x ∈ I, x ≠ 0 ∧ ((d : ℚ) ^ 2) * |nrd x| = n := by
    obtain ⟨x, hx, hx0⟩ := hI0
    obtain ⟨n, hn⟩ := hint x hx
    exact ⟨n, x, hx, hx0, hn⟩
  classical
  obtain ⟨α, hαI, hα0, hαn⟩ := Nat.find_spec hex
  refine ⟨α, hαI, fun β hβ => ?_⟩
  set x : B := (nrd α)⁻¹ • (β * star α)
  obtain ⟨q, hq, hlt⟩ := euclid x
  refine ⟨q, hq, ?_⟩
  by_contra hne
  have hmem : β - q * α ∈ I := I.sub_mem hβ (hI q hq α hαI)
  have hne' : β - q * α ≠ 0 := sub_ne_zero.mpr hne
  have hfac : β - q * α = (x - q) * α := by
    rw [sub_mul, div_mul_cancel' β α hα0]
  obtain ⟨m, hm⟩ := hint _ hmem
  have hmin := Nat.find_min' hex ⟨β - q * α, hmem, hne', hm⟩
  have hpos : 0 < |nrd α| := abs_pos.mpr (nrd_ne_zero hα0)
  have hd2 : (0 : ℚ) < (d : ℚ) ^ 2 := by positivity
  have hlt' : ((d : ℚ) ^ 2) * |nrd (β - q * α)| < ((d : ℚ) ^ 2) * |nrd α| := by
    rw [hfac, nrd_mul, abs_mul]
    have := mul_lt_mul_of_pos_right hlt hpos
    rw [one_mul] at this
    exact mul_lt_mul_of_pos_left this hd2
  rw [hm, hαn] at hlt'
  have : m < Nat.find hex := by exact_mod_cast hlt'
  omega


/-! ## The lattice glue -/

open HDec.FibreQMNorm in
/-- `ι(x) v`. -/
abbrev act (x : B) (v : Fin 2 → ℂ) : Fin 2 → ℂ := qmMatB x *ᵥ v

theorem qmMatB_mul (x y : B) : FibreQMNorm.qmMatB (x * y) = FibreQMNorm.qmMatB x * FibreQMNorm.qmMatB y :=
  HDec.HSyn.G0Split.FibreQM.PeriodGlue.cM_mul x y

theorem qmMatB_one : FibreQMNorm.qmMatB 1 = 1 := HDec.HSyn.G0Split.FibreQM.PeriodGlue.cM_one

theorem qmMatB_add (x y : B) : FibreQMNorm.qmMatB (x + y) = FibreQMNorm.qmMatB x + FibreQMNorm.qmMatB y := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [FibreQMNorm.qmMatB, BPAnalytic.QM.iota, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

theorem qmMatB_smul (r : ℚ) (x : B) : FibreQMNorm.qmMatB (r • x) = (r : ℂ) • FibreQMNorm.qmMatB x := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [FibreQMNorm.qmMatB, BPAnalytic.QM.iota, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

theorem qmMatB_zero : FibreQMNorm.qmMatB 0 = 0 := by
  have h := qmMatB_add 0 0
  simpa using h

theorem act_add (x y : B) (v) : act (x + y) v = act x v + act y v := by
  simp [act, qmMatB_add, Matrix.add_mulVec]

theorem act_zero (v) : act 0 v = 0 := by simp [act, qmMatB_zero]

theorem act_neg (x : B) (v) : act (-x) v = -act x v := by
  have h := act_add x (-x) v
  rw [add_neg_cancel, act_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem act_sub (x y : B) (v) : act (x - y) v = act x v - act y v := by
  rw [sub_eq_add_neg, act_add, act_neg, ← sub_eq_add_neg]

theorem act_mul (x y : B) (v) : act (x * y) v = act x (act y v) := by
  show FibreQMNorm.qmMatB (x * y) *ᵥ v = FibreQMNorm.qmMatB x *ᵥ (FibreQMNorm.qmMatB y *ᵥ v)
  rw [qmMatB_mul, Matrix.mulVec_mulVec]

theorem act_one (v) : act 1 v = v := by simp [act, qmMatB_one]

theorem act_smul (r : ℚ) (x : B) (v) : act (r • x) v = (r : ℂ) • act x v := by
  simp [act, qmMatB_smul, Matrix.smul_mulVec]

/-- `ι(x)` is injective on `ℂ²` for `x ≠ 0` (`B` is a division algebra). -/
theorem act_eq_zero {x : B} {v : Fin 2 → ℂ} (hv : v ≠ 0) (h : act x v = 0) : x = 0 := by
  by_contra hx
  apply hv
  have e : ((nrd x)⁻¹ • star x) * x = 1 := by
    have := div_mul_cancel' 1 x hx
    simpa using this
  rw [← act_one v, ← e, act_mul, h]
  simp [act]

theorem oBasis_mem (k : Fin 4) : BPAnalytic.QM.oBasis k ∈ LeafQM.O := by
  fin_cases k
  · exact ⟨![1, 0, 0, 0], by ext <;> simp [BPAnalytic.QM.oBasis, LeafQM.ofInt]⟩
  · exact ⟨![0, 1, 0, 0], by ext <;> simp [BPAnalytic.QM.oBasis, LeafQM.ofInt]⟩
  · exact ⟨![0, 0, 1, 0], by ext <;> simp [BPAnalytic.QM.oBasis, LeafQM.ofInt]⟩
  · exact ⟨![0, 0, 0, 1], by ext <;> simp [BPAnalytic.QM.oBasis, LeafQM.ofInt]⟩

theorem ofInt_eq_sum (n : Fin 4 → ℤ) :
    LeafQM.ofInt n = ∑ k, ((n k : ℚ)) • BPAnalytic.QM.oBasis k := by
  ext <;> simp [LeafQM.ofInt, BPAnalytic.QM.oBasis, Fin.sum_univ_four] <;> ring

theorem act_ofInt (n : Fin 4 → ℤ) (v) :
    act (LeafQM.ofInt n) v = ∑ k, n k • act (BPAnalytic.QM.oBasis k) v := by
  rw [ofInt_eq_sum, Fin.sum_univ_four, Fin.sum_univ_four, act_add, act_add, act_add,
    act_smul, act_smul, act_smul, act_smul]
  simp only [← Int.cast_smul_eq_zsmul ℂ]
  push_cast; rfl

theorem mem_qmOrbit_iff (w z : Fin 2 → ℂ) :
    z ∈ FibreQMNorm.qmOrbit w ↔ ∃ q ∈ LeafQM.O, z = act q w := by
  unfold FibreQMNorm.qmOrbit
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨LeafQM.ofInt c, ⟨c, rfl⟩, by rw [act_ofInt]; exact hc.symm⟩
  · rintro ⟨q, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, by rw [act_ofInt]⟩

theorem ofInt_eq_zero {n : Fin 4 → ℤ} (h : LeafQM.ofInt n = 0) : n = 0 := by
  have h2 := congrArg QuaternionAlgebra.imJ h
  have h3 := congrArg QuaternionAlgebra.imK h
  have h0 := congrArg QuaternionAlgebra.re h
  have h1 := congrArg QuaternionAlgebra.imI h
  simp [LeafQM.ofInt] at h0 h1 h2 h3
  funext k; fin_cases k <;> simp <;> [skip; skip; exact h2; exact h3]
  · rw [h2] at h0; simpa using h0
  · rw [h3] at h1; simpa using h1

theorem finrank_C2 : Module.finrank ℝ (Fin 2 → ℂ) = 4 := by
  rw [Module.finrank_pi_fintype, Complex.finrank_real_complex]; simp

/-- **Row H-46 proved.** `QMClassNumberOne` holds, with no hypothesis. -/
theorem qmClassNumberOne_proof : HDec.HSyn.G0Split.FibreQM.QMClassNumberOne := by
  intro Λ _ hlat hstab
  haveI := hlat
  have hstab' : ∀ q ∈ LeafQM.O, ∀ z ∈ Λ, act q z ∈ Λ := fun q hq z hz => hstab ⟨q, hq⟩ z hz
  -- a nonzero vector of `Λ`
  obtain ⟨v, hvΛ, hv0⟩ : ∃ v ∈ Λ, v ≠ 0 := by
    by_contra h
    push Not at h
    have hb : Λ = ⊥ := (Submodule.eq_bot_iff _).2 h
    have hs := hlat.span_top
    rw [hb] at hs
    have : (⊥ : Submodule ℝ (Fin 2 → ℂ)) = ⊤ := by simpa using hs
    exact bot_ne_top this
  haveI : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  haveI : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ
  have hrank : Module.finrank ℤ Λ = 4 := by rw [ZLattice.rank ℝ Λ, finrank_C2]
  -- the four vectors `ι(b_k) v`
  let g : Fin 4 → Λ := fun k => ⟨act (BPAnalytic.QM.oBasis k) v, hstab' _ (oBasis_mem k) v hvΛ⟩
  have hsum : ∀ c : Fin 4 → ℤ, ((∑ k, c k • g k : Λ) : Fin 2 → ℂ) = act (LeafQM.ofInt c) v := by
    intro c; rw [act_ofInt]; simp [g]
  have hg : LinearIndependent ℤ g := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h1 : act (LeafQM.ofInt c) v = 0 := by rw [← hsum, hc]; rfl
    have := ofInt_eq_zero (act_eq_zero hv0 h1)
    intro k; exact congrFun this k
  -- torsion: every `λ ∈ Λ` has a nonzero multiple in `ι(𝒪) v`
  have htors : ∀ l : Λ, ∃ c : ℤ, c ≠ 0 ∧ ∃ n : Fin 4 → ℤ, ((c • l : Λ) : Fin 2 → ℂ) = act (LeafQM.ofInt n) v := by
    intro l
    have hni : ¬ LinearIndependent ℤ (Fin.cons l g : Fin 5 → Λ) := by
      intro hli
      have := hli.fintype_card_le_finrank
      rw [hrank] at this; simp at this
    rw [Fintype.not_linearIndependent_iff] at hni
    obtain ⟨c, hc, i, hi⟩ := hni
    rw [Fin.sum_univ_succ] at hc
    simp only [Fin.cons_zero, Fin.cons_succ] at hc
    have hc0 : c 0 ≠ 0 := by
      intro h0
      rw [h0, zero_smul, zero_add] at hc
      have := (Fintype.linearIndependent_iff.mp hg) (fun k => c k.succ) hc
      refine hi ?_
      refine Fin.cases h0 (fun k => this k) i
    refine ⟨c 0, hc0, fun k => -c k.succ, ?_⟩
    have e : c 0 • l = -∑ k : Fin 4, c k.succ • g k := eq_neg_of_add_eq_zero_left hc
    rw [e, Submodule.coe_neg, ← hsum]
    simp [Finset.sum_neg_distrib, neg_smul]
  -- the uniform denominator
  let N' : Submodule ℤ Λ := Submodule.span ℤ (Set.range g)
  have hN'mem : ∀ l : Λ, l ∈ N' ↔ ∃ n : Fin 4 → ℤ, (l : Fin 2 → ℂ) = act (LeafQM.ofInt n) v := by
    intro l
    rw [Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, hc⟩; exact ⟨c, by rw [← hc, hsum]⟩
    · rintro ⟨n, hn⟩; exact ⟨n, Subtype.ext (by rw [hsum, hn])⟩
  have htorsQ : Module.IsTorsion ℤ (Λ ⧸ N') := by
    intro m
    induction m using Submodule.Quotient.induction_on with
    | H l =>
      obtain ⟨c, hc0, n, hn⟩ := htors l
      refine ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc0⟩, ?_⟩
      change c • (Submodule.Quotient.mk l : Λ ⧸ N') = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hN'mem]
      exact ⟨n, hn⟩
  obtain ⟨d0, hd0ann, hd0nz⟩ := Submodule.annihilator_top_inter_nonZeroDivisors htorsQ
  have hd0 : d0 ≠ 0 := nonZeroDivisors.ne_zero hd0nz
  have hd0l : ∀ l : Λ, d0 • l ∈ N' := by
    intro l
    have := (Submodule.mem_annihilator.mp hd0ann) (Submodule.Quotient.mk l) Submodule.mem_top
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    exact this
  -- the ideal `I = {x : ι(x) v ∈ Λ}`
  let I : AddSubgroup B :=
    { carrier := {x | act x v ∈ Λ}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at *; rw [act_add]; exact Λ.add_mem hx hy
      zero_mem' := by simp only [Set.mem_setOf_eq]; rw [act_zero]; exact Λ.zero_mem
      neg_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *; rw [act_neg]; exact Λ.neg_mem hx }
  have hI : ∀ q ∈ LeafQM.O, ∀ x ∈ I, q * x ∈ I := by
    intro q hq x hx
    change act (q * x) v ∈ Λ
    rw [act_mul]; exact hstab' q hq _ hx
  have hdI : ∀ x ∈ I, ((d0.natAbs : ℕ) : ℚ) • x ∈ LeafQM.O := by
    intro x hx
    obtain ⟨n, hn⟩ := (hN'mem _).1 (hd0l ⟨act x v, hx⟩)
    have e1 : act ((d0 : ℚ) • x) v = act (LeafQM.ofInt n) v := by
      rw [act_smul, ← hn]; simp [← Int.cast_smul_eq_zsmul ℂ]
    have e2 : (d0 : ℚ) • x = LeafQM.ofInt n := by
      have := act_eq_zero hv0 (show act ((d0 : ℚ) • x - LeafQM.ofInt n) v = 0 by rw [act_sub, e1, sub_self])
      exact sub_eq_zero.mp this
    have hmem : (d0 : ℚ) • x ∈ LeafQM.O := e2 ▸ ⟨n, rfl⟩
    rcases Int.natAbs_eq d0 with h | h
    · rw [h] at hmem; simpa using hmem
    · rw [h] at hmem
      have := LeafQM.O.neg_mem hmem
      simp only [Int.cast_neg, Int.cast_natCast, neg_smul, neg_neg] at this
      exact this
  -- every vector of `Λ` is `ι(x) v`
  have hrep : ∀ z ∈ Λ, ∃ x ∈ I, z = act x v := by
    intro z hz
    obtain ⟨c, hc0, n, hn⟩ := htors ⟨z, hz⟩
    refine ⟨(c : ℚ)⁻¹ • LeafQM.ofInt n, ?_, ?_⟩
    · change act _ v ∈ Λ
      rw [act_smul, ← hn]
      have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
      simp [← Int.cast_smul_eq_zsmul ℂ, smul_smul, inv_mul_cancel₀ hcC, hz]
    · rw [act_smul, ← hn]
      have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
      simp [← Int.cast_smul_eq_zsmul ℂ, smul_smul, inv_mul_cancel₀ hcC]
  obtain ⟨α, hαI, hαgen⟩ := principal_of_lattice I hI d0.natAbs (Int.natAbs_pos.mpr hd0) hdI
  refine ⟨act α v, ?_, ?_⟩
  · -- `w` is not a complex multiple of a real vector
    rintro ⟨c, r, hw⟩
    let L : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℂ) :=
      { toFun := fun u => c • (fun i => (u i : ℂ))
        map_add' := fun u u' => by ext i; simp [mul_add]
        map_smul' := fun t u => by ext i; simp [Complex.real_smul]; ring }
    have hsub : (Λ : Set (Fin 2 → ℂ)) ⊆ LinearMap.range L := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hrep z hz
      obtain ⟨q, hq, hxq⟩ := hαgen x hx
      rw [hxq, act_mul, hw]
      refine ⟨BPAnalytic.QM.iota q *ᵥ r, ?_⟩
      ext i; fin_cases i <;>
        simp [L, act, FibreQMNorm.qmMatB, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    have htop : LinearMap.range L = ⊤ := by
      rw [eq_top_iff, ← hlat.span_top]
      exact Submodule.span_le.mpr hsub
    have h1 := LinearMap.finrank_range_le L
    rw [htop, finrank_top ℝ (Fin 2 → ℂ), finrank_C2] at h1
    simp at h1
  · ext z
    rw [mem_qmOrbit_iff]
    constructor
    · intro hz
      obtain ⟨x, hx, rfl⟩ := hrep z hz
      obtain ⟨q, hq, rfl⟩ := hαgen x hx
      exact ⟨q, hq, act_mul q α v⟩
    · rintro ⟨q, hq, rfl⟩
      rw [← act_mul]
      exact hI q hq α hαI

end HDec.QMSplit.CNO

#print axioms HDec.QMSplit.CNO.qmClassNumberOne_proof
#print axioms HDec.QMSplit.CNO.principal_of_lattice
