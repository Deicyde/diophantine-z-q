import ZInQKernel.OneProof.H.TailO

/-! # OneProof H, leaf-fold7 part U: qm-split over the chain (`scratch/qm-split/ClassNumberOne.lean`, `YuLeaf.lean`,
`QMAut.lean`, `STQM.lean`, `ThetaSplit.lean`, `ModuliSplit.lean`, verbatim apart from this banner, `import TailK`
replaced by the chain module `TailO`, the dropped `#print axioms` lines and closing `example`s, and a
`section`/`end` wrapper around each file).

qm-split compiled these files over leaf-fold4's olean chain; here they are over the OneProof chain, where
op-dedupe replaced many `HDec` copies by the kernel's constants (aliases). Main theorems
(docs/research/qm-split.md): `HDec.QMSplit.CNO.qmClassNumberOne_proof` (H-46, no hypothesis),
`HDec.QMSplit.Yu.qmDichotomyYu_of_yu` (H-35), `HDec.QMSplit.Aut.rows_of_C` (H-61, H-63, H-42),
`HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.stqm_of` (H-86), `HDec.QMSplit.Theta.thetaModularity_of`
(H-2), `HDec.QMSplit.Moduli.r1b_of'` (H-20). -/

section QMSplit_ClassNumberOne


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

end -- noncomputable section

end QMSplit_ClassNumberOne

section QMSplit_YuLeaf


/-!
# qm-split, row H-35: `PkgI3.QMDichotomyYu` from Yu's Theorem 1.1 in published form

The row (`HDec.PkgI3.QMDichotomyYu`, leaf-fold4 chain `LPrefix.lean` l.2892, imported) is Yu's theorem
with the splitting clause dropped. The leaf below keeps the clause: in the second case the imaginary
quadratic field `k = ℚ(√d)` splits `B`, `k ⊗_ℚ B ≅ M₂(k)`. The proof of the row drops it.

Check: `scratch/qm-split/chk.sh scratch/qm-split/YuLeaf.lean`.
-/

set_option linter.all false

noncomputable section

namespace HDec.QMSplit.Yu

open HDec HDec.PkgI3 PkgI3.AbVar Polynomial
open scoped Quaternion TensorProduct

/-- **LEAF (Chia-Fu Yu, *Endomorphism algebras of QM abelian surfaces*, J. Pure Appl. Algebra 217 (2013),
Thm 1.1, journal p. 907; arXiv:1210.1125 Thm 1.1; the journal first page was read by the locator audit,
`docs/research/locators.md` row T27; volume number UNVERIFIED).** Let `A` be an abelian surface over an
algebraically closed field `k` of characteristic `0`, and `B = (a, b)_ℚ` an indefinite quaternion division
algebra with a `ℚ`-algebra embedding `B → End⁰(A)`. Then `End⁰(A) ≅ B`, or `End⁰(A) ≅ M₂(K)` for an
imaginary quadratic field `K = ℚ(√d)`, `d < 0`, that splits `B` (`K ⊗_ℚ B ≅ M₂(K)` as `K`-algebras).

Form: the printed statement in characteristic `0`, except that the attribution of the two cases (simple
`A` in the first, non-simple `A` in the second, as the audit reads the theorem) is dropped (a weaker
conclusion). `End⁰(A) = ℚ ⊗_ℤ End(A)` (`PkgI3.AbVar.End0`) over the kernel's abelian varieties
`PkgI3.AbVar`; the division hypothesis is "every nonzero element is a unit"; indefinite is
`QuatIndefinite a b` (`0 < a ∨ 0 < b`), the same hypotheses as the row. -/
def YuThm11 : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : AbVar k), A.dim = 2 →
    ∀ a b : ℚ, QuatIndefinite a b → (∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x) →
      Nonempty (ℍ[ℚ, a, b] →ₐ[ℚ] End0 A) →
        Nonempty (End0 A ≃ₐ[ℚ] ℍ[ℚ, a, b]) ∨
          ∃ d : ℚ, d < 0 ∧
            Nonempty (End0 A ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) ∧
            Nonempty ((AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)) ⊗[ℚ] ℍ[ℚ, a, b] ≃ₐ[AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)]
              Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)))

/-- **Row H-35 from the published form**: drop the splitting clause. -/
theorem qmDichotomyYu_of_yu (h : YuThm11) : PkgI3.QMDichotomyYu := by
  intro k _ _ _ A hA a b hind hdiv hemb
  rcases h k A hA a b hind hdiv hemb with h1 | ⟨d, hd, h2, -⟩
  · exact Or.inl h1
  · exact Or.inr ⟨d, hd, h2⟩

end HDec.QMSplit.Yu

end -- noncomputable section

end QMSplit_YuLeaf

section QMSplit_QMAut


/-!
# qm-split, rows H-61 `QMAutCard` and H-63 `ALFixedPoints`

Both rows (`HDec.HeckeRest.QMAutCard`, `HDec.HeckeRest.ALFixedPoints`, leaf-fold4 chain `TailG.lean`
l.9932, l.9958; imported) are proved from one published-form leaf `QMCentralizerCM` (the description of
`End_𝒪(A)` at points of `X₆`: `ℤ`, or an order `Φ⁻¹(𝒪)` optimally embedded by some `Φ : k → B`, `k`
imaginary quadratic) by computation:

* §1 imaginary quadratic fields: a non-rational element has negative discriminant (`disc_neg`), from
  `IsTotallyComplex` (a nonnegative discriminant makes every complex embedding real);
* §2 elements of `B`: `x² − trd(x) x + nrd(x) = 0`; for `R = Φ⁻¹(𝒪)` every unit is `±1` or a root of
  `u² + 1`, `u² ∓ u + 1` (`unit_cases`: `nrd = 1` on units, `trd ∈ ℤ`, `trd² < 4`);
* §3 counting `Rˣ` (`4`, `6`, `2`) and the exclusivity of the three CM types;
* §4 `QMIso q q ≃ (com q)ˣ`, transport along `com q ≃+* R`, and the two rows.

Check: `scratch/qm-split/chk.sh scratch/qm-split/QMAut.lean`.
-/

set_option linter.all false

noncomputable section

namespace HDec.QMSplit.Aut

open NumberField

/-! ## §1 Imaginary quadratic fields -/

section Imag

variable {k : Type} [Field k] [NumberField k] [IsTotallyComplex k] (hk : Module.finrank ℚ k = 2)
include hk

/-- In a quadratic field, a non-rational `y` spans with `1`. -/
theorem span_two {y : k} (hy : ∀ c : ℚ, y ≠ algebraMap ℚ k c) (x : k) :
    ∃ a b : ℚ, x = algebraMap ℚ k a + algebraMap ℚ k b * y := by
  have hni : ¬ LinearIndependent ℚ ![(1 : k), y, x] := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [hk] at this; simp at this
  rw [Fintype.not_linearIndependent_iff] at hni
  obtain ⟨g, hg, i, hi⟩ := hni
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hg
  by_cases h2 : g 2 = 0
  · exfalso
    rw [h2, zero_smul, add_zero] at hg
    by_cases h1 : g 1 = 0
    · rw [h1, zero_smul, add_zero, smul_eq_zero] at hg
      rcases hg with hg | hg
      · fin_cases i <;> simp_all
      · exact one_ne_zero hg
    · apply hy (-(g 0) / g 1)
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hg
      have hg1 : algebraMap ℚ k (g 1) ≠ 0 := by simpa using h1
      field_simp
      simp only [map_neg, map_div₀]
      field_simp
      linear_combination hg
  · refine ⟨-(g 0) / g 2, -(g 1) / g 2, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, mul_one] at hg
    have hg2 : algebraMap ℚ k (g 2) ≠ 0 := by simpa using h2
    simp only [map_neg, map_div₀]
    field_simp
    linear_combination hg

/-- **A non-rational element of an imaginary quadratic field has negative discriminant.** -/
theorem disc_neg {y : k} (hy : ∀ c : ℚ, y ≠ algebraMap ℚ k c) {t n : ℚ}
    (h : y * y - algebraMap ℚ k t * y + algebraMap ℚ k n = 0) : t ^ 2 < 4 * n := by
  by_contra hle
  push Not at hle
  obtain ⟨φ⟩ : Nonempty (k →+* ℂ) := inferInstance
  apply IsTotallyComplex.complexEmbedding_not_isReal φ
  rw [ComplexEmbedding.isReal_iff]
  -- `φ y` is real
  have hφy : (starRingEnd ℂ) (φ y) = φ y := by
    have hq := congrArg φ h
    simp only [map_sub, map_add, map_mul, map_zero, eq_ratCast, map_ratCast] at hq
    set z := φ y
    set D : ℝ := t ^ 2 - 4 * n
    have hle' : ((4 * n : ℚ) : ℝ) ≤ ((t ^ 2 : ℚ) : ℝ) := by exact_mod_cast hle
    have hD : 0 ≤ D := by simp only [D]; push_cast at hle' ⊢; linarith
    have hsq : (2 * z - t) ^ 2 = ((Real.sqrt D : ℝ) : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hD]
      simp only [D]; push_cast
      linear_combination 4 * hq
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
    · have : z = ((t + Real.sqrt D) / 2 : ℝ) := by
        push_cast; linear_combination h1 / 2
      rw [this, Complex.conj_ofReal]
    · have : z = ((t - Real.sqrt D) / 2 : ℝ) := by
        push_cast; linear_combination h1 / 2
      rw [this, Complex.conj_ofReal]
  ext x
  obtain ⟨a, b, rfl⟩ := span_two hk hy x
  rw [ComplexEmbedding.conjugate_coe_eq]
  simp only [map_add, map_mul, eq_ratCast, map_ratCast, hφy]

/-- No element of an imaginary quadratic field squares to a nonnegative non-square rational. -/
theorem no_real_sqrt {y : k} {c : ℚ} (hc : 0 ≤ c) (hns : ∀ a : ℚ, a * a ≠ c)
    (h : y * y = algebraMap ℚ k c) : False := by
  have hy : ∀ a : ℚ, y ≠ algebraMap ℚ k a := by
    rintro a rfl
    apply hns a
    exact (algebraMap ℚ k).injective (by rw [map_mul, h])
  have := disc_neg hk hy (t := 0) (n := -c) (by rw [h]; simp)
  linarith

end Imag


/-! ## §2 Elements of `B` and units of `Φ⁻¹(𝒪)` -/

abbrev B := LeafQM.B

/-- The reduced norm of `B = (2, −3)`. -/
def nrd (x : B) : ℚ := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2

theorem nrd_mul (x y : B) : nrd (x * y) = nrd x * nrd y := by
  simp [nrd]; ring

theorem quat_sq (x : B) : x * x - (2 * x.re) • x + (nrd x) • (1 : B) = 0 := by
  ext <;> simp [nrd] <;> ring

theorem nrd_algebraMap (c : ℚ) : nrd (algebraMap ℚ B c) = c ^ 2 := by
  simp [nrd]

theorem O_int {x : B} (hx : x ∈ LeafQM.O) : (∃ z : ℤ, nrd x = z) ∧ (∃ z : ℤ, 2 * x.re = z) := by
  obtain ⟨n, rfl⟩ := hx
  refine ⟨⟨n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2), ?_⟩,
    ⟨2 * n 0 + n 2, ?_⟩⟩ <;> simp [nrd, LeafQM.ofInt] <;> ring

section Order

variable {k : Type} [Field k] [NumberField k] [IsTotallyComplex k] (hk : Module.finrank ℚ k = 2)
  (Φ : k →ₐ[ℚ] B)
include hk

theorem Φ_rel (y : k) :
    y * y - algebraMap ℚ k (2 * (Φ y).re) * y + algebraMap ℚ k (nrd (Φ y)) = 0 := by
  apply Φ.toRingHom.injective
  have := quat_sq (Φ y)
  rw [← Algebra.smul_def, Algebra.algebraMap_eq_smul_one]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, map_add, map_mul, map_smul, map_one,
    map_zero]
  exact this

theorem nrd_pos {y : k} (hy : y ≠ 0) : 0 < nrd (Φ y) := by
  by_cases hr : ∃ c : ℚ, y = algebraMap ℚ k c
  · obtain ⟨c, rfl⟩ := hr
    rw [AlgHom.commutes, nrd_algebraMap]
    have : c ≠ 0 := by rintro rfl; simp at hy
    positivity
  · push Not at hr
    have := disc_neg hk hr (Φ_rel hk Φ y)
    nlinarith [sq_nonneg (2 * (Φ y).re)]

/-- **Units of `Φ⁻¹(𝒪)`.** Every unit is `±1` or a root of `u² + 1`, `u² − u + 1` or `u² + u + 1`. -/
theorem unit_cases (u : (LeafQM.O.comap Φ.toRingHom)ˣ) :
    ((u : LeafQM.O.comap Φ.toRingHom) : k) = 1 ∨ ((u : LeafQM.O.comap Φ.toRingHom) : k) = -1 ∨
    ((u : LeafQM.O.comap Φ.toRingHom) : k) * u + 1 = 0 ∨
    ((u : LeafQM.O.comap Φ.toRingHom) : k) * u - u + 1 = 0 ∨
    ((u : LeafQM.O.comap Φ.toRingHom) : k) * u + u + 1 = 0 := by
  set y : k := ((u : LeafQM.O.comap Φ.toRingHom) : k)
  set y' : k := (((u⁻¹ : (LeafQM.O.comap Φ.toRingHom)ˣ) : LeafQM.O.comap Φ.toRingHom) : k)
  have hyy' : y * y' = 1 := congrArg Subtype.val u.mul_inv
  have hy0 : y ≠ 0 := by rintro h; rw [h, zero_mul] at hyy'; exact zero_ne_one hyy'
  have hy'0 : y' ≠ 0 := by rintro h; rw [h, mul_zero] at hyy'; exact zero_ne_one hyy'
  have hyO : Φ y ∈ LeafQM.O := (u : LeafQM.O.comap Φ.toRingHom).2
  have hy'O : Φ y' ∈ LeafQM.O := ((u⁻¹ : (LeafQM.O.comap Φ.toRingHom)ˣ) : LeafQM.O.comap Φ.toRingHom).2
  obtain ⟨⟨z, hz⟩, ⟨m, hm⟩⟩ := O_int hyO
  obtain ⟨⟨z', hz'⟩, -⟩ := O_int hy'O
  have hzz : (z : ℚ) * z' = 1 := by
    rw [← hz, ← hz', ← nrd_mul, ← map_mul, hyy', map_one]
    simp [nrd]
  have hzpos : (0 : ℚ) < z := hz ▸ nrd_pos hk Φ hy0
  have hz1 : z = 1 := by
    have h1 : z * z' = 1 := by exact_mod_cast hzz
    have h2 : 0 < z := by exact_mod_cast hzpos
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with h | h <;> [exact h; omega]
  have hrel := Φ_rel hk Φ y
  rw [hm, hz, hz1] at hrel
  by_cases hr : ∃ c : ℚ, y = algebraMap ℚ k c
  · obtain ⟨c, hc⟩ := hr
    have hc2 : c ^ 2 = 1 := by
      rw [← nrd_algebraMap, ← AlgHom.commutes Φ, ← hc, hz, hz1]; simp
    have hcc : (c - 1) * (c + 1) = 0 := by linear_combination hc2
    rcases mul_eq_zero.1 hcc with h | h
    · left; rw [hc, show c = 1 by linear_combination h, map_one]
    · right; left; rw [hc, show c = -1 by linear_combination h, map_neg, map_one]
  · push Not at hr
    have hd := disc_neg hk hr hrel
    have hm2 : m ^ 2 < 4 := by
      have : ((m : ℚ)) ^ 2 < 4 := by simpa using hd
      exact_mod_cast this
    have : m = -1 ∨ m = 0 ∨ m = 1 := by
      have h1 : m < 2 := by nlinarith
      have h2 : -2 < m := by nlinarith
      omega
    rcases this with rfl | rfl | rfl
    · right; right; right; right
      have := hrel; simp at this; linear_combination this
    · right; right; left
      have := hrel; simp at this; linear_combination this
    · right; right; right; left
      have := hrel; simp at this; linear_combination this

end Order


/-! ## §3 Counting units; exclusivity of the CM types -/

theorem not_sq (s : ℚ) (c : ℤ) (hc : ¬ IsSquare c) (h : s * s = c) : False := by
  have h1 : IsSquare (c : ℚ) := ⟨s, by rw [← h]⟩
  rw [Rat.isSquare_iff] at h1
  simp at h1
  exact hc h1

theorem card_units_of_list {k : Type} [Field k] (R : Subring k) (L : List k) (hL : L.Nodup)
    (hinv : ∀ x ∈ L, ∃ x' ∈ L, x * x' = 1) (hmem : ∀ x ∈ L, x ∈ R)
    (hall : ∀ u : Rˣ, ((u : R) : k) ∈ L) : Nat.card Rˣ = L.length := by
  classical
  let f : Rˣ → k := fun u => ((u : R) : k)
  have hf : Function.Injective f := by
    intro u v h; apply Units.ext; apply Subtype.ext; exact h
  rw [← Nat.card_range_of_injective hf]
  have hrange : Set.range f = (L.toFinset : Set k) := by
    ext x
    simp only [Set.mem_range, Finset.mem_coe, List.mem_toFinset]
    constructor
    · rintro ⟨u, rfl⟩; exact hall u
    · intro hx
      obtain ⟨x', hx', hxx'⟩ := hinv x hx
      exact ⟨⟨⟨x, hmem x hx⟩, ⟨x', hmem x' hx'⟩, Subtype.ext hxx',
        Subtype.ext (by rw [mul_comm]; exact hxx')⟩, rfl⟩
  rw [hrange, Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hL]

/-- `a + b r`. -/
def ev {k : Type} [Field k] [Algebra ℚ k] (r : k) (p : ℚ × ℚ) : k :=
  algebraMap ℚ k p.1 + algebraMap ℚ k p.2 * r

theorem ev_inj {k : Type} [Field k] [Algebra ℚ k] {r : k} (hr : ∀ c : ℚ, r ≠ algebraMap ℚ k c) :
    Function.Injective (ev r) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [ev] at h
  by_cases hb : b = b'
  · subst hb
    have : algebraMap ℚ k a = algebraMap ℚ k a' := by linear_combination h
    rw [(algebraMap ℚ k).injective this]
  · exfalso
    apply hr ((a' - a) / (b - b'))
    have hb' : algebraMap ℚ k (b - b') ≠ 0 := by
      rw [ne_eq, map_eq_zero]; exact sub_ne_zero.mpr hb
    rw [map_div₀]
    field_simp
    simp only [map_sub]
    linear_combination h

section CountK

variable {k : Type} [Field k] [NumberField k] [IsTotallyComplex k] (hk : Module.finrank ℚ k = 2)
include hk

theorem excl_4_3 {r s : k} (hr : r * r = -1) (hs : s * s - s + 1 = 0) : False :=
  no_real_sqrt hk (y := r * (2 * s - 1)) (c := 3) (by norm_num)
    (fun a h => not_sq a 3 (by decide +kernel) (by exact_mod_cast h))
    (by simp; linear_combination (4 * s * s - 4 * s + 1) * hr - 4 * hs)


theorem excl_4_24 {r s : k} (hr : r * r = -1) (hs : s * s = -6) : False :=
  no_real_sqrt hk (y := r * s) (c := 6) (by norm_num)
    (fun a h => not_sq a 6 (by decide +kernel) (by exact_mod_cast h))
    (by simp; linear_combination s * s * hr - hs)

theorem excl_3_24 {r s : k} (hr : r * r - r + 1 = 0) (hs : s * s = -6) : False :=
  no_real_sqrt hk (y := (2 * r - 1) * s) (c := 18) (by norm_num)
    (fun a h => not_sq a 18 (by decide +kernel) (by exact_mod_cast h))
    (by simp; linear_combination 4 * s * s * hr + (-3) * hs)

theorem not_rat_4 {r : k} (hr : r * r = -1) : ∀ c : ℚ, r ≠ algebraMap ℚ k c := by
  rintro c rfl
  have : c * c = -1 := (algebraMap ℚ k).injective (by simpa using hr)
  nlinarith [sq_nonneg c]

theorem not_rat_3 {r : k} (hr : r * r - r + 1 = 0) : ∀ c : ℚ, r ≠ algebraMap ℚ k c := by
  rintro c rfl
  have : c * c - c + 1 = 0 := (algebraMap ℚ k).injective (by simpa using hr)
  nlinarith [sq_nonneg (c - 1/2)]

theorem one_ne_neg_one' : (1 : k) ≠ -1 := by
  intro h
  have : (2 : k) = 0 := by linear_combination h
  exact two_ne_zero this

variable (Φ : k →ₐ[ℚ] B)

open Classical in
/-- **The unit count of `R = Φ⁻¹(𝒪)`**: `4` with a square root of `−1`, `6` with a root of
`x² − x + 1`, `2` otherwise. -/
theorem card_units_R :
    Nat.card (LeafQM.O.comap Φ.toRingHom)ˣ =
      if (∃ r ∈ LeafQM.O.comap Φ.toRingHom, r * r = -1) then 4
      else if (∃ r ∈ LeafQM.O.comap Φ.toRingHom, r * r - r + 1 = 0) then 6 else 2 := by
  set R := LeafQM.O.comap Φ.toRingHom
  have hU := unit_cases hk Φ
  split_ifs with h4 h3
  · obtain ⟨r, hrR, hr⟩ := h4
    have hnr := not_rat_4 hk hr
    have e : ([(1, 0), (-1, 0), (0, 1), (0, -1)] : List (ℚ × ℚ)).map (ev r) = [1, -1, r, -r] := by
      simp [ev]
    rw [card_units_of_list R [1, -1, r, -r]]
    · rfl
    · rw [← e]; exact List.Nodup.map (ev_inj hnr) (by decide)
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨1, by simp, by ring⟩
      · exact ⟨-1, by simp, by ring⟩
      · exact ⟨-x, by simp, by linear_combination -hr⟩
      · exact ⟨r, by simp, by linear_combination -hr⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact R.one_mem
      · exact R.neg_mem R.one_mem
      · exact hrR
      · exact R.neg_mem hrR
    · intro u
      set y : k := ((u : R) : k)
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases hU u with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · have : (y - r) * (y + r) = 0 := by linear_combination h - hr
        rcases mul_eq_zero.1 this with h' | h'
        · exact Or.inr (Or.inr (Or.inl (by linear_combination h')))
        · exact Or.inr (Or.inr (Or.inr (by linear_combination h')))
      · exact (excl_4_3 hk hr h).elim
      · exact (excl_4_3 hk hr (s := -y) (by linear_combination h)).elim
  · obtain ⟨r, hrR, hr⟩ := h3
    have hnr := not_rat_3 hk hr
    have e : ([(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)] : List (ℚ × ℚ)).map (ev r) =
        [1, -1, r, -r, 1 - r, -1 + r] := by
      simp [ev]; ring_nf
    rw [card_units_of_list R [1, -1, r, -r, 1 - r, -1 + r]]
    · rfl
    · rw [← e]; exact List.Nodup.map (ev_inj hnr) (by decide)
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, by simp, by ring⟩
      · exact ⟨-1, by simp, by ring⟩
      · exact ⟨1 - x, by simp, by linear_combination -hr⟩
      · exact ⟨-1 + r, by simp, by linear_combination -hr⟩
      · exact ⟨r, by simp, by linear_combination -hr⟩
      · exact ⟨-r, by simp, by linear_combination -hr⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact R.one_mem
      · exact R.neg_mem R.one_mem
      · exact hrR
      · exact R.neg_mem hrR
      · exact R.sub_mem R.one_mem hrR
      · exact R.add_mem (R.neg_mem R.one_mem) hrR
    · intro u
      set y : k := ((u : R) : k)
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases hU u with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact (excl_4_3 hk (r := y) (by linear_combination h) hr).elim
      · have : (y - r) * (y - (1 - r)) = 0 := by linear_combination h - hr
        rcases mul_eq_zero.1 this with h' | h'
        · exact Or.inr (Or.inr (Or.inl (by linear_combination h')))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linear_combination h')))))
      · have : (y + r) * (y - (-1 + r)) = 0 := by linear_combination h - hr
        rcases mul_eq_zero.1 this with h' | h'
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by linear_combination h'))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linear_combination h')))))
  · push Not at h4 h3
    rw [card_units_of_list R [1, -1]]
    · rfl
    · simp [one_ne_neg_one' hk]
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨1, by simp, by ring⟩
      · exact ⟨-1, by simp, by ring⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact R.one_mem
      · exact R.neg_mem R.one_mem
    · intro u
      set y : k := ((u : R) : k)
      have hyR : y ∈ R := (u : R).2
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases hU u with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (h4 y hyR (by linear_combination h)).elim
      · exact (h3 y hyR h).elim
      · exact (h3 (-y) (R.neg_mem hyR) (by linear_combination h)).elim

end CountK


/-! ## §4 Automorphisms of a QM pair; the leaf; the rows -/

section Iso

open CategoryTheory LeafQM.AV PkgI3

variable {K : Type} [Field K] {A : AbVar K}

theorem mem_com_of {q : QMStr A} (f : AbVar.End A)
    (h : ∀ a : LeafQM.O, (q.iota a).hom ≫ f.hom = f.hom ≫ (q.iota a).hom) : f ∈ com q := by
  rw [com, Subring.mem_centralizer_iff]
  rintro _ ⟨a, rfl⟩
  exact AbVar.Hom.ext' (h a).symm

theorem comm_of_mem_com {q : QMStr A} {f : AbVar.End A} (hf : f ∈ com q) (a : LeafQM.O) :
    (q.iota a).hom ≫ f.hom = f.hom ≫ (q.iota a).hom := by
  rw [com, Subring.mem_centralizer_iff] at hf
  have := congrArg AbVar.Hom.hom (hf (q.iota a) ⟨a, rfl⟩)
  exact this.symm

/-- **`Aut(A, ι) = End_𝒪(A)^×`.** -/
def isoUnitEquiv (q : QMStr A) : QMIso q q ≃ (com q)ˣ where
  toFun G :=
    { val := ⟨G.φ, mem_com_of G.φ G.equivariant⟩
      inv := ⟨G.ψ, mem_com_of G.ψ G.symm.equivariant⟩
      val_inv := Subtype.ext (AbVar.Hom.ext' G.right)
      inv_val := Subtype.ext (AbVar.Hom.ext' G.left) }
  invFun u :=
    { φ := (u.val : AbVar.End A)
      ψ := (u.inv : AbVar.End A)
      left := congrArg AbVar.Hom.hom (congrArg Subtype.val u.inv_val)
      right := congrArg AbVar.Hom.hom (congrArg Subtype.val u.val_inv)
      equivariant := comm_of_mem_com u.val.2 }
  left_inv G := rfl
  right_inv u := Units.ext rfl

end Iso

section Transport

variable {S T : Type} [Ring S] [Ring T] (e : S ≃+* T)

theorem ex_iff (P : ∀ {R : Type} [Ring R], R → Prop) (hP : ∀ x, P x ↔ P (e x)) :
    (∃ x : S, P x) ↔ ∃ y : T, P y :=
  ⟨fun ⟨x, hx⟩ => ⟨e x, (hP x).1 hx⟩, fun ⟨y, hy⟩ => ⟨e.symm y, (hP _).2 (by simpa using hy)⟩⟩

end Transport

open LeafQM.AV PkgI3 in
/-- The three CM predicates as statements about the ring `com q`. -/
theorem cm_iff {K : Type} [Field K] {A : AbVar K} (q : QMStr A) :
    (HasCM4 q ↔ ∃ x : com q, x * x = -1) ∧ (HasCM3 q ↔ ∃ x : com q, x * x - x + 1 = 0) ∧
      (HasCM24 q ↔ ∃ x : com q, x * x = -6) := by
  refine ⟨⟨fun ⟨φ, hφ, h⟩ => ⟨⟨φ, hφ⟩, Subtype.ext h⟩,
      fun ⟨x, hx⟩ => ⟨x.1, x.2, congrArg Subtype.val hx⟩⟩,
    ⟨fun ⟨φ, hφ, h⟩ => ⟨⟨φ, hφ⟩, Subtype.ext h⟩,
      fun ⟨x, hx⟩ => ⟨x.1, x.2, congrArg Subtype.val hx⟩⟩,
    ⟨fun ⟨φ, hφ, h⟩ => ⟨⟨φ, hφ⟩, Subtype.ext h⟩,
      fun ⟨x, hx⟩ => ⟨x.1, x.2, congrArg Subtype.val hx⟩⟩⟩

theorem ex4_iff {S T : Type} [Ring S] [Ring T] (e : S ≃+* T) :
    (∃ x : S, x * x = -1) ↔ ∃ y : T, y * y = -1 :=
  ⟨fun ⟨x, hx⟩ => ⟨e x, by rw [← map_mul, hx, map_neg, map_one]⟩,
   fun ⟨y, hy⟩ => ⟨e.symm y, by rw [← map_mul, hy, map_neg, map_one]⟩⟩

theorem ex3_iff {S T : Type} [Ring S] [Ring T] (e : S ≃+* T) :
    (∃ x : S, x * x - x + 1 = 0) ↔ ∃ y : T, y * y - y + 1 = 0 :=
  ⟨fun ⟨x, hx⟩ => ⟨e x, by rw [← map_mul, ← map_sub, ← map_one e, ← map_add, hx, map_zero]⟩,
   fun ⟨y, hy⟩ => ⟨e.symm y, by rw [← map_mul, ← map_sub, ← map_one e.symm, ← map_add, hy, map_zero]⟩⟩

theorem ex24_iff {S T : Type} [Ring S] [Ring T] (e : S ≃+* T) :
    (∃ x : S, x * x = -6) ↔ ∃ y : T, y * y = -6 :=
  ⟨fun ⟨x, hx⟩ => ⟨e x, by rw [← map_mul, hx, map_neg, map_ofNat]⟩,
   fun ⟨y, hy⟩ => ⟨e.symm y, by rw [← map_mul, hy, map_neg, map_ofNat]⟩⟩

theorem sub_ex_iff {k : Type} [Field k] (R : Subring k) :
    ((∃ x : R, x * x = -1) ↔ ∃ r ∈ R, r * r = -1) ∧
    ((∃ x : R, x * x - x + 1 = 0) ↔ ∃ r ∈ R, r * r - r + 1 = 0) ∧
    ((∃ x : R, x * x = -6) ↔ ∃ r ∈ R, r * r = -6) := by
  refine ⟨⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, congrArg Subtype.val hx⟩,
      fun ⟨r, hr, h⟩ => ⟨⟨r, hr⟩, Subtype.ext h⟩⟩,
    ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, congrArg Subtype.val hx⟩,
      fun ⟨r, hr, h⟩ => ⟨⟨r, hr⟩, Subtype.ext h⟩⟩,
    ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, congrArg Subtype.val hx⟩,
      fun ⟨r, hr, h⟩ => ⟨⟨r, hr⟩, Subtype.ext h⟩⟩⟩

/-- **LEAF (CM points on the Shimura curve `X₆ = X₀⁶(1)`: the centralizer of the QM).** For an abelian
surface `A/ℚ̄` with QM `ι : 𝒪 ↪ End(A)` by the maximal order `𝒪` of the indefinite quaternion algebra
`B = (2, −3)` of discriminant `6`, the centralizer `End_𝒪(A) = com(ι)` is either `ℤ`, or isomorphic to
the order `Φ⁻¹(𝒪)` of an imaginary quadratic field `k` for some `ℚ`-embedding `Φ : k → B` (an optimal
embedding; `(A, ι)` is then a CM point by `Φ⁻¹(𝒪)`).

Sources (UNVERIFIED locators, no network): Shimura, *Construction of class fields and zeta functions of
algebraic curves*, Ann. of Math. 85 (1967), §§1-3 (for `A_τ = ℂ²/ι(𝒪)(τ,1)ᵀ`,
`End_𝒪(A_τ) = Φ_τ(k) ∩ 𝒪` with `Φ_τ(k)` the commutant of the fixed point `τ`); Jordan, *Arithmetic of
a quaternion algebra*, thesis, Harvard 1981, §3; González–Rotger, *Non-elliptic Shimura curves of genus
one*, J. Math. Soc. Japan 58 (2006), §5 (CM points by an order `S` ↔ optimal embeddings `S ↪ 𝒪`);
Rotger, Crelle 561 (2003), §2. Form: the printed description is over `ℂ` (`QMCentralizerCMC`, §8); this
`ℚ̄` form is PROVED from it and the bundle's textbook leaf T11(b) in §8 (`qmCentralizerCM_of`). Not stronger: the optimal embedding is existential
and `B ≅ B^op` preserves `𝒪`. -/
def QMCentralizerCM : Prop :=
  ∀ (A : PkgI3.AbVar (AlgebraicClosure ℚ)), A.dim = 2 → ∀ q : LeafQM.AV.QMStr A,
    Nonempty (LeafQM.AV.com q ≃+* ℤ) ∨
    ∃ (k : Type) (_ : Field k) (_ : NumberField k), IsTotallyComplex k ∧ Module.finrank ℚ k = 2 ∧
      ∃ Φ : k →ₐ[ℚ] B, Nonempty (LeafQM.AV.com q ≃+* LeafQM.O.comap Φ.toRingHom)

open LeafQM.AV PkgI3 Classical in
/-- **Row H-61 from the leaf.** -/
theorem qmAutCard_of (h : QMCentralizerCM) : HDec.HeckeRest.QMAutCard := by
  intro A hA q
  have hcard : Nat.card (QMIso q q) = Nat.card (com q)ˣ := Nat.card_congr (isoUnitEquiv q)
  obtain ⟨h4i, h3i, h24i⟩ := cm_iff q
  rcases h A hA q with he | ⟨k, _, _, hkc, hk2, Φ, he⟩
  · obtain ⟨e⟩ := he
    have n4 : ¬ HasCM4 q := by
      rw [h4i, ex4_iff e]; rintro ⟨y, hy⟩; nlinarith [sq_nonneg y]
    have n3 : ¬ HasCM3 q := by
      rw [h3i, ex3_iff e]; rintro ⟨y, hy⟩; nlinarith [sq_nonneg (2 * y - 1)]
    have n24 : ¬ HasCM24 q := by
      rw [h24i, ex24_iff e]; rintro ⟨y, hy⟩; nlinarith [sq_nonneg y]
    refine ⟨?_, fun h => n4 h.1, fun h => n4 h.1, fun h => n3 h.1⟩
    rw [if_neg n4, if_neg n3, hcard, Nat.card_congr (Units.mapEquiv e.toMulEquiv).toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_units_int]
  · obtain ⟨e⟩ := he
    haveI := hkc
    set R := LeafQM.O.comap Φ.toRingHom
    obtain ⟨s4, s3, s24⟩ := sub_ex_iff R
    have e4 : HasCM4 q ↔ ∃ r ∈ R, r * r = -1 := by rw [h4i, ex4_iff e, s4]
    have e3 : HasCM3 q ↔ ∃ r ∈ R, r * r - r + 1 = 0 := by rw [h3i, ex3_iff e, s3]
    have e24 : HasCM24 q ↔ ∃ r ∈ R, r * r = -6 := by rw [h24i, ex24_iff e, s24]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hcard, Nat.card_congr (Units.mapEquiv e.toMulEquiv).toEquiv, card_units_R hk2 Φ]
      by_cases c4 : HasCM4 q
      · rw [if_pos c4, if_pos (e4.1 c4)]
      · rw [if_neg c4, if_neg (fun h => c4 (e4.2 h))]
        by_cases c3 : HasCM3 q
        · rw [if_pos c3, if_pos (e3.1 c3)]
        · rw [if_neg c3, if_neg (fun h => c3 (e3.2 h))]
    · rintro ⟨a, b⟩
      obtain ⟨r, -, hr⟩ := e4.1 a; obtain ⟨s, -, hs⟩ := e3.1 b
      exact excl_4_3 hk2 hr hs
    · rintro ⟨a, b⟩
      obtain ⟨r, -, hr⟩ := e4.1 a; obtain ⟨s, -, hs⟩ := e24.1 b
      exact excl_4_24 hk2 hr hs
    · rintro ⟨a, b⟩
      obtain ⟨r, -, hr⟩ := e3.1 a; obtain ⟨s, -, hs⟩ := e24.1 b
      exact excl_3_24 hk2 hr hs


/-! ## §5 `ALFixedPoints`: computations in `B` -/

/-- Anisotropy: `3c² = 2e² + 2b² + 6d²` over `ℤ` forces `e = 0` (descent mod 3). -/
theorem aniso_m2 : ∀ (n : ℕ) (e b c d : ℤ), e.natAbs = n → 3 * c ^ 2 = 2 * e ^ 2 + 2 * b ^ 2 + 6 * d ^ 2 → e = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro e b c d hn h
    have key : ∀ x y z w : ZMod 3, 3 * z ^ 2 = 2 * x ^ 2 + 2 * y ^ 2 + 6 * w ^ 2 → x = 0 ∧ y = 0 := by
      decide
    obtain ⟨he, hb⟩ := key (e : ZMod 3) (b : ZMod 3) (c : ZMod 3) (d : ZMod 3) (by exact_mod_cast congrArg (Int.cast : ℤ → ZMod 3) h)
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at he hb
    obtain ⟨e', rfl⟩ := he
    obtain ⟨b', rfl⟩ := hb
    push_cast at h hn
    have h' : c ^ 2 = 6 * e' ^ 2 + 6 * b' ^ 2 + 2 * d ^ 2 := by linarith
    have key2 : ∀ x y z w : ZMod 3, x ^ 2 = 6 * z ^ 2 + 6 * w ^ 2 + 2 * y ^ 2 → x = 0 ∧ y = 0 := by decide
    obtain ⟨hc, hd⟩ := key2 (c : ZMod 3) (d : ZMod 3) (e' : ZMod 3) (b' : ZMod 3) (by exact_mod_cast congrArg (Int.cast : ℤ → ZMod 3) h')
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc hd
    obtain ⟨c', rfl⟩ := hc
    obtain ⟨d', rfl⟩ := hd
    push_cast at h'
    have h'' : 3 * c' ^ 2 = 2 * e' ^ 2 + 2 * b' ^ 2 + 6 * d' ^ 2 := by linarith
    by_cases he0 : e' = 0
    · simp [he0]
    · have hlt : e'.natAbs < n := by
        rw [← hn, Int.natAbs_mul]; simp; omega
      exact absurd (ih _ hlt e' b' c' d' rfl h'') he0

open QuaternionAlgebra in
/-- No element of `B` squares to `−2` (`ℚ(√−2)` does not embed in `B`: `3` splits in it). -/
theorem no_sq_neg2 (x : B) : x * x ≠ -2 := by
  intro hx
  have hq := quat_sq x
  rw [hx] at hq
  have h0 := congrArg QuaternionAlgebra.re hq
  have h1 := congrArg QuaternionAlgebra.imI hq
  have h2 := congrArg QuaternionAlgebra.imJ hq
  have h3 := congrArg QuaternionAlgebra.imK hq
  simp [nrd, re_ofNat, imI_ofNat, imJ_ofNat, imK_ofNat] at h0 h1 h2 h3
  by_cases hre : x.re = 0
  · rw [hre] at h0
    set E : ℤ := ((x.imI.den * x.imJ.den * x.imK.den : ℕ) : ℤ)
    have hE : (E : ℚ) ≠ 0 := by simp [E]
    obtain ⟨b, hb⟩ : ∃ z : ℤ, (z : ℚ) = x.imI * E :=
      ⟨x.imI.num * (x.imJ.den * x.imK.den : ℕ), by
        simp only [E]; push_cast; rw [← Rat.mul_den_eq_num x.imI]; ring⟩
    obtain ⟨c, hc⟩ : ∃ z : ℤ, (z : ℚ) = x.imJ * E :=
      ⟨x.imJ.num * (x.imI.den * x.imK.den : ℕ), by
        simp only [E]; push_cast; rw [← Rat.mul_den_eq_num x.imJ]; ring⟩
    obtain ⟨d, hd⟩ : ∃ z : ℤ, (z : ℚ) = x.imK * E :=
      ⟨x.imK.num * (x.imI.den * x.imJ.den : ℕ), by
        simp only [E]; push_cast; rw [← Rat.mul_den_eq_num x.imK]; ring⟩
    have hint : 3 * c ^ 2 = 2 * E ^ 2 + 2 * b ^ 2 + 6 * d ^ 2 := by
      have : (3 * c ^ 2 : ℚ) = 2 * E ^ 2 + 2 * b ^ 2 + 6 * d ^ 2 := by
        rw [hb, hc, hd]; linear_combination (E : ℚ) ^ 2 * h0
      exact_mod_cast this
    exact hE (by exact_mod_cast aniso_m2 _ E b c d rfl hint)
  · have hI : x.imI = 0 := h1.resolve_left hre
    have hJ : x.imJ = 0 := h2.resolve_left hre
    have hK : x.imK = 0 := h3.resolve_left hre
    rw [hI, hJ, hK] at h0
    nlinarith [sq_nonneg x.re]


/-- `x ∈ 𝒪`, `x² = −3` ⇒ `(1 + x)/2 ∈ 𝒪` (`𝒪 ⊗ ℤ₂` is the maximal order of the local division algebra,
which contains the cube roots of unity). -/
theorem half_mem_of_sq_neg3 {x : B} (hxO : x ∈ LeafQM.O) (hx : x * x = -3) :
    ((1 : ℚ) / 2) • (1 + x) ∈ LeafQM.O := by
  have hq := quat_sq x
  rw [hx] at hq
  have h0 := congrArg QuaternionAlgebra.re hq
  have h1 := congrArg QuaternionAlgebra.imI hq
  have h2 := congrArg QuaternionAlgebra.imJ hq
  have h3 := congrArg QuaternionAlgebra.imK hq
  simp [nrd, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat,
    QuaternionAlgebra.imK_ofNat] at h0 h1 h2 h3
  have hre : x.re = 0 := by
    by_contra hre
    rw [h1.resolve_left hre, h2.resolve_left hre, h3.resolve_left hre] at h0
    nlinarith [sq_nonneg x.re]
  obtain ⟨n, rfl⟩ := hxO
  simp only [LeafQM.ofInt] at hre h0
  have hn2 : n 2 = -2 * n 0 := by
    have : ((n 2 : ℤ) : ℚ) = -2 * n 0 := by linarith
    exact_mod_cast this
  rw [hre] at h0
  have hQ : 3 * n 0 ^ 2 - 2 * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2) = 3 := by
    have e : ((n 2 : ℤ) : ℚ) = -2 * n 0 := by exact_mod_cast hn2
    have : (3 * (n 0 : ℚ) ^ 2 - 2 * ((n 1 : ℚ) ^ 2 + n 1 * n 3 + n 3 ^ 2)) = 3 := by
      rw [e] at h0; linear_combination h0
    exact_mod_cast this
  -- parities
  have k1 : ∀ a b c : ZMod 2, 3 * a ^ 2 - 2 * (b ^ 2 + b * c + c ^ 2) = 3 → a - 1 = 0 := by decide
  have ho := k1 (n 0) (n 1) (n 3) (by exact_mod_cast congrArg (Int.cast : ℤ → ZMod 2) hQ)
  have ho' : ((n 0 - 1 : ℤ) : ZMod 2) = 0 := by push_cast; exact ho
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ho'
  obtain ⟨a, ha⟩ := ho'
  have hQ' : n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2 = 6 * a ^ 2 + 6 * a := by
    have e : n 0 = 2 * a + 1 := by push_cast at ha; linarith
    rw [e] at hQ; linarith
  have k2 : ∀ b c : ZMod 2, b ^ 2 + b * c + c ^ 2 = 0 → b = 0 ∧ c = 0 := by decide
  obtain ⟨hb, hc⟩ := k2 (n 1) (n 3) (by
    have := congrArg (Int.cast : ℤ → ZMod 2) hQ'
    push_cast at this
    rw [this, show (6 : ZMod 2) = 0 from rfl]; ring)
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hb hc
  obtain ⟨b, hb⟩ := hb
  obtain ⟨d, hd⟩ := hc
  refine ⟨![a + 1, b, -(2 * a + 1), d], ?_⟩
  have e0 : (n 0 : ℚ) = 2 * a + 1 := by push_cast at ha; exact_mod_cast (by linarith : n 0 = 2 * a + 1)
  have e1 : (n 1 : ℚ) = 2 * b := by push_cast at hb; exact_mod_cast hb
  have e3 : (n 3 : ℚ) = 2 * d := by push_cast at hd; exact_mod_cast hd
  have e2 : (n 2 : ℚ) = -2 * (2 * a + 1) := by rw [← e0]; exact_mod_cast hn2
  ext <;> simp [LeafQM.ofInt, e0, e1, e2, e3] <;> ring

/-! ## §6 `ALFixedPoints`: the twist data and the case analysis -/

section TwistData

open LeafQM.AV PkgI3

/-- From `(A, ι ∘ α) ≅ (A, ι)` with `α` conjugation by `τ` (`τ² = c` central): elements `V, W` of
`End_𝒪(A)` with `V² = c W` and `W` a unit (`V = φ ι(τ)`, `W = φ²`). -/
theorem twist_data {A : AbVar (AlgebraicClosure ℚ)} (q : QMStr A) (α : LeafQM.O ≃+* LeafQM.O)
    (τ : LeafQM.O) (c : ℤ) (hατ : α τ = τ) (hcomm : ∀ a, α a * τ = τ * a) (hαα : ∀ a, α (α a) = a)
    (hττ : τ * τ = (c : LeafQM.O)) (G : QMIso (q.twist α) q) :
    ∃ V W Winv : com q, V * V = (c : com q) * W ∧ W * Winv = 1 := by
  set φ : AbVar.End A := G.φ
  set ψ : AbVar.End A := G.ψ
  have eq1 : ∀ a, φ * q.iota (α a) = q.iota a * φ := fun a => AbVar.Hom.ext' (G.equivariant a)
  have eq2 : ∀ a, ψ * q.iota a = q.iota (α a) * ψ := fun a => AbVar.Hom.ext' (G.symm.equivariant a)
  have hφψ : φ * ψ = 1 := AbVar.Hom.ext' G.right
  have hψφ : ψ * φ = 1 := AbVar.Hom.ext' G.left
  have memc : ∀ z : AbVar.End A, (∀ a, q.iota a * z = z * q.iota a) → z ∈ com q := by
    intro z hz
    rw [com, Subring.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    exact hz a
  have hW : φ * φ ∈ com q := memc _ fun a => by
    rw [← mul_assoc, ← eq1, mul_assoc, ← eq1, hαα, mul_assoc]
  have hWi : ψ * ψ ∈ com q := memc _ fun a => by
    have h1 := eq2 (α a)
    rw [hαα] at h1
    rw [mul_assoc, eq2, ← mul_assoc, ← h1, mul_assoc]
  have hV : φ * q.iota τ ∈ com q := memc _ fun a => by
    rw [← mul_assoc, ← eq1, mul_assoc, ← map_mul, hcomm, map_mul, mul_assoc]
  refine ⟨⟨_, hV⟩, ⟨_, hW⟩, ⟨_, hWi⟩, ?_, ?_⟩
  · apply Subtype.ext
    have h1 : q.iota τ * φ = φ * q.iota τ := by rw [← eq1, hατ]
    change φ * q.iota τ * (φ * q.iota τ) = ((c : com q) : AbVar.End A) * (φ * φ)
    rw [show ((c : com q) : AbVar.End A) = (c : AbVar.End A) by push_cast; rfl]
    calc φ * q.iota τ * (φ * q.iota τ) = φ * (q.iota τ * φ) * q.iota τ := by noncomm_ring
      _ = φ * φ * (q.iota (τ * τ)) := by rw [h1, map_mul]; noncomm_ring
      _ = (c : AbVar.End A) * (φ * φ) := by rw [hττ, map_intCast, (Int.cast_commute c _).eq]
  · apply Subtype.ext
    change φ * φ * (ψ * ψ) = 1
    calc φ * φ * (ψ * ψ) = φ * (φ * ψ) * ψ := by noncomm_ring
      _ = 1 := by rw [hφψ, mul_one, hφψ]

end TwistData


theorem nsq (c : ℤ) (hc : ¬ IsSquare c) : ∀ a : ℚ, a * a ≠ c :=
  fun a h => not_sq a c hc h

section ALArith

variable {k : Type} [Field k] [NumberField k] [IsTotallyComplex k] (hk : Module.finrank ℚ k = 2)
  (Φ : k →ₐ[ℚ] B)
include hk

theorem unit_cases' {w winv : k} (hw : w ∈ LeafQM.O.comap Φ.toRingHom)
    (hwi : winv ∈ LeafQM.O.comap Φ.toRingHom) (h : w * winv = 1) :
    w = 1 ∨ w = -1 ∨ w * w + 1 = 0 ∨ w * w - w + 1 = 0 ∨ w * w + w + 1 = 0 := by
  let U : (LeafQM.O.comap Φ.toRingHom)ˣ :=
    ⟨⟨w, hw⟩, ⟨winv, hwi⟩, Subtype.ext h, Subtype.ext (by rw [mul_comm]; exact h)⟩
  exact unit_cases hk Φ U

theorem al2 {v w winv : k} (hv : v ∈ LeafQM.O.comap Φ.toRingHom) (hw : w ∈ LeafQM.O.comap Φ.toRingHom)
    (hwi : winv ∈ LeafQM.O.comap Φ.toRingHom) (h : w * winv = 1) (hvv : v * v = 2 * w) :
    ∃ r ∈ LeafQM.O.comap Φ.toRingHom, r * r = -1 := by
  have negB : ∀ y : k, y * y = -2 → False := fun y hy =>
    no_sq_neg2 (Φ y) (by rw [← map_mul, hy, map_neg, map_ofNat])
  rcases unit_cases' hk Φ hw hwi h with h1 | h1 | h1 | h1 | h1
  · exact (no_real_sqrt hk (y := v) (c := 2) (by norm_num) (nsq 2 (by decide +kernel))
      (by rw [hvv, h1]; simp)).elim
  · exact (negB v (by rw [hvv, h1]; ring)).elim
  · exact ⟨w, hw, by linear_combination h1⟩
  · exact (negB (v * w) (by linear_combination w * w * hvv + 2 * (w + 1) * h1)).elim
  · exact (no_real_sqrt hk (y := v * w) (c := 2) (by norm_num) (nsq 2 (by decide +kernel))
      (by simp; linear_combination w * w * hvv + 2 * (w - 1) * h1)).elim

theorem al3 {v w winv : k} (hv : v ∈ LeafQM.O.comap Φ.toRingHom) (hw : w ∈ LeafQM.O.comap Φ.toRingHom)
    (hwi : winv ∈ LeafQM.O.comap Φ.toRingHom) (h : w * winv = 1) (hvv : v * v = -3 * w) :
    ∃ r ∈ LeafQM.O.comap Φ.toRingHom, r * r - r + 1 = 0 := by
  rcases unit_cases' hk Φ hw hwi h with h1 | h1 | h1 | h1 | h1
  · refine ⟨algebraMap ℚ k (1 / 2) * (1 + v), ?_, ?_⟩
    · show Φ (algebraMap ℚ k (1 / 2) * (1 + v)) ∈ LeafQM.O
      have hvO : Φ v ∈ LeafQM.O := hv
      have := half_mem_of_sq_neg3 hvO (by rw [← map_mul, hvv, h1, mul_one, map_neg, map_ofNat])
      rw [map_mul, AlgHom.commutes, map_add, map_one, ← Algebra.smul_def]
      exact this
    · rw [h1] at hvv
      simp only [map_div₀, map_one, map_ofNat]
      field_simp
      linear_combination hvv
  · exact (no_real_sqrt hk (y := v) (c := 3) (by norm_num) (nsq 3 (by decide +kernel))
      (by rw [hvv, h1]; simp)).elim
  · exact (no_real_sqrt hk (y := v * (1 + w)) (c := 6) (by norm_num) (nsq 6 (by decide +kernel))
      (by simp; linear_combination (1 + w) * (1 + w) * hvv + (-3 * w - 6) * h1)).elim
  · exact ⟨w, hw, h1⟩
  · exact ⟨-w, (LeafQM.O.comap Φ.toRingHom).neg_mem hw, by linear_combination h1⟩

theorem al6 {v w winv : k} (hv : v ∈ LeafQM.O.comap Φ.toRingHom) (hw : w ∈ LeafQM.O.comap Φ.toRingHom)
    (hwi : winv ∈ LeafQM.O.comap Φ.toRingHom) (h : w * winv = 1) (hvv : v * v = 6 * w) :
    ∃ r ∈ LeafQM.O.comap Φ.toRingHom, r * r = -6 := by
  rcases unit_cases' hk Φ hw hwi h with h1 | h1 | h1 | h1 | h1
  · exact (no_real_sqrt hk (y := v) (c := 6) (by norm_num) (nsq 6 (by decide +kernel))
      (by rw [hvv, h1]; simp)).elim
  · exact ⟨v, hv, by rw [hvv, h1]; ring⟩
  · exact (no_real_sqrt hk (y := v * (1 - w)) (c := 12) (by norm_num) (nsq 12 (by decide +kernel))
      (by simp; linear_combination (1 - w) * (1 - w) * hvv + (6 * w - 12) * h1)).elim
  · exact ⟨v * w, (LeafQM.O.comap Φ.toRingHom).mul_mem hv hw,
      by linear_combination w * w * hvv + 6 * (w + 1) * h1⟩
  · exact (no_real_sqrt hk (y := v * w) (c := 6) (by norm_num) (nsq 6 (by decide +kernel))
      (by simp; linear_combination w * w * hvv + 6 * (w - 1) * h1)).elim

end ALArith


section Conj

open LeafQM.AV.Pin.Exact LeafQM.AV.Pin.NormO

theorem conjO_facts (u : LeafQM.Bˣ) (hu : IsNorm u) (huO : (u : B) ∈ LeafQM.O) (c : ℤ)
    (huu : (u : B) * u = (c : B)) :
    conjO u hu ⟨u, huO⟩ = ⟨u, huO⟩ ∧ (∀ a, conjO u hu a * ⟨u, huO⟩ = ⟨u, huO⟩ * a) ∧
      (∀ a, conjO u hu (conjO u hu a) = a) ∧
      (⟨u, huO⟩ : LeafQM.O) * ⟨u, huO⟩ = (c : LeafQM.O) := by
  refine ⟨Subtype.ext ?_, fun a => Subtype.ext ?_, fun a => Subtype.ext ?_, Subtype.ext ?_⟩
  · simp [conjO_apply]
  · simp [conjO_apply, mul_assoc]
  · have hc : ((u : B) * u) * a = a * ((u : B) * u) := by rw [huu]; exact (Int.cast_commute c _)
    simp only [conjO_apply]
    calc (u : B) * ((u : B) * a * ((u⁻¹ : LeafQM.Bˣ) : B)) * ((u⁻¹ : LeafQM.Bˣ) : B)
        = ((u : B) * u * a) * (((u⁻¹ : LeafQM.Bˣ) : B) * ((u⁻¹ : LeafQM.Bˣ) : B)) := by noncomm_ring
      _ = (a * ((u : B) * u)) * (((u⁻¹ : LeafQM.Bˣ) : B) * ((u⁻¹ : LeafQM.Bˣ) : B)) := by rw [hc]
      _ = a := by simp [mul_assoc]
  · simp only [Subring.coe_mul]
    rw [huu]; push_cast; rfl

theorem tt1 : (tt 1 : B) = LeafQM.ofInt ei := rfl
theorem tt2 : (tt 2 : B) = LeafQM.ofInt ej := rfl
theorem tt3 : (tt 3 : B) = LeafQM.ofInt ei * LeafQM.ofInt ej := rfl

theorem tt_mem (k : Fin 4) (hk : k ≠ 0) : (tt k : B) ∈ LeafQM.O := by
  fin_cases k
  · exact absurd rfl hk
  · exact ⟨ei, rfl⟩
  · exact ⟨ej, rfl⟩
  · exact ⟨LeafQM.mulCoord ei ej, by show (tt 3 : B) = _; rw [tt3, LeafQM.ofInt_mul]⟩

theorem tt1_sq : (tt 1 : B) * tt 1 = ((2 : ℤ) : B) := by
  rw [tt1]; ext <;> simp [LeafQM.ofInt, ei, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num
theorem tt2_sq : (tt 2 : B) * tt 2 = ((-3 : ℤ) : B) := by
  rw [tt2]; ext <;> simp [LeafQM.ofInt, ej, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num
theorem tt3_sq : (tt 3 : B) * tt 3 = ((6 : ℤ) : B) := by
  rw [tt3]; ext <;> simp [LeafQM.ofInt, ei, ej, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num

end Conj

theorem int_case (c : ℤ) (h1 : ¬ IsSquare c) (h2 : ¬ IsSquare (-c)) (v w wi : ℤ) (hv : v * v = c * w)
    (hw : w * wi = 1) : False := by
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hw with rfl | rfl
  · exact h1 ⟨v, by linarith⟩
  · exact h2 ⟨v, by linarith⟩

open LeafQM.AV PkgI3 LeafQM.AV.Pin.Exact in
/-- **Row H-63 from the leaf.** -/
theorem alFixedPoints_of (h : QMCentralizerCM) : HDec.HeckeRest.ALFixedPoints := by
  intro A hA q
  -- the twist data for `k = 1, 2, 3`
  have data : ∀ (kk : Fin 4) (c : ℤ), kk ≠ 0 → (tt kk : B) * tt kk = (c : B) →
      Nonempty (QMIso (q.twist (rep kk)) q) → ∃ V W Winv : com q, V * V = (c : com q) * W ∧ W * Winv = 1 := by
    intro kk c hk0 hsq ⟨G⟩
    obtain ⟨f1, f2, f3, f4⟩ := conjO_facts (tt kk) (tt_isNorm kk) (tt_mem kk hk0) c hsq
    exact twist_data q (rep kk) _ c f1 f2 f3 f4 G
  obtain ⟨h4i, h3i, h24i⟩ := cm_iff q
  rcases h A hA q with he | ⟨k, _, _, hkc, hk2, Φ, he⟩
  · obtain ⟨e⟩ := he
    have zc : ∀ (kk : Fin 4) (c : ℤ), kk ≠ 0 → (tt kk : B) * tt kk = (c : B) → ¬ IsSquare c → ¬ IsSquare (-c) →
        ¬ Nonempty (QMIso (q.twist (rep kk)) q) := by
      intro kk c hk0 hsq n1 n2 hG
      obtain ⟨V, W, Wi, hV, hW⟩ := data kk c hk0 hsq hG
      apply int_case c n1 n2 (e V) (e W) (e Wi)
      · rw [← map_mul, hV, map_mul, map_intCast, Int.cast_id]
      · rw [← map_mul, hW, map_one]
    refine ⟨fun hG => (zc 1 2 (by decide) tt1_sq (by decide +kernel) (by decide +kernel) hG).elim,
      fun hG => (zc 2 (-3) (by decide) tt2_sq (by decide +kernel) (by decide +kernel) hG).elim,
      fun hG => (zc 3 6 (by decide) tt3_sq (by decide +kernel) (by decide +kernel) hG).elim⟩
  · obtain ⟨e⟩ := he
    haveI := hkc
    set R := LeafQM.O.comap Φ.toRingHom
    obtain ⟨s4, s3, s24⟩ := sub_ex_iff R
    have e4 : HasCM4 q ↔ ∃ r ∈ R, r * r = -1 := by rw [h4i, ex4_iff e, s4]
    have e3 : HasCM3 q ↔ ∃ r ∈ R, r * r - r + 1 = 0 := by rw [h3i, ex3_iff e, s3]
    have e24 : HasCM24 q ↔ ∃ r ∈ R, r * r = -6 := by rw [h24i, ex24_iff e, s24]
    have tr : ∀ (kk : Fin 4) (c : ℤ), kk ≠ 0 → (tt kk : B) * tt kk = (c : B) →
        Nonempty (QMIso (q.twist (rep kk)) q) →
        ∃ v w wi : k, v ∈ R ∧ w ∈ R ∧ wi ∈ R ∧ w * wi = 1 ∧ v * v = c * w := by
      intro kk c hk0 hsq hG
      obtain ⟨V, W, Wi, hV, hW⟩ := data kk c hk0 hsq hG
      refine ⟨(e V : R), (e W : R), (e Wi : R), (e V).2, (e W).2, (e Wi).2, ?_, ?_⟩
      · have := congrArg Subtype.val (show e W * e Wi = 1 by rw [← map_mul, hW, map_one])
        exact this
      · have := congrArg Subtype.val (show e V * e V = (c : R) * e W by
          rw [← map_mul, hV, map_mul, map_intCast])
        rw [show ((((c : R) * e W : R)) : k) = (c : k) * (e W : R) by push_cast; rfl] at this
        exact this
    refine ⟨fun hG => ?_, fun hG => ?_, fun hG => ?_⟩
    · obtain ⟨v, w, wi, hv, hw, hwi, hww, hvv⟩ := tr 1 2 (by decide) tt1_sq hG
      exact e4.2 (al2 hk2 Φ hv hw hwi hww (by rw [hvv]; push_cast; ring))
    · obtain ⟨v, w, wi, hv, hw, hwi, hww, hvv⟩ := tr 2 (-3) (by decide) tt2_sq hG
      exact e3.2 (al3 hk2 Φ hv hw hwi hww (by rw [hvv]; push_cast; ring))
    · obtain ⟨v, w, wi, hv, hw, hwi, hww, hvv⟩ := tr 3 6 (by decide) tt3_sq hG
      exact e24.2 (al6 hk2 Φ hv hw hwi hww (by rw [hvv]; push_cast; ring))


/-! ## §7 Row H-42 `CMOptimalEmbedding` from the leaf -/

theorem isFractionRing_of_mul_mem {K : Type} [Field K] [CharZero K] (R : Subring K)
    (h : ∀ x : K, ∃ d : ℕ, d ≠ 0 ∧ (d : K) * x ∈ R) : IsFractionRing R K := by
  rw [IsFractionRing, isLocalization_iff]
  refine ⟨fun y => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · have hy : (y : R) ≠ 0 := nonZeroDivisors.coe_ne_zero y
    exact IsUnit.mk0 _ (by
      change ((y : R) : K) ≠ 0
      exact fun h0 => hy (Subtype.ext h0))
  · obtain ⟨d, hd, hdz⟩ := h z
    have hdR : (d : K) ∈ R := natCast_mem R d
    have hd0 : (⟨(d : K), hdR⟩ : R) ∈ nonZeroDivisors R :=
      mem_nonZeroDivisors_of_ne_zero (fun h0 => hd (by
        have h1 : ((d : ℕ) : K) = 0 := congrArg Subtype.val h0
        exact_mod_cast h1))
    refine ⟨(⟨(d : K) * z, hdz⟩, ⟨_, hd0⟩), ?_⟩
    change z * (d : K) = (d : K) * z
    ring
  · exact ⟨1, by simpa using Subtype.ext hxy⟩

theorem O_spans {x : B} : ∃ d : ℕ, d ≠ 0 ∧ (d : ℚ) • x ∈ LeafQM.O := by
  refine ⟨x.re.den * x.imI.den * x.imJ.den * x.imK.den, by positivity, ?_⟩
  set D : ℕ := x.re.den * x.imI.den * x.imJ.den * x.imK.den
  have hint : ∀ (q : ℚ) (n : ℕ), q.den ∣ n → ∃ z : ℤ, (z : ℚ) = (n : ℚ) * q := by
    intro q n hn
    obtain ⟨m, rfl⟩ := hn
    exact ⟨m * q.num, by push_cast; rw [← Rat.mul_den_eq_num q]; ring⟩
  obtain ⟨a, ha⟩ := hint x.re D ⟨x.imI.den * x.imJ.den * x.imK.den, by simp only [D]; ring⟩
  obtain ⟨b, hb⟩ := hint x.imI D ⟨x.re.den * x.imJ.den * x.imK.den, by simp only [D]; ring⟩
  obtain ⟨c, hc⟩ := hint x.imJ D ⟨x.re.den * x.imI.den * x.imK.den, by simp only [D]; ring⟩
  obtain ⟨d, hd⟩ := hint x.imK D ⟨x.re.den * x.imI.den * x.imJ.den, by simp only [D]; ring⟩
  refine ⟨![a - c, b - d, 2 * c, 2 * d], ?_⟩
  ext <;> simp [LeafQM.ofInt, ha, hb, hc, hd] <;> ring

theorem order_spans {k' : Type} [Field k'] [NumberField k'] (R' : Subring k')
    (hR' : R' ≤ (integralClosure ℤ k').toSubring) (hc : LeafQM.AV.conductor R' ≠ 0) (x : k') :
    ∃ d : ℕ, d ≠ 0 ∧ (d : k') * x ∈ R' := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ k').2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  set H := R'.toAddSubgroup.addSubgroupOf (integralClosure ℤ k').toSubring.toAddSubgroup
  have hidx : H.index = LeafQM.AV.conductor R' := rfl
  have hmem : (y • x) ∈ (integralClosure ℤ k').toSubring.toAddSubgroup := hyint
  have h1 := AddSubgroup.nsmul_index_mem H ⟨y • x, hmem⟩
  rw [AddSubgroup.mem_addSubgroupOf] at h1
  change H.index • (y • x) ∈ R' at h1
  set z : ℤ := (H.index : ℤ) * y
  have hz0 : z ≠ 0 := mul_ne_zero (by rw [hidx]; exact_mod_cast hc) hy0
  have hzx : (z : k') * x ∈ R' := by
    have e : (z : k') * x = H.index • (y • x) := by
      simp only [z, zsmul_eq_mul, nsmul_eq_mul]; push_cast; ring
    rw [e]; exact h1
  refine ⟨z.natAbs, by simpa using hz0, ?_⟩
  have hcast : ((z.natAbs : ℕ) : k') = (z : k') ∨ ((z.natAbs : ℕ) : k') = -(z : k') := by
    rcases Int.natAbs_eq z with h | h
    · left; rw [← Int.cast_natCast, ← h]
    · right; rw [← Int.cast_natCast, show ((z.natAbs : ℤ)) = -z by omega, Int.cast_neg]
  rcases hcast with h | h
  · rw [h]; exact hzx
  · rw [h, neg_mul]; exact R'.neg_mem hzx

open LeafQM.AV in
/-- **Row H-42 from the leaf.** -/
theorem cmOptimalEmbedding_of (h : QMCentralizerCM) : HDec.FS5NoCM.CMOptimalEmbedding := by
  intro P k' _ _ _ hk2' R' hR' hc0 he'
  obtain ⟨e'⟩ := he'
  rcases h P.A P.surface P.q with he | ⟨k, _, _, hkc, hk2, Φ, he⟩
  · -- `R' ≅ ℤ` is impossible for an order of finite index in `𝓞_k'`
    exfalso
    obtain ⟨e⟩ := he
    have f : ℤ ≃+* R' := e.symm.trans e'
    have hall : ∀ r : R', ∃ n : ℤ, (r : k') = n := by
      intro r
      refine ⟨f.symm r, ?_⟩
      have h1 : f (f.symm r) = r := f.apply_symm_apply r
      have h2 : f (f.symm r) = ((f.symm r : ℤ) : R') := eq_intCast f _
      have h3 : r = ((f.symm r : ℤ) : R') := h1.symm.trans h2
      conv_lhs => rw [h3]
      push_cast; rfl
    -- a non-rational element of `k'`
    obtain ⟨x, hx⟩ : ∃ x : k', ∀ c : ℚ, x ≠ algebraMap ℚ k' c := by
      by_contra hno
      push Not at hno
      have : Module.finrank ℚ k' = 1 := by
        rw [finrank_eq_one_iff_of_nonzero' (1 : k') one_ne_zero]
        intro x; obtain ⟨c, rfl⟩ := hno x; exact ⟨c, by simp [Algebra.smul_def]⟩
      omega
    obtain ⟨d, hd, hdx⟩ := order_spans R' hR' hc0 x
    obtain ⟨n, hn⟩ := hall ⟨_, hdx⟩
    apply hx ((n : ℚ) / d)
    have hdk : (d : k') ≠ 0 := by exact_mod_cast hd
    simp only [map_div₀, map_intCast, map_natCast]
    field_simp
    rw [mul_comm]; exact hn
  · obtain ⟨e⟩ := he
    haveI := hkc
    set R := LeafQM.O.comap Φ.toRingHom
    let ψ : R' ≃+* R := e'.symm.trans e
    haveI : IsFractionRing R' k' := isFractionRing_of_mul_mem R' (order_spans R' hR' hc0)
    haveI : IsFractionRing R k := isFractionRing_of_mul_mem R (fun y => by
      obtain ⟨d, hd, hdy⟩ := O_spans (x := Φ y)
      refine ⟨d, hd, ?_⟩
      show Φ ((d : k) * y) ∈ LeafQM.O
      have e1 : Φ ((d : k) * y) = (d : ℚ) • Φ y := by
        rw [map_mul, map_natCast, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
      rw [e1]; exact hdy)
    let σ : k' ≃+* k := IsFractionRing.ringEquivOfRingEquiv ψ
    have hσ : ∀ r : R', σ r = ψ r := fun r => IsFractionRing.ringEquivOfRingEquiv_algebraMap ψ r
    refine ⟨(Φ.toRingHom.comp σ.toRingHom).toRatAlgHom, ?_⟩
    ext x
    change x ∈ R' ↔ Φ (σ x) ∈ LeafQM.O
    constructor
    · intro hx
      have := hσ ⟨x, hx⟩
      change Φ (σ x) ∈ LeafQM.O
      rw [this]; exact (ψ ⟨x, hx⟩).2
    · intro hx
      let r : R := ⟨σ x, hx⟩
      have h1 := hσ (ψ.symm r)
      rw [RingEquiv.apply_symm_apply] at h1
      have : ((ψ.symm r : R') : k') = x := σ.injective h1
      rw [← this]; exact (ψ.symm r).2

/-! ## §8 The leaf in its printed setting (over `ℂ`) and the passage to `ℚ̄` by T11(b) -/

/-- **LEAF (`QMCentralizerCM` over `ℂ`, the printed setting).** Same statement as `QMCentralizerCM`, for
abelian surfaces with QM by `𝒪` over `ℂ` (Shimura 1967 §§1-3: `A_τ = ℂ²/ι(𝒪)(τ,1)ᵀ`,
`End_𝒪(A_τ) = Φ_τ(k) ∩ 𝒪`; Jordan 1981 §3; González–Rotger 2006 §5; locators UNVERIFIED). -/
def QMCentralizerCMC : Prop :=
  ∀ (A : PkgI3.AbVar ℂ), A.dim = 2 → ∀ q : LeafQM.AV.QMStr A,
    Nonempty (LeafQM.AV.com q ≃+* ℤ) ∨
    ∃ (k : Type) (_ : Field k) (_ : NumberField k), IsTotallyComplex k ∧ Module.finrank ℚ k = 2 ∧
      ∃ Φ : k →ₐ[ℚ] B, Nonempty (LeafQM.AV.com q ≃+* LeafQM.O.comap Φ.toRingHom)

open LeafQM.AV in
/-- **The `ℚ̄` form from the `ℂ` form and T11(b)** (the bundle's textbook leaf `T11b_Rigidity`: base change
`ℚ̄ → ℂ` is bijective on endomorphisms). The centralizer of `ι` corresponds to that of its base change. -/
theorem qmCentralizerCM_of (hC : QMCentralizerCMC) (hR : ZInQ.LeafPush2.T11b_Rigidity) :
    QMCentralizerCM := by
  intro A hA q
  let ιe : AlgebraicClosure ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) ℂ := ιe.toRingHom.toAlgebra
  let e := HDec.G0ModField.KernelField.endBC A ℂ
  have he : Function.Bijective e := by
    refine ⟨HDec.G0ModField.KernelField.endBC_injective A ℂ, fun g => ?_⟩
    obtain ⟨φ, ⟨hφ, hφe⟩, -⟩ := hR (AlgebraicClosure ℚ) ℂ A A g.hom inferInstance
    exact ⟨PkgI3.AbVar.Hom.mk' φ, PkgI3.AbVar.Hom.ext' hφe⟩
  let qC : QMStr (A.baseChange ℂ) := ⟨e.comp q.iota, he.1.comp q.injective⟩
  have hdim : (A.baseChange ℂ).dim = 2 := by rw [PkgI3.AbVar.dim_baseChange]; exact hA
  have hcom : com qC = (com q).map e := by
    ext ψ
    simp only [com, Subring.mem_centralizer_iff, Subring.mem_map, Set.mem_range]
    constructor
    · intro h
      obtain ⟨φ, rfl⟩ := he.2 ψ
      refine ⟨φ, ?_, rfl⟩
      rintro _ ⟨a, rfl⟩
      apply he.1
      rw [map_mul, map_mul]
      exact h _ ⟨a, rfl⟩
    · rintro ⟨φ, hφ, rfl⟩ _ ⟨a, rfl⟩
      change e (q.iota a) * e φ = e φ * e (q.iota a)
      rw [← map_mul, ← map_mul, hφ _ ⟨a, rfl⟩]
  let E : com q ≃+* com qC :=
    ((RingEquiv.ofBijective e he).subringMap (s := com q)).trans (RingEquiv.subringCongr hcom.symm)
  rcases hC (A.baseChange ℂ) hdim qC with hf | ⟨k, i1, i2, hk, hk2, Φ, hf⟩
  · obtain ⟨f⟩ := hf; exact Or.inl ⟨E.trans f⟩
  · obtain ⟨f⟩ := hf; exact Or.inr ⟨k, i1, i2, hk, hk2, Φ, ⟨E.trans f⟩⟩

/-- **Rows H-61, H-63, H-42 from the printed `ℂ`-form of the leaf and T11(b).** -/
theorem rows_of_C (hC : QMCentralizerCMC) (hR : ZInQ.LeafPush2.T11b_Rigidity) :
    HDec.HeckeRest.QMAutCard ∧ HDec.HeckeRest.ALFixedPoints ∧ HDec.FS5NoCM.CMOptimalEmbedding :=
  ⟨qmAutCard_of (qmCentralizerCM_of hC hR), alFixedPoints_of (qmCentralizerCM_of hC hR),
    cmOptimalEmbedding_of (qmCentralizerCM_of hC hR)⟩

end HDec.QMSplit.Aut

end -- noncomputable section

end QMSplit_QMAut

section QMSplit_STQM


/-!
# qm-split, row H-86: `STQM` from the Shimura–Taniyama descent theorem in published form

The row `STQM` (leafq-check, `scratch/leafq-check/CMDescendsGlue.lean` l.40 @ w54; not in the chain, so its
definition and `bcC` are copied verbatim below, in the same namespace context and with the same `open`s)
says: a QM surface over `ℂ` with CM by `ℤ[i]`, `ℤ[ζ₃]` or `ℤ[√−6]` is `A₀ ×_{ℚ̄,ιe} ℂ` for some `A₀/ℚ̄`.

The published theorem (`ShimuraTaniyamaQbar`, below): an abelian variety over `ℂ` whose `End⁰` contains a
field of degree `2 dim A` (complex multiplication) has a model over `ℚ̄`. The glue proved here: the CM
element `φ` (or `2φ − 1`) and `ι(i)` commute, square to `d ∈ {−1, −3, −6}` and `2`, and generate a copy of
the field `E_d = ℚ(√2)(√d)` of degree 4 inside `End⁰(A)`; `End⁰(A) = ℚ ⊗ End(A)` is nonzero because
`n ↦ n·1 = ι(n)` is injective and `ℚ` is flat over `ℤ`.

Check: `scratch/qm-split/chk.sh scratch/qm-split/STQM.lean`.
-/

set_option linter.all false

noncomputable section

namespace HDec.HSyn.G0Split.FibreQM.PeriodMapH
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open HSyn.G0Split.FibreQM

namespace QMSplitSTQM

/-! ## The row, copied verbatim (leafq-check `CMDescendsGlue.lean` l.26-43) -/

/-- `A₀ ×_{ℚ̄, ιe} ℂ`. -/
noncomputable abbrev bcC (ιe : Qbar →+* ℂ) (A₀ : PkgI3.AbVar Qbar) : PkgI3.AbVar ℂ :=
  @PkgI3.AbVar.baseChange Qbar _ A₀ ℂ _ ιe.toAlgebra

/-- **LEAF (Shimura–Taniyama, QM form).** A QM abelian surface over `ℂ` with CM by `ℤ[i]`, `ℤ[ζ₃]` or
`ℤ[√−6]` (an endomorphism `φ` commuting with `ι(𝒪)` with `φ² = −1`, `φ² − φ + 1 = 0` or `φ² = −6`) is
isomorphic, as an abelian variety, to `A₀ ×_{ℚ̄,ιe} ℂ` for some abelian variety `A₀/ℚ̄` and some
`ιe : ℚ̄ → ℂ`.

Published: an abelian variety over `ℂ` of CM type is isomorphic to the base change of an abelian variety
over a number field (Shimura–Taniyama, *Complex multiplication of abelian varieties*, 1961, §12.4;
Shimura, *Abelian varieties with complex multiplication and modular functions*, 1998, §12.4, Prop. 26;
UNVERIFIED numbers). It applies: `ι(i)` and `φ` commute, `ι(i)² = 2`, so `End⁰(A) ⊇ ℚ(√2, φ)`, a CM
field of degree `4 = 2 dim A`. A consequence of the published statement. -/
def STQM : Prop :=
  ∀ (A : PkgI3.AbVar ℂ) (q : QMStr A), A.dim = 2 → (HasCM4 q ∨ HasCM3 q ∨ HasCM24 q) →
    ∃ (ιe : Qbar →+* ℂ) (A₀ : PkgI3.AbVar Qbar) (e : PkgI3.AbVar.Hom (bcC ιe A₀) A)
      (e' : PkgI3.AbVar.Hom A (bcC ιe A₀)), e.hom ≫ e'.hom = 𝟙 _ ∧ e'.hom ≫ e.hom = 𝟙 _

/-! ## The published theorem -/

/-- **LEAF (Shimura–Taniyama: abelian varieties with complex multiplication are defined over `ℚ̄`).**
Let `A` be an abelian variety over `ℂ` (here of dimension 2) such that `End⁰(A) = ℚ ⊗ End(A)` contains a
field `E` with `[E : ℚ] = 2 dim A` (an injective `ℚ`-algebra map `E → End⁰(A)`). Then `A` is isomorphic to
`A₀ ×_{ℚ̄, ιe} ℂ` for an abelian variety `A₀` over `ℚ̄` and an embedding `ιe : ℚ̄ → ℂ`.

Sources: G. Shimura and Y. Taniyama, *Complex multiplication of abelian varieties and its applications to
number theory*, Publ. Math. Soc. Japan 6 (1961), §12.4, Prop. 26; G. Shimura, *Abelian varieties with
complex multiplication and modular functions*, Princeton 1998, §12.4, Prop. 26; J. S. Milne, *Complex
multiplication* (notes), §7 ("abelian varieties with CM over `ℂ` are defined over `ℚ^al`"); all numbers
UNVERIFIED (no network). Form: the printed statement with "CM" specialized to "a field of degree `2g` in
`End⁰`" and `g = 2`; the printed conclusion is a model over a number field `L ⊂ ℂ`, and the `ℚ̄`-form is
that model base-changed to the algebraic closure of `L` in `ℂ` (Milne prints the `ℚ^al` form). -/
def ShimuraTaniyamaQbar : Prop :=
  ∀ (A : PkgI3.AbVar ℂ), A.dim = 2 → ∀ (E : Type) [Field E] [Algebra ℚ E], Module.finrank ℚ E = 4 →
    (∃ f : E →ₐ[ℚ] PkgI3.AbVar.End0 A, Function.Injective f) →
    ∃ (ιe : Qbar →+* ℂ) (A₀ : PkgI3.AbVar Qbar) (e : PkgI3.AbVar.Hom (bcC ιe A₀) A)
      (e' : PkgI3.AbVar.Hom A (bcC ιe A₀)), e.hom ≫ e'.hom = 𝟙 _ ∧ e'.hom ≫ e.hom = 𝟙 _

/-! ## The fields `E_d = ℚ(√2)(√d)` -/

open Polynomial

abbrev K1 := AdjoinRoot (X ^ 2 - C (2 : ℚ))

instance factK1 : Fact (Irreducible (X ^ 2 - C (2 : ℚ))) := ⟨by
  apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
  intro b hb
  have : IsSquare (2 : ℚ) := ⟨b, by rw [← hb]; ring⟩
  rw [Rat.isSquare_iff] at this; norm_num at this⟩

theorem K1_finrank : Module.finrank ℚ K1 = 2 := by
  rw [(AdjoinRoot.powerBasis (X_pow_sub_C_ne_zero (by norm_num) _)).finrank]
  simp [AdjoinRoot.powerBasis_dim]

/-- The real embedding `√2 ↦ √2`. -/
def sig : K1 →+* ℝ := AdjoinRoot.lift (algebraMap ℚ ℝ) (Real.sqrt 2) (by simp [Real.sq_sqrt])

theorem K1_no_neg_sq (d : ℚ) (hd : d < 0) (b : K1) : b ^ 2 ≠ algebraMap ℚ K1 d := by
  intro h
  have := congrArg sig h
  rw [map_pow, eq_ratCast (algebraMap ℚ K1) d, map_ratCast] at this
  have : (0 : ℝ) ≤ (sig b) ^ 2 := sq_nonneg _
  have : (d : ℝ) < 0 := by exact_mod_cast hd
  linarith

abbrev Ed (d : ℚ) := AdjoinRoot (X ^ 2 - C (algebraMap ℚ K1 d))

theorem irr_d (d : ℚ) (hd : d < 0) : Irreducible (X ^ 2 - C (algebraMap ℚ K1 d)) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two (K1_no_neg_sq d hd)

theorem Ed_finrank (d : ℚ) [Fact (Irreducible (X ^ 2 - C (algebraMap ℚ K1 d)))] :
    Module.finrank ℚ (Ed d) = 4 := by
  rw [← Module.finrank_mul_finrank ℚ K1 (Ed d), K1_finrank,
    (AdjoinRoot.powerBasis (X_pow_sub_C_ne_zero (by norm_num) _)).finrank]
  simp [AdjoinRoot.powerBasis_dim]


/-! ## `End⁰(A)` is nonzero; the embedding `E_d → End⁰(A)` -/

section End0

open scoped TensorProduct IsMulCommutative

variable {A : PkgI3.AbVar ℂ}

theorem end0_nontrivial (q : QMStr A) : Nontrivial (PkgI3.AbVar.End0 A) := by
  let j : ℤ →ₗ[ℤ] PkgI3.AbVar.End A := LinearMap.toSpanSingleton ℤ _ 1
  have hj : Function.Injective j := by
    intro m n h
    have hO : (m : LeafQM.O) = (n : LeafQM.O) := by
      apply q.injective
      simp only [j, LinearMap.toSpanSingleton_apply] at h
      rw [map_intCast, map_intCast, ← zsmul_one, ← zsmul_one, h]
    have h' : ((m : LeafQM.O) : LeafQM.B) = ((n : LeafQM.O) : LeafQM.B) := congrArg Subtype.val hO
    have := congrArg QuaternionAlgebra.re h'
    simpa using this
  haveI : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := ℚ) j hj
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h1 : j.lTensor ℚ ((1 : ℚ) ⊗ₜ[ℤ] (1 : ℤ)) = 1 := by
    simp [j, LinearMap.lTensor_tmul]; rfl
  have h2 : (1 : ℚ) ⊗ₜ[ℤ] (1 : ℤ) = 0 := hinj (by rw [h1, map_zero]; exact h.symm)
  have := congrArg (TensorProduct.rid ℤ ℚ) h2
  simp at this


/-- **The field `E_d` inside `End⁰(A)`**: for `ψ ∈ End_𝒪(A)` with `ψ² = d < 0`, the map `√2 ↦ 1 ⊗ ι(i)`,
`√d ↦ 1 ⊗ ψ` is an injective `ℚ`-algebra map `E_d → End⁰(A)`. -/
theorem embed_Ed (q : QMStr A) (d : ℤ) (hd : d < 0) (ψ : PkgI3.AbVar.End A) (hψ : ψ ∈ com q)
    (hψψ : ψ * ψ = (d : PkgI3.AbVar.End A))
    [Fact (Irreducible (X ^ 2 - C (algebraMap ℚ K1 (d : ℚ))))] :
    ∃ f : Ed (d : ℚ) →ₐ[ℚ] PkgI3.AbVar.End0 A, Function.Injective f := by
  set α : PkgI3.AbVar.End0 A := (1 : ℚ) ⊗ₜ[ℤ] q.iota oI
  set β : PkgI3.AbVar.End0 A := (1 : ℚ) ⊗ₜ[ℤ] ψ
  have hαα : α * α = algebraMap ℚ (PkgI3.AbVar.End0 A) 2 := by
    simp only [α, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, ← map_mul, oI_sq, map_add, map_one,
      TensorProduct.tmul_add, ← Algebra.TensorProduct.one_def, map_ofNat]
    exact one_add_one_eq_two
  have hββ : β * β = algebraMap ℚ (PkgI3.AbVar.End0 A) (d : ℚ) := by
    simp only [β, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, hψψ,
      Algebra.TensorProduct.algebraMap_apply]
    rw [← zsmul_one, ← TensorProduct.smul_tmul]
    simp [zsmul_eq_mul]
  have hαβ : α * β = β * α := by
    have hc : q.iota oI * ψ = ψ * q.iota oI := by
      rw [com, Subring.mem_centralizer_iff] at hψ
      exact hψ _ ⟨oI, rfl⟩
    simp only [α, β, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, hc]
  set S := Algebra.adjoin ℚ ({α, β} : Set (PkgI3.AbVar.End0 A))
  haveI hS : IsMulCommutative S := by
    apply Algebra.isMulCommutative_adjoin
    intro x hx y hy _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hαβ
    · exact hαβ.symm
    · exact Commute.refl _
  letI cS : CommRing S := { (inferInstance : Ring S) with mul_comm := fun x y => hS.is_comm.comm x y }
  let αS : S := ⟨α, Algebra.subset_adjoin (by simp)⟩
  let βS : S := ⟨β, Algebra.subset_adjoin (by simp)⟩
  have hα2 : αS ^ 2 = algebraMap ℚ S 2 := Subtype.ext (by
    change α ^ 2 = algebraMap ℚ (PkgI3.AbVar.End0 A) 2; rw [sq, hαα])
  have hβ2 : βS ^ 2 = algebraMap ℚ S (d : ℚ) := Subtype.ext (by
    change β ^ 2 = algebraMap ℚ (PkgI3.AbVar.End0 A) (d : ℚ); rw [sq, hββ])
  let i₁ : K1 →+* S := AdjoinRoot.lift (algebraMap ℚ S) αS (by
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, hα2, sub_self])
  have hi : i₁ (algebraMap ℚ K1 (d : ℚ)) = algebraMap ℚ S (d : ℚ) :=
    RingHom.congr_fun (RingHom.ext_rat (i₁.comp (algebraMap ℚ K1)) (algebraMap ℚ S)) _
  let f₀ : Ed (d : ℚ) →+* S := AdjoinRoot.lift i₁ βS (by
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, hi, hβ2, sub_self])
  let f : Ed (d : ℚ) →+* PkgI3.AbVar.End0 A := S.val.toRingHom.comp f₀
  haveI := end0_nontrivial q
  exact ⟨f.toRatAlgHom, f.injective⟩

/-- **Row H-86 from the published theorem.** -/
theorem stqm_of (h : ShimuraTaniyamaQbar) : STQM := by
  intro A q hA hCM
  obtain ⟨d, hd, ψ, hψ, hψψ⟩ :
      ∃ d : ℤ, d < 0 ∧ ∃ ψ ∈ com q, ψ * ψ = (d : PkgI3.AbVar.End A) := by
    rcases hCM with ⟨φ, hφ, h4⟩ | ⟨φ, hφ, h3⟩ | ⟨φ, hφ, h24⟩
    · exact ⟨-1, by norm_num, φ, hφ, by rw [h4]; simp⟩
    · refine ⟨-3, by norm_num, φ + φ - 1, (com q).sub_mem ((com q).add_mem hφ hφ) (com q).one_mem, ?_⟩
      have hφφ : φ * φ = φ - 1 := by
        rw [← sub_eq_zero, ← h3]; abel
      have e : (φ + φ - 1) * (φ + φ - 1) = -(1 + 1 + 1) := by
        simp only [add_mul, mul_add, sub_mul, mul_sub, _root_.one_mul, _root_.mul_one, hφφ]
        abel
      rw [e]; push_cast; norm_num
    · exact ⟨-6, by norm_num, φ, hφ, by rw [h24]; simp⟩
  haveI : Fact (Irreducible (X ^ 2 - C (algebraMap ℚ K1 (d : ℚ)))) := ⟨irr_d d (by exact_mod_cast hd)⟩
  obtain ⟨f, hf⟩ := embed_Ed q d hd ψ hψ hψψ
  exact h A hA (Ed (d : ℚ)) (Ed_finrank (d : ℚ)) ⟨f, hf⟩

end End0

end QMSplitSTQM

end HDec.HSyn.G0Split.FibreQM.PeriodMapH

end -- noncomputable section

end QMSplit_STQM

section QMSplit_ThetaSplit


/-!
# qm-split, row H-2: `PkgI1.ThetaModularity` split into Igusa's two printed statements

The row (`HDec.PkgI1.ThetaModularity`, leaf-fold4 chain `LPrefix.lean` l.295; imported) is the conjunction
of two transformation laws. Igusa prints them as the modularity of two Siegel modular forms of degree 2 with
their theta expressions: `ψ₄ = 2⁻² Σ_{m even} θ_m⁸` (weight 4) and `χ₁₀ = −2⁻¹⁴ ∏_{m even} θ_m²` (weight 10),
both for `Γ₂ = Sp₄(ℤ)` with trivial character. The two leaves below are those statements in Igusa's
normalization; the row follows by clearing the constants.

Check: `scratch/qm-split/chk.sh scratch/qm-split/ThetaSplit.lean`.
-/

set_option linter.all false

noncomputable section

namespace HDec.QMSplit.Theta

open HDec.PkgI1

/-- `ψ₄ = 2⁻² Σ_{m even} θ_m⁸` (Igusa's normalization). -/
def psi4 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := (1 / 4 : ℂ) * thetaSum8 Ω

/-- `χ₁₀ = −2⁻¹⁴ ∏_{m even} θ_m²` (Igusa's normalization). -/
def chi10 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := (-1 / 2 ^ 14 : ℂ) * thetaProd2 Ω

/-- **LEAF (Igusa: `ψ₄` is a Siegel modular form of weight 4 for `Sp₄(ℤ)`, with its theta expression).**
`ψ₄(Ω) = 2⁻² Σ_{m even} θ_m(Ω)⁸` satisfies `ψ₄(M·Ω) = det(CΩ + D)⁴ ψ₄(Ω)` for `M = [[A,B],[C,D]] ∈ Sp₄(ℤ)`
and `Ω` in the Siegel upper half-space of degree 2.

Source: J.-I. Igusa, *On Siegel modular forms of genus two*, Amer. J. Math. 84 (1962), 175-200, and
*On Siegel modular forms of genus two (II)*, Amer. J. Math. 86 (1964), 392-412 (the Eisenstein series
`ψ₄` and its expression `2⁻² Σ θ_m⁸`); *Modular forms and projective invariants*, Amer. J. Math. 89
(1967), 817-855, pp. 833-834, 848 (the row's locators; page numbers UNVERIFIED, no network). The sign
conventions of `spAct`/`spFactor` and Mathlib's `symplecticGroup` (`J = [[0, −1], [1, 0]]`, the same
group as `[[0, 1], [−1, 0]]`) were checked numerically by leaf-review-a (`theta_mod_check.py`).
Form: the printed modularity of `ψ₄` with its theta expression (published form, with the caveat that
Igusa defines `ψ₄` as an Eisenstein series and prints the theta expression as a theorem; the
transformation law of the theta expression is then the conjunction, read off the same text). -/
def IgusaPsi4 : Prop :=
  ∀ M ∈ Matrix.symplecticGroup (Fin 2) ℤ, ∀ Ω ∈ SiegelH2,
    psi4 (spAct M Ω) = spFactor M Ω ^ 4 * psi4 Ω

/-- **LEAF (Igusa: `χ₁₀` is a Siegel cusp form of weight 10 for `Sp₄(ℤ)`, with its theta expression).**
`χ₁₀(Ω) = −2⁻¹⁴ ∏_{m even} θ_m(Ω)²` satisfies `χ₁₀(M·Ω) = det(CΩ + D)¹⁰ χ₁₀(Ω)` for `M ∈ Sp₄(ℤ)`
(trivial character).

Source: Igusa, Amer. J. Math. 84 (1962) (the cusp form `χ₁₀` and `χ₁₀ = −2⁻¹⁴ ∏ θ_m²`); Amer. J. Math. 89
(1967), p. 848 (page UNVERIFIED). Form: as for `IgusaPsi4`. -/
def IgusaChi10 : Prop :=
  ∀ M ∈ Matrix.symplecticGroup (Fin 2) ℤ, ∀ Ω ∈ SiegelH2,
    chi10 (spAct M Ω) = spFactor M Ω ^ 10 * chi10 Ω

/-- **Row H-2 from the two printed statements** (clear the constants `2⁻²`, `−2⁻¹⁴`). -/
theorem thetaModularity_of (h4 : IgusaPsi4) (h10 : IgusaChi10) : ThetaModularity := by
  intro M hM Ω hΩ
  have a := h4 M hM Ω hΩ
  have b := h10 M hM Ω hΩ
  simp only [psi4, chi10] at a b
  constructor
  · linear_combination 4 * a
  · linear_combination (-(2 : ℂ) ^ 14) * b

end HDec.QMSplit.Theta

end -- noncomputable section

end QMSplit_ThetaSplit

section QMSplit_ModuliSplit


/-!
# qm-split, rows H-1 `R1R2fpRep`, H-20 `r1b`, H-43 `X6ConicModel`, H-59 `Y3Connected`: witness splits

These four rows are statements about *one* witness `(Y, Φ, X, Ψ, fY, π₆)` of the moduli problems
(`Y₃` fine, `X₆` coarse), with several clauses. A published theorem is a statement about the canonical
model; to state the parts separately, each clause is stated here for *every* witness of the defining
property `R1fpProps` (resp. `X6Props`). Each such universal Prop is

* the published statement about the canonical model (named in its docstring), **and**
* the transport of that statement to an arbitrary witness, through the comparison isomorphism of two
  witnesses of `R1fpProps` (qm-pin §3.3: `R1univProps` both ways gives inverse morphisms, identity on all
  field points, hence identity), or the uniqueness of the coarse space given `fY`.

So the universal Props are GLUE (consequence of one published statement + a transport the project owes),
except `CanonicalModelY3` (existence, the published representability statement). The rows are proved here
from them; the proofs are logical assembly (no new mathematics). Check:
`scratch/qm-split/chk.sh scratch/qm-split/ModuliSplit.lean`.
-/

set_option linter.all false

noncomputable section

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-! ## Shared leaf -/

/-- **LEAF (representability of the level-3 QM moduli problem; the canonical model `Y₃ = Sh_{K₃}`).** Some
`ℚ`-scheme `Y` with bijections `Φ : Y(K) ≃ M3(K)` satisfies the clause list `R1fpProps` (proper, smooth of
relative dimension 1, a `ℚ̄`-point, naturality, a universal family `R1famProps`, universality
`R1univProps`). Shimura, Ann. of Math. 85 (1967), Main Thms I-II; Deligne, Sém. Bourbaki 389 (1971),
Thm 4.21, Cor. 5.7 (canonical models of PEL type; fine moduli at the neat level `K₃ = (1 + 3𝒪̂)^×`); with
Lemma QP for the polarization (rv-qm-polar). Locators UNVERIFIED; the audit calls R1 a "qualified
consequence" (the specialization of Deligne's PEL model to this functor needs a human check). -/
def CanonicalModelY3 : Prop := ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ

/-! ## H-1 `R1R2fpRep` -/

/-- **GLUE (project; Yoneda).** On a fine moduli witness, `Aut(𝒪)`-twists and right multiplication by
`𝒪^×` on level structures are induced by automorphisms of `Y`: apply `R1univProps` to the twisted universal
family (both ways) and use that a morphism inducing the identity on all field points is the identity. -/
def HeckeOfFine : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ → R1heckeProps Y Φ

/-- **GLUE (coarse space `X₆ = Y₃/G` and its geometric connectedness).** For a fine witness, there are a
coarse witness `X` of the QM pairs, `fY : Y → X` (the forgetful map, surjective on `ℚ̄`-points) and `X` is
geometrically connected. Needs: the quotient of a projective curve by a finite group (SGA 1, Exp. V,
Prop. 1.8; Mumford, *Abelian varieties*, §7 Thm), its moduli interpretation on `ℚ̄`-points, and
`π₀(X₆ ⊗ ℚ̄) = ℤ̂^×/nrd(𝒪̂^×) = 1` (Deligne, Bourbaki 389, §2; Shimura 1967); locators UNVERIFIED. -/
def CoarseX6OfFine : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ → R1heckeProps Y Φ →
    ∃ (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
      (fY : Y ⟶ X), X6Props Y Φ X Ψ fY ∧ (∀ x : fieldPt Qbar ⟶ X, ∃ y : fieldPt Qbar ⟶ Y, y ≫ fY = x) ∧
        LeafAdopt.R1pi0Props X

/-- **GLUE (the Hauptmodul of `X₆/W`, Baba–Granath).** For a coarse witness `X`, there is `π₆ : X → P¹`
whose fibres on `ℚ̄`-points are the `Aut(𝒪)`-twist classes, with `0, ∞, −16/27` exactly at CM by `ℤ[i]`,
`ℤ[ζ₃]`, `ℤ[√−6]`, surjective on `ℚ̄`-points. Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 and §3.1
(`X₆/W ≅ P¹_ℚ`, the three branch points), normalized by a Möbius map; transport to the witness `X`.
Locators UNVERIFIED. -/
def HauptmodulOfX6 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    R1fpProps Y Φ → X6Props Y Φ X Ψ fY →
      ∃ π₆ : ToP1 X.left, LeafAdopt.R2X6PropsIff X Ψ π₆ ∧
        ∀ t : OnePoint Qbar, ∃ x : fieldPt Qbar ⟶ X, π₆.val (K := Qbar) x.left = t

/-- **GLUE (Shimura reciprocity at the CM points; R1rec).** On a fine witness, the residue field of a
`ℚ̄`-point with CM by `ℤ[i]`, `ℤ[ζ₃]` or `ℤ[√−6]` is unramified above 5. Shimura, *Introduction to the
arithmetic theory of automorphic functions*, 1971, Thm 9.6 / Shimura 1967 Main Thm II (reciprocity on the
canonical model: the field of moduli lies in the ray class field of conductor 3), transported. -/
def ReciprocityOfFine : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ → R1recProps Y Φ

/-- **GLUE (residue fields of CM points on `X₆`; R5).** González–Rotger, J. Math. Soc. Japan 58 (2006),
Thm 5.12 (fields of definition of CM points on `X₀^D(N)`), transported to every coarse witness. -/
def ResidueOfX6 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    R1fpProps Y Φ → X6Props Y Φ X Ψ fY → R5ptProps X Ψ

/-- **Row H-1 from the split.** -/
theorem r1r2fpRep_of (hE : CanonicalModelY3) (hH : HeckeOfFine) (hX : CoarseX6OfFine)
    (hP : HauptmodulOfX6) (hR : ReciprocityOfFine) (h5 : ResidueOfX6) : LeafAdopt.R1R2fpRep := by
  obtain ⟨Y, Φ, h1⟩ := hE
  have hh := hH Y Φ h1
  obtain ⟨X, Ψ, fY, h6, hsurj, hpi0⟩ := hX Y Φ h1 hh
  obtain ⟨π₆, h2, ht⟩ := hP Y Φ X Ψ fY h1 h6
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hR Y Φ h1, ⟨ht, hsurj⟩, h5 Y Φ X Ψ fY h1 h6, hpi0⟩

/-! ## H-59 `Y3Connected` -/

/-- **GLUE (connectedness of `Y₃` over `ℚ`).** Every fine witness is connected. Published content: the
geometric components of `Sh_K` are `ℚ^×_{>0}\𝔸_f^×/nrd(K)`, with `Gal(ℚ̄/ℚ)` acting through the cyclotomic
character (Deligne, Bourbaki 389, §§2-3; *Variétés de Shimura*, 1979, Thm 2.6.3; Milne, *Introduction to
Shimura varieties*, §13); for `K₃` two geometric components swapped by `Gal(ℚ(√−3)/ℚ)`. Transport to a
witness: the chain's `exists_surjective_of_R1fp` (compiled), as in `TSHecke.connectedSpace_of_R1fp`. -/
def ConnectedOfFine : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ → ConnectedSpace Y.left

/-- **Row H-59 from the split.** -/
theorem y3Connected_of (hE : CanonicalModelY3) (hC : ConnectedOfFine) : TSHecke.Y3Connected := by
  obtain ⟨Y, Φ, h1⟩ := hE
  exact ⟨Y, Φ, h1, hC Y Φ h1⟩

/-- Conversely (compiled in the chain): `Y3Connected` gives `ConnectedOfFine`, so the split is an
equivalence given the shared leaf. -/
theorem connectedOfFine_of (h : TSHecke.Y3Connected) : ConnectedOfFine :=
  fun _ _ h1 => TSHecke.connectedSpace_of_R1fp h h1

/-! ## H-20 `r1b` -/

/-- **LEAF candidate (Shimura's complex uniformization, family form, composed with every algebraic map to
`P¹`).** Some fine witness `(Y, Φ)` carries `τ ↦ y_τ ∈ Y(ℂ)` with the object at `y_τ` equal to
`ℂ²/ι(𝒪)(τ,1)ᵀ` with its `ι` (`IsR1bFamily`), and `τ ↦ π(y_τ)` continuous and holomorphic into `P¹(ℂ)` for
every `π : Y → P¹`. Shimura, Ann. of Math. 85 (1967), Main Thm I (the holomorphic `φ : ℍ → V(ℂ)`); Deligne,
Bourbaki 389, §4.15 (analytic families); the composition with an algebraic `π` is holomorphic (algebraic maps
are holomorphic on the analytification; GAGA level). Locators UNVERIFIED; the "every `π`" reading is a
consequence of the printed statement plus that composition step (flag). -/
def ShimuraFamily : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧
    ∀ π : ToP1 Y.left, HSyn.G0Split.FibreQM.R1bFamily Y Φ π

/-- **GLUE (project; transport of the family between fine witnesses).** If one fine witness carries the
family for every `π`, so does every other: the comparison isomorphism `g : Y' ≅ Y` (qm-pin §3.3) carries
`y_τ` to `y_τ ≫ g⁻¹`, and `π' ∘ g⁻¹` is a map `Y → P¹` (`ToP1.comp`). -/
def R1bTransport : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (Y' : Over (Spec (CommRingCat.of ℚ)))
    (Φ' : PtEquiv Y'), R1fpProps Y Φ → R1fpProps Y' Φ' →
    (∀ π : ToP1 Y.left, HSyn.G0Split.FibreQM.R1bFamily Y Φ π) →
    ∀ π' : ToP1 Y'.left, HSyn.G0Split.FibreQM.R1bFamily Y' Φ' π'

/-- **Row H-20 from the split** (the research field `r1b` of C4''). -/
theorem r1b_of (hS : ShimuraFamily) (hT : R1bTransport) :
    ∀ h : LeafAdopt.R1R2fpRep,
      HSyn.G0Split.FibreQM.R1bFamily (HSyn.G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
        (HSyn.G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
        (HSyn.G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h)) := by
  intro h
  obtain ⟨Y, Φ, h1, hall⟩ := hS
  exact hT Y Φ _ _ h1 (HSyn.G0Split.FibreQM.own_spec _).1 hall _

/-! ## H-43 `X6ConicModel` -/

/-- **GLUE (the conic model of `X₆`).** For every witness of the leaf bundle's clause list, `X` is, on
`ℚ̄`-points and Galois-equivariantly, the conic `Y² + 3X² + 3Z² = 0` with `π₆ = −16(X² + Z²)/(27Z²)`.
Published: Kurihara, J. Fac. Sci. Univ. Tokyo 25 (1979) (`X₀(6,1) : x² + y² + 3 = 0`); Elkies, ANTS-III,
LNCS 1423 (1998), §3 (the coordinate `t` on `X*(6)` and `X₆ = X*(6)(√−t, √(3(t − 1)))`); locators
UNVERIFIED. Transport to the witness: the isomorphism of the witness with the canonical model (uniqueness of
the coarse space with `fY`; CurveBijIso-type glue, H-85). Alternative derivation from the clause list alone
(leaf-review-a §5.11): Kummer theory of the `(ℤ/2)²`-cover `X₆ → X₆/W ≅ P¹` branched at the three CM values,
with the residue fields `ℚ(i)`, `ℚ(√−3)` from R5. -/
def ConicOfWitness : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    FS5NoCM.R1R2fpFullProps Y Φ X Ψ fY π₆ → X6Kummer.ConicModel X π₆

/-- **Row H-43 from the bundle leaf `r1r2` (H-1) and the conic glue.** -/
theorem x6ConicModel_of (hR : LeafAdopt.R1R2fpRep) (hC : ConicOfWitness) : X6Kummer.X6ConicModel := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h⟩ := LeafAdopt.R1R2fp_of_rep hR
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h, hC Y Φ X Ψ fY π₆ h⟩

/-! ## The comparison isomorphism of fine witnesses; `HeckeOfFine` and `R1bTransport` proved

Reducedness of smooth schemes over a domain: copied verbatim from model-glue
(`scratch/model-glue/ModelGlue5.lean`, Parts 12 and 15 @ av-glue's worktree), itself from smooth-fibre. -/

section Comparison

open CategoryTheory AlgebraicGeometry Limits

/-- An étale algebra over a domain is reduced (copied verbatim from task smooth-fibre,
`ZInQKernel/Contrib/SmoothFibre/Basic.lean`, `ZInQ.SmoothFibre.isReduced_of_etale_of_isDomain`). -/
theorem isReduced_of_etale_of_isDomain' (P S : Type*) [CommRing P] [IsDomain P] [CommRing S]
    [Algebra P S] [Algebra.Etale P S] : IsReduced S := by
  let K := FractionRing P
  let f := Algebra.TensorProduct.includeRight (R := P) (A := K) (B := S)
  have hinj : Function.Injective f := by
    have : ⇑f = (LinearMap.rTensor S (Algebra.ofId P K).toLinearMap).comp
        (Algebra.TensorProduct.lid P S).symm.toLinearMap := by
      ext x; simp [f]
    rw [this]
    exact (Module.Flat.rTensor_preserves_injective_linearMap _
      (IsFractionRing.injective P K)).comp (Algebra.TensorProduct.lid P S).symm.injective
  have : IsReduced (TensorProduct P K S) := Algebra.FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective (f : S →+* TensorProduct P K S) hinj

/-- A smooth algebra over a domain is reduced (the proof of smooth-fibre's
`isReduced_of_smooth_of_field`, with a domain in place of a field). -/
theorem isReduced_of_smooth_of_isDomain (k A : Type*) [CommRing k] [IsDomain k] [CommRing A]
    [Algebra k A] [Algebra.Smooth k A] : IsReduced A := by
  refine ⟨fun x hx => ?_⟩
  by_contra hne
  let I : Ideal A := (Ideal.span {x} : Submodule A A).annihilator
  have hI : I ≠ ⊤ := by
    intro h
    have h1 : (1 : A) ∈ I := h ▸ Submodule.mem_top
    rw [Submodule.mem_annihilator_span_singleton, one_smul] at h1
    exact hne h1
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hI
  have := hm.isPrime
  have : Algebra.IsSmoothAt k m := inferInstance
  obtain ⟨f, hf, n, inst, -, hst⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := m)
  have : IsReduced (Localization.Away f) :=
    isReduced_of_etale_of_isDomain' (MvPolynomial (Fin n) k) _
  have h0 : algebraMap A (Localization.Away f) x = 0 := (hx.map _).eq_zero
  obtain ⟨⟨_, k', rfl⟩, hk⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f) x).1 h0
  apply hf
  apply hm.isPrime.mem_of_pow_mem k'
  apply hle
  rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  exact hk

/-- A smooth scheme over a domain is reduced. -/
theorem isReduced_of_smooth_domain {R : CommRingCat.{0}} [IsDomain R] {X : Scheme.{0}}
    (f : X ⟶ Spec R) [Smooth f] : IsReduced X := by
  refine @IsReduced.of_openCover X X.affineCover (fun i => ?_)
  have hsm : Smooth (X.affineCover.f i ≫ f) := inferInstance
  have hring := (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp hsm
  letI := ((X.affineCover.f i ≫ f).appTop).hom.toAlgebra
  haveI : Algebra.Smooth Γ(Spec R, ⊤) Γ(X.affineCover.X i, ⊤) :=
    RingHom.smooth_algebraMap.1 hring
  haveI : _root_.IsReduced Γ(X.affineCover.X i, ⊤) :=
    isReduced_of_smooth_of_isDomain Γ(Spec R, ⊤) _
  exact isReduced_of_isAffine_isReduced _


/-- **A self-map of a fine witness fixing every field point is the identity** (`Y` is reduced, being smooth
over `ℚ`, and separated, being proper; two maps agreeing on all residue-field points agree). -/
theorem eq_id_of_fieldPts {Y : Over (Spec (CommRingCat.of ℚ))} (hP : IsProper Y.hom)
    (hS : SmoothOfRelativeDimension 1 Y.hom) (h : Y ⟶ Y)
    (hpt : ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y), y ≫ h = y) : h = 𝟙 Y := by
  haveI : Smooth Y.hom := hS.smooth
  haveI : IsReduced Y.left := isReduced_of_smooth_domain Y.hom
  apply Over.OverMorphism.ext
  refine ext_of_fromSpecResidueField_eq h.left (𝟙 _) Y.hom Set.univ dense_univ ?_ (by simp)
  intro x _
  let φ : CommRingCat.of ℚ ⟶ Y.left.residueField x :=
    Spec.preimage (Y.left.fromSpecResidueField x ≫ Y.hom)
  letI : Algebra ℚ (Y.left.residueField x) := φ.hom.toAlgebra
  let y : fieldPt (Y.left.residueField x) ⟶ Y :=
    Over.homMk (Y.left.fromSpecResidueField x) (by
      change _ = Spec.map φ
      exact (Spec.map_preimage _).symm)
  have := congrArg CommaMorphism.left (hpt _ y)
  exact this

theorem eq_id_of_Φ {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} (h1 : R1fpProps Y Φ) (h : Y ⟶ Y)
    (hpt : ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y), Φ K (y ≫ h) = Φ K y) : h = 𝟙 Y :=
  eq_id_of_fieldPts h1.1 h1.2.1 h fun K _ _ y => (Φ K).injective (hpt K y)

/-- **The comparison isomorphism of two fine witnesses** (qm-pin §3.3, compiled here): `R1univProps` both
ways gives `g : Y' → Y` and `g' : Y → Y'` compatible with the moduli bijections; both composites fix every
field point, hence are identities. -/
theorem compare_iso {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    (h : R1fpProps Y Φ) (h' : R1fpProps Y' Φ') :
    ∃ g : Y' ≅ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'),
      Φ' K y = Φ K (y ≫ g.hom) := by
  obtain ⟨g, hg⟩ := LeafQM.AV.Pin.phi_part (LeafQM.AV.Pin.R1fpProps.univ h) h'
  obtain ⟨g', hg'⟩ := LeafQM.AV.Pin.phi_part (LeafQM.AV.Pin.R1fpProps.univ h') h
  have e1 : g' ≫ g = 𝟙 Y := eq_id_of_Φ h _ fun K _ _ y => by
    rw [← Category.assoc, ← hg K (y ≫ g'), ← hg' K y]
  have e2 : g ≫ g' = 𝟙 Y' := eq_id_of_Φ h' _ fun K _ _ y => by
    rw [← Category.assoc, ← hg' K (y ≫ g), ← hg K y]
  exact ⟨⟨g, g', e2, e1⟩, hg⟩

variable {K : Type} [Field K]

set_option maxHeartbeats 2000000 in
/-- `((P.twist α).twist α.symm) ≅ P`. -/
def isoTwistSymm (P : QML3 K) (α : O ≃+* O) : ((P.twist α).twist α.symm).Iso P :=
  { φ := (QML3.Iso.refl P).φ
    ψ := (QML3.Iso.refl P).ψ
    left := (QML3.Iso.refl P).left
    right := (QML3.Iso.refl P).right
    equivariant := fun a => by
      have h : ((P.twist α).twist α.symm).q.iota a = P.q.iota a := by
        show P.q.iota (α (α.symm a)) = P.q.iota a
        rw [RingEquiv.apply_symm_apply]
      rw [h]; exact (QML3.Iso.refl P).equivariant a
    level := fun a => by
      have h : ((P.twist α).twist α.symm).e.eta a = P.e.eta a := by
        show P.e.eta (α (α.symm a)) = P.e.eta a
        rw [RingEquiv.apply_symm_apply]
      rw [h]; exact (QML3.Iso.refl P).level a }

theorem M3.twist_symm_twist (α : O ≃+* O) (c : M3 K) : M3.twist α.symm (M3.twist α c) = c := by
  induction c using Quotient.inductionOn with
  | h P => exact Quotient.sound ⟨isoTwistSymm P α⟩

theorem M3.twist_twist_symm (α : O ≃+* O) (c : M3 K) : M3.twist α (M3.twist α.symm c) = c := by
  have := M3.twist_symm_twist α.symm c
  rwa [RingEquiv.symm_symm] at this

set_option maxHeartbeats 2000000 in
/-- `P.rightMul 1 ≅ P`. -/
def isoRightMulOne (P : QML3 K) : (P.rightMul 1).Iso P :=
  { φ := (QML3.Iso.refl P).φ
    ψ := (QML3.Iso.refl P).ψ
    left := (QML3.Iso.refl P).left
    right := (QML3.Iso.refl P).right
    equivariant := fun a => (QML3.Iso.refl P).equivariant a
    level := fun a => by
      have h : (P.rightMul 1).e.eta a = P.e.eta a := by
        show P.e.eta (a * ((1 : Oˣ) : O)) = P.e.eta a
        rw [Units.val_one, _root_.mul_one]
      rw [h]; exact (QML3.Iso.refl P).level a }

theorem M3.rightMul_inv (u : Oˣ) (c : M3 K) : M3.rightMul u⁻¹ (M3.rightMul u c) = c := by
  rw [M3.rightMul_rightMul, inv_mul_cancel]
  induction c using Quotient.inductionOn with
  | h P => exact Quotient.sound ⟨isoRightMulOne P⟩

theorem M3.rightMul_inv' (u : Oˣ) (c : M3 K) : M3.rightMul u (M3.rightMul u⁻¹ c) = c := by
  have := M3.rightMul_inv u⁻¹ c
  rwa [inv_inv] at this

/-- From a self-map `g` of a fine witness inducing a bijection `τ` on classes with inverse induced by `g'`,
an automorphism. -/
theorem iso_of_pair {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} (h1 : R1fpProps Y Φ)
    (τ τ' : ∀ (K : Type) [Field K], M3 K → M3 K)
    (hττ' : ∀ (K : Type) [Field K] (c : M3 K), τ' K (τ K c) = c)
    (hτ'τ : ∀ (K : Type) [Field K] (c : M3 K), τ K (τ' K c) = c)
    (g g' : Y ⟶ Y)
    (hg : ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y), Φ K (y ≫ g) = τ K (Φ K y))
    (hg' : ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y), Φ K (y ≫ g') = τ' K (Φ K y)) :
    ∃ e : Y ≅ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y),
      Φ K (y ≫ e.hom) = τ K (Φ K y) := by
  have e1 : g ≫ g' = 𝟙 Y := eq_id_of_Φ h1 _ fun K _ _ y => by
    rw [← Category.assoc, hg' K (y ≫ g), hg K y, hττ']
  have e2 : g' ≫ g = 𝟙 Y := eq_id_of_Φ h1 _ fun K _ _ y => by
    rw [← Category.assoc, hg K (y ≫ g'), hg' K y, hτ'τ]
  exact ⟨⟨g, g', e1, e2⟩, hg⟩

/-- A family twisted by `α` (on `ι` and on `η`). -/
def twistFam {S : Scheme.{0}} (𝒜 : QMFamily S) (α : O ≃+* O) : QMFamily S where
  F := 𝒜.F
  proper := 𝒜.proper
  smooth := 𝒜.smooth
  iota a := 𝒜.iota (α a)
  iota_over a := 𝒜.iota_over (α a)
  eta a := 𝒜.eta (α a)
  eta_sec a := 𝒜.eta_sec (α a)

/-- A family with `η` right-multiplied by `u`. -/
def rightMulFam {S : Scheme.{0}} (𝒜 : QMFamily S) (u : Oˣ) : QMFamily S where
  F := 𝒜.F
  proper := 𝒜.proper
  smooth := 𝒜.smooth
  iota := 𝒜.iota
  iota_over := 𝒜.iota_over
  eta a := 𝒜.eta (a * u)
  eta_sec a := 𝒜.eta_sec (a * u)

theorem isFibre_twist {S : Scheme.{0}} {𝒜 : QMFamily S} {L : Type} [Field L]
    {y : Spec (CommRingCat.of L) ⟶ S} {P : QML3 L} (h : IsFibreOf 𝒜 y P) (α : O ≃+* O) :
    IsFibreOf (twistFam 𝒜 α) y (P.twist α) := by
  obtain ⟨g, hpb, hι, hη⟩ := h
  exact ⟨g, hpb, fun a => hι (α a), fun a => hη (α a)⟩

theorem isFibre_rightMul {S : Scheme.{0}} {𝒜 : QMFamily S} {L : Type} [Field L]
    {y : Spec (CommRingCat.of L) ⟶ S} {P : QML3 L} (h : IsFibreOf 𝒜 y P) (u : Oˣ) :
    IsFibreOf (rightMulFam 𝒜 u) y (P.rightMul u) := by
  obtain ⟨g, hpb, hι, hη⟩ := h
  exact ⟨g, hpb, hι, fun a => hη (a * u)⟩

/-- The self-map classifying a modified universal family. -/
theorem classify {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} (h1 : R1fpProps Y Φ)
    (𝒜 : QMFamily Y.left)
    (h𝒜 : ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y) (P : QML3 K),
      Φ K y = M3.mk P → IsFibreOf 𝒜 y.left P)
    (𝒜' : QMFamily Y.left) (τ : ∀ (K : Type) [Field K], QML3 K → QML3 K)
    (hτ : ∀ (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ Y.left) (P : QML3 K),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜' y (τ K P)) :
    ∃ g : Y ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y) (P : QML3 K),
      Φ K y = M3.mk P → Φ K (y ≫ g) = M3.mk (τ K P) := by
  have hall : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ Y), ∃ P : QML3 K,
      IsFibreOf 𝒜' s.left P := by
    intro K _ _ s
    obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ K s)
    exact ⟨τ K P, hτ K s.left P (h𝒜 K s P hP.symm)⟩
  obtain ⟨g, hg⟩ := (LeafQM.AV.Pin.R1fpProps.univ h1) Y h1.1 h1.2.1 𝒜' hall
  exact ⟨g, fun K _ _ y P hP => hg K y (τ K P) (hτ K y.left P (h𝒜 K y P hP))⟩

/-- **`HeckeOfFine` is a theorem.** -/
theorem heckeOfFine_proof : HeckeOfFine := by
  intro Y Φ h1
  obtain ⟨𝒜, h𝒜⟩ := h1.2.2.2.2.1
  refine ⟨fun α => ?_, fun u => ?_⟩
  · obtain ⟨g, hg⟩ := classify h1 𝒜 h𝒜 (twistFam 𝒜 α) (fun _ _ P => P.twist α)
      (fun _ _ y P h => isFibre_twist h α)
    obtain ⟨g', hg'⟩ := classify h1 𝒜 h𝒜 (twistFam 𝒜 α.symm) (fun _ _ P => P.twist α.symm)
      (fun _ _ y P h => isFibre_twist h α.symm)
    refine iso_of_pair h1 (fun K _ => M3.twist α) (fun K _ => M3.twist α.symm)
      (fun K _ c => M3.twist_symm_twist α c) (fun K _ c => M3.twist_twist_symm α c) g g' ?_ ?_
    · intro K _ _ y
      obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ K y)
      rw [hg K y P hP.symm, ← hP]; rfl
    · intro K _ _ y
      obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ K y)
      rw [hg' K y P hP.symm, ← hP]; rfl
  · obtain ⟨g, hg⟩ := classify h1 𝒜 h𝒜 (rightMulFam 𝒜 u) (fun _ _ P => P.rightMul u)
      (fun _ _ y P h => isFibre_rightMul h u)
    obtain ⟨g', hg'⟩ := classify h1 𝒜 h𝒜 (rightMulFam 𝒜 u⁻¹) (fun _ _ P => P.rightMul u⁻¹)
      (fun _ _ y P h => isFibre_rightMul h u⁻¹)
    refine iso_of_pair h1 (fun K _ => M3.rightMul u) (fun K _ => M3.rightMul u⁻¹)
      (fun K _ c => M3.rightMul_inv u c) (fun K _ c => M3.rightMul_inv' u c) g g' ?_ ?_
    · intro K _ _ y
      obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ K y)
      rw [hg K y P hP.symm, ← hP]; rfl
    · intro K _ _ y
      obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ K y)
      rw [hg' K y P hP.symm, ← hP]; rfl

/-- **`R1bTransport` is a theorem** (the comparison isomorphism carries the family). -/
theorem r1bTransport_proof : R1bTransport := by
  intro Y Φ Y' Φ' h h' hall π'
  obtain ⟨g, hg⟩ := compare_iso h h'
  obtain ⟨yτ, hy1, hy2, hy3⟩ := hall (π'.comp g.inv.left)
  have hfun : (fun τ => π'.val (K := ℂ) (yτ τ ≫ g.inv).left) =
      (fun τ => (π'.comp g.inv.left).val (K := ℂ) (yτ τ).left) := by
    funext τ
    exact (ToP1.val_comp_right π' g.inv.left (yτ τ).left).symm
  refine ⟨fun τ => yτ τ ≫ g.inv, fun τ => ?_, ?_, ?_⟩
  · obtain ⟨P, hP, rest⟩ := hy1 τ
    refine ⟨P, ?_, rest⟩
    rw [hg, Category.assoc, g.inv_hom_id, Category.comp_id]; exact hP
  · simp only at hfun ⊢; rw [hfun]; exact hy2
  · intro τ; simp only at hfun ⊢; rw [hfun]; exact hy3 τ

end Comparison

/-- **Row H-1 with `HeckeOfFine` discharged.** -/
theorem r1r2fpRep_of' (hE : CanonicalModelY3) (hX : CoarseX6OfFine) (hP : HauptmodulOfX6)
    (hR : ReciprocityOfFine) (h5 : ResidueOfX6) : LeafAdopt.R1R2fpRep :=
  r1r2fpRep_of hE heckeOfFine_proof hX hP hR h5

/-- **Row H-20 from the leaf candidate `ShimuraFamily` alone** (`R1bTransport` discharged). -/
theorem r1b_of' (hS : ShimuraFamily) :
    ∀ h : LeafAdopt.R1R2fpRep,
      HSyn.G0Split.FibreQM.R1bFamily (HSyn.G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
        (HSyn.G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
        (HSyn.G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h)) :=
  r1b_of hS r1bTransport_proof

end HDec.QMSplit.Moduli

end -- noncomputable section

end QMSplit_ModuliSplit
