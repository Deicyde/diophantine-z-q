import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.HDecomp.Conductor.Breaks
import ZInQKernel.Contrib.TauCeti.NumberTheory.Padics.AlgebraicClosure
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.AutomorphismAction
import ZInQKernel.Contrib.TauCeti.RingTheory.Ideal.RamificationGroup

/-!
# G15: the kernel's global ramification groups are the `LadicCond` ones of the closure in `ℚ̄_p`

Let `L` be a number field and `j : L →+* ℚ̄_p` (`ℚ̄_p = PadicAlgCl p`) an embedding. Then
* `x ↦ ‖j x‖` is equivalent to the `P`-adic valuation of `L` for the prime
  `P = primeOf j = {x ∈ 𝓞 L | ‖j x‖ < 1}` (`isEquiv_nv`);
* `Lj j = ℚ_p(j L)`, a `LadicCond.Fld p`, has `j π` as a uniformizer for any `P`-uniformizer `π`
  (`isUnif_j_unif`);
* for `σ ∈ G_{ℚ_p}` and `τ ∈ Gal(L/ℚ)` with `j ∘ τ = σ ∘ j`,
  `σ ∈ LadicCond.ramSet (Lj j) i ↔ τ ∈ GlueConductor.ramGroup L P i` (`mem_ramSet_iff`);
* for `L/ℚ` Galois, `LadicCond.ramCard (Lj j) i = GlueConductor.ramCard L P i`
  (`ramCard_Lj_eq`).

No `sorry`, no `axiom`.
-/

open NumberField IsDedekindDomain
open scoped NNReal Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.G15.Ladic

variable {p : ℕ} [Fact p.Prime] {L : Type} [Field L] (j : L →+* PadicAlgCl p)

/-! ## §1. The valuation `x ↦ ‖j x‖` and its prime -/

/-- `x ↦ ‖j x‖₊` as a valuation of `L`. -/
def nv : Valuation L ℝ≥0 := (PadicAlgCl.valued p).v.comap j

theorem nv_apply (x : L) : nv j x = ‖j x‖₊ := rfl

theorem coe_nv (x : L) : (nv j x : ℝ) = ‖j x‖ := rfl

variable [NumberField L]

omit [NumberField L] in
/-- Integers of `L` have `‖j x‖ ≤ 1` (the unit ball of `ℚ̄_p` is integrally closed). -/
theorem norm_le_one (x : 𝓞 L) : ‖j (x : L)‖ ≤ 1 := by
  have hv := Valuation.integer.integers (PadicAlgCl.valued p).v
  have hint : IsIntegral ℤ (j (x : L)) := (x.2.map j.toIntAlgHom)
  have h := hv.mem_of_integral (hint.tower_top (A := (PadicAlgCl.valued p).v.integer))
  change ‖j (x : L)‖₊ ≤ 1 at h
  exact_mod_cast h

theorem nv_int_le_one (x : 𝓞 L) : nv j (x : L) ≤ 1 := by
  rw [nv_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  exact norm_le_one j x

/-- The ideal `{x ∈ 𝓞 L | ‖j x‖ < 1}`. -/
def primeIdeal : Ideal (𝓞 L) where
  carrier := {x | ‖j (x : L)‖ < 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one j c)) hx

theorem mem_primeIdeal (x : 𝓞 L) : x ∈ primeIdeal j ↔ ‖j (x : L)‖ < 1 := Iff.rfl

theorem primeIdeal_isPrime : (primeIdeal j).IsPrime where
  ne_top' h := by
    have : (1 : 𝓞 L) ∈ primeIdeal j := h ▸ Submodule.mem_top
    simp [mem_primeIdeal] at this
  mem_or_mem' {a b} hab := by
    simp only [mem_primeIdeal, map_mul] at *
    rw [norm_mul] at hab
    by_contra! h
    have ha := le_antisymm (norm_le_one j a) h.1
    have hb := le_antisymm (norm_le_one j b) h.2
    rw [ha, hb, one_mul] at hab
    exact lt_irrefl _ hab

theorem natCast_mem_primeIdeal : (p : 𝓞 L) ∈ primeIdeal j := by
  rw [mem_primeIdeal]
  push_cast
  rw [map_natCast]
  have h := PadicAlgCl.norm_extends p (p : ℚ_[p])
  rw [map_natCast] at h
  rw [h, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

theorem primeIdeal_ne_bot : primeIdeal j ≠ ⊥ := by
  intro h
  have := natCast_mem_primeIdeal j
  rw [h, Ideal.mem_bot] at this
  have h0 : ((p : 𝓞 L) : L) = 0 := by rw [this]; rfl
  push_cast at h0
  exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h0)

/-- **The prime `P` of `𝓞 L` below `j`**: `{x ∈ 𝓞 L | ‖j x‖ < 1}`. -/
def primeOf : HeightOneSpectrum (𝓞 L) where
  asIdeal := primeIdeal j
  isPrime := primeIdeal_isPrime j
  ne_bot := primeIdeal_ne_bot j

theorem mem_primeOf (x : 𝓞 L) : x ∈ (primeOf j).asIdeal ↔ ‖j (x : L)‖ < 1 := Iff.rfl

theorem primeOf_liesOver : (primeOf j).asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  constructor
  have hprime : ((primeOf j).asIdeal.under ℤ).IsPrime := Ideal.IsPrime.under ℤ _
  have hle : Ideal.span {(p : ℤ)} ≤ (primeOf j).asIdeal.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under, Ideal.mem_comap]
    rw [map_natCast]
    exact natCast_mem_primeIdeal j
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp Fact.out) |>.isMaximal (by
        simpa using (Fact.out : p.Prime).ne_zero)
  exact hmax.eq_of_le hprime.ne_top hle

/-! ## §2. `‖j ·‖` is equivalent to the `P`-adic valuation -/

section Equiv

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/-- A valuation `u` of `L` with `u ≤ 1` on `𝓞 L` and `u x < 1 ↔ x ∈ w` on `𝓞 L` satisfies
`u z ≤ 1 ↔ z = n/d` with `n, d ∈ 𝓞 L`, `d ∉ w`. -/
theorem le_one_iff_exists (w : HeightOneSpectrum (𝓞 L)) (u : Valuation L Γ)
    (h1 : ∀ x : 𝓞 L, u (x : L) ≤ 1) (h2 : ∀ x : 𝓞 L, u (x : L) < 1 ↔ x ∈ w.asIdeal) (z : L) :
    u z ≤ 1 ↔ ∃ n d : 𝓞 L, d ∉ w.asIdeal ∧ z * (d : L) = n := by
  have hd1 : ∀ d : 𝓞 L, d ∉ w.asIdeal → u (d : L) = 1 := fun d hd =>
    le_antisymm (h1 d) (not_lt.mp fun h => hd ((h2 d).mp h))
  constructor
  · intro hz
    obtain ⟨n, d, h | h⟩ := w.exists_primeCompl_mul_eq_or_mul_eq (K := L) z
    · exact ⟨n, d, d.2, h⟩
    · by_cases hn : n ∈ w.asIdeal
      · exfalso
        have hun := (h2 n).mpr hn
        have h' := congrArg u h
        rw [map_mul, hd1 d d.2] at h'
        have : u z * u (n : L) < 1 :=
          lt_of_le_of_lt (by simpa using mul_le_mul_left hz (u (n : L))) hun
        exact absurd h' (ne_of_lt this)
      · exact ⟨d, n, hn, h⟩
  · rintro ⟨n, d, hd, h⟩
    have h' := congrArg u h
    rw [map_mul, hd1 d hd, mul_one] at h'
    rw [h']
    exact h1 n

/-- The `w`-adic valuation satisfies the hypotheses of `le_one_iff_exists`. -/
theorem valuation_le_one_iff_exists (w : HeightOneSpectrum (𝓞 L)) (z : L) :
    w.valuation L z ≤ 1 ↔ ∃ n d : 𝓞 L, d ∉ w.asIdeal ∧ z * (d : L) = n :=
  le_one_iff_exists w (w.valuation L) (fun x => w.valuation_le_one (K := L) x)
    (fun x => w.valuation_lt_one_iff_mem (K := L) x) z

end Equiv

theorem nv_int_lt_one_iff (x : 𝓞 L) : nv j (x : L) < 1 ↔ x ∈ (primeOf j).asIdeal := by
  rw [mem_primeOf, nv_apply, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]

/-- **`‖j ·‖` is equivalent to the `P`-adic valuation**, `P = primeOf j`. -/
theorem isEquiv_nv : ((primeOf j).valuation L).IsEquiv (nv j) :=
  Valuation.isEquiv_of_val_le_one fun z =>
    (valuation_le_one_iff_exists (primeOf j) z).trans
      (le_one_iff_exists (primeOf j) (nv j) (nv_int_le_one j) (nv_int_lt_one_iff j) z).symm

/-- A uniformizer of `P = primeOf j` in `𝓞 L`. -/
def unif : 𝓞 L := ((primeOf j).intValuation_exists_uniformizer).choose

theorem valuation_unif : (primeOf j).valuation L (unif j : L) = WithZero.exp (-1 : ℤ) := by
  rw [show ((unif j : 𝓞 L) : L) = algebraMap (𝓞 L) L (unif j) from rfl,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact ((primeOf j).intValuation_exists_uniformizer).choose_spec

theorem unif_mem : unif j ∈ (primeOf j).asIdeal := by
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L)]
  show (primeOf j).valuation L (unif j : L) < 1
  rw [valuation_unif]
  simp

theorem norm_unif_lt_one : ‖j (unif j : L)‖ < 1 := (mem_primeOf j _).mp (unif_mem j)

/-- **`‖j y‖ ≤ ‖j π‖^k ↔ y ∈ P^k`** for `y ∈ 𝓞 L`. -/
theorem norm_le_unif_pow_iff (y : 𝓞 L) (k : ℕ) :
    ‖j (y : L)‖ ≤ ‖j (unif j : L)‖ ^ k ↔ y ∈ (primeOf j).asIdeal ^ k := by
  rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap
    (K := L)]
  have h1 : ‖j (y : L)‖ ≤ ‖j (unif j : L)‖ ^ k ↔ nv j (y : L) ≤ nv j ((unif j : L) ^ k) := by
    rw [map_pow, ← NNReal.coe_le_coe, NNReal.coe_pow, coe_nv, coe_nv]
  rw [h1, ← (isEquiv_nv j) (y : L) ((unif j : L) ^ k), map_pow, valuation_unif, ← WithZero.exp_nsmul]
  simp only [smul_neg, nsmul_eq_mul, mul_one]

/-- **`j π` has the largest absolute value `< 1` on `j L`.** -/
theorem norm_le_norm_unif {z : L} (hz : ‖j z‖ < 1) : ‖j z‖ ≤ ‖j (unif j : L)‖ := by
  have hz' : nv j z < nv j 1 := by
    rw [map_one, ← NNReal.coe_lt_coe, coe_nv, NNReal.coe_one]; exact hz
  rw [← (isEquiv_nv j).lt_iff_lt, map_one] at hz'
  have hle : (primeOf j).valuation L z ≤ (primeOf j).valuation L (unif j : L) := by
    rw [valuation_unif]
    by_cases h0 : (primeOf j).valuation L z = 0
    · rw [h0]; exact zero_le
    · rw [← WithZero.exp_log h0] at hz' ⊢
      rw [WithZero.exp_le_exp]
      rw [WithZero.exp_lt_one_iff] at hz'
      omega
  rw [(isEquiv_nv j) z (unif j : L)] at hle
  rw [← coe_nv, ← coe_nv]
  exact_mod_cast hle

/-! ## §3. The local field `Lj j = ℚ_p(j L)` and its uniformizer -/

/-- `j L` as a `ℚ`-subfield of `ℚ̄_p`. -/
def jField : IntermediateField ℚ (PadicAlgCl p) := (j.toRatAlgHom).fieldRange

theorem mem_jField (y : PadicAlgCl p) : y ∈ jField j ↔ ∃ x : L, j x = y := Iff.rfl

/-- **The closure of `j L` in `ℚ̄_p`**: the `ℚ_p`-subfield `ℚ_p(j L)`, a `LadicCond.Fld p`. -/
def Lj : LadicCond.Fld p := IntermediateField.adjoin ℚ_[p] (jField j : Set (PadicAlgCl p))

theorem j_mem_Lj (x : L) : j x ∈ Lj j :=
  IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩

/-- `j L` is dense in `Lj j` (Tau Ceti's `exists_mem_norm_sub_lt_of_mem_adjoin`). -/
theorem exists_norm_sub_lt {y : PadicAlgCl p} (hy : y ∈ Lj j) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : L, ‖y - j x‖ < ε := by
  obtain ⟨y₀, ⟨x, rfl⟩, h⟩ := TauCeti.exists_mem_norm_sub_lt_of_mem_adjoin p (jField j) hy hε
  exact ⟨x, h⟩

theorem norm_eq_of_norm_sub_lt {y z : PadicAlgCl p} (h : ‖y - z‖ < ‖y‖) : ‖z‖ = ‖y‖ := by
  have hne : ‖y‖ ≠ ‖-(y - z)‖ := by rw [norm_neg]; exact ne_of_gt h
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [norm_neg, max_eq_left h.le] at this
  rw [← this]; congr 1; ring

theorem norm_sub_le_max' (a b : PadicAlgCl p) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg, ← norm_neg b]
  exact IsUltrametricDist.norm_add_le_max _ _

theorem unif_ne_zero : (unif j : L) ≠ 0 := by
  intro h
  have := valuation_unif j
  rw [h, map_zero] at this
  exact WithZero.zero_ne_coe this

theorem norm_unif_pos : 0 < ‖j (unif j : L)‖ :=
  norm_pos_iff.mpr ((map_ne_zero j).mpr (unif_ne_zero j))

/-- **`j π` is a uniformizer of `Lj j`** (in `LadicCond`'s sense). -/
theorem isUnif_unif : LadicCond.IsUnif (Lj j) (j (unif j : L)) := by
  refine ⟨j_mem_Lj j _, norm_unif_lt_one j, fun y hy hy1 => ?_⟩
  by_cases h0 : y = 0
  · rw [h0, norm_zero]; exact (norm_unif_pos j).le
  · obtain ⟨x, hx⟩ := exists_norm_sub_lt j hy (norm_pos_iff.mpr h0)
    have hxy := norm_eq_of_norm_sub_lt hx
    rw [← hxy] at hy1 ⊢
    exact norm_le_norm_unif j hy1

/-- All uniformizers of `Lj j` have the absolute value of `j π`. -/
theorem norm_eq_of_isUnif {ϖ : PadicAlgCl p} (h : LadicCond.IsUnif (Lj j) ϖ) :
    ‖ϖ‖ = ‖j (unif j : L)‖ :=
  le_antisymm ((isUnif_unif j).2.2 ϖ h.1 h.2.1) (h.2.2 _ (isUnif_unif j).1 (isUnif_unif j).2.1)

/-! ## §4. `σ ∈ ramSet (Lj j) i ↔ τ ∈ ramGroup L P i` -/

section RamSet

variable {j} {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} {τ : Gal(L/ℚ)}

theorem norm_j_apply (hστ : ∀ x, j (τ x) = σ (j x)) (x : L) : ‖j (τ x)‖ = ‖j x‖ := by
  rw [hστ, AlgEquiv.norm_apply]

theorem coe_smul_sub (τ : Gal(L/ℚ)) (x : 𝓞 L) : ((τ • x - x : 𝓞 L) : L) = τ (x : L) - x := by
  push_cast
  rfl

/-- For `τ ∈ G_i(P)` and `x ∈ L` with `‖j x‖ ≤ 1` (not only `x ∈ 𝓞 L`):
`‖j (τ x - x)‖ ≤ ‖j π‖^(i+1)`. -/
theorem norm_sub_le_of_mem_ramGroup (hστ : ∀ x, j (τ x) = σ (j x)) {i : ℕ}
    (hτ : τ ∈ GlueConductor.ramGroup L (primeOf j).asIdeal i) {x : L} (hx : ‖j x‖ ≤ 1) :
    ‖j (τ x - x)‖ ≤ ‖j (unif j : L)‖ ^ (i + 1) := by
  have hx' : nv j x ≤ 1 := by
    rw [← NNReal.coe_le_coe, coe_nv, NNReal.coe_one]; exact hx
  obtain ⟨n, d, hd, h⟩ :=
    (le_one_iff_exists (primeOf j) (nv j) (nv_int_le_one j) (nv_int_lt_one_iff j) x).mp hx'
  have hmem : ∀ y : 𝓞 L, ‖j (τ (y : L) - y)‖ ≤ ‖j (unif j : L)‖ ^ (i + 1) := by
    intro y
    rw [← coe_smul_sub]
    exact (norm_le_unif_pow_iff j _ _).mpr (Ideal.mem_inertia.mp hτ y)
  have hd1 : ‖j (d : L)‖ = 1 :=
    le_antisymm (norm_le_one j d) (not_lt.mp fun h' => hd ((mem_primeOf j d).mpr h'))
  have hτd : ‖j (τ (d : L))‖ = 1 := by rw [norm_j_apply hστ, hd1]
  have hτh : τ x * τ (d : L) = τ (n : L) := by rw [← map_mul, h]
  have key : (τ x - x) * ((d : L) * τ (d : L)) =
      (τ (n : L) - n) * d - n * (τ (d : L) - d) := by
    linear_combination (d : L) * hτh - τ (d : L) * h
  have hnorm := congrArg (fun z => ‖j z‖) key
  simp only [map_mul, norm_mul, hd1, hτd, mul_one] at hnorm
  rw [hnorm, map_sub, map_mul, map_mul]
  refine le_trans (norm_sub_le_max' _ _) (max_le ?_ ?_)
  · rw [norm_mul, hd1, mul_one]; exact hmem n
  · rw [norm_mul]
    exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one j n)) (hmem d)

/-- **The lower ramification sets agree**: for `σ ∈ G_{ℚ_p}` and `τ ∈ Gal(L/ℚ)` with
`j ∘ τ = σ ∘ j`, `σ ∈ LadicCond.ramSet (Lj j) i ↔ τ ∈ GlueConductor.ramGroup L P i`. -/
theorem mem_ramSet_iff (hστ : ∀ x, j (τ x) = σ (j x)) (i : ℕ) :
    σ ∈ LadicCond.ramSet (Lj j) i ↔ τ ∈ GlueConductor.ramGroup L (primeOf j).asIdeal i := by
  constructor
  · rintro ⟨ϖ, hϖ, hb⟩
    rw [Ideal.mem_inertia]
    intro x
    rw [← norm_le_unif_pow_iff, coe_smul_sub, map_sub, hστ, ← norm_eq_of_isUnif j hϖ]
    exact hb _ (j_mem_Lj j _) (norm_le_one j x)
  · intro hτ
    refine ⟨j (unif j : L), isUnif_unif j, fun y hy hy1 => ?_⟩
    set ε := ‖j (unif j : L)‖ ^ (i + 1) with hε
    have hε0 : 0 < ε := pow_pos (norm_unif_pos j) _
    have hε1 : ε ≤ 1 := pow_le_one₀ (norm_nonneg _) (norm_unif_lt_one j).le
    obtain ⟨x, hx⟩ := exists_norm_sub_lt j hy hε0
    have hjx : ‖j x‖ ≤ 1 := by
      have : j x = y + -(y - j x) := by ring
      rw [this]
      refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le hy1 ?_)
      rw [norm_neg]; exact hx.le.trans hε1
    have h1 := norm_sub_le_of_mem_ramGroup hστ hτ hjx
    rw [map_sub, hστ] at h1
    have : σ y - y = σ (y - j x) + ((σ (j x) - j x) + (j x - y)) := by
      rw [map_sub]; ring
    rw [this]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ?_)
    · rw [AlgEquiv.norm_apply]; exact hx.le
    · refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le h1 ?_)
      rw [← norm_neg, neg_sub]; exact hx.le

end RamSet

/-! ## §5. The decomposition group preserves `‖j ·‖`; lifts to `G_{ℚ_p}` -/

section Lift

/-- Two `ℝ≥0`-valuations equivalent to the `w`-adic one and agreeing at one `a` with
`0 < v_w(a) < 1` are equal. -/
theorem eq_of_isEquiv (w : HeightOneSpectrum (𝓞 L)) (u₁ u₂ : Valuation L ℝ≥0)
    (h₁ : (w.valuation L).IsEquiv u₁) (h₂ : (w.valuation L).IsEquiv u₂) {a : L} (ha0 : a ≠ 0)
    (ha1 : w.valuation L a < 1) (hu : u₁ a = u₂ a) (z : L) : u₁ z = u₂ z := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer L
  have key : ∀ y : L, y ≠ 0 →
      w.valuation L y = w.valuation L (π ^ (-(WithZero.log (w.valuation L y)))) := by
    intro y hy
    have hy' : w.valuation L y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
    simp only [smul_eq_mul, mul_neg, mul_one, neg_neg, WithZero.exp_log hy']
  have hval : ∀ (u : Valuation L ℝ≥0), (w.valuation L).IsEquiv u → ∀ y : L, y ≠ 0 →
      u y = u π ^ (-(WithZero.log (w.valuation L y))) := by
    intro u hu y hy
    rw [← map_zpow₀]
    have e := key y hy
    exact le_antisymm ((hu _ _).mp e.le) ((hu _ _).mp e.ge)
  have hπeq : u₁ π = u₂ π := by
    have ha' : w.valuation L a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha0
    have hm : WithZero.log (w.valuation L a) < 0 := by
      rw [← WithZero.exp_lt_one_iff, WithZero.exp_log ha']; exact ha1
    obtain ⟨k, hk⟩ : ∃ k : ℕ, -(WithZero.log (w.valuation L a)) = (k : ℤ) :=
      ⟨(-(WithZero.log (w.valuation L a))).toNat, by omega⟩
    have hk0 : k ≠ 0 := by omega
    have e := hu
    rw [hval u₁ h₁ a ha0, hval u₂ h₂ a ha0, hk, zpow_natCast, zpow_natCast] at e
    exact (pow_left_inj₀ zero_le zero_le hk0).mp e
  by_cases hz : z = 0
  · rw [hz, map_zero, map_zero]
  · rw [hval u₁ h₁ z hz, hval u₂ h₂ z hz, hπeq]

theorem coe_smul (τ : Gal(L/ℚ)) (y : 𝓞 L) : ((τ • y : 𝓞 L) : L) = τ (y : L) := rfl

/-- **The decomposition group of `P = primeOf j` preserves `‖j ·‖`.** -/
theorem norm_j_apply_of_mem_stabilizer {τ : Gal(L/ℚ)}
    (hτ : τ ∈ MulAction.stabilizer Gal(L/ℚ) (primeOf j).asIdeal) (x : L) :
    ‖j (τ x)‖ = ‖j x‖ := by
  have hP : τ • (primeOf j).asIdeal = (primeOf j).asIdeal := hτ
  let u' : Valuation L ℝ≥0 := (nv j).comap (τ : L →+* L)
  have hu' : ∀ y, u' y = nv j (τ y) := fun _ => rfl
  have h1 : ∀ y : 𝓞 L, u' (y : L) ≤ 1 := fun y => by
    rw [hu', ← coe_smul]; exact nv_int_le_one j _
  have h2 : ∀ y : 𝓞 L, u' (y : L) < 1 ↔ y ∈ (primeOf j).asIdeal := fun y => by
    rw [hu', ← coe_smul, nv_int_lt_one_iff]
    calc τ • y ∈ (primeOf j).asIdeal ↔ τ • y ∈ τ • (primeOf j).asIdeal := by rw [hP]
      _ ↔ y ∈ (primeOf j).asIdeal := Ideal.smul_mem_pointwise_smul_iff
  have he : ((primeOf j).valuation L).IsEquiv u' :=
    Valuation.isEquiv_of_val_le_one fun z =>
      (valuation_le_one_iff_exists _ z).trans (le_one_iff_exists _ u' h1 h2 z).symm
  have hp0 : (p : L) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp1 : (primeOf j).valuation L (p : L) < 1 := by
    have h := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) (primeOf j) (p : 𝓞 L)).mpr
      (natCast_mem_primeIdeal j)
    simpa using h
  have hpu : u' (p : L) = nv j (p : L) := by rw [hu', map_natCast]
  have := eq_of_isEquiv (primeOf j) u' (nv j) he (isEquiv_nv j) hp0 hp1 hpu x
  rw [hu'] at this
  rw [← coe_nv, ← coe_nv, this]

/-- `L ≅ j L` over `ℚ`. -/
def jEquiv : L ≃ₐ[ℚ] jField j := AlgEquiv.ofInjectiveField j.toRatAlgHom

theorem coe_jEquiv (x : L) : ((jEquiv j x : jField j) : PadicAlgCl p) = j x := rfl

instance : FiniteDimensional ℚ (jField j) := (jEquiv j).toLinearEquiv.finiteDimensional

variable [IsGalois ℚ L]

instance : IsGalois ℚ (jField j) := IsGalois.of_algEquiv (jEquiv j)

/-- **`σ ↦ σ|_{j L}`**: the `τ ∈ Gal(L/ℚ)` with `j ∘ τ = σ ∘ j`. -/
def tauOf (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : Gal(L/ℚ) :=
  (jEquiv j).trans (((σ.restrictScalars ℚ).restrictNormal (jField j)).trans (jEquiv j).symm)

theorem tauOf_spec (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : L) :
    j (tauOf j σ x) = σ (j x) := by
  rw [← coe_jEquiv]
  simp only [tauOf, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars ℚ) (jField j) (jEquiv j x)

theorem eq_tauOf {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} {τ : Gal(L/ℚ)}
    (hστ : ∀ x, j (τ x) = σ (j x)) : τ = tauOf j σ := by
  ext x
  apply j.injective
  rw [hστ, tauOf_spec]

/-- **Every element of the decomposition group lifts to `G_{ℚ_p}`** (Tau Ceti's
`exists_algEquiv_apply_eq_of_norm_apply_eq`). -/
theorem exists_lift {τ : Gal(L/ℚ)}
    (hτ : τ ∈ MulAction.stabilizer Gal(L/ℚ) (primeOf j).asIdeal) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∀ x, j (τ x) = σ (j x) := by
  let φ : jField j →ₐ[ℚ] PadicAlgCl p :=
    (j.toRatAlgHom.comp (τ : L →ₐ[ℚ] L)).comp (jEquiv j).symm.toAlgHom
  have hφ' : ∀ x : L, φ (jEquiv j x) = j (τ x) := fun x => by
    show j.toRatAlgHom (τ ((jEquiv j).symm (jEquiv j x))) = _
    rw [AlgEquiv.symm_apply_apply]
    rfl
  have hφ : ∀ y : jField j, ‖φ y‖ = ‖(y : PadicAlgCl p)‖ := by
    intro y
    obtain ⟨x, rfl⟩ := (jEquiv j).surjective y
    rw [hφ', coe_jEquiv, norm_j_apply_of_mem_stabilizer j hτ]
  obtain ⟨h, hh⟩ := TauCeti.exists_algEquiv_apply_eq_of_norm_apply_eq p (jField j) φ hφ
  refine ⟨h, fun x => ?_⟩
  have := hh (jEquiv j x)
  rw [hφ', coe_jEquiv] at this
  exact this.symm

end Lift

/-! ## §6. `ramCard (Lj j) i = ramCard L P i` -/

section Card

/-- Images of `S` under two maps with the same fibres have the same cardinality. -/
theorem card_image_eq_of_fibres {X Y Z : Type*} (f : X → Y) (g : X → Z)
    (h : ∀ a b, f a = f b ↔ g a = g b) (S : Set X) : Nat.card (f '' S) = Nat.card (g '' S) := by
  classical
  let F : f '' S → g '' S := fun y => ⟨g y.2.choose, y.2.choose, y.2.choose_spec.1, rfl⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨y₁, h₁⟩ ⟨y₂, h₂⟩ he
      have he' : g h₁.choose = g h₂.choose := congrArg Subtype.val he
      have := (h _ _).mpr he'
      rw [h₁.choose_spec.2, h₂.choose_spec.2] at this
      exact Subtype.ext this
    · rintro ⟨z, a, ha, rfl⟩
      refine ⟨⟨f a, a, ha, rfl⟩, Subtype.ext ?_⟩
      have hc := (⟨a, ha, rfl⟩ : f a ∈ f '' S).choose_spec
      exact (h _ _).mp hc.2
  exact Nat.card_congr (Equiv.ofBijective F hF)

variable [IsGalois ℚ L]

theorem restr_eq_iff (σ σ' : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    LadicCond.restr (Lj j) σ = LadicCond.restr (Lj j) σ' ↔ tauOf j σ = tauOf j σ' := by
  constructor
  · intro h
    ext x
    apply j.injective
    rw [tauOf_spec, tauOf_spec]
    exact congrFun h ⟨j x, j_mem_Lj j x⟩
  · intro h
    funext y
    have hj : ∀ x : L, σ (j x) = σ' (j x) := fun x => by
      rw [← tauOf_spec, ← tauOf_spec, h]
    have hy : (y : PadicAlgCl p) ∈ Algebra.adjoin ℚ_[p] (jField j : Set (PadicAlgCl p)) := by
      have : (y : PadicAlgCl p) ∈
          IntermediateField.adjoin ℚ_[p] (jField j : Set (PadicAlgCl p)) := y.2
      rwa [← IntermediateField.mem_toSubalgebra,
        IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
          fun x _ => Algebra.IsAlgebraic.isAlgebraic x] at this
    have hle : Algebra.adjoin ℚ_[p] (jField j : Set (PadicAlgCl p)) ≤
        AlgHom.equalizer (σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p) σ' := by
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩
      exact hj x
    exact hle hy

/-- **`g_i(ℚ_p(j L)/ℚ_p) = |G_i(P)|`**: the kernel's local `LadicCond.ramCard` of the closure of
`j L` in `ℚ̄_p` is the kernel's global `GlueConductor.ramCard` of `P = primeOf j`. -/
theorem ramCard_Lj_eq (i : ℕ) :
    LadicCond.ramCard (Lj j) i = GlueConductor.ramCard L (primeOf j).asIdeal i := by
  unfold LadicCond.ramCard
  rw [card_image_eq_of_fibres (LadicCond.restr (Lj j)) (tauOf j) (restr_eq_iff j)]
  have : tauOf j '' LadicCond.ramSet (Lj j) i =
      (GlueConductor.ramGroup L (primeOf j).asIdeal i : Set Gal(L/ℚ)) := by
    ext τ
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact (mem_ramSet_iff (tauOf_spec j σ) i).mp hσ
    · intro hτ
      have hst : τ ∈ MulAction.stabilizer Gal(L/ℚ) (primeOf j).asIdeal := by
        have := Ideal.ramificationGroup_le_stabilizer (G := Gal(L/ℚ)) (primeOf j).asIdeal i
        rw [Ideal.ramificationGroup_def] at this
        exact this hτ
      obtain ⟨σ, hσ⟩ := exists_lift j hst
      exact ⟨σ, (mem_ramSet_iff hσ i).mpr hτ, (eq_tauOf j hσ).symm⟩
  rw [this]
  rfl

end Card

/-! ## §7. `Lj j` is finite Galois over `ℚ_p`; specialising `upperAbs` -/

section FinGal

/-- `Lj j = ℚ_p(α)` for a primitive element `α` of `j L / ℚ`. -/
theorem exists_Lj_eq_adjoin_simple :
    ∃ α : PadicAlgCl p, Lj j = IntermediateField.adjoin ℚ_[p] {α} := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ (jField j)
  have h1 := IntermediateField.adjoin_map ℚ {α} (jField j).val
  rw [hα, Set.image_singleton] at h1
  have h2 : (⊤ : IntermediateField ℚ (jField j)).map (jField j).val = jField j := by
    ext y
    constructor
    · rintro ⟨z, -, rfl⟩; exact z.2
    · intro hy; exact ⟨⟨y, hy⟩, trivial, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, (jField j).val α = a := ⟨_, rfl⟩
  rw [ha] at h1
  have hj : jField j = IntermediateField.adjoin ℚ {a} := h2.symm.trans h1
  have ha' : a ∈ jField j := ha ▸ α.2
  refine ⟨a, le_antisymm ?_ ?_⟩
  · have hle : jField j ≤ (IntermediateField.adjoin ℚ_[p] {a}).restrictScalars ℚ := by
      rw [hj, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact IntermediateField.mem_adjoin_simple_self ℚ_[p] a
    rw [Lj, IntermediateField.adjoin_le_iff]
    intro y hy
    exact hle hy
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact IntermediateField.subset_adjoin _ _ ha'

theorem finiteDimensional_Lj : FiniteDimensional ℚ_[p] (Lj j) := by
  obtain ⟨α, hα⟩ := exists_Lj_eq_adjoin_simple j
  rw [hα]
  exact IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral α)

variable [IsGalois ℚ L]

theorem normal_Lj : Normal ℚ_[p] (Lj j) := by
  rw [IntermediateField.normal_iff_forall_map_le']
  intro σ
  rw [Lj, IntermediateField.adjoin_map]
  apply IntermediateField.adjoin.mono
  rintro _ ⟨y, ⟨x, rfl⟩, rfl⟩
  exact ⟨tauOf j σ x, tauOf_spec j σ x⟩

/-- **`Lj j` is finite Galois over `ℚ_p`** (`LadicCond.IsFinGal`). -/
theorem isFinGal_Lj : LadicCond.IsFinGal (Lj j) := by
  have := finiteDimensional_Lj j
  have := normal_Lj j
  exact ⟨inferInstance, IsGalois.mk⟩

/-- **The absolute upper filtration specialises to `Lj j`**: `σ ∈ G_{ℚ_p}^v` implies
`σ ∈ upperSet (Lj j) v`. -/
theorem mem_upperSet_of_mem_upperAbs {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} {v : ℝ}
    (hσ : σ ∈ LadicCond.upperAbs p v) : σ ∈ LadicCond.upperSet (Lj j) v :=
  hσ (Lj j) (isFinGal_Lj j)

end FinGal

end ZInQ.Contrib.G15.Ladic

end
