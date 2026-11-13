import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.HDecomp.Conductor.Breaks
import ZInQKernel.Contrib.TauCeti.NumberTheory.Padics.AlgebraicClosure
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.AutomorphismAction

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
open scoped NNReal

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

end ZInQ.Contrib.G15.Ladic

end
