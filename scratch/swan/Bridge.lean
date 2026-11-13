import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.HDecomp.Conductor.I6Base

/-!
# swan, part 2: transport of Herbrand's theorem from DVRs to the subfields of `ℚ̄_p`

Goal: `HerbrandUpper` (Swan.lean §6) from `PkgI6.HerbrandQuotient` (kernel leaf I6.8, proved by
task t-different over DVRs). For a finite Galois `E/ℚ_p` inside `ℚ̄_p`, `𝓞_E = {x ∈ E : ‖x‖ ≤ 1}`
is the integral closure of `ℤ_p` in `E`; `Gal(𝓞_E/ℤ_p) ≅ Gal(E/ℚ_p)` (Mathlib's `galRestrict`)
carries `PkgI6.lowerRam` to `LadicCond.ramSet`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SwanBridge

open PkgI4 LadicCond Polynomial

variable {p : ℕ} [Fact p.Prime]

/-! ## §1. `𝓞_E` -/

/-- `y ∈ ℚ̄_p` is integral over `ℤ_p` iff `‖y‖ ≤ 1` (the norm of `ℚ̄_p` is the spectral norm). -/
theorem isIntegral_iff_norm_le_one (y : Kbar p) : IsIntegral ℤ_[p] y ↔ ‖y‖ ≤ 1 := by
  have hyQ : IsIntegral ℚ_[p] y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hyQ)]
  constructor
  · intro hy n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hy, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl : minpoly ℚ_[p] y ∈ lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hyQ)
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[p], hq, minpoly.aeval]

theorem norm_algebraMap_le_one (a : ℤ_[p]) : ‖algebraMap ℤ_[p] (Kbar p) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (Kbar p), PadicAlgCl.norm_extends]
  exact PadicInt.norm_le_one a

/-- `𝓞_E = {x ∈ E : ‖x‖ ≤ 1}`, as a `ℤ_p`-subalgebra of `ℚ̄_p`. -/
def OE (E : Fld p) : Subalgebra ℤ_[p] (Kbar p) where
  carrier := {x | x ∈ E ∧ ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => ⟨E.mul_mem ha.1 hb.1, by
    rw [norm_mul]; nlinarith [norm_nonneg a, norm_nonneg b, ha.2, hb.2]⟩
  add_mem' := fun {a b} ha hb => ⟨E.add_mem ha.1 hb.1,
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha.2 hb.2)⟩
  algebraMap_mem' := fun a => ⟨by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (Kbar p)]
    exact E.algebraMap_mem _, norm_algebraMap_le_one a⟩

theorem mem_OE {E : Fld p} {x : Kbar p} : x ∈ OE E ↔ x ∈ E ∧ ‖x‖ ≤ 1 := Iff.rfl

variable (E : Fld p)

/-- `𝓞_E → E`. -/
def toE : OE E →+* E where
  toFun x := ⟨x, x.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

instance algOE : Algebra (OE E) E := (toE E).toAlgebra

theorem algebraMap_OE_coe (x : OE E) : ((algebraMap (OE E) E x : E) : Kbar p) = x := rfl

instance : IsScalarTower ℤ_[p] (OE E) E :=
  IsScalarTower.of_algebraMap_eq fun a => by
    apply Subtype.ext
    rw [algebraMap_OE_coe]
    rfl

instance towerE : IsScalarTower ℤ_[p] E (Kbar p) :=
  IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] E, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (Kbar p)]
    rfl

instance isIntegralClosure_OE : IsIntegralClosure (OE E) ℤ_[p] E where
  algebraMap_injective := fun a b h => Subtype.ext (congrArg Subtype.val h :)
  isIntegral_iff := by
    intro x
    have hint : IsIntegral ℤ_[p] x ↔ IsIntegral ℤ_[p] (x : Kbar p) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ_[p] E (Kbar p))
        (algebraMap E (Kbar p)).injective).symm
    rw [hint, isIntegral_iff_norm_le_one]
    constructor
    · intro h; exact ⟨⟨x, x.2, h⟩, rfl⟩
    · rintro ⟨y, rfl⟩; exact y.2.2

/-! ## §2. `𝓞_E` is a DVR, finite over `ℤ_p`; its maximal ideal by norms -/

section DVR

variable [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E]

instance isFractionRing_OE : IsFractionRing (OE E) E :=
  IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[p] ℚ_[p] E (OE E)

instance finite_OE : Module.Finite ℤ_[p] (OE E) :=
  IsIntegralClosure.finite ℤ_[p] ℚ_[p] E (OE E)

omit [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E] in
theorem algebraMap_Kbar_injective : Function.Injective (algebraMap ℤ_[p] (Kbar p)) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (Kbar p)]
  exact (algebraMap ℚ_[p] _).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])

instance faithful_Kbar : FaithfulSMul ℤ_[p] (Kbar p) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 algebraMap_Kbar_injective

instance torsionFree_Kbar : Module.IsTorsionFree ℤ_[p] (Kbar p) :=
  FaithfulSMul.to_isTorsionFree ℤ_[p] (Kbar p)

instance torsionFree_OE : Module.IsTorsionFree ℤ_[p] (OE E) :=
  Subalgebra.instIsTorsionFree (OE E)

variable {E}

theorem norm_pos_of_ne {x : OE E} (hx : x ≠ 0) : 0 < ‖(x : Kbar p)‖ :=
  norm_pos_iff.2 fun h => hx (Subtype.ext h)

/-- Units of `𝓞_E` are the elements of norm `1`. -/
theorem isUnit_iff {x : OE E} : IsUnit x ↔ ‖(x : Kbar p)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ‖((u : OE E) : Kbar p)‖ * ‖(((u⁻¹ : (OE E)ˣ) : OE E) : Kbar p)‖ = 1 := by
      rw [← norm_mul]
      have : ((u : OE E) : Kbar p) * (((u⁻¹ : (OE E)ˣ) : OE E) : Kbar p) = 1 := by
        rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
      rw [this, norm_one]
    have h2 := (u : OE E).2.2
    have h3 := ((u⁻¹ : (OE E)ˣ) : OE E).2.2
    nlinarith [norm_nonneg ((u : OE E) : Kbar p),
      norm_nonneg (((u⁻¹ : (OE E)ˣ) : OE E) : Kbar p)]
  · intro h
    have hx0 : (x : Kbar p) ≠ 0 := by intro h0; rw [h0, norm_zero] at h; exact zero_ne_one h
    refine isUnit_iff_exists_inv.2 ⟨⟨(x : Kbar p)⁻¹, E.inv_mem x.2.1, ?_⟩, ?_⟩
    · rw [norm_inv, h, inv_one]
    · apply Subtype.ext
      change (x : Kbar p) * (x : Kbar p)⁻¹ = 1
      exact mul_inv_cancel₀ hx0

/-- Divisibility in `𝓞_E` by norms. -/
theorem dvd_iff {a x : OE E} (ha : a ≠ 0) : a ∣ x ↔ ‖(x : Kbar p)‖ ≤ ‖(a : Kbar p)‖ := by
  have ha0 : (a : Kbar p) ≠ 0 := fun h => ha (Subtype.ext h)
  constructor
  · rintro ⟨c, rfl⟩
    change ‖(a : Kbar p) * (c : Kbar p)‖ ≤ _
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) c.2.2
  · intro h
    refine ⟨⟨(x : Kbar p) / a, E.div_mem x.2.1 a.2.1, ?_⟩, ?_⟩
    · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
    · apply Subtype.ext
      change (x : Kbar p) = (a : Kbar p) * ((x : Kbar p) / a)
      field_simp

variable (E)

/-- A uniformizer of `E` as an element of `𝓞_E`. -/
def unif : OE E :=
  ⟨(exists_isUnif (L := E) inferInstance).choose,
    (exists_isUnif (L := E) inferInstance).choose_spec.1,
    (exists_isUnif (L := E) inferInstance).choose_spec.2.1.le⟩

theorem isUnif_unif : IsUnif E ((unif E : OE E) : Kbar p) :=
  (exists_isUnif (L := E) inferInstance).choose_spec

theorem unif_norm_pos : 0 < ‖((unif E : OE E) : Kbar p)‖ := by
  have hpL : (p : Kbar p) ∈ E := by
    rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
    exact IntermediateField.algebraMap_mem _ _
  have h1 := (isUnif_unif E).2.2 (p : Kbar p) hpL isUnif_bot.2.1
  have h2 : 0 < ‖(p : Kbar p)‖ := by
    rw [norm_p_kbar]; exact inv_pos.2 (Nat.cast_pos.2 (Fact.out : p.Prime).pos)
  exact lt_of_lt_of_le h2 h1

theorem unif_ne_zero : unif E ≠ 0 := fun h => by
  have := unif_norm_pos E; rw [h] at this; simp at this

theorem irreducible_unif : Irreducible (unif E) := by
  have hr := isUnif_unif E
  have hr0 := unif_norm_pos E
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · rw [isUnit_iff] at hu; linarith [hr.2.1]
  · have hn : ‖((unif E : OE E) : Kbar p)‖ = ‖(a : Kbar p)‖ * ‖(b : Kbar p)‖ := by
      rw [hab, Subalgebra.coe_mul, norm_mul]
    by_contra hcon
    push Not at hcon
    rw [isUnit_iff, isUnit_iff] at hcon
    have ha1 : ‖(a : Kbar p)‖ < 1 := lt_of_le_of_ne a.2.2 hcon.1
    have hb1 : ‖(b : Kbar p)‖ < 1 := lt_of_le_of_ne b.2.2 hcon.2
    have ha := hr.2.2 _ a.2.1 ha1
    have hb := hr.2.2 _ b.2.1 hb1
    have hlt : ‖((unif E : OE E) : Kbar p)‖ * ‖((unif E : OE E) : Kbar p)‖ <
        ‖((unif E : OE E) : Kbar p)‖ := by nlinarith [hr.2.1]
    nlinarith [norm_nonneg (a : Kbar p), norm_nonneg (b : Kbar p)]

/-- Every nonzero `x ∈ 𝓞_E` is `ϖ^n` times a unit. -/
theorem exists_assoc {x : OE E} (hx : x ≠ 0) : ∃ n : ℕ, Associated (unif E ^ n) x := by
  classical
  set r := ‖((unif E : OE E) : Kbar p)‖ with hr
  have hr0 := unif_norm_pos E
  have hr1 : r < 1 := (isUnif_unif E).2.1
  have hx0 := norm_pos_of_ne hx
  have hex : ∃ k : ℕ, r ^ (k + 1) < ‖(x : Kbar p)‖ := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hx0 hr1
    exact ⟨k, lt_of_le_of_lt (pow_le_pow_of_le_one hr0.le hr1.le (Nat.le_succ k)) hk⟩
  set n := Nat.find hex with hn
  have hn1 : r ^ (n + 1) < ‖(x : Kbar p)‖ := Nat.find_spec hex
  have hn2 : ‖(x : Kbar p)‖ ≤ r ^ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, pow_zero]; exact x.2.2
    · have := Nat.find_min hex (show n - 1 < n by omega)
      push Not at this
      rwa [show n - 1 + 1 = n by omega] at this
  have hdvd : unif E ^ n ∣ x := by
    rw [dvd_iff (pow_ne_zero n (unif_ne_zero E)), Subalgebra.coe_pow, norm_pow]
    exact hn2
  obtain ⟨u, hu⟩ := hdvd
  have hu0 : u ≠ 0 := by rintro rfl; rw [mul_zero] at hu; exact hx hu
  have hunit : IsUnit u := by
    rw [isUnit_iff]
    have hnx : ‖(x : Kbar p)‖ = r ^ n * ‖(u : Kbar p)‖ := by
      rw [hu, Subalgebra.coe_mul, norm_mul, Subalgebra.coe_pow, norm_pow]
    by_contra hne
    have hlt : ‖(u : Kbar p)‖ < 1 := lt_of_le_of_ne u.2.2 hne
    have hle := (isUnif_unif E).2.2 _ u.2.1 hlt
    rw [hnx, pow_succ] at hn1
    have : r ^ n * ‖(u : Kbar p)‖ ≤ r ^ n * r := mul_le_mul_of_nonneg_left hle (by positivity)
    linarith
  exact ⟨n, ⟨hunit.unit, by rw [hu]; rfl⟩⟩

instance dvr_OE : IsDiscreteValuationRing (OE E) :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨unif E, irreducible_unif E, fun hx => exists_assoc E hx⟩

/-- `𝔪^{i+1} = {x : ‖x‖ ≤ ‖ϖ‖^{i+1}}`. -/
theorem mem_maximalIdeal_pow {x : OE E} (i : ℕ) :
    x ∈ IsLocalRing.maximalIdeal (OE E) ^ (i + 1) ↔
      ‖(x : Kbar p)‖ ≤ ‖((unif E : OE E) : Kbar p)‖ ^ (i + 1) := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 (irreducible_unif E),
    Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    dvd_iff (pow_ne_zero _ (unif_ne_zero E)), Subalgebra.coe_pow, norm_pow]

end DVR

end SwanBridge
