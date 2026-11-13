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

/-! ## §3. `Gal(𝓞_E/ℤ_p)` and the ramification dictionary -/

section Galois

variable [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E]

/-- `G_{ℚ_p} → Gal(E/ℚ_p) ≅ Gal(𝓞_E/ℤ_p)` (restriction, then Mathlib's `galRestrict`). -/
def res : GQp p →* (OE E ≃ₐ[ℤ_[p]] OE E) :=
  (galRestrict ℤ_[p] ℚ_[p] E (OE E)).toMonoidHom.comp (AlgEquiv.restrictNormalHom E)

theorem res_apply (σ : GQp p) (x : OE E) : ((res E σ x : OE E) : Kbar p) = σ (x : Kbar p) := by
  have h1 := algebraMap_galRestrict_apply ℤ_[p] (AlgEquiv.restrictNormalHom E σ) x
  have h2 := AlgEquiv.restrictNormal_commutes σ E (algebraMap (OE E) E x)
  rw [← algebraMap_OE_coe, ← algebraMap_OE_coe E x]
  change ((algebraMap (OE E) E (galRestrict ℤ_[p] ℚ_[p] E (OE E)
    (AlgEquiv.restrictNormalHom E σ) x) : E) : Kbar p) = _
  rw [h1]
  exact h2

theorem res_surjective : Function.Surjective (res E) :=
  (galRestrict ℤ_[p] ℚ_[p] E (OE E)).surjective.comp (AlgEquiv.restrictNormalHom_surjective _)

/-- Every `x ∈ E` has `p^k x ∈ 𝓞_E` for some `k`. -/
theorem exists_pow_mul_mem {x : Kbar p} (hx : x ∈ E) : ∃ k : ℕ, (p : Kbar p) ^ k * x ∈ OE E := by
  have hpL : (p : Kbar p) ∈ E := by
    rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
    exact IntermediateField.algebraMap_mem _ _
  have hp1 : ‖(p : Kbar p)‖ < 1 := isUnif_bot.2.1
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (‖x‖ + 1) by positivity) hp1
  refine ⟨k, E.mul_mem (pow_mem hpL k) hx, ?_⟩
  rw [norm_mul, norm_pow]
  rw [lt_div_iff₀ (by positivity)] at hk
  nlinarith [norm_nonneg x, pow_nonneg (norm_nonneg (p : Kbar p)) k]

theorem res_eq_iff {σ τ : GQp p} : res E σ = res E τ ↔ ∀ x ∈ E, σ x = τ x := by
  constructor
  · intro h x hx
    obtain ⟨k, hk⟩ := exists_pow_mul_mem E hx
    have h1 := res_apply E σ ⟨_, hk⟩
    rw [h, res_apply] at h1
    simp only [map_mul, map_pow, map_natCast] at h1
    have hp0 : ((p : Kbar p)) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    exact (mul_left_cancel₀ hp0 h1).symm
  · intro h
    ext x
    rw [res_apply, res_apply, h _ x.2.1]

theorem ramSet_iff {σ : GQp p} {i : ℕ} :
    σ ∈ ramSet E i ↔ res E σ ∈ PkgI6.lowerRam ℤ_[p] (OE E) i := by
  rw [PkgI6.mem_lowerRam]
  constructor
  · rintro ⟨ϖ, hϖ, hb⟩ b
    rw [mem_maximalIdeal_pow, Subalgebra.coe_sub, res_apply, ← (isUnif_unif E).norm_eq hϖ]
    exact hb b b.2.1 b.2.2
  · intro h
    refine ⟨_, isUnif_unif E, fun x hx hx1 => ?_⟩
    have := (mem_maximalIdeal_pow E i).1 (h ⟨x, hx, hx1⟩)
    rwa [Subalgebra.coe_sub, res_apply] at this

theorem ramSetR_iff {σ : GQp p} {t : ℝ} :
    σ ∈ ramSetR E t ↔ res E σ ∈ PkgI6.lowerRamR ℤ_[p] (OE E) t := by
  unfold ramSetR PkgI6.lowerRamR
  split_ifs
  · exact ⟨fun _ => Subgroup.mem_top _, fun _ => trivial⟩
  · exact ramSet_iff E

/-- Two maps that separate the same pairs have images of the same cardinality. -/
theorem card_image_eq {α β γ : Type*} (F : α → β) (G : α → γ) (hFG : ∀ a b, F a = F b ↔ G a = G b)
    (S : Set α) : Nat.card (F '' S) = Nat.card (G '' S) := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun y => ⟨G y.2.choose, Set.mem_image_of_mem _ y.2.choose_spec.1⟩) ⟨?_, ?_⟩)
  · intro y1 y2 h
    have h' : G y1.2.choose = G y2.2.choose := congrArg Subtype.val h
    apply Subtype.ext
    rw [← y1.2.choose_spec.2, ← y2.2.choose_spec.2]
    exact (hFG _ _).2 h'
  · rintro ⟨_, a, ha, rfl⟩
    refine ⟨⟨F a, a, ha, rfl⟩, Subtype.ext ?_⟩
    exact (hFG _ _).1 (⟨F a, a, ha, rfl⟩ : F '' S).2.choose_spec.2

theorem coe_lowerRamR (t : ℝ) :
    (PkgI6.lowerRamR ℤ_[p] (OE E) t : Set (OE E ≃ₐ[ℤ_[p]] OE E)) = res E '' ramSetR E t := by
  ext s
  constructor
  · intro hs
    obtain ⟨σ, rfl⟩ := res_surjective E s
    exact ⟨σ, (ramSetR_iff E).2 hs, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact (ramSetR_iff E).1 hσ

theorem card_lowerRamR (t : ℝ) :
    Nat.card (PkgI6.lowerRamR ℤ_[p] (OE E) t) = ramCardR E t := by
  rw [← SetLike.coe_sort_coe, coe_lowerRamR, ramCardR]
  refine (card_image_eq (restr E) (res E) (fun a b => ?_) _).symm
  rw [restr_eq_iff', res_eq_iff]
where
  restr_eq_iff' {a b : GQp p} : restr E a = restr E b ↔ ∀ x ∈ E, a x = b x :=
    ⟨fun h x hx => congrFun h ⟨x, hx⟩, fun h => funext fun x => h x x.2⟩

theorem ramCardR_zero : ramCardR E 0 = ramCard E 0 := by
  unfold ramCardR ramSetR ramCard
  rw [if_neg (by norm_num)]
  simp

theorem herbrandPhi_eq : PkgI6.herbrandPhi ℤ_[p] (OE E) = phiAt E := by
  funext u
  unfold PkgI6.herbrandPhi phiAt
  congr 1
  funext t
  rw [card_lowerRamR, card_lowerRamR, ramCardR_zero]

theorem upperSet_iff {σ : GQp p} {v : ℝ} :
    σ ∈ upperSet E v ↔ res E σ ∈ PkgI6.upperRam ℤ_[p] (OE E) v := by
  unfold upperSet PkgI6.upperRam
  rw [herbrandPhi_eq]
  exact ramSetR_iff E

end Galois

end SwanBridge
