
/-! ## §7c (local-glue). Raynaud's criterion (R6) at the place of `embP`: the rational case

`raynaudPlace_rational` (proved): if `A[m]` is `K`-rational (`m ≥ 3`, `p ∤ m`), the leaf R6
(`ObjBridge.RaynaudCriterion`) gives `RaynaudPlace A m`. The valuation-theoretic bridge is proved:
* `wK`, `OK`: the valuation subrings of `K̄` and `K` at the place of `embP` (norm `≤ 1` after
  `K̄ ≅ ℚ̄ → ℚ̄_p`); `OK` is a DVR (`OK_ne_top` and neron-lg's `isDiscreteValuationRing_of_ne_top`);
* `m`, `ℓ` prime to `p` are units of `OK`;
* a wild `σ'` (over `decomp σ`) lies in the inertia group of `wK` (`isInertia_of_wild`).
The general case of `RaynaudPlace` needs R6 over `K(A[m])` and the base change of `A`. -/

noncomputable section

namespace G15Ram

open PkgI4 (GQp GQ decomp)
open LadicCond
open CategoryTheory MonObj
open scoped Pointwise

section RaynaudSec

/-- The valuation subring `{x : ‖f x‖ ≤ 1}` for a ring map `f` to an ultrametric normed field. -/
def normVS {F E : Type*} [Field F] [NormedField E] [IsUltrametricDist E] (f : F →+* E) :
    ValuationSubring F where
  carrier := {x | ‖f x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_mul, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha
  mem_or_inv_mem' x := by
    by_cases h : ‖f x‖ ≤ 1
    · exact Or.inl h
    · right
      show ‖f x⁻¹‖ ≤ 1
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp h))

theorem mem_normVS {F E : Type*} [Field F] [NormedField E] [IsUltrametricDist E] (f : F →+* E)
    (x : F) : x ∈ normVS f ↔ ‖f x‖ ≤ 1 := Iff.rfl

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [NumberField K]

/-- `ℚ̄ ≅ K̄` (`qEmbRing` is bijective). -/
def eK (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ ≃+* AlgebraicClosure K :=
  RingEquiv.ofBijective (G0Galois.qEmbRing K)
    ⟨(G0Galois.qEmbRing K).injective, qEmbRing_surjective K⟩

/-- `K̄ ≅ ℚ̄ → ℚ̄_p`, the place of `embP` on `K̄`. -/
def ιbar (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [NumberField K] :
    AlgebraicClosure K →+* Kbar p :=
  (embP (p := p)).comp (eK K).symm.toRingHom

/-- The valuation ring of `K̄` at the place of `embP`. -/
def wK (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [NumberField K] :
    ValuationSubring (AlgebraicClosure K) :=
  normVS (ιbar p K)

/-- The valuation ring of `K` at the place of `embP`. -/
def OK (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [NumberField K] : ValuationSubring K :=
  normVS ((ιbar p K).comp (algebraMap K (AlgebraicClosure K)))

theorem wK_comap : (wK p K).comap (algebraMap K (AlgebraicClosure K)) = OK p K := by
  ext x; exact Iff.rfl

theorem OK_ne_top : OK p K ≠ ⊤ := by
  intro h
  have hmem : ((p : K))⁻¹ ∈ OK p K := by rw [h]; exact ValuationSubring.mem_top _
  rw [OK, mem_normVS] at hmem
  simp only [map_inv₀, map_natCast, norm_inv] at hmem
  rw [norm_p_kbar, inv_inv] at hmem
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  linarith

instance OK_dvr : IsDiscreteValuationRing (OK p K) :=
  ZInQ.NeronLG.isDiscreteValuationRing_of_ne_top _ OK_ne_top

/-- A natural number prime to `p` is a unit of `OK`. -/
theorem isUnit_natCast_OK {n : ℕ} (hn : ¬ p ∣ n) : IsUnit ((n : OK p K)) := by
  have hnorm : ‖(n : Kbar p)‖ = 1 := norm_natCast_kbar hn
  have hn0 : (n : K) ≠ 0 := by
    intro h0
    have : (n : Kbar p) = 0 := by
      have := congrArg ((ιbar p K).comp (algebraMap K (AlgebraicClosure K))) h0
      simpa using this
    rw [this, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hinv : ((n : K))⁻¹ ∈ OK p K := by
    rw [OK, mem_normVS]
    simp only [map_inv₀, map_natCast, norm_inv, hnorm, inv_one, le_refl]
  refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
  change ((n : OK p K) : K) * ((n : K))⁻¹ = 1
  rw [show ((n : OK p K) : K) = (n : K) from by simp]
  exact mul_inv_cancel₀ hn0

/-- `ιbar ∘ σ' = σ ∘ ιbar` for `σ'` over `decomp σ` (proved, from `resQ_spec`, `decomp_spec`). -/
theorem ιbar_apply {σ : GQp p} {σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) (y : AlgebraicClosure K) :
    ιbar p K (σ' y) = σ (ιbar p K y) := by
  obtain ⟨z, rfl⟩ := (eK K).surjective y
  have h1 : σ' (eK K z) = eK K (decomp p σ z) := by
    have := G0Galois.resQ_spec K σ' z
    rw [hσ'] at this
    exact this.symm
  simp only [ιbar, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [h1, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply, decomp_spec]

theorem norm_wild_eq {σ : GQp p} (hσ : σ ∈ wildSet) (u : Kbar p) : ‖σ u‖ = ‖u‖ := by
  by_cases hu : u = 0
  · rw [hu, map_zero]
  have h := hσ u hu
  have : σ u = u + (σ u - u) := by ring
  rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt h),
    max_eq_left (le_of_lt h)]

/-- **A wild `σ'` lies in the inertia group of `wK` (proved).** -/
theorem isInertia_of_wild {σ : GQp p} (hσ : σ ∈ wildSet)
    {σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) : PkgI2.IsInertia (wK p K) σ' := by
  have hnorm : ∀ y, ‖ιbar p K (σ' y)‖ = ‖ιbar p K y‖ := fun y => by
    rw [ιbar_apply hσ', norm_wild_eq hσ]
  have hnorm' : ∀ y, ‖ιbar p K (σ'⁻¹ y)‖ = ‖ιbar p K y‖ := fun y => by
    have := hnorm (σ'⁻¹ y)
    rw [show σ' (σ'⁻¹ y) = y from by
      change (σ' * σ'⁻¹) y = y; rw [mul_inv_cancel]; rfl] at this
    exact this.symm
  have hdec : σ' ∈ (wK p K).decompositionSubgroup K := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    change ‖ιbar p K (σ'⁻¹ x)‖ ≤ 1 ↔ ‖ιbar p K x‖ ≤ 1
    rw [hnorm']
  refine ⟨hdec, ?_⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  apply RingEquiv.ext
  intro r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  change (⟨σ', hdec⟩ : (wK p K).decompositionSubgroup K) • IsLocalRing.residue (wK p K) a =
    IsLocalRing.residue (wK p K) a
  rw [← IsLocalRing.ResidueField.residue_smul]
  apply Ideal.Quotient.eq.mpr
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  set b : wK p K := (⟨σ', hdec⟩ : (wK p K).decompositionSubgroup K) • a - a with hb
  have hbval : (b : AlgebraicClosure K) = σ' a - a := rfl
  have hlt : ‖ιbar p K (b : AlgebraicClosure K)‖ < 1 := by
    rw [hbval, map_sub, ιbar_apply hσ']
    by_cases ha0 : ιbar p K (a : AlgebraicClosure K) = 0
    · rw [ha0, map_zero, sub_zero, norm_zero]; exact zero_lt_one
    · exact lt_of_lt_of_le (hσ _ ha0) a.2
  obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.1 hu
  have hc' : ιbar p K (b : AlgebraicClosure K) * ιbar p K (c : AlgebraicClosure K) = 1 := by
    rw [← map_mul]
    have := congrArg Subtype.val hc
    simp only [Subring.coe_mul, OneMemClass.coe_one] at this
    rw [show ((b * c : wK p K) : AlgebraicClosure K) = (b : AlgebraicClosure K) * c from rfl] at this
    rw [this, map_one]
  have hcn : ‖ιbar p K (c : AlgebraicClosure K)‖ ≤ 1 := c.2
  have := congrArg norm hc'
  rw [norm_mul, norm_one] at this
  have h0 : 0 ≤ ‖ιbar p K (b : AlgebraicClosure K)‖ := norm_nonneg _
  nlinarith

/-- **`RaynaudPlace` when `A[m]` is `K`-rational, from the leaf R6 (proved).** -/
theorem raynaudPlace_rational (hR6 : ObjBridge.RaynaudCriterion) (A : PkgI3.AbVar K) {m : ℕ}
    (hm3 : 3 ≤ m) (hpm : ¬ p ∣ m)
    (hrat : ∀ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct τ P = P) :
    RaynaudPlace (p := p) A m := by
  intro σ hσ σ' hσ' _ ℓ hℓ hℓp n x hx
  have hℓp' : ¬ p ∣ ℓ := fun h =>
    hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out hℓ).mp h).symm
  exact hR6 K (OK p K) (wK p K) wK_comap (ObjBridge.toGrp A) m hm3 (isUnit_natCast_OK hpm)
    hrat σ' (isInertia_of_wild hσ hσ') ℓ hℓ (isUnit_natCast_OK hℓp') n x hx

end RaynaudSec

end G15Ram

end

#print axioms G15Ram.isInertia_of_wild
#print axioms G15Ram.raynaudPlace_rational
