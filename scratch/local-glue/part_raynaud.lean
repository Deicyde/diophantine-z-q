
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


/-! ### The general case: R6 over the field of `A[m]`, via the base change of `A` -/

section RaynaudGen

variable {p : ℕ} [Fact p.Prime]

/-- `normVS f ≠ ⊤` for a map of a field to `ℚ̄_p` (`1/p ∉`). -/
theorem normVS_ne_top {F : Type} [Field F] [CharZero F] (f : F →+* Kbar p) : normVS f ≠ ⊤ := by
  intro h
  have hmem : ((p : F))⁻¹ ∈ normVS f := by rw [h]; exact ValuationSubring.mem_top _
  rw [mem_normVS] at hmem
  simp only [map_inv₀, map_natCast, norm_inv] at hmem
  rw [norm_p_kbar, inv_inv] at hmem
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  linarith

/-- A natural number prime to `p` is a unit of `normVS f`. -/
theorem isUnit_natCast_normVS {F : Type} [Field F] (f : F →+* Kbar p) {n : ℕ} (hn : ¬ p ∣ n) :
    IsUnit ((n : normVS f)) := by
  have hnorm : ‖(n : Kbar p)‖ = 1 := norm_natCast_kbar hn
  have hn0 : (n : F) ≠ 0 := by
    intro h0
    have : (n : Kbar p) = 0 := by simpa using congrArg f h0
    rw [this, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hinv : ((n : F))⁻¹ ∈ normVS f := by
    rw [mem_normVS]
    simp only [map_inv₀, map_natCast, norm_inv, hnorm, inv_one, le_refl]
  refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
  change ((n : normVS f) : F) * ((n : F))⁻¹ = 1
  rw [show ((n : normVS f) : F) = (n : F) from by simp]
  exact mul_inv_cancel₀ hn0

/-- **Wild elements are inertial (general form, proved).** If `f ∘ τ = σ ∘ f` with `σ` wild, then
`τ` lies in the inertia group of `normVS f`. -/
theorem isInertia_of_wild_gen {K₀ Ω : Type} [Field K₀] [Field Ω] [Algebra K₀ Ω]
    (f : Ω →+* Kbar p) {σ : GQp p} (hσ : σ ∈ wildSet) (τ : Ω ≃ₐ[K₀] Ω)
    (hf : ∀ y, f (τ y) = σ (f y)) : PkgI2.IsInertia (normVS f) τ := by
  have hnorm : ∀ y, ‖f (τ y)‖ = ‖f y‖ := fun y => by rw [hf, norm_wild_eq hσ]
  have hnorm' : ∀ y, ‖f (τ⁻¹ y)‖ = ‖f y‖ := fun y => by
    have := hnorm (τ⁻¹ y)
    rw [show τ (τ⁻¹ y) = y from by
      change (τ * τ⁻¹) y = y; rw [mul_inv_cancel]; rfl] at this
    exact this.symm
  have hdec : τ ∈ (normVS f).decompositionSubgroup K₀ := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    change ‖f (τ⁻¹ x)‖ ≤ 1 ↔ ‖f x‖ ≤ 1
    rw [hnorm']
  refine ⟨hdec, ?_⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  apply RingEquiv.ext
  intro r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  change (⟨τ, hdec⟩ : (normVS f).decompositionSubgroup K₀) • IsLocalRing.residue (normVS f) a =
    IsLocalRing.residue (normVS f) a
  rw [← IsLocalRing.ResidueField.residue_smul]
  apply Ideal.Quotient.eq.mpr
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  set b : normVS f := (⟨τ, hdec⟩ : (normVS f).decompositionSubgroup K₀) • a - a with hb
  have hbval : (b : Ω) = τ a - a := rfl
  have hlt : ‖f (b : Ω)‖ < 1 := by
    rw [hbval, map_sub, hf]
    by_cases ha0 : f (a : Ω) = 0
    · rw [ha0, map_zero, sub_zero, norm_zero]; exact zero_lt_one
    · exact lt_of_lt_of_le (hσ _ ha0) a.2
  obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.1 hu
  have hc' : f (b : Ω) * f (c : Ω) = 1 := by
    rw [← map_mul]
    have := congrArg Subtype.val hc
    simp only [Subring.coe_mul, OneMemClass.coe_one] at this
    rw [show ((b * c : normVS f) : Ω) = (b : Ω) * c from rfl] at this
    rw [this, map_one]
  have hcn : ‖f (c : Ω)‖ ≤ 1 := c.2
  have := congrArg norm hc'
  rw [norm_mul, norm_one] at this
  have h0 : 0 ≤ ‖f (b : Ω)‖ := norm_nonneg _
  nlinarith

variable {K : Type} [Field K] [NumberField K]

/-- The stabilizer of `A(K̄)[m]` in `G_K`. -/
def torsStab (A : PkgI3.AbVar K) (m : ℕ) :
    Subgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) where
  carrier := {τ | ∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct τ P = P}
  mul_mem' {a b} ha hb P hP := by
    rw [← galAct_galAct, hb P hP, ha P hP]
  one_mem' P _ := by
    change PkgI3.AbVar.galHom 1 ≫ P = P
    rw [PkgI3.AbVar.galHom_one, Category.id_comp]
  inv_mem' {a} ha P hP := by
    calc A.galAct a⁻¹ P = A.galAct a⁻¹ (A.galAct a P) := by rw [ha P hP]
      _ = P := galAct_inv_galAct A a P

/-- The stabilizer of `A[m]` contains `G_{F'}` for a finite `F'/K` (from `ptFinite`, `A[m]`
finite by I2-Tors). -/
theorem exists_fin_le_torsStab (A : PkgI3.AbVar K) (m : ℕ) [NeZero m] (hT : TorsGL A m) :
    ∃ F' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K F' ∧
      F'.fixingSubgroup ≤ torsStab A m := by
  obtain ⟨e, -⟩ := hT
  haveI : Finite {P : A.Pt (AlgebraicClosure K) | P ^ m = 1} := Finite.of_equiv _ e.symm
  choose F hF hP using fun P : {P : A.Pt (AlgebraicClosure K) | P ^ m = 1} => ptFinite A P.1
  haveI : ∀ i, FiniteDimensional K (F i) := hF
  refine ⟨⨆ i, F i, inferInstance, fun τ hτ P hPm => ?_⟩
  refine hP ⟨P, hPm⟩ τ (fun x hx => ?_)
  rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
  exact hτ x ((le_iSup F ⟨P, hPm⟩) hx)

/-- **`RaynaudPlace` from the leaves R6 and I2-Tors (proved), for `dim A = 2`, `3 ≤ m`,
`p ∤ m`.** R6 is applied over `F = K(A[m])` (the fixed field of the stabilizer of `A[m]`, finite
by `ptFinite`) to the base change `A_F`, with the valuation rings at the place of `embP`
transported along `K̄ ≅ F̄`; points of `A_F` are those of `A` (`bcPt`, `trPt`, copied from
scratch/unram-tate). -/
theorem raynaudPlace_of_R6 (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (A : PkgI3.AbVar K) (hdim : A.dim = 2) {m : ℕ}
    (hm3 : 3 ≤ m) (hpm : ¬ p ∣ m) : RaynaudPlace (p := p) A m := by
  intro σ hσ σ' hσ' hfix ℓ hℓ hℓp n x hx
  set σg : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ' with hσg
  haveI : NeZero m := ⟨by omega⟩
  set H := torsStab A m with hHdef
  obtain ⟨F', hF'fd, hF'H⟩ := exists_fin_le_torsStab A m (torsGL_of_leaf hTors A hdim m (by omega))
  have hHopen : IsOpen (H : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) :=
    Subgroup.isOpen_mono hF'H (IntermediateField.fixingSubgroup_isOpen F')
  have hHclosed : IsClosed (H : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) :=
    Subgroup.isClosed_of_isOpen H hHopen
  set F : IntermediateField K (AlgebraicClosure K) := IntermediateField.fixedField H with hFdef
  have hFH : F.fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHclosed⟩
  have hFF' : F ≤ F' := by
    intro y hy
    rw [← InfiniteGalois.fixedField_fixingSubgroup F']
    rw [IntermediateField.mem_fixedField_iff] at hy ⊢
    exact fun τ hτ => hy τ (hF'H hτ)
  haveI : FiniteDimensional K F :=
    Module.Finite.of_injective (IntermediateField.inclusion hFF').toLinearMap
      (IntermediateField.inclusion hFF').injective
  haveI : FiniteDimensional ℚ F := Module.Finite.trans K F
  haveI : NumberField F := ⟨⟩
  -- `σ'` fixes `F`
  have hσ'F : ∀ y ∈ F, σg y = y := fun y hy =>
    ((IntermediateField.mem_fixedField_iff _ _).mp hy) σg hfix
  have hℓp' : ¬ p ∣ ℓ := fun h =>
    hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out hℓ).mp h).symm
  -- `K̄` is an algebraic closure of `F`
  haveI : IsAlgClosure F (AlgebraicClosure K) :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := K) (L := F) (A := AlgebraicClosure K)⟩
  let Ω := AlgebraicClosure F
  let ψ : Ω ≃ₐ[F] AlgebraicClosure K := IsAlgClosure.equiv F Ω (AlgebraicClosure K)
  let σF : AlgebraicClosure K ≃ₐ[F] AlgebraicClosure K :=
    { σg.toRingEquiv with commutes' := fun c => hσ'F c c.2 }
  let σ₁ : Ω ≃ₐ[F] Ω := (ψ.trans σF).trans ψ.symm
  have hσ₁ : ∀ y, ψ (σ₁ y) = σg (ψ y) := fun y => by
    simp only [σ₁, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
    rfl
  let f₁ : Ω →+* Kbar p := (ιbar p K).comp (ψ : Ω →+* AlgebraicClosure K)
  have hf₁ : ∀ y, f₁ (σ₁ y) = σ (f₁ y) := fun y => by
    change ιbar p K (ψ (σ₁ y)) = σ (ιbar p K (ψ y))
    rw [hσ₁ y]
    exact ιbar_apply (σ' := σg) hσ' (ψ y)
  let w₁ : ValuationSubring Ω := normVS f₁
  let O₁ : ValuationSubring F := normVS (f₁.comp (algebraMap F Ω))
  have hw₁ : w₁.comap (algebraMap F Ω) = O₁ := by ext; exact Iff.rfl
  haveI : IsDiscreteValuationRing O₁ :=
    ZInQ.NeronLG.isDiscreteValuationRing_of_ne_top _ (normVS_ne_top _)
  -- points of `A_F` over `Ω` are points of `A` over `K̄`
  let A₁ : PkgI3.AbVar F := A.baseChange F
  let ψK : Ω ≃ₐ[K] AlgebraicClosure K := ψ.restrictScalars K
  let Φ : A₁.Pt Ω ≃* A.Pt (AlgebraicClosure K) :=
    (UnramTate.bcPt A Ω).trans (UnramTate.trPt A ψK)
  have hΦ : ∀ (τ₁ : Ω ≃ₐ[F] Ω) (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K),
      (∀ y, τ (ψ y) = ψ (τ₁ y)) → ∀ z, Φ (A₁.galAct τ₁ z) = A.galAct τ (Φ z) := by
    intro τ₁ τ h z
    change UnramTate.trPt A ψK (UnramTate.bcPt A Ω (A₁.galAct τ₁ z)) =
      A.galAct τ (UnramTate.trPt A ψK (UnramTate.bcPt A Ω z))
    rw [UnramTate.bcPt_galAct, UnramTate.trPt_galAct A ψK (τ₁.restrictScalars K) τ h]
  have hrat : ∀ τ₁ : Ω ≃ₐ[F] Ω, ∀ z ∈ PkgI2.torsion (ObjBridge.toGrp A₁) Ω m,
      PkgI2.galAct (ObjBridge.toGrp A₁) τ₁ z = z := by
    intro τ₁ z₀ hz
    let z : A₁.Pt Ω := z₀
    change A₁.galAct τ₁ z = z
    let τF : AlgebraicClosure K ≃ₐ[F] AlgebraicClosure K := (ψ.symm.trans τ₁).trans ψ
    let τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := τF.restrictScalars K
    have hτ : ∀ y, τ (ψ y) = ψ (τ₁ y) := fun y => by
      change ψ (τ₁ (ψ.symm (ψ y))) = ψ (τ₁ y)
      rw [AlgEquiv.symm_apply_apply]
    have hτH : τ ∈ H := by
      rw [← hFH, IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      exact τF.commutes ⟨y, hy⟩
    have hz' : z ^ m = 1 := hz
    have hzm : (Φ z) ^ m = 1 := by rw [← map_pow, hz', map_one]
    have h1 := hΦ τ₁ τ hτ z
    rw [hτH (Φ z) hzm] at h1
    exact Φ.injective h1
  have hxm : (Φ.symm x) ^ (ℓ ^ n) = 1 := by rw [← map_pow, hx, map_one]
  have hU := hR6 F O₁ w₁ hw₁ (ObjBridge.toGrp A₁) m hm3 (isUnit_natCast_normVS _ hpm) hrat σ₁
    (isInertia_of_wild_gen f₁ hσ σ₁ hf₁) ℓ hℓ (isUnit_natCast_normVS _ hℓp') n (Φ.symm x) hxm
  have hU' : A₁.galAct σ₁ (A₁.galAct σ₁ (Φ.symm x)) * (A₁.galAct σ₁ (Φ.symm x))⁻¹ *
      (A₁.galAct σ₁ (Φ.symm x))⁻¹ * Φ.symm x = 1 := hU
  have hcomm : ∀ z, Φ (A₁.galAct σ₁ z) = A.galAct σg (Φ z) :=
    hΦ σ₁ σg (fun y => (hσ₁ y).symm)
  have h2 := congrArg Φ hU'
  simp only [map_one, map_mul, map_inv, hcomm, MulEquiv.apply_symm_apply] at h2
  exact h2

/-- **`TateWildK` at `p ≥ 7`, `p ≠ ℓ`, from the leaves R6 and I2-Tors alone (proved).**
`m = 3` for `p ≠ 13`, `m = 7` for `p = 13` (`raynaudPlace_of_R6`, `tateWildK_of_raynaud`). -/
theorem tateWildK_of_R6 (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    {A : PkgI3.AbVar K} (hdim : A.dim = 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (h7 : 7 ≤ p) :
    TateWildK (p := p) A ℓ := by
  have hp : p.Prime := Fact.out
  refine tateWildK_of_raynaud hℓp h7 hTors hdim (fun _ => raynaudPlace_of_R6 hR6 hTors A hdim
    (by norm_num) ?_) (fun h13 => raynaudPlace_of_R6 hR6 hTors A hdim (by norm_num) ?_)
  · intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  · intro h
    rw [h13] at h
    norm_num at h

end RaynaudGen

end G15Ram

end

#print axioms G15Ram.isInertia_of_wild
#print axioms G15Ram.raynaudPlace_rational
#print axioms G15Ram.raynaudPlace_of_R6
#print axioms G15Ram.tateWildK_of_R6
