import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Orders.Picard
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_PeriodPair_Uniformization
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_discriminant_ne_zero
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! Complex lattices of invertible fractional ideals. Provenance (c). -/

noncomputable section

open NumberField Module TauCeti.GlobalNumberFields FractionalIdeal
open scoped nonZeroDivisors

namespace ZInQ.Manuscript.RC.CMField2

variable {K : Type} [Field K] [NumberField K]

/-- Port of FowlerBridges.exists_fractionalIdeal_basis at dfc6804f30bb08ec33abefeca76cba33405b8984,
ZInQKernel/Contrib/OneProof/FowlerBridgesIdeals.lean. -/
theorem exists_ideal_basis (O : NumberFieldOrder K) (hk : finrank ℚ K = 2)
    (J : FractionalIdeal O.toSubalgebra⁰ K) (hJ : J ≠ 0) :
    Nonempty (Basis (Fin 2) ℤ J) := by
  classical
  let e := (J.equivNumOfIsLocalization).restrictScalars ℤ
  let f := ((Submodule.subtype J.num).restrictScalars ℤ).comp e.toLinearMap
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  let : Module.Finite ℤ J := Module.Finite.of_injective f hf
  let : Module.Free ℤ J := Free.of_equiv (LinearEquiv.ofInjective f hf).symm
  have hO : finrank ℤ O.toSubalgebra = 2 := by
    let b := Free.chooseBasis ℤ O.toSubalgebra
    rw [finrank_eq_card_basis b, ← finrank_eq_card_basis (b.localizationLocalization ℚ ℤ⁰ K), hk]
  obtain ⟨x, hx, hx0⟩ : ∃ x : K, x ∈ J ∧ x ≠ 0 := by
    by_contra! h
    apply hJ
    ext y
    rw [mem_zero_iff]
    exact ⟨h y, fun hy => hy.symm ▸ J.zero_mem⟩
  let g := (LinearMap.toSpanSingleton O.toSubalgebra J ⟨x, hx⟩).restrictScalars ℤ
  have hg : Function.Injective g := by
    intro a b hab
    have he : (a : K) * x = (b : K) * x := by
      simpa [g, Algebra.smul_def] using congrArg (fun z : J => (z : K)) hab
    exact Subtype.ext (mul_right_cancel₀ hx0 he)
  have hlo := LinearMap.finrank_le_finrank_of_injective hg
  have hhi := LinearMap.finrank_le_finrank_of_injective hf
  have hdim : finrank ℤ J = 2 := by omega
  let b := Free.chooseBasis ℤ J
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ J) = Fintype.card (Fin 2) := by
    rw [← finrank_eq_card_basis b, hdim, Fintype.card_fin]
  exact ⟨b.reindex (Fintype.equivOfCardEq hcard)⟩

/-- A rational basis of an imaginary quadratic field maps to a real basis of ℂ.
It suffices to normalize the second vector to 1: if the first vector were then
real, both basis vectors would be fixed by conjugation. -/
private theorem embedding_indep (κ : K →+* ℂ) [IsTotallyComplex K]
    (b : Basis (Fin 2) ℚ K) : LinearIndependent ℝ ![κ (b 0), κ (b 1)] := by
  let v := b 1
  let u := b 0
  have hv : v ≠ 0 := b.ne_zero 1
  have hκv : κ v ≠ 0 := (_root_.map_ne_zero κ).mpr hv
  let e := ((LinearEquiv.smulOfNeZero K K v hv).restrictScalars ℚ).symm
  let c := b.map e
  have hc0 : c 0 = u / v := by
    change v⁻¹ * u = u / v
    rw [div_eq_mul_inv, mul_comm]
  have hc1 : c 1 = 1 := by
    change v⁻¹ * v = 1
    exact inv_mul_cancel₀ hv
  have him : (κ (u / v)).im ≠ 0 := by
    intro he
    apply IsTotallyComplex.complexEmbedding_not_isReal κ
    rw [ComplexEmbedding.isReal_iff]
    have hlin : (ComplexEmbedding.conjugate κ).toRatAlgHom.toLinearMap =
        κ.toRatAlgHom.toLinearMap := by
      apply c.ext
      intro i
      fin_cases i
      · change (starRingEnd ℂ) (κ (c 0)) = κ (c 0)
        rw [hc0, Complex.conj_eq_iff_im]
        exact he
      · change (starRingEnd ℂ) (κ (c 1)) = κ (c 1)
        rw [hc1, map_one, map_one]
    exact RingHom.ext fun x => LinearMap.congr_fun hlin x
  rw [LinearIndependent.pair_iff]
  intro a d h
  change a • κ u + d • κ v = 0 at h
  have hh : (a : ℂ) * (κ u / κ v) + (d : ℂ) = 0 := by
    have hh := congrArg (fun z : ℂ => z / κ v) h
    simpa only [Complex.real_smul, add_div, mul_div_assoc, mul_div_cancel_right₀ _ hκv,
      zero_div] using hh
  have hi := congrArg Complex.im hh
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, Complex.zero_im, ← map_div₀] at hi
  have ha : a = 0 := (mul_eq_zero.mp hi).resolve_right him
  simp [ha] at hh
  exact ⟨ha, hh⟩

variable (O : NumberFieldOrder K)

/-- A period pair for the complex image of the given invertible fractional ideal. -/
def idealPeriod (hk : finrank ℚ K = 2) (hc : IsTotallyComplex K)
    (κ : K →+* ℂ) (J : O.invertibleProperFractionalIdeals) : PeriodPair := by
  letI := hc
  let b := Classical.choice (exists_ideal_basis O hk J.val (Units.ne_zero J))
  let v : Fin 2 → K := fun i => b i
  have hv : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp
    (b.linearIndependent.map' ((Submodule.subtype J.val.val).restrictScalars ℤ)
      (LinearMap.ker_eq_bot_of_injective Subtype.val_injective))
  let c := basisOfLinearIndependentOfCardEqFinrank hv (by simpa using hk.symm)
  have hv' : ⇑c = v := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  exact ⟨κ (v 0), κ (v 1), by simpa only [hv'] using embedding_indep κ c⟩

set_option backward.isDefEq.respectTransparency false in
theorem idealPeriod_lattice (hk : finrank ℚ K = 2) (hc : IsTotallyComplex K)
    (κ : K →+* ℂ) (J : O.invertibleProperFractionalIdeals) :
    ((idealPeriod O hk hc κ J).lattice : Set ℂ) = κ '' (J.val : Set K) := by
  let b := Classical.choice (exists_ideal_basis O hk J.val (Units.ne_zero J))
  let k := κ.toRatAlgHom.toLinearMap.restrictScalars ℤ
  let j := (Submodule.subtype J.val.val).restrictScalars ℤ
  have hspan : Submodule.span ℤ (Set.range (fun i => k (j (b i)))) =
      LinearMap.range (k.comp j) := by
    change Submodule.span ℤ (Set.range ((k.comp j) ∘ ⇑b)) = _
    rw [Set.range_comp (⇑(k.comp j)) (⇑b), ← Submodule.map_span, b.span_eq, Submodule.map_top]
  have hvec : Set.range (fun i => k (j (b i))) = {κ (b 0 : K), κ (b 1 : K)} := by
    ext z
    change z ∈ Set.range (fun i => κ (b i : K)) ↔ _
    simp [Fin.exists_fin_two, eq_comm]
  change (Submodule.span ℤ {κ (b 0 : K), κ (b 1 : K)} : Set ℂ) = _
  rw [← hvec, hspan]
  ext z
  exact ⟨fun ⟨x, hx⟩ => ⟨x, x.property, hx⟩, fun ⟨x, hx, hx'⟩ => ⟨⟨x, hx⟩, hx'⟩⟩

/-- The singular modulus of an embedded invertible proper ideal. -/
def singularModulus (hk : finrank ℚ K = 2) (hc : IsTotallyComplex K)
    (κ : K →+* ℂ) (J : O.invertibleProperFractionalIdeals) : ℂ :=
  (idealPeriod O hk hc κ J).jLattice

/-- The singular modulus depends only on the lattice it presents. -/
theorem jLattice_eq_of_lattice_eq {L M : PeriodPair} (h : L.lattice = M.lattice) :
    L.jLattice = M.jLattice := by
  have hG (n : ℕ) : L.G n = M.G n := by
    unfold PeriodPair.G
    let e : L.lattice ≃ M.lattice := (LinearEquiv.ofEq _ _ h).toEquiv
    rw [← e.tsum_eq]; rfl
  unfold PeriodPair.jLattice PeriodPair.g₂ PeriodPair.g₃
  rw [hG 4, hG 6]

/-- Rescaling a period pair leaves the singular modulus unchanged. -/
theorem jLattice_scale (L : PeriodPair) (a : ℂˣ) : (L.scale a).jLattice = L.jLattice := by
  let b := ((a : ℂ) ^ 12)⁻¹
  have hb : b ≠ 0 := inv_ne_zero (pow_ne_zero _ a.ne_zero)
  have h₂ := P2MW.S_PeriodPair_discriminant_ne_zero.PeriodPair.g₂_scale L a
  have h₃ := P2MW.S_PeriodPair_discriminant_ne_zero.PeriodPair.g₃_scale L a
  have h₂' : (L.scale a).g₂ ^ 3 = b * L.g₂ ^ 3 := by
    rw [h₂, mul_pow, inv_pow, ← pow_mul]
  have h₃' : (L.scale a).g₃ ^ 2 = b * L.g₃ ^ 2 := by
    rw [h₃, mul_pow, inv_pow, ← pow_mul]
  have hD : b * L.g₂ ^ 3 - 27 * (b * L.g₃ ^ 2) = b * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    ring
  unfold PeriodPair.jLattice
  rw [h₂', h₃', hD, mul_left_comm (1728 : ℂ), mul_div_mul_left _ _ hb]

/-- The scaled lattice is the image of multiplication by the scaling factor. -/
theorem lattice_scale (L : PeriodPair) (a : ℂˣ) :
    ((L.scale a).lattice : Set ℂ) = (fun z : ℂ => (a : ℂ) * z) '' (L.lattice : Set ℂ) := by
  let f : ℂ →ₗ[ℤ] ℂ := (Algebra.lmul ℝ ℂ (a : ℂ)).restrictScalars ℤ
  change (Submodule.span ℤ {(a : ℂ) * L.ω₁, (a : ℂ) * L.ω₂} : Set ℂ) =
    (Submodule.map f L.lattice : Set ℂ)
  rw [PeriodPair.lattice, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
  rfl

/-- Equivalent invertible ideals have the same singular modulus. -/
theorem singularModulus_eq_of_mkPic_eq (hk : finrank ℚ K = 2) (hc : IsTotallyComplex K)
    (κ : K →+* ℂ) {I J : O.invertibleProperFractionalIdeals} (h : O.mkPic I = O.mkPic J) :
    singularModulus O hk hc κ I = singularModulus O hk hc κ J := by
  have h₁ : O.mkPic (J / I) = 1 := by rw [map_div, h, div_self']
  have hpr := ClassGroup.mk_eq_one_iff.mp h₁
  obtain ⟨a', ha'⟩ := @Submodule.IsPrincipal.principal _ _ _ _ _ _ hpr
  have hI : (J / I).val = spanSingleton O.toSubalgebra⁰ a' :=
    coeToSubmodule_injective (ha'.trans (coe_spanSingleton _ _).symm)
  have ha0 : a' ≠ 0 := by
    intro he
    apply Units.ne_zero (J / I)
    rw [hI, he, map_zero]
  let a := Units.mk0 a' ha0
  have ha : toPrincipalIdeal O.toSubalgebra K a = J / I := by
    apply Units.ext
    rw [coe_toPrincipalIdeal, hI]
    rfl
  have hj : toPrincipalIdeal O.toSubalgebra K a * I = J := by rw [ha, div_mul_cancel]
  let al := Units.map κ.toMonoidHom a
  let L := idealPeriod O hk hc κ I
  let M := idealPeriod O hk hc κ J
  rw [singularModulus, singularModulus, ← jLattice_scale L al]
  apply jLattice_eq_of_lattice_eq
  apply SetLike.coe_injective
  rw [lattice_scale, idealPeriod_lattice, idealPeriod_lattice]
  have hJ : J.val = spanSingleton O.toSubalgebra⁰ (a : K) * I.val := by
    rw [← hj, Units.val_mul, coe_toPrincipalIdeal]
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(a : K) * x, ?_, map_mul κ _ _⟩
    change (a : K) * x ∈ J.val
    rw [hJ, mem_singleton_mul]
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    change x ∈ J.val at hx
    rw [hJ, mem_singleton_mul] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨κ y, ⟨y, hy, rfl⟩, (map_mul κ _ _).symm⟩


end ZInQ.Manuscript.RC.CMField2
