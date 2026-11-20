import ZInQKernel.Contrib.OneProof.RC.CMField2.HeegnerLattice
import ZInQKernel.Contrib.OneProof.RC.CMField2.OrderGenerator
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_jLattice_ofTau

/-! Ideal lattices of primitive binary quadratic forms. On-the-spot calculation
(c), for tex 2915–2916. -/

noncomputable section
open NumberField Module TauCeti.GlobalNumberFields FractionalIdeal
open ZInQ.Contrib.CloudB3RC53.CST
open scoped nonZeroDivisors Pointwise

namespace ZInQ.Manuscript.RC.CMField2

variable {K : Type} [Field K] [NumberField K]
variable (O : NumberFieldOrder K)

/-- The O-span of the two lattice generators. -/
def formIdeal (a : ℤ) (ω : K) : FractionalIdeal O.toSubalgebra⁰ K :=
  spanFinset O.toSubalgebra Finset.univ ![(a : K), ω]

theorem formIdeal_coe (a : ℤ) (ω : K) :
    ((formIdeal O a ω : FractionalIdeal O.toSubalgebra⁰ K) : Submodule O.toSubalgebra K) =
      Submodule.span O.toSubalgebra {(a : K), ω} := by
  rw [formIdeal, spanFinset_coe]
  congr 1
  ext x
  simp [eq_comm, or_comm]

/-- If 1 and ω generate the order and ω solves the form equation, the ideal
has the intended underlying integer lattice. -/
theorem formIdeal_restrictScalars (a B c : ℤ) (ω : K)
    (hgen : ∀ x : O.toSubalgebra, ∃ u v : ℤ, (x : K) = (u : K) + (v : K) * ω)
    (hω : ω ^ 2 + (B : K) * ω + (a : K) * (c : K) = 0) :
    ((formIdeal O a ω : Submodule O.toSubalgebra K).restrictScalars ℤ) = pairLattice a ω := by
  let S := pairLattice a ω
  have ha : (a : K) ∈ S := Submodule.subset_span (by simp)
  have hw : ω ∈ S := Submodule.subset_span (by simp)
  have hmul_a : ω * (a : K) ∈ S := by
    rw [mul_comm, ← zsmul_eq_mul]
    exact S.smul_mem a hw
  have hmul_w : ω * ω ∈ S := by
    have he : ω * ω = (-B) • ω + (-c) • (a : K) := by
      simp only [zsmul_eq_mul, Int.cast_neg]
      linear_combination hω
    rw [he]
    exact S.add_mem (S.smul_mem _ hw) (S.smul_mem _ ha)
  let T : Submodule O.toSubalgebra K :=
    { S.toAddSubmonoid with
      smul_mem' := fun r x hx => by
        obtain ⟨u, v, hr⟩ := hgen r
        have hx' : ω * x ∈ S := by
          have hz : x ∈ S := hx
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
          · intro z hz
            rcases (Set.mem_insert_iff.mp hz) with rfl | h
            · exact hmul_a
            · rw [Set.mem_singleton_iff.mp h]
              exact hmul_w
          · simp
          · intro x y _ _ hx hy
            simpa only [mul_add] using S.add_mem hx hy
          · intro r x _ hx
            simpa only [mul_smul_comm] using S.smul_mem r hx
        rw [Algebra.smul_def]
        change (r : K) * x ∈ S
        rw [hr, add_mul, mul_assoc, ← zsmul_eq_mul, ← zsmul_eq_mul]
        exact S.add_mem (S.smul_mem u hx) (S.smul_mem v hx') }
  rw [formIdeal_coe]
  refine le_antisymm ?_ (Submodule.span_le.mpr ?_)
  · change _ ≤ T.restrictScalars ℤ
    apply Submodule.restrictScalars_mono ℤ
    apply Submodule.span_le.mpr
    intro x hx
    change x ∈ S
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hw
  · intro x hx
    exact Submodule.subset_span hx

/-- The product of the form ideal and its conjugate is the principal ideal (a).
Primitivity is supplied as the integer Bézout equation. -/
theorem formIdeal_mul_conjugate (a B c : ℤ) (ω : K) (hmem : ω ∈ O.toSubalgebra)
    (hω : ω ^ 2 + (B : K) * ω + (a : K) * (c : K) = 0)
    {u v w : ℤ} (hbez : u * a + v * B + w * c = 1) :
    formIdeal O a ω * formIdeal O a (-(B : K) - ω) = spanSingleton O.toSubalgebra⁰ (a : K) := by
  let ω' : K := -(B : K) - ω
  have hw' : ω' ∈ O.toSubalgebra := O.toSubalgebra.sub_mem
    (O.toSubalgebra.neg_mem (O.toSubalgebra.intCast_mem B)) hmem
  have hww : ω * ω' = (a : K) * (c : K) := by
    dsimp [ω']
    linear_combination -hω
  apply coeToSubmodule_injective
  change ((formIdeal O a ω * formIdeal O a ω' : FractionalIdeal O.toSubalgebra⁰ K) :
    Submodule O.toSubalgebra K) = ((spanSingleton O.toSubalgebra⁰ (a : K) :
    FractionalIdeal O.toSubalgebra⁰ K) : Submodule O.toSubalgebra K)
  rw [coe_mul, formIdeal_coe, formIdeal_coe, coe_spanSingleton, Submodule.span_mul_span]
  have hin (x : K) (hx : x ∈ O.toSubalgebra) :
      (a : K) * x ∈ Submodule.span O.toSubalgebra ({(a : K)} : Set K) := by
    refine Submodule.mem_span_singleton.mpr ⟨⟨x,hx⟩, ?_⟩
    rw [Algebra.smul_def]
    change x * (a : K) = (a : K) * x
    exact mul_comm _ _
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro z ⟨x, hx, y, hy, hz⟩
    change x * y = z at hz
    rw [← hz]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
    · exact hin _ (O.toSubalgebra.intCast_mem a)
    · exact hin _ hw'
    · rw [mul_comm]; exact hin _ hmem
    · rw [hww]; exact hin _ (O.toSubalgebra.intCast_mem c)
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    let S := Submodule.span O.toSubalgebra
      (({(a : K), ω} : Set K) * {(a : K), ω'})
    have h₁ : (a : K) * (a : K) ∈ S :=
      Submodule.subset_span ⟨_, by simp, _, by simp, rfl⟩
    have h₂ : (a : K) * (B : K) ∈ S := by
      have hcw : (a : K) * ω' ∈ S := Submodule.subset_span ⟨_, by simp, _, by simp, rfl⟩
      have hmw : ω * (a : K) ∈ S := Submodule.subset_span ⟨_, by simp, _, by simp, rfl⟩
      have he : (a : K) * (B : K) = -((a : K) * ω' + ω * (a : K)) := by dsimp [ω']; ring
      rw [he]
      exact S.neg_mem (S.add_mem hcw hmw)
    have h₃ : (a : K) * (c : K) ∈ S :=
      hww ▸ Submodule.subset_span ⟨_, by simp, _, by simp, rfl⟩
    have he : u • ((a : K) * (a : K)) + v • ((a : K) * (B : K)) +
        w • ((a : K) * (c : K)) = (a : K) := by
      simp only [zsmul_eq_mul]
      have h : (u : K) * (a : K) + (v : K) * (B : K) + (w : K) * (c : K) = 1 := by
        exact_mod_cast hbez
      linear_combination (a : K) * h
    change (a : K) ∈ S
    rw [← he]
    exact (S.restrictScalars ℤ).add_mem
      ((S.restrictScalars ℤ).add_mem
        ((S.restrictScalars ℤ).smul_mem _ h₁) ((S.restrictScalars ℤ).smul_mem _ h₂))
      ((S.restrictScalars ℤ).smul_mem _ h₃)

/-- A primitive form of nonzero leading coefficient gives an invertible
fractional ideal in the specified order. -/
theorem formIdeal_isUnit (a B c : ℤ) (ω : K) (hmem : ω ∈ O.toSubalgebra)
    (ha : a ≠ 0) (hprim : Int.gcd (Int.gcd a B : ℤ) c = 1)
    (hω : ω ^ 2 + (B : K) * ω + (a : K) * (c : K) = 0) :
    IsUnit (formIdeal O a ω) := by
  have hb₁ := Int.gcd_eq_gcd_ab a B
  let g : ℤ := Int.gcd a B
  change g = _ at hb₁
  have hb₂ := Int.gcd_eq_gcd_ab g c
  rw [show Int.gcd g c = 1 from hprim, Nat.cast_one] at hb₂
  have hbez : (Int.gcdA (Int.gcd a B : ℤ) c * Int.gcdA a B) * a +
      (Int.gcdA (Int.gcd a B : ℤ) c * Int.gcdB a B) * B +
      Int.gcdB (Int.gcd a B : ℤ) c * c = 1 := by linear_combination -hb₂ - Int.gcdA g c * hb₁
  have he := formIdeal_mul_conjugate O a B c ω hmem hω hbez
  apply isUnit_of_mul_isUnit_left (y := formIdeal O a (-(B : K) - ω))
  rw [he]
  have h : (a : K) ≠ 0 := by exact_mod_cast ha
  exact ⟨toPrincipalIdeal O.toSubalgebra K (Units.mk0 _ h), coe_toPrincipalIdeal _⟩

/-- The j-value of the displayed fractional ideal is the j-value of the form
parameter, if its chosen order generator has the indicated complex image. -/
theorem analyticJ_eq_singularModulus_of_generator (hk : finrank ℚ K = 2)
    (hc : IsTotallyComplex K) (κ : K →+* ℂ) {a B c d : ℤ}
    (ha : 0 < a) (hd : d < 0) (ω : K) (hmem : ω ∈ O.toSubalgebra)
    (hgen : ∀ x : O.toSubalgebra, ∃ u v : ℤ, (x : K) = (u : K) + (v : K) * ω)
    (hω : ω ^ 2 + (B : K) * ω + (a : K) * (c : K) = 0)
    (he : κ ω = (-(B : ℂ) + Complex.I * (Real.sqrt (-(d : ℝ)) : ℂ)) / 2)
    (hprim : Int.gcd (Int.gcd a B : ℤ) c = 1) :
    ∃ J : O.invertibleProperFractionalIdeals,
      X0Model.analyticJ (cmPoint a B d) = singularModulus O hk hc κ J := by
  let hunit := formIdeal_isUnit O a B c ω hmem ha.ne' hprim hω
  let J : O.invertibleProperFractionalIdeals := hunit.unit
  let L := PeriodPair.ofTau (cmPoint a B d)
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  let u := Units.mk0 (a : ℂ) ha0
  refine ⟨J, ?_⟩
  rw [← show L.jLattice = X0Model.analyticJ (cmPoint a B d) from PeriodPair.jLattice_ofTau _]
  change L.jLattice = (idealPeriod O hk hc κ J).jLattice
  rw [← jLattice_scale L u]
  apply jLattice_eq_of_lattice_eq
  apply SetLike.coe_injective
  rw [idealPeriod_lattice, show J.val = formIdeal O a ω from hunit.unit_spec]
  have hJ : (formIdeal O a ω : Set K) = (pairLattice a ω : Set K) :=
    congrArg (fun U : Submodule ℤ K => (U : Set K))
      (formIdeal_restrictScalars O a B c ω hgen hω)
  rw [hJ]
  let k := κ.toRatAlgHom.toLinearMap.restrictScalars ℤ
  change ((L.scale u).lattice : Set ℂ) = ((pairLattice a ω).map k : Set ℂ)
  rw [pairLattice, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
  have hw : (a : ℂ) * (cmPoint a B d : ℂ) = κ ω := by
    rw [coe_cmPoint_of_neg ha hd, he]
    field_simp
  change (Submodule.span ℤ {((a : ℂ) * (cmPoint a B d : ℂ)), (a : ℂ) * 1} : Set ℂ) =
    (Submodule.span ℤ {κ (a : K), κ ω} : Set ℂ)
  rw [hw, mul_one, map_intCast]
  congr 2
  exact Set.pair_comm _ _

/-- The oriented level ideal times the ideal for the scaled parameter is the
original form ideal. If the level ideal is invertible this identifies the
scaled ideal with its inverse translate. -/
theorem formIdeal_mul_scaled {N A B C a : ℤ} (ω : K) (ha : A = N * a)
    (hcop : IsCoprime N B)
    (hgen : ∀ x : O.toSubalgebra, ∃ u v : ℤ, (x : K) = (u : K) + (v : K) * ω)
    (hω : ω ^ 2 + (B : K) * ω + (A : K) * (C : K) = 0) :
    formIdeal O N ω * formIdeal O a ω = formIdeal O A ω := by
  have hscale : (A : K) = (N : K) * (a : K) := by exact_mod_cast ha
  have h₁ : ω ^ 2 + (B : K) * ω + (N : K) * ((a * C : ℤ) : K) = 0 := by
    push_cast
    rw [hscale] at hω
    linear_combination hω
  have h₂ : ω ^ 2 + (B : K) * ω + (a : K) * ((N * C : ℤ) : K) = 0 := by
    push_cast
    rw [hscale] at hω
    linear_combination hω
  apply coeToSubmodule_injective
  apply SetLike.coe_injective
  change (((formIdeal O N ω * formIdeal O a ω : FractionalIdeal O.toSubalgebra⁰ K) :
      Submodule O.toSubalgebra K).restrictScalars ℤ : Set K) = _
  change _ = (((formIdeal O A ω : Submodule O.toSubalgebra K).restrictScalars ℤ) : Set K)
  rw [coe_mul, Submodule.restrictScalars_mul, formIdeal_restrictScalars O N B (a * C) ω hgen h₁,
    formIdeal_restrictScalars O a B (N * C) ω hgen h₂,
    formIdeal_restrictScalars O A B C ω hgen hω, heegner_pairLattice_mul ω ha hcop hω]

/-- The scaled lattice is the inverse translate by an invertible oriented
level ideal. -/
theorem formIdeal_scaled_eq_levelInverse_mul {N A B C a : ℤ} (ω : K) (ha : A = N * a)
    (hN : N ≠ 0) (hcop : IsCoprime N B) (hmem : ω ∈ O.toSubalgebra)
    (hgen : ∀ x : O.toSubalgebra, ∃ u v : ℤ, (x : K) = (u : K) + (v : K) * ω)
    (hω : ω ^ 2 + (B : K) * ω + (A : K) * (C : K) = 0) :
    ∃ J : O.invertibleProperFractionalIdeals, J.val = formIdeal O N ω ∧
      formIdeal O a ω = (J⁻¹).val * formIdeal O A ω := by
  have hω' : ω ^ 2 + (B : K) * ω + (N : K) * ((a * C : ℤ) : K) = 0 := by
    have he : (A : K) = (N : K) * (a : K) := by exact_mod_cast ha
    rw [he] at hω
    push_cast
    linear_combination hω
  have hprim : Int.gcd (Int.gcd N B : ℤ) (a * C) = 1 := by
    rw [Int.isCoprime_iff_gcd_eq_one.mp hcop, Nat.cast_one]
    simp
  obtain ⟨J, hJ⟩ := formIdeal_isUnit O N B (a * C) ω hmem hN hprim hω'
  refine ⟨J, hJ, ?_⟩
  rw [← formIdeal_mul_scaled O ω ha hcop hgen hω, ← hJ, ← mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, one_mul]

/-- The two plane coordinate values of a Heegner point are singular moduli
for the same order in a single complex embedding. -/
theorem exists_heegner_singularModuli_in_embedding (hk : finrank ℚ K = 2) (hc : IsTotallyComplex K)
    (κ : K →+* ℂ)
    {N : ℕ} [NeZero N] {d A B C : ℤ} (hD : O.discr = d) (hd : d < 0)
    (hcop : IsCoprime d (N : ℤ)) (hf : IsHeegnerForm N d A B C) :
    ∃ (I J : O.invertibleProperFractionalIdeals),
      X0Model.analyticJ (cmPoint A B d) = singularModulus O hk hc κ I ∧
      X0Model.analyticJN N (cmPoint A B d) = singularModulus O hk hc κ J := by
  obtain ⟨ω, hmem, hgen, hω, he⟩ := exists_heegner_generator_in_embedding O hk hc κ hD hd hf.2.2.1
  obtain ⟨a, ha, hg⟩ := heegner_scaled_form hcop hf
  have hω' : ω ^ 2 + (B : K) * ω + (a : K) * (((N : ℤ) * C : ℤ) : K) = 0 := by
    have hh : (A : K) = (N : K) * (a : K) := by exact_mod_cast ha
    rw [hh] at hω
    push_cast
    linear_combination hω
  obtain ⟨I, hI⟩ := analyticJ_eq_singularModulus_of_generator O hk hc κ hf.1 hd
    ω hmem hgen hω he hf.2.2.2
  obtain ⟨J, hJ⟩ := analyticJ_eq_singularModulus_of_generator O hk hc κ hg.1 hd
    ω hmem hgen hω' he hg.2.2.2
  exact ⟨I, J, hI, by rw [X0Model.analyticJN, dilate_cmPoint_eq hf.1 ha hd]; exact hJ⟩

/-- Both coordinates are proper ideal singular moduli in one complex embedding. -/
theorem exists_heegner_singularModuli (hk : finrank ℚ K = 2) (hc : IsTotallyComplex K)
    {N : ℕ} [NeZero N] {d A B C : ℤ} (hD : O.discr = d) (hd : d < 0)
    (hcop : IsCoprime d (N : ℤ)) (hf : IsHeegnerForm N d A B C) :
    ∃ (κ : K →+* ℂ) (I J : O.invertibleProperFractionalIdeals),
      X0Model.analyticJ (cmPoint A B d) = singularModulus O hk hc κ I ∧
      X0Model.analyticJN N (cmPoint A B d) = singularModulus O hk hc κ J :=
  ⟨Classical.choice inferInstance,
    exists_heegner_singularModuli_in_embedding O hk hc _ hD hd hcop hf⟩


end ZInQ.Manuscript.RC.CMField2
