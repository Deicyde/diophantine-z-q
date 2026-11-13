import ZInQKernel.Contrib.TYZGenus.RingClass
open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory

noncomputable section
namespace ZInQ.Contrib.TYZGenus.RingClass
open ZInQ.RouteK.Rank5b

section Restrict
variable {K : Type} [Field K] [NumberField K]

theorem ideleClassArtinMap_restrict {M L : IntermediateField K (SeparableClosure K)}
    [NumberField M] [NumberField L] [IsAbelianGalois K M] [IsAbelianGalois K L] (h : M ≤ L)
    (c : IdeleClassGroup (𝓞 K) K) :
    (IntermediateField.inclusion h).restrictNormalHom (ideleClassArtinMap K L c) =
      ideleClassArtinMap K M c := by
  apply Abelianization.of_injective
  have h1 := of_ideleClassArtinMap K L L.val c
  have h2 := of_ideleClassArtinMap K M M.val c
  have h3 := congrArg (fun φ => φ (Additive.ofMul c))
    (globalArtinMap_comp K L (IntermediateField.inclusion h) L.val)
  have hv : L.val.comp (IntermediateField.inclusion h) = M.val := by ext; rfl
  simp only [AddMonoidHom.comp_apply, hv] at h3
  rw [h2, ← h3, ← Abelianization.map_of, h1]
  rfl

/-- The canonical surjection `Pic O → Cl(K)`, through idele classes: `Q_max ∘ Q_O⁻¹`. -/
def picToMax (O : NumberFieldOrder K) : Pic O →* Pic (maximalNumberFieldOrder K) :=
  (QuotientGroup.lift _ (ringClassIdeleQuotient (maximalNumberFieldOrder K))
    (ker_le_ker_maximal O)).comp
    (QuotientGroup.quotientKerEquivOfSurjective _ (ringClassIdeleQuotient_surjective O)).symm.toMonoidHom

theorem picToMax_ringClassIdeleQuotient (O : NumberFieldOrder K) (t : IdeleClassGroup (𝓞 K) K) :
    picToMax O (ringClassIdeleQuotient O t) = ringClassIdeleQuotient (maximalNumberFieldOrder K) t := by
  have : (QuotientGroup.quotientKerEquivOfSurjective _ (ringClassIdeleQuotient_surjective O)).symm
      (ringClassIdeleQuotient O t) = (t : IdeleClassGroup (𝓞 K) K ⧸ (ringClassIdeleQuotient O).ker) :=
    (MulEquiv.symm_apply_eq _).2 rfl
  simp only [picToMax, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this, QuotientGroup.lift_mk]

theorem maximal_conductorModulus_dvd (O : NumberFieldOrder K) :
    (maximalNumberFieldOrder K).conductorModulus ∣ O.conductorModulus := by
  rw [conductorModulus_maximalNumberFieldOrder]; exact Modulus.one_dvd _

/-- The Picard class of (the contraction of) a principal ideal of `𝓞 K` maps to `1` in `Cl(K)`. -/
theorem picToMax_picClass_span (O : NumberFieldOrder K) (β : 𝓞 K)
    (hβ : Ideal.span {β} ∈ integralIdealsPrimeTo O.conductorModulus) :
    picToMax O (O.picClass ⟨_, hβ⟩) = 1 := by
  obtain ⟨t, ht⟩ := rayClassQuotient_surjective O.conductorModulus (idealClass O.conductorModulus ⟨_, hβ⟩)
  have hQ : ringClassIdeleQuotient O t = O.picClass ⟨_, hβ⟩ := by
    rw [ringClassIdeleQuotient_apply, ht, rayClassToPic_idealClass]
  rw [← hQ, picToMax_ringClassIdeleQuotient, ringClassIdeleQuotient_apply,
    ← classMap_rayClassQuotient (maximal_conductorModulus_dvd O), ht, classMap_idealClass,
    rayClassToPic_idealClass, picClass_eq_one_iff]
  exact ⟨β, β.2, rfl⟩

theorem restrictNormalHom_inclusion_apply {M L : IntermediateField K (SeparableClosure K)}
    [Normal K M] (h : M ≤ L) (σ : Gal(L/K)) (x : M) :
    IntermediateField.inclusion h ((IntermediateField.inclusion h).restrictNormalHom σ x) =
      σ (IntermediateField.inclusion h x) := by
  letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
  exact AlgEquiv.restrictNormal_commutes σ M x

/-- **Compatibility of ring class reciprocity with `Pic O → Cl(K)`**: the Artin symbol of `c` in
the ring class field of `O`, restricted to the Hilbert class field, is the Artin symbol of the
image of `c` in `Cl(K)`. -/
theorem restrict_ringClassArtinEquiv (O : NumberFieldOrder K) (c : Pic O) :
    (IntermediateField.inclusion (ringClassField_maximal_le O)).restrictNormalHom
        (ringClassArtinEquiv O c) =
      ringClassArtinEquiv (maximalNumberFieldOrder K) (picToMax O c) := by
  obtain ⟨t, rfl⟩ := ringClassIdeleQuotient_surjective O c
  rw [ringClassArtinEquiv_ringClassIdeleQuotient, ideleClassArtinMap_restrict,
    picToMax_ringClassIdeleQuotient, ringClassArtinEquiv_ringClassIdeleQuotient]

/-- An element of `Pic O` in the kernel of `Pic O → Cl(K)` acts trivially on the Hilbert class
field. -/
theorem ringClassArtinEquiv_apply_of_picToMax_eq_one (O : NumberFieldOrder K) {c : Pic O}
    (hc : picToMax O c = 1) (x : ringClassField (maximalNumberFieldOrder K)) :
    ringClassArtinEquiv O c (IntermediateField.inclusion (ringClassField_maximal_le O) x) =
      IntermediateField.inclusion (ringClassField_maximal_le O) x := by
  rw [← restrictNormalHom_inclusion_apply, restrict_ringClassArtinEquiv, hc, map_one]
  rfl


omit [NumberField K] in
theorem mem_lift_fixedField_zpowers {L : Type*} [Field L] [Algebra K L] {E : IntermediateField K L}
    (σ : Gal(E/K)) (y : E) (h : σ y = y) :
    (y : L) ∈ IntermediateField.lift (IntermediateField.fixedField (Subgroup.zpowers σ)) := by
  rw [IntermediateField.mem_lift]
  rintro ⟨g, hg⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  exact (MulAction.stabilizer _ y).zpow_mem (MulAction.mem_stabilizer_iff.2 (show σ • y = y from h)) k

set_option maxRecDepth 10000 in
/-- `H_d ⊆ H'_d ⊆ H_{d,4}`: `σ_{1+2ϖ}` acts trivially on the Hilbert class field. -/
theorem hilbertField_le_Hprime (d : ℕ) [NeZero d] : hilbertField d ≤ Hprime d := by
  intro x hx
  have hc : picToMax (O4 d) (sigmaClass d) = 1 := by
    rw [sigmaClass_eq]; exact picToMax_picClass_span (O4 d) (alpha d) alphaIdeal_mem
  have h1 := ringClassArtinEquiv_apply_of_picToMax_eq_one (O4 d) hc ⟨x, hx⟩
  have h2 := mem_lift_fixedField_zpowers (artin4 d (sigmaClass d)) _ h1
  have h3 : ((IntermediateField.inclusion (ringClassField_maximal_le (O4 d)) ⟨x, hx⟩ : H4 d) :
      SeparableClosure (QNeg d)) = x := rfl
  rw [h3] at h2
  exact h2

end Restrict
end ZInQ.Contrib.TYZGenus.RingClass
end
