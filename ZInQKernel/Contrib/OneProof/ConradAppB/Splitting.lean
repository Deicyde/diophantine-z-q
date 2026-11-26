import ZInQKernel.Contrib.OneProof.ConradAppB.Defs
import ZInQKernel.Contrib.OneProof.C8LocAlg

/-!
# The unramified–cyclotomic splitting of a local character

Let `L/ℚ_p` be finite inside `ℚ̄_p` and let `χ : G_{ℚ_p} → L^×` be continuous. Then `χ = μ η`
with `μ` continuous and trivial on the inertia subgroup and `η` trivial on the kernel of the
`p`-adic cyclotomic character `χ_cyc`. This is local class field theory for `ℚ_p`
(J. Neukirch, *Algebraic Number Theory*, Ch. V, §1 and §2):

* `χ` is trivial on the closure of the commutator subgroup (its kernel is closed), so it factors
  through the topological abelianization `G_{ℚ_p}^{ab}` as `χᵃᵇ`, continuous for the quotient
  topology;
* `ψ(v) = χᵃᵇ(Art(v⁻¹))` for `v ∈ ℤ_p^×` is continuous, because the local Artin map `Art` is;
* `η = ψ ∘ χ_cyc` and `μ = χ η⁻¹`. Every element `σ` of the inertia subgroup represents `Art(u)`
  for a unit `u ∈ ℤ_p^×`, and then `χ_cyc(σ) = u⁻¹`; so `η(σ) = χᵃᵇ(Art(u)) = χ(σ)` and
  `μ(σ) = 1`.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.SenWeightZero


open HDec.G0Galois.C8Conrad

namespace UnramCycSplitting

variable (p : ℕ) [Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}

/-- `χ` as a homomorphism on `Field.absoluteGaloisGroup ℚ_[p]`, the same group. -/
def absHom (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Lˣ) :
    Field.absoluteGaloisGroup ℚ_[p] →* Lˣ :=
  χ

/-- A character of `G_{ℚ_p}` that is continuous into `ℚ̄_p` is trivial on the closure of the
commutator subgroup: its kernel is a closed subgroup containing all commutators. -/
theorem topologicalClosure_commutator_le_ker (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Lˣ)
    (hχ : Continuous (fun σ => (((χ σ : Lˣ) : L) : PadicAlgCl p))) :
    (commutator (Field.absoluteGaloisGroup ℚ_[p])).topologicalClosure ≤ (absHom p χ).ker := by
  refine Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker _) ?_
  have hc : Continuous (fun σ : Field.absoluteGaloisGroup ℚ_[p] =>
      (((absHom p χ σ : Lˣ) : L) : PadicAlgCl p)) := hχ
  have h : ((absHom p χ).ker : Set (Field.absoluteGaloisGroup ℚ_[p])) =
      (fun σ : Field.absoluteGaloisGroup ℚ_[p] => (((absHom p χ σ : Lˣ) : L) : PadicAlgCl p)) ⁻¹'
        {1} := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      simp [h]
    · intro h
      exact Units.ext (Subtype.ext h)
  rw [h]
  exact isClosed_singleton.preimage hc

/-- The factorization `χᵃᵇ` of `χ` through the topological abelianization of `G_{ℚ_p}`. -/
def abChar (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Lˣ)
    (hχ : Continuous (fun σ => (((χ σ : Lˣ) : L) : PadicAlgCl p))) :
    Field.absoluteGaloisGroupAbelianization ℚ_[p] →* Lˣ :=
  QuotientGroup.lift _ (absHom p χ) (topologicalClosure_commutator_le_ker p χ hχ)

theorem abChar_mk (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Lˣ)
    (hχ : Continuous (fun σ => (((χ σ : Lˣ) : L) : PadicAlgCl p)))
    (σ : Field.absoluteGaloisGroup ℚ_[p]) :
    abChar p χ hχ (σ : Field.absoluteGaloisGroupAbelianization ℚ_[p]) = χ σ :=
  rfl

/-- `χᵃᵇ` is continuous for the quotient topology. -/
theorem continuous_abChar (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Lˣ)
    (hχ : Continuous (fun σ => (((χ σ : Lˣ) : L) : PadicAlgCl p))) :
    Continuous (fun a => (((abChar p χ hχ a : Lˣ) : L) : PadicAlgCl p)) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 hχ

/-- `ψ(v) = χᵃᵇ(Art(v⁻¹))` for `v ∈ ℤ_p^×`. -/
def unitChar (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Lˣ)
    (hχ : Continuous (fun σ => (((χ σ : Lˣ) : L) : PadicAlgCl p))) : ℤ_[p]ˣ →* Lˣ :=
  ((abChar p χ hχ).comp ((TauCeti.ClassFieldTheory.artinMap ℚ_[p]).comp
    (Units.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).toMonoidHom))).comp invMonoidHom

theorem unitChar_apply (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Lˣ)
    (hχ : Continuous (fun σ => (((χ σ : Lˣ) : L) : PadicAlgCl p))) (v : ℤ_[p]ˣ) :
    unitChar p χ hχ v = abChar p χ hχ (TauCeti.ClassFieldTheory.artinMap ℚ_[p] (unitsQp p v⁻¹)) :=
  rfl

/-- `ψ` is continuous: the local Artin map is continuous. -/
theorem continuous_unitChar (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Lˣ)
    (hχ : Continuous (fun σ => (((χ σ : Lˣ) : L) : PadicAlgCl p))) :
    Continuous (fun v => (((unitChar p χ hχ v : Lˣ) : L) : PadicAlgCl p)) := by
  have h1 : Continuous (Units.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).toMonoidHom) :=
    Continuous.units_map _ continuous_subtype_val
  exact (continuous_abChar p χ hχ).comp
    ((TauCeti.ClassFieldTheory.continuous_artinMap ℚ_[p]).comp (h1.comp continuous_inv))

/-- `η = ψ ∘ χ_cyc`. -/
def cycPart (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Lˣ)
    (hχ : Continuous (fun σ => (((χ σ : Lˣ) : L) : PadicAlgCl p))) :
    (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Lˣ :=
  (unitChar p χ hχ).comp (TauCeti.localCyclotomicCharacter p ℚ_[p])

theorem cycPart_apply (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Lˣ)
    (hχ : Continuous (fun σ => (((χ σ : Lˣ) : L) : PadicAlgCl p)))
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    cycPart p χ hχ σ = unitChar p χ hχ (cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv) :=
  rfl

/-- `η` is continuous, as `ψ` and `χ_cyc` are. -/
theorem continuous_cycPart (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Lˣ)
    (hχ : Continuous (fun σ => (((χ σ : Lˣ) : L) : PadicAlgCl p))) :
    Continuous (fun σ => (((cycPart p χ hχ σ : Lˣ) : L) : PadicAlgCl p)) :=
  (continuous_unitChar p χ hχ).comp (TauCeti.localCyclotomicCharacter_continuous p ℚ_[p])

/-- `η` is trivial on the kernel of `χ_cyc`. -/
theorem cycPart_eq_one (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Lˣ)
    (hχ : Continuous (fun σ => (((χ σ : Lˣ) : L) : PadicAlgCl p)))
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv = 1) : cycPart p χ hχ σ = 1 := by
  rw [cycPart_apply, hσ, map_one]

/-- On the inertia subgroup `η = χ`: an inertia element `σ` represents `Art(u)` for a unit `u`,
and `χ_cyc(σ) = u⁻¹`, so `η(σ) = χᵃᵇ(Art(u)) = χ(σ)`. -/
theorem cycPart_eq_of_isInertia (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Lˣ)
    (hχ : Continuous (fun σ => (((χ σ : Lˣ) : L) : PadicAlgCl p)))
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hσ : IsInertia p σ) : cycPart p χ hχ σ = χ σ := by
  obtain ⟨u, hu⟩ := exists_unit_isArtinLift p σ hσ
  have hc : cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv = u⁻¹ :=
    cyc_of_isArtinLift p σ u hu
  rw [cycPart_apply, hc, unitChar_apply, inv_inv]
  have hu' : (QuotientGroup.mk (show Field.absoluteGaloisGroup ℚ_[p] from σ) :
      Field.absoluteGaloisGroupAbelianization ℚ_[p]) =
      TauCeti.ClassFieldTheory.artinMap ℚ_[p] (unitsQp p u) := hu
  rw [← hu']
  rfl

end UnramCycSplitting

open UnramCycSplitting in
/-- **The unramified–cyclotomic splitting** (local class field theory for `ℚ_p`): `μ = χ η⁻¹` and
`η = ψ ∘ χ_cyc`. -/
theorem unramifiedCyclotomicSplitting_proof : UnramifiedCyclotomicSplitting := by
  intro p _ L _ χ hχ
  refine ⟨χ * (cycPart p χ hχ)⁻¹, cycPart p χ hχ, fun σ => ?_, ?_, fun σ hσ => ?_,
    fun σ hσ => cycPart_eq_one p χ hχ σ hσ⟩
  · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, inv_mul_cancel_right]
  · have hη := continuous_cycPart p χ hχ
    have h : (fun σ => ((((χ * (cycPart p χ hχ)⁻¹) σ : Lˣ) : L) : PadicAlgCl p)) =
        fun σ => (((χ σ : Lˣ) : L) : PadicAlgCl p) *
          ((((cycPart p χ hχ σ : Lˣ) : L) : PadicAlgCl p))⁻¹ := by
      funext σ
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
        IntermediateField.coe_mul, IntermediateField.coe_inv]
    rw [h]
    exact hχ.mul (hη.inv₀ fun σ h0 => (cycPart p χ hχ σ).ne_zero (Subtype.ext h0))
  · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, cycPart_eq_of_isInertia p χ hχ σ hσ,
      mul_inv_cancel]

end ZInQ.Contrib.SenWeightZero

end

