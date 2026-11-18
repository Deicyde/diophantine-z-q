import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.Valuation

/-! The arithmetic Frobenius preserving the chosen Chebotarev prime acts on
the actual valuation ring and induces the p-th power on its residue field. -/

noncomputable section

open IsLocalRing
open ZInQ.Contrib.ChebFD.C10 (Zbar Qbar GQ)

namespace ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace

variable {g : GQ} {p : ℕ} [Fact p.Prime] (v : FrobeniusPlace g p)

private abbrev integerFrob (g : GQ) : Zbar ≃ₐ[ℤ] Zbar :=
  galRestrict ℤ ℚ Qbar Zbar g

private theorem integerFrob_at : (integerFrob g).toAlgHom.IsArithFrobAt v.prime := by
  intro x
  rw [v.under, ZInQ.Contrib.ChebFD.C10.card_quot p]
  exact v.frob x _ (by
    change algebraMap Zbar Qbar (_ - x ^ p) = _
    rw [map_sub, map_pow]
    exact congrArg (fun a : Qbar => a - (x : Qbar) ^ p)
      (algebraMap_galRestrict_apply ℤ g x))

private theorem integerFrob_compl :
    Submonoid.map (integerFrob g) v.prime.primeCompl = v.prime.primeCompl := by
  have h (x : Zbar) : integerFrob g x ∈ v.prime ↔ x ∈ v.prime := by
    change x ∈ v.prime.comap (integerFrob g).toAlgHom ↔ _
    rw [(v.integerFrob_at).comap_eq]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mt (h y).mp hy
  · intro hx
    change x ∉ v.prime at hx
    exact ⟨(integerFrob g).symm x, mt (h _).mpr
      (by simpa only [AlgEquiv.apply_symm_apply] using hx), AlgEquiv.apply_symm_apply _ _⟩

/-- The decomposition element as an automorphism of the localized algebraic integers. -/
def localFrob : v.localRing.toSubring ≃ₐ[ℤ] v.localRing.toSubring :=
  IsLocalization.algEquivOfAlgEquiv v.localRing.toSubring v.localRing.toSubring (integerFrob g)
    (v.integerFrob_compl)

/-- On local integers, the decomposition element is the original absolute automorphism. -/
theorem coe_localFrob (x : v.localRing.toSubring) :
    ((v.localFrob x : v.localRing.toSubring) : Qbar) = g (x : Qbar) := by
  have h : (Subring.subtype v.localRing.toSubring).comp
      (v.localFrob : v.localRing.toSubring →+* v.localRing.toSubring) =
      g.toRingHom.comp (Subring.subtype v.localRing.toSubring) := by
    apply IsLocalization.ringHom_ext v.prime.primeCompl
    ext a
    change ((v.localFrob (algebraMap Zbar v.localRing.toSubring a) : v.localRing.toSubring) : Qbar) =
      g ((algebraMap Zbar v.localRing.toSubring a : v.localRing.toSubring) : Qbar)
    rw [localFrob, IsLocalization.algEquivOfAlgEquiv_eq]
    change algebraMap Zbar Qbar (integerFrob g a) = _
    exact algebraMap_galRestrict_apply ℤ g a
  exact RingHom.congr_fun h x

/-- The residue field of the localized ring is the common geometric quotient. -/
def localResidueEquiv : (Zbar ⧸ v.prime) ≃+* ResidueField v.localRing.toSubring :=
  (IsLocalization.AtPrime.equivQuotMaximalIdeal v.prime v.localRing.toSubring).toRingEquiv

/-- Arithmetic Frobenius on the localized ring reduces to the p-th power. -/
theorem localFrob_residue (x : v.localRing.toSubring) :
    residue v.localRing.toSubring (v.localFrob x) = (residue v.localRing.toSubring x) ^ p := by
  have hs (a : Zbar) : v.localResidueEquiv (Ideal.Quotient.mk v.prime a) =
      residue v.localRing.toSubring (algebraMap Zbar v.localRing.toSubring a) := rfl
  obtain ⟨a, ha'⟩ := (v.localResidueEquiv.surjective.comp Ideal.Quotient.mk_surjective)
    (residue v.localRing.toSubring x)
  have ha : residue v.localRing.toSubring (algebraMap Zbar v.localRing.toSubring a) =
      residue v.localRing.toSubring x :=
    (hs a).symm.trans ha'
  have hcomp := congrArg (ResidueField.map (v.localFrob : v.localRing.toSubring →+* v.localRing.toSubring)) ha
  rw [ResidueField.map_residue, ResidueField.map_residue] at hcomp
  change residue v.localRing.toSubring (v.localFrob (algebraMap Zbar v.localRing.toSubring a)) =
    residue v.localRing.toSubring (v.localFrob x) at hcomp
  rw [← hcomp, ← ha]
  rw [localFrob, IsLocalization.algEquivOfAlgEquiv_eq, ← hs, ← hs, ← map_pow]
  exact congrArg v.localResidueEquiv (v.frob_on_integers a)

/-- Identify the localized integers with the valuation ring of the emitted valuation. -/
def localValuationEquiv : v.localRing.toSubring ≃+* v.valuationRing.valuation.valuationSubring :=
  RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
    (v.valuationRing.valuationSubring_valuation).symm)

/-- The decomposition element preserves integrality, in both directions. -/
theorem valuation_frob_le_one_iff (x : Qbar) :
    v.valuationRing.valuation (g x) ≤ 1 ↔ v.valuationRing.valuation x ≤ 1 := by
  rw [(v.valuationRing).valuation_le_one_iff (g x),
    (v.valuationRing).valuation_le_one_iff x]
  change g x ∈ v.localRing.toSubring ↔ x ∈ v.localRing.toSubring
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := v.localFrob.surjective ⟨g x, hx⟩
    have he : g (a : Qbar) = g x := (v.coe_localFrob a).symm.trans
      (congrArg (fun z : v.localRing.toSubring => (z : Qbar)) ha)
    exact g.injective he ▸ a.property
  · intro hx
    exact v.coe_localFrob ⟨x, hx⟩ ▸ (v.localFrob ⟨x, hx⟩).property

/-- The residue action in the valuation API used by the curve reduction homomorphism. -/
theorem valuation_frob_residue (x : Qbar) (hx : v.valuationRing.valuation x ≤ 1) :
    residue v.valuationRing.valuation.valuationSubring ⟨g x, (v.valuation_frob_le_one_iff x).mpr hx⟩ =
      (residue v.valuationRing.valuation.valuationSubring ⟨x, hx⟩) ^ p := by
  let a : v.localRing.toSubring := ⟨x, (v.valuationRing.valuation_le_one_iff x).mp hx⟩
  have ha : v.localValuationEquiv a = (⟨x, hx⟩ : v.valuationRing.valuation.valuationSubring) :=
    Subtype.ext rfl
  have hg : v.localValuationEquiv (v.localFrob a) =
      (⟨g x, (v.valuation_frob_le_one_iff x).mpr hx⟩ : v.valuationRing.valuation.valuationSubring) :=
    Subtype.ext (v.coe_localFrob a)
  have hs := congrArg (ResidueField.mapEquiv v.localValuationEquiv) (v.localFrob_residue a)
  rw [map_pow, ResidueField.mapEquiv_apply, ResidueField.map_residue,
    ResidueField.mapEquiv_apply, ResidueField.map_residue] at hs
  change residue v.valuationRing.valuation.valuationSubring (v.localValuationEquiv (v.localFrob a)) =
    (residue v.valuationRing.valuation.valuationSubring (v.localValuationEquiv a)) ^ p at hs
  rw [ha, hg] at hs
  exact hs

#print axioms integerFrob_at
#print axioms integerFrob_compl
#print axioms localFrob
#print axioms coe_localFrob
#print axioms localResidueEquiv
#print axioms localFrob_residue
#print axioms localValuationEquiv
#print axioms valuation_frob_le_one_iff
#print axioms valuation_frob_residue

end ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace
