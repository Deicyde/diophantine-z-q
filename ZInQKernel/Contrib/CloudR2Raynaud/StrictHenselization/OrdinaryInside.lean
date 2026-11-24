/-
Additive ordinary same-closure field/comap realization.  All certified
strict modules remain unchanged.  Ordinary residue=κ(O) is the ACTUAL
residueMap isomorphism, and the κ(O) point is e⁻¹∘resP with original
O-compatibility.  No whole-special-fibre IsIso, model, NMP or descent claim.
-/
import ZInQKernel.Contrib.CloudR2Raynaud.StrictHenselization.OrdinaryRealization
import ZInQKernel.Contrib.CloudR2Raynaud.StrictHenselization.SeparableFraction
import ZInQKernel.Contrib.CloudR2Raynaud.StrictHenselization.HenselizationField
import ZInQKernel.Contrib.CloudR2Raynaud.StrictHenselization.Port.RingEquivTransport

set_option autoImplicit false
noncomputable section
universe u v

namespace ZInQ.Contrib.CloudR2Raynaud.StrictHenselization.Ordinary

open IsLocalRing CategoryTheory
open ZInQ.Contrib.CloudR2Raynaud.StrictHenselization

variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]

/-- The fractional image of the actually realized ordinary ring is exactly
    the SAME-w comap, with the original κ(O) residue map and point. -/
theorem realization_to_ordinary_inside
    (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O)
    (Rh : Type u) [CommRing Rh] [IsDomain Rh] [IsDiscreteValuationRing Rh]
    [Algebra O Rh] [HenselianLocalRing Rh]
    (hind : (CommAlgCat.etale.{u} O).ind.{u} (CommAlgCat.of O Rh))
    (eκ : ResidueField O ≃+* ResidueField Rh)
    (heκ : ∀ r : O, eκ (residue O r) = residue Rh (algebraMap O Rh r))
    (f : Rh →+* w) [IsLocalHom f] (hfinj : Function.Injective f)
    (hfO : f.comp (algebraMap O Rh) = comapHom hw)
    (hfix : ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ w.decompositionSubgroup K →
      ∀ r : Rh, σ (f r : Ω) = (f r : Ω)) :
    ∃ (E : IntermediateField K Ω)
      (hE : (w.comap (algebraMap E Ω)).comap (algebraMap K E) = O),
      IsDiscreteValuationRing (w.comap (algebraMap E Ω)) ∧
      HenselianLocalRing (w.comap (algebraMap E Ω)) ∧ Algebra.IsSeparable K E ∧
      (letI : Algebra O (w.comap (algebraMap E Ω)) := (comapHom hE).toAlgebra
       (CommAlgCat.etale.{u} O).ind.{u} (CommAlgCat.of O (w.comap (algebraMap E Ω)))) ∧
      ∃ e : ResidueField O ≃+* ResidueField (w.comap (algebraMap E Ω)),
        residueMap hE = e.toRingHom ∧
        (residuePoint e).comp (comapHom hE) = residue O ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ w.decompositionSubgroup K → ∀ x ∈ E, σ x = x := by
  let F := FractionRing Rh
  let b : Rh →+* Ω := w.subtype.comp f
  have hbinj : Function.Injective b := w.subtype_injective.comp hfinj
  let φ₀ : F →+* Ω := IsFractionRing.lift (A := Rh) (K := F) hbinj
  have hφ₀ (r : Rh) : φ₀ (algebraMap Rh F r) = (f r : Ω) :=
    IsFractionRing.lift_algebraMap hbinj r
  have hOinj : Function.Injective (comapHom hw) := by
    intro a c hac
    apply O.subtype_injective
    apply (algebraMap K Ω).injective
    exact congrArg (fun x : w => (x : Ω)) hac
  have hθinj : Function.Injective (algebraMap O Rh) := by
    intro a c hac
    apply hOinj
    rw [← hfO]
    exact congrArg f hac
  let c : O →+* F := (algebraMap Rh F).comp (algebraMap O Rh)
  have hcinj : Function.Injective c := (IsFractionRing.injective Rh F).comp hθinj
  let g : K →+* F := IsFractionRing.lift (A := O) (K := K) hcinj
  letI : Algebra K F := g.toAlgebra
  haveI : IsScalarTower O Rh F := inferInstance
  haveI : IsScalarTower O K F := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply O Rh F]
    exact (IsFractionRing.lift_algebraMap hcinj r).symm
  have hOK : algebraMap O K = O.subtype := by
    ext r
    rfl
  have hφK : φ₀.comp g = algebraMap K Ω := by
    apply IsFractionRing.ringHom_ext (A := O)
    intro r
    calc
      (φ₀.comp g) (algebraMap O K r) =
          φ₀ (algebraMap Rh F (algebraMap O Rh r)) :=
        congrArg φ₀ (IsFractionRing.lift_algebraMap hcinj r)
      _ = (f (algebraMap O Rh r) : Ω) := hφ₀ _
      _ = algebraMap K Ω (algebraMap O K r) := by
        simpa only [RingHom.comp_apply, comapHom_coe, hOK, ValuationSubring.subtype_apply] using
          congrArg (fun x : w => (x : Ω)) (RingHom.congr_fun hfO r)
  let φ : F →ₐ[K] Ω :=
    { toRingHom := φ₀
      commutes' := fun r => RingHom.congr_fun hφK r }
  let E := φ.fieldRange
  let eF : F ≃ₐ[K] E := AlgEquiv.ofInjectiveField φ
  let P := w.comap (algebraMap E Ω)
  have heF (x : F) : ((eF x : E) : Ω) = φ₀ x := rfl
  let θ : Rh →+* E := eF.toRingHom.comp (algebraMap Rh F)
  have hθw (r : Rh) : algebraMap E Ω (θ r) ∈ w := by
    change φ₀ (algebraMap Rh F r) ∈ w
    rw [hφ₀]
    exact (f r).2
  let θP : Rh →+* P := θ.codRestrict P.toSubring hθw
  have hθP (r : Rh) : ((θP r : E) : Ω) = (f r : Ω) := hφ₀ r
  have hθPinj : Function.Injective θP := by
    intro r s hrs
    apply hfinj
    apply w.subtype_injective
    have h := congrArg (fun p : P => ((p : E) : Ω)) hrs
    rw [hθP, hθP] at h
    exact h
  have hθPsurj : Function.Surjective θP := by
    intro x
    obtain ⟨z, hz⟩ := eF.surjective (x : E)
    have hwz : φ₀ z ∈ w := by
      rw [← heF, hz]
      exact x.2
    obtain ⟨r, hr⟩ := fraction_preimage_of_local w f φ₀ hφ₀ z hwz
    refine ⟨r, Subtype.ext ?_⟩
    change eF (algebraMap Rh F r) = (x : E)
    rw [hr, hz]
  let eR : Rh ≃+* P := RingEquiv.ofBijective θP ⟨hθPinj, hθPsurj⟩
  haveI : IsLocalHom eR.toRingHom := IsLocalHom.of_surjective eR.toRingHom (by
    simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using eR.surjective)
  have heR (r : Rh) : ((eR r : E) : Ω) = (f r : Ω) := hθP r
  have hE : P.comap (algebraMap K E) = O := by
    dsimp only [P]
    rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq, hw]
  have heRO : eR.toRingHom.comp (algebraMap O Rh) = comapHom hE := by
    apply RingHom.ext
    intro r
    apply Subtype.ext
    apply Subtype.ext
    change ((eR (algebraMap O Rh r) : E) : Ω) =
      algebraMap E Ω (algebraMap K E (r : K))
    rw [heR]
    have h := congrArg (fun x : w => (x : Ω)) (RingHom.congr_fun hfO r)
    exact h.trans (IsScalarTower.algebraMap_apply K E Ω (r : K)).symm
  haveI : Algebra.IsSeparable K F := separable_fraction_of_indEtale hind
  have hsepE : Algebra.IsSeparable K E := AlgEquiv.Algebra.isSeparable eF
  have hdvrP : IsDiscreteValuationRing P :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eR
  have hhenP : HenselianLocalRing P := Port.HenselianLocalRing.of_ringEquiv eR
  have hindP : (letI : Algebra O P := (comapHom hE).toAlgebra
      (CommAlgCat.etale.{u} O).ind.{u} (CommAlgCat.of O P)) := by
    letI : Algebra O P := (comapHom hE).toAlgebra
    let eA : Rh ≃ₐ[O] P :=
      { eR with commutes' := fun r => RingHom.congr_fun heRO r }
    exact (CommAlgCat.etale O).ind.prop_of_iso (CommAlgCat.isoMk eA) hind
  let ep : ResidueField O ≃+* ResidueField P := eκ.trans (ResidueField.mapEquiv eR)
  have hep : ∀ r : O, ep (residue O r) = residue P (comapHom hE r) := by
    intro r
    change (ResidueField.mapEquiv eR) (eκ (residue O r)) = residue P (comapHom hE r)
    rw [heκ r]
    change (ResidueField.map eR.toRingHom) (residue Rh (algebraMap O Rh r)) =
      residue P (comapHom hE r)
    have hc : eR.toRingHom (algebraMap O Rh r) = comapHom hE r :=
      RingHom.congr_fun heRO r
    rw [ResidueField.map_residue, hc]
  have hres : residueMap hE = ep.toRingHom := by
    apply RingHom.ext
    intro z
    obtain ⟨r, rfl⟩ := residue_surjective z
    rw [residueMap_residue]
    exact (hep r).symm
  have hpoint : (residuePoint ep).comp (comapHom hE) = residue O := by
    letI : Algebra O P := (comapHom hE).toAlgebra
    have hepa : ∀ r : O, ep (residue O r) = residue P (algebraMap O P r) := by
      intro r
      simpa only [RingHom.algebraMap_toAlgebra] using hep r
    simpa only [RingHom.algebraMap_toAlgebra] using residuePoint_comp ep hepa
  refine ⟨E, hE, hdvrP, hhenP, hsepE, hindP, ep, hres, hpoint, ?_⟩
  intro σ hσ x hx
  obtain ⟨z, rfl⟩ := hx
  have hσr : ∀ r : Rh, σ (φ₀ (algebraMap Rh F r)) = φ₀ (algebraMap Rh F r) := by
    intro r
    rw [hφ₀]
    exact hfix σ hσ r
  obtain ⟨r, s, _, rfl⟩ := IsFractionRing.div_surjective Rh z
  change σ (φ₀ (algebraMap Rh F r / algebraMap Rh F s)) =
    φ₀ (algebraMap Rh F r / algebraMap Rh F s)
  simp only [map_div₀, hσr]

/-- CLOSED ordinary henselian DVR and true κ(O)-point in the SAME original Ω.
    The strict P0 and the ordinary Rh/DVR/nonvanishing are constructed inside
    the proof; none is a caller premise. -/
theorem exists_ordinaryHenselianDVR_inside [IsAlgClosed Ω]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O) :
    ∃ (E : IntermediateField K Ω)
      (hE : (w.comap (algebraMap E Ω)).comap (algebraMap K E) = O),
      IsDiscreteValuationRing (w.comap (algebraMap E Ω)) ∧
      HenselianLocalRing (w.comap (algebraMap E Ω)) ∧ Algebra.IsSeparable K E ∧
      (letI : Algebra O (w.comap (algebraMap E Ω)) := (comapHom hE).toAlgebra
       (CommAlgCat.etale.{u} O).ind.{u} (CommAlgCat.of O (w.comap (algebraMap E Ω)))) ∧
      ∃ e : ResidueField O ≃+* ResidueField (w.comap (algebraMap E Ω)),
        residueMap hE = e.toRingHom ∧
        (residuePoint e).comp (comapHom hE) = residue O ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ w.decompositionSubgroup K → ∀ x ∈ E, σ x = x := by
  obtain ⟨Rh, _, _, _, _, hhen, hind, e, he, f, hfloc, hfinj, hfO, hfix⟩ :=
    exists_ordinaryDVR_toW O w hw
  letI := hhen
  letI := hfloc
  exact realization_to_ordinary_inside O w hw Rh hind e he f hfinj hfO hfix

/-- The actual ordinary image is in the SEPARABLE decomposition-fixed field;
    no equality with an imperfect full fixed field is asserted. -/
theorem le_henselizationField_of_separable_and_fixed
    {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
    (w : ValuationSubring Ω) (E : IntermediateField K Ω) [Algebra.IsSeparable K E]
    (hfix : ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ w.decompositionSubgroup K → ∀ x ∈ E, σ x = x) :
    E ≤ henselizationField (K := K) w := by
  dsimp only [henselizationField]
  apply le_inf
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    exact fun σ hσ => hfix σ hσ x hx
  · exact (le_separableClosure_iff K Ω E).mpr inferInstance

end ZInQ.Contrib.CloudR2Raynaud.StrictHenselization.Ordinary
