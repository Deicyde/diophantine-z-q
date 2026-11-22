/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Definitions.Def_AlgebraicGeometry_Kmf2FiberSpecTensorStalkLeg1AffineDatum. Apache-2.0.
Modification notice (CloudB3 Worker13, 2026-11-15/16): ported to Lean 4.35.0 / Mathlib v4.35.0
(namespace-wrapped port on origin/cloud-b3/w13-recovery).
Modified for the Z-in-Q kernel (charpoly-port, 2026-11-17): the Worker13 port unwrapped into the
CloudB3W16Torsion conventions (original declaration namespaces; imports relocated to the
CloudB3W16Torsion vendor; the FLT-suffixed renames of CloudB3W16Torsion/NOTICE.md applied; port
shim commands removed). Mathematical statements and proofs retained, subject to Lean 4.35 adaptations
listed in scratch/charpoly-port/log.md.
Full original notices/credits: LICENSE, NOTICE.upstream, ATTRIBUTION.upstream.md in this vendor root.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

noncomputable def kmf2_fiberSpecTensorIso
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : PrimeSpectrum R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p ≅
      Spec (CommRingCat.of (p.asIdeal.Fiber S)) :=
  pullbackSymmetry _ _ ≪≫
    (pullback.congrHom
      (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField
        (CommRingCat.of R) p).symm rfl ≪≫
      asIso (pullback.map _ _ _ _
        (Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of R) p).inv) (𝟙 _) (𝟙 _)
        (by simp) (by simp))) ≪≫
    pullbackSpecIso R p.asIdeal.ResidueField S

theorem kmf2_fiberSpecTensorIso_hom_includeRight
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : PrimeSpectrum R) :
    (kmf2_fiberSpecTensorIso R S p).hom ≫
        Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight
            (R := R) (A := p.asIdeal.ResidueField) (B := S)))) =
      (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι p := by
  simp only [kmf2_fiberSpecTensorIso, Scheme.Hom.fiberι, Iso.trans_hom, asIso_hom,
    pullback.congrHom_hom, Category.assoc, pullbackSpecIso_hom_snd,
    pullback.lift_snd, Category.comp_id]
  exact pullbackSymmetry_hom_comp_snd _ _

theorem kmf2_fiberSpecTensorIso_point_comap
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : PrimeSpectrum R)
    (w : (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) :
    (((kmf2_fiberSpecTensorIso R S p).hom w).asIdeal).comap
        (Algebra.TensorProduct.includeRight
          (R := R) (A := p.asIdeal.ResidueField) (B := S)).toRingHom =
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι p w).asIdeal := by
  have h1 : Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
      (Algebra.TensorProduct.includeRight
        (R := R) (A := p.asIdeal.ResidueField) (B := S))))
        ((kmf2_fiberSpecTensorIso R S p).hom w) =
      (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι p w := by
    rw [← Scheme.Hom.comp_apply, kmf2_fiberSpecTensorIso_hom_includeRight]
  have h2 := congrArg PrimeSpectrum.asIdeal h1
  rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom] at h2
  exact h2

theorem kmf2_fiberStalk_localizationAtPrime
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : PrimeSpectrum R)
    (w : (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) :
    Nonempty
      (((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p).presheaf.stalk w ≃+*
        Localization.AtPrime ((kmf2_fiberSpecTensorIso R S p).hom w).asIdeal) :=
  ⟨(asIso ((kmf2_fiberSpecTensorIso R S p).hom.stalkMap w)).commRingCatIsoToRingEquiv.symm.trans
    ((StructureSheaf.stalkIso (p.asIdeal.Fiber S)
      ((kmf2_fiberSpecTensorIso R S p).hom w)).symm.toRingEquiv)⟩

theorem kmf2_fiberStalkLeg1_affineDatum
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (x : Spec (CommRingCat.of S)) :
    ∃ (Q : Ideal ((Spec.map (CommRingCat.ofHom (algebraMap R S))
        x).asIdeal.Fiber S)) (_ : Q.IsPrime),
      Q.comap (Algebra.TensorProduct.includeRight
        (R := R)
        (A := (Spec.map (CommRingCat.ofHom (algebraMap R S)) x).asIdeal.ResidueField)
        (B := S)).toRingHom = x.asIdeal ∧
      Nonempty
        (((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber
            (Spec.map (CommRingCat.ofHom (algebraMap R S)) x)).presheaf.stalk
          ((Spec.map (CommRingCat.ofHom (algebraMap R S))).asFiber x) ≃+*
          Localization.AtPrime Q) := by
  refine ⟨((kmf2_fiberSpecTensorIso R S
      (Spec.map (CommRingCat.ofHom (algebraMap R S)) x)).hom
        ((Spec.map (CommRingCat.ofHom (algebraMap R S))).asFiber x)).asIdeal,
    ((kmf2_fiberSpecTensorIso R S
      (Spec.map (CommRingCat.ofHom (algebraMap R S)) x)).hom
        ((Spec.map (CommRingCat.ofHom (algebraMap R S))).asFiber x)).2, ?_, ?_⟩
  · rw [kmf2_fiberSpecTensorIso_point_comap]
    rw [Scheme.Hom.fiberι_asFiber]
  · exact kmf2_fiberStalk_localizationAtPrime R S
      (Spec.map (CommRingCat.ofHom (algebraMap R S)) x)
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).asFiber x)

end

