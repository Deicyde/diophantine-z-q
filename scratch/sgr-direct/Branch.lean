import ZInQKernel.Contrib.OneProof.SGRDirectNV

set_option linter.style.haveILetI false

noncomputable section

open Polynomial CategoryTheory AlgebraicGeometry GlueDescent.B2Q
open HDec HDec.G0ModField HDec.PropTSRed HDec.PropTSGlue HDec.HeckeRestNV LeafQM LeafQM.AV

namespace SGRDirect

/-- **`HeckeBranchFibreUnram` is a theorem** from `R1R2fp` (its reciprocity clause at the CM points,
`residue_unramified_over_branch`) and T5 (through `MobiusGlue`, which transfers residue fields of points
between triples). -/
theorem heckeBranchFibreUnram (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure) :
    HeckeBranchFibreUnram := by
  intro Y Φ π h1 hh h2 E _ _ _ _ _ _ hN p hp hp324 𝔓 h𝔓 h𝔓u φ
  obtain ⟨Y₀, Φ₀, π₀, h1₀, h2₀, hbr⟩ := residue_unramified_over_branch hRR
  obtain ⟨g, hΦ, hπ⟩ := Pin.sameTripleMor_of_mobius (CurveGlue.mobiusGlue_of_T5 hT)
    (Pin.cm_objects_of_R1R2fp hRR) h1₀ h2₀ h1 h2
  obtain ⟨h, hO, -, hval⟩ := hN
  set ψ : integralClosure ℚ[X] E →+* Qbar := φ.comp (Ideal.Quotient.mk 𝔓) with hψdef
  let y : fieldPt Qbar ⟶ Y :=
    Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ h) (PropTSRed.spec_to_specQ_eq _ _)
  have hC : ∀ c : ℚ, ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) (C c)) = algebraMap ℚ Qbar c := by
    intro c
    have hsub : ((ψ.comp (algebraMap ℚ[X] (integralClosure ℚ[X] E))).comp C : ℚ →+* Qbar) =
        algebraMap ℚ Qbar := Subsingleton.elim _ _
    exact congrArg (fun f : ℚ →+* Qbar => f c) hsub
  have hX : ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = (-16 / 27 : Qbar) := by
    have hmem : X - C (-16 / 27 : ℚ) ∈ 𝔓.under ℚ[X] := by
      rw [h𝔓u]; exact Ideal.mem_span_singleton_self _
    have h0 : ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) (X - C (-16 / 27 : ℚ))) = 0 := by
      rw [hψdef, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr (show _ ∈ 𝔓 from hmem),
        map_zero]
    rw [map_sub, map_sub, hC, sub_eq_zero] at h0
    rw [h0]
    simp
  have hyv : π.val (K := Qbar) y.left = OnePoint.some (-16 / 27 : Qbar) := by
    have := hval ψ
    rw [hX] at this
    exact this
  have hres : residueImage (X := Y.left) y.left = IntermediateField.adjoin ℚ (Set.range φ) := by
    show residueImage (X := Y.left) (Spec.map (CommRingCat.ofHom ψ) ≫ h) = _
    rw [residueImage_comp_openImmersion h, residueImage_specMap]
    congr 1
    ext z
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨Ideal.Quotient.mk _ b, rfl⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
      exact ⟨b, rfl⟩
  have h0 := hbr (y ≫ g) (Or.inr (Or.inr (by rw [← hπ y]; exact hyv)))
  rw [PropTSRed.residueImage_comp_eq_of_pt g hΦ y, hres] at h0
  obtain ⟨hfin, hdisc⟩ := h0
  letI : NumberField (IntermediateField.adjoin ℚ (Set.range φ)) := @NumberField.mk _ _ _ hfin
  exact GlueB3Unram.unramifiedAt_of_not_dvd_discr _ p hp (hdisc p hp (by omega))

end SGRDirect

#print axioms SGRDirect.heckeBranchFibreUnram
