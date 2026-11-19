import ZInQKernel.Contrib.OneProof.NeronDedekind.Near
import ZInQKernel.Contrib.OneProof.MumfordGroupLawNeron
import ZInQKernel.Contrib.OneProof.EGAIV_8_10_5_xii
import ZInQKernel.Contrib.CloudW01Spread.FinitePresentation

/-!
# Néron models over Dedekind domains from the DVR case

This formalizes the globalization argument in Bosch–Lütkebohmert–Raynaud,
*Néron Models* (Springer, 1990), §1.4, Proposition 1 (p. 18) and the proof
of Theorem 3 (pp. 19–20). The remaining input is local existence over a DVR,
Corollary 2 of §1.3 (p. 16), with the Néron mapping property of §1.2,
Definition 1 (p. 12).
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace NeronExtDedekind

open ZInQ.Contrib.SpreadOut ZInQ.Contrib.GroupLawNeron

section GoodModel

variable {D L : Type} [CommRing D] [IsDedekindDomain D] [Field L]
  [Algebra D L] [IsFractionRing D L]

/-- An abelian variety spreads to a smooth proper group scheme on a principal open.
Viewed over `Spec D`, this model is Néron at each closed point of that open. -/
private theorem goodModel (hD : ¬ IsField D) (A : PkgI3.AbVar L) :
    ∃ (M : Over (S D)) (_ : Smooth M.hom) (_ : IsSeparated M.hom) (_ : QuasiCompact M.hom)
      (_ : (gf D L).obj M ≅ A.X) (f : D), f ≠ 0 ∧
        ∀ (w : Ideal D) [w.IsMaximal], f ∉ w → NeronExt.LocNeron L w M := by
  let p : Ideal D := ⊥
  have := isLocalization_bot (D := D) (L := L)
  let c := GapBLR.specCone p L
  let B : Over c.pt := A.X
  let _ : GrpObj B := A.grp
  have : IsProper B.hom := A.proper
  have : Smooth B.hom := A.smooth
  obtain ⟨a, G, hgrp, hsmooth, hproper, gen, _⟩ :=
    exists_grpObj_descend (GapBLR.specDiag p) c (GapBLR.specConeIsLimit p L)
      EGAIV_8_8_2_ii_proof ZInQ.Contrib.EGAProperLimit.egaIV_8_10_5_xii_proof
      EGAIV_17_7_8_ii_proof B
  let f := a.unop.s
  let ι := GapBLR.ej a
  let g := c.π.app a
  let _ : GrpObj G := hgrp
  have : Smooth G.hom := hsmooth
  have : IsProper G.hom := hproper
  have : IsOpenImmersion ι := by
    dsimp [ι]
    infer_instance
  have : QuasiCompact ι := by
    change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap D (Localization.Away f))))
    infer_instance
  let M : Over (S D) := Over.mk (G.hom ≫ ι)
  have : Smooth M.hom := show Smooth (G.hom ≫ ι) from inferInstance
  have : IsSeparated M.hom := show IsSeparated (G.hom ≫ ι) from inferInstance
  have : QuasiCompact M.hom := show QuasiCompact (G.hom ≫ ι) from inferInstance
  have hgen : g ≫ ι = jL D L := GapBLR.π_ej L a
  let e : (gf D L).obj M ≅ A.X :=
    NeronExt.pbCongr hgen.symm M ≪≫ (Over.pullbackComp g ι).app M ≪≫
      (Over.pullback g).mapIso (NeronExt.pbMapIso ι G) ≪≫ gen
  have hf : f ≠ 0 := ne_zero_of_idx a
  refine ⟨M, inferInstance, inferInstance, inferInstance, e, f, hf, fun w hw hfw => ?_⟩
  have hw0 : w ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hw hD
  let _ := NeronExt.locAlg L w
  have := NeronExt.locAlg_tower L w
  have : IsDiscreteValuationRing (Localization.AtPrime w) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain D hw0 _
  have : IsFractionRing (Localization.AtPrime w) L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization w.primeCompl _ L
  -- The same principal open is a stage in the diagram for the localization at `w`.
  let b : (GapBLR.Idx w)ᵒᵖ := Opposite.op ⟨f, hfw⟩
  let jw' : Spec (CommRingCat.of (Localization.AtPrime w)) ⟶ (GapBLR.specDiag p).obj a :=
    (GapBLR.specCone w (Localization.AtPrime w)).π.app b
  let jw := Spec.map (CommRingCat.ofHom (algebraMap D (Localization.AtPrime w)))
  have hjw : jw' ≫ ι = jw := GapBLR.π_ej (Localization.AtPrime w) b
  let iso : (Over.pullback jw).obj M ≅ (Over.pullback jw').obj G :=
    NeronExt.pbCongr hjw.symm M ≪≫ (Over.pullbackComp jw' ι).app M ≪≫
      (Over.pullback jw').mapIso (NeronExt.pbMapIso ι G)
  let _ : GrpObj ((Over.pullback jw').obj G) := Functor.grpObjObj
  have : IsProper ((Over.pullback jw').obj G).hom := show IsProper (pullback.snd _ _) from inferInstance
  have : Smooth ((Over.pullback jw').obj G).hom := show Smooth (pullback.snd _ _) from inferInstance
  exact NeronExt.isNeronModelOver_of_iso iso
    (NeronExt.isNeronModelOver_of_grpObj (Localization.AtPrime w) L _)

end GoodModel

/-- BLR §1.4, Theorem 3 over an affine Dedekind base, derived from local existence
for abelian varieties over DVRs (BLR §1.3, Corollary 2). -/
theorem neronSchemeExtensionDedekind_of_dvr (hDVR : NeronSchemeExtensionDVR) :
    NeronSchemeExtensionDedekind := by
  intro D _ _ L _ _ _ A hD
  obtain ⟨M, hsmooth, hsep, hqc, eM, f, hf, hM⟩ := goodModel hD A
  have : Smooth M.hom := hsmooth
  have : IsSeparated M.hom := hsep
  have : QuasiCompact M.hom := hqc
  have hcov : ∀ x : S D, ∃ U : (S D).Opens, x ∈ U ∧ Nonempty (NeronOn D L A.X U) := by
    intro x
    obtain ⟨v, hv, hxv⟩ := Ideal.exists_le_maximal (PrimeSpectrum.asIdeal (R := D) x)
      (PrimeSpectrum.isPrime (R := D) x).ne_top
    have : v.IsMaximal := hv
    have hv0 : v ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hv hD
    let _ := NeronExt.locAlg L v
    have := NeronExt.locAlg_tower L v
    have : IsDiscreteValuationRing (Localization.AtPrime v) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain D hv0 _
    have : IsFractionRing (Localization.AtPrime v) L :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization v.primeCompl _ L
    obtain ⟨N, hNsmooth, hNsep, hNqc, eN, hNext⟩ := hDVR (Localization.AtPrime v) L A
    have : Smooth N.hom := hNsmooth
    have : IsSeparated N.hom := hNsep
    have hN : CToPrinted.IsNeronModelOver (Localization.AtPrime v) L N := by
      refine ⟨hNsmooth, hNsep, inferInstance, hNqc, fun Y _ => ⟨?_, ?_⟩⟩
      · intro g g' he
        apply neron_extension_injective N eN Y
        exact congrArg (· ≫ eN.hom) he
      · intro g
        obtain ⟨g', he⟩ := hNext Y (g ≫ eN.hom)
        exact ⟨g', (cancel_mono eN.hom).mp he⟩
    obtain ⟨U, hvU, hU⟩ := near hD A.X v N ⟨hN, ⟨eN⟩⟩ M eM f hf hM
    refine ⟨U, ?_, hU⟩
    have hle : (show PrimeSpectrum D from x) ≤ (show PrimeSpectrum D from pt v) := hxv
    exact ((PrimeSpectrum.le_iff_specializes _ _).mp hle).mem_open U.isOpen hvU
  let n := glued A.X hcov
  exact ⟨n.X, n.smooth, n.sep, n.qc, n.e, fun Y _ => n.ext Y (Scheme.Hom.preimage_top _)⟩

end NeronExtDedekind
