import ZInQKernel.Contrib.OneProof.SZThm33.ValuationWeilEvaluation
import ZInQKernel.Contrib.OneProof.SZThm33.ValuationResidueFibre
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.RankOneTestModel
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.TestModelProjection
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ValuationPairingCoefficient

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open Scheme.Modules HDec.WeilPairing ReductSplit PkgI3 PkgI3.AbVar ZInQ.HeightSplit
open PicDict PicDict.Transport PicDict.DirectPairing ZInQ.ToricOrthogonality
open scoped CategoryTheory.MonObj

namespace SZRaynaud.Ambient

variable {K : Type} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {w : ValuationSubring (AlgebraicClosure K)} (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
  (A : AbVar K) (M : GroupModelO A O) [GeometricallyIntegral M.G.hom]

/-- Projection from the geometric special fibre to the model. -/
private abbrev geometricSpecialProjection {A : AbVar K} (M : GroupModelO A O) :=
  Limits.pullback.fst M.G.hom (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- A torsion section whose geometric specialization is in a rank-one
torus pairs trivially with every lifted torsion section of the identity model. -/
theorem valuationWeilValue_eq_one_of_rankOne
    {n : ℕ} (hn : 0 < n) (hu : IsUnit (n : O)) (hchar : (n : K) ≠ 0)
    (d : puncturedLine (ResBarO O) ⟶ geomSpecialFibre M) [IsMonHom d]
    (x y : Over.mk (base hw) ⟶ M.G) (hx : x ^ n = 1) (hy : y ^ n = 1)
    (x₀ : 𝟙_ (Over (Spec (CommRingCat.of (ResBarO O)))) ⟶ puncturedLine (ResBarO O))
    (y₀ : 𝟙_ (Over (Spec (CommRingCat.of (ResBarO O)))) ⟶ geomSpecialFibre M)
    (hx₀ : x₀ ^ n = 1) (hy₀ : y₀ ^ n = 1)
    (hxp : x₀.left ≫ d.left ≫ geometricSpecialProjection M =
      valuationGeometricResidue hw ≫ (valuationSectionEquiv hw A M x).left ≫ (Limits.pullback.fst M.G.hom (base hw)))
    (hyp : y₀.left ≫ geometricSpecialProjection M =
      valuationGeometricResidue hw ≫ (valuationSectionEquiv hw A M y).left ≫ (Limits.pullback.fst M.G.hom (base hw)))
    (L : M.G.left.Modules) [SheafOfModules.IsInvertible L] :
    letI : SheafOfModules.IsInvertible (Relative.genericModelLine M L) := by
      unfold Relative.genericModelLine
      infer_instance
    value A (Scheme.Pic.mk (Relative.genericModelLine M L)) hn hchar
      (valuationTorsionPoint hw A M x hx) (valuationTorsionPoint hw A M y hy) = 1 := by
  let genericProjection := Limits.pullback.fst M.G.hom (base hw)
  have : IsCommMonObj M.G := ZInQ.FaltingsRestate.isCommMonObj_groupModelO M
  have : IsProper (Limits.pullback.snd M.G.hom (jO O)) := by
    have : IsIso M.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso M.gen).hom)
    change IsProper ((Over.pullback (jO O)).obj M.G).hom
    rw [← Over.w M.gen.hom]
    infer_instance
  have : IsIntegral M.G.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian M.G.hom
  have hconst := (appTop_bijective_of_proper_generic (K := K) M.G.hom η[M.G].left (Over.w η[M.G])).surjective
  have : Smooth (geomSpecialFibre M).hom :=
    show Smooth (Limits.pullback.snd M.G.hom (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))))) from inferInstance
  have : GeometricallyIntegral (geomSpecialFibre M).hom :=
    show GeometricallyIntegral (Limits.pullback.snd M.G.hom (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))))) from inferInstance
  let xw := valuationSectionEquiv hw A M x
  let yw := valuationSectionEquiv hw A M y
  have hxw : xw ^ n = 1 := by rw [← map_pow, hx, map_one]
  have hyw : yw ^ n = 1 := by rw [← map_pow, hy, map_one]
  have hc : genericProjection ≫ M.G.hom = (valuationModel hw A M).hom ≫ base hw := Limits.pullback.condition
  have hp : geometricSpecialProjection M ≫ M.G.hom = (geomSpecialFibre M).hom ≫ valuationGeometricResidue hw ≫ base hw := by
    rw [valuationGeometricResidue_comp_base]
    exact Limits.pullback.condition
  have hη : η[(geomSpecialFibre M)].left ≫ geometricSpecialProjection M =
      (valuationGeometricResidue hw ≫ base hw) ≫ η[M.G].left := by
    rw [valuationGeometricResidue_comp_base]
    exact testModel_projection_origin M.G (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))))
  have hηX : η[(valuationModel hw A M)].left ≫ genericProjection = (base hw) ≫ η[M.G].left :=
    testModel_projection_origin M.G (base hw)
  have hpm : (multiplyBy (geomSpecialFibre M) n).left ≫ geometricSpecialProjection M =
      geometricSpecialProjection M ≫ (multiplyBy M.G n).left :=
    testModel_projection_multiply M.G (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O)))) n
  have hcm : (multiplyBy (valuationModel hw A M) n).left ≫ genericProjection = genericProjection ≫ (multiplyBy M.G n).left :=
    testModel_projection_multiply M.G (base hw) n
  let L₀ := Scheme.Pic.mk L
  obtain ⟨D, hDinv, hD⟩ := Scheme.Pic.exists_mk_eq (productDeltaClass M.G L₀)
  obtain ⟨J⟩ := nonempty_iso_powerFirst_powerSecond (K := K) M.G L₀ D hD n
  obtain ⟨ψ, hψ⟩ := exists_testModel_trivialization_special_eq_one
    M.G (valuationModel hw A M) (geomSpecialFibre M) (base hw) genericProjection hc
    (valuationGeometricResidue hw) (geometricSpecialProjection M) d hp hη hηX
    n hpm hcm hconst xw yw hxw hyw x₀ y₀ hx₀ hy₀ hxp hyp L₀ D hD J
  let a := testPointSlice M.G (valuationModel hw A M) (base hw) genericProjection hc yw
  let m := (multiplyBy (valuationModel hw A M) n).left
  let t := (translateBy (valuationModel hw A M) xw).left
  let ht := congrArg Over.Hom.left (translateBy_comp_multiplyBy (valuationModel hw A M) xw n hxw)
  let f := wf t m ht ((pullback a).obj D) ψ
  have : SheafOfModules.IsInvertible (Relative.genericModelLine M L) := by
    unfold Relative.genericModelLine
    infer_instance
  let Lη := Scheme.Pic.mk (Relative.genericModelLine M L)
  let u := value A Lη hn hchar (valuationTorsionPoint hw A M x hx) (valuationTorsionPoint hw A M y hy)
  let β := (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure K))).inv
  have hcoeff : (gen ≫ η[(valuationModel hw A M)].left).appTop f = β (u : AlgebraicClosure K) :=
    valuationWeilEvaluation_at_generic hw A M hn hchar x y hx hy L D hD a
      (testPointSlice_fst M.G (valuationModel hw A M) (base hw) genericProjection hc yw)
      (testPointSlice_snd M.G (valuationModel hw A M) (base hw) genericProjection hc yw) ht ψ
  have hpow : ((gen ≫ η[(valuationModel hw A M)].left).appTop f) ^ n = 1 := by
    rw [hcoeff, ← map_pow, ← Units.val_pow_eq_pow_val, show u ^ n = 1 from value_pow A Lη hn hchar _ _,
      Units.val_one, map_one]
  have hres : (n : IsLocalRing.ResidueField w) ≠ 0 := by
    simpa only [map_natCast] using (hu.map ((IsLocalRing.residue w).comp (comapHom hw))).ne_zero
  have h1 := eval_eq_one_of_specialization_at_section η[(valuationModel hw A M)].left w.subtype Subtype.val_injective
    (geomResidueEquiv hw).toRingHom hres f hpow
      (by rw [← valuationGeometricResidue_eq]; exact hψ)
  have ht1 : (gen ≫ η[(valuationModel hw A M)].left).appTop f = 1 := by
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h1, map_one]
  change u = 1
  apply Units.ext
  apply (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure K))).commRingCatIsoToRingEquiv.symm.injective
  exact hcoeff.symm.trans (ht1.trans (map_one β.hom).symm)

end SZRaynaud.Ambient
