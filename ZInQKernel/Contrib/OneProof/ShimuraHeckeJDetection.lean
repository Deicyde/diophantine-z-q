import ZInQKernel.Contrib.OneProof.HeckePin
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.Dimension
import Mathlib.Algebra.AlgebraicCard

/-! Detecting constancy on the points used in the composite action. -/

noncomputable section

namespace ShimuraSteps.HeckeJ

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves PkgI3 PkgI3.AbVar AfTateLam AfTateLam.HeckePin
open X1Igusa.Weber UpperHalfPlane
open Filter

variable {N : ℕ} {X : Over SpecQ} [IsIntegral X.left] {jX tX : X.left.functionField}

/-- The (j) coordinate of a realized point has its analytic value even where the
non-generic branch of the Weber function is used. -/
theorem regAt_j_of_atTau {x : CPt X} {τ : UpperHalfPlane} (hx : AtTau N jX tX x τ) :
    RegAt x jX (Jf τ) := by
  let P : Polynomial (Polynomial ℤ) := Polynomial.C Polynomial.X
  have hP : AfTateOr.ev2 P jX tX = jX := by simp [P, AfTateOr.ev2]
  have h1 : AfTateOr.ev2 (1 : Polynomial (Polynomial ℤ)) jX tX = 1 := by simp [AfTateOr.ev2]
  have eP (w : UpperHalfPlane) : X1Igusa.Weber.evAn N (AfTateOr.toQ P) w = Jf w := by
    simp [P, AfTateOr.toQ, X1Igusa.Weber.evAn, Jf, ofComplex_apply]
  have e1 (w : UpperHalfPlane) : X1Igusa.Weber.evAn N (AfTateOr.toQ 1) w = 1 := by
    simp [X1Igusa.Weber.evAn]
  have hc : Continuous (fun w : UpperHalfPlane => Jf w) :=
    diffOn_Jf.continuousOn.comp_continuous UpperHalfPlane.continuous_coe fun w => w.im_pos
  have hlim := (hc.continuousAt (x := τ)).continuousWithinAt (s := {τ}ᶜ)
  have hg := hx P 1 (Jf τ) (by rw [h1]; exact one_ne_zero)
  simp only [eP, e1, div_one, hP, h1] at hg
  exact hg hlim

private theorem regAt_stalk {x : CPt X} {g : X.left.functionField} {c : ℂ}
    (h : RegAt x g c) :
    ∃ r : X.left.presheaf.stalk (x.left (IsLocalRing.closedPoint ℂ)),
      algebraMap _ X.left.functionField r = g ∧ Scheme.stalkClosedPointTo x.left r = c := by
  obtain ⟨U, hU, s, hx, hs, hc⟩ := h
  let : Nonempty U := hU
  have hmem : x.left (IsLocalRing.closedPoint ℂ) ∈ U :=
    hx (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (ptObj (K := ℚ) ℂ).left.Opens) from trivial)
  refine ⟨X.left.presheaf.germ U _ hmem s, by simpa using hs, ?_⟩
  let v : Spec (CommRingCat.of ℂ) ⟶ X.left := x.left
  have hmem' : v (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈ U := hmem
  have he := Scheme.germ_stalkClosedPointTo v U hmem'
  have he' : X.left.presheaf.germ U _ hmem' ≫ Scheme.stalkClosedPointTo v =
      v.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom := by
    rw [he]
    simp only [Scheme.Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
      Category.assoc]
    congr 3
  exact (congrArg (fun k : Γ(X.left, U) ⟶ CommRingCat.of ℂ => k s) he').trans hc

private theorem eval_generic_of_regAt {x : CPt X}
    (hx : x.left (IsLocalRing.closedPoint ℂ) = genericPoint X.left)
    {g : X.left.functionField} {c : ℂ} (h : RegAt x g c) :
    ∃ e : X.left.functionField →+* ℂ, e g = c := by
  obtain ⟨r, hr, hv⟩ := regAt_stalk h
  have hi : Inseparable (genericPoint X.left) (x.left (IsLocalRing.closedPoint ℂ)) := by
    rw [hx]
  let e := X.left.presheaf.stalkCongr hi
  have hmap : e.inv r = algebraMap _ X.left.functionField r := by
    change X.left.presheaf.stalkSpecializes hi.specializes r =
      X.left.presheaf.stalkSpecializes ((genericPoint_spec X.left).specializes trivial) r
    rfl
  refine ⟨(Scheme.stalkClosedPointTo x.left).hom.comp e.hom.hom, ?_⟩
  rw [← hr, ← hmap]
  exact (congrArg (fun t : X.left.presheaf.stalk (x.left (IsLocalRing.closedPoint ℂ)) ⟶
    X.left.presheaf.stalk (x.left (IsLocalRing.closedPoint ℂ)) =>
    Scheme.stalkClosedPointTo x.left (t r))
    e.inv_hom_id).trans hv

private theorem isAlgebraic_of_regAt_closed (hC : IsCurve X) {x : CPt X}
    (hx : IsClosed {x.left (IsLocalRing.closedPoint ℂ)}) {g : X.left.functionField} {c : ℂ}
    (h : RegAt x g c) : IsAlgebraic ℚ c := by
  let y := x.left (IsLocalRing.closedPoint ℂ)
  have : IsProper X.hom := hC.proper
  have hc : IsClosedImmersion (X.left.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have : IsFinite (X.left.fromSpecResidueField y ≫ X.hom) := by
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  let φ := Spec.preimage (X.left.fromSpecResidueField y ≫ X.hom)
  have hφ : Spec.map φ = X.left.fromSpecResidueField y ≫ X.hom := Spec.map_preimage _
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  let : Algebra ℚ (X.left.residueField y) := φ.hom.toAlgebra
  have : Module.Finite ℚ (X.left.residueField y) := hfin
  have : Algebra.IsAlgebraic ℚ (X.left.residueField y) := Algebra.IsAlgebraic.of_finite _ _
  obtain ⟨r, -, hr⟩ := regAt_stalk h
  let v : Spec (CommRingCat.of ℂ) ⟶ X.left := x.left
  let ψ := (Scheme.descResidueField (Scheme.stalkClosedPointTo v)).hom.toRatAlgHom
  have he : ψ (X.left.residue y r) = c := by
    change Scheme.descResidueField (Scheme.stalkClosedPointTo v) (X.left.residue y r) = c
    rw [← CommRingCat.comp_apply, Scheme.residue_descResidueField, hr]
  rw [← he]
  exact (Algebra.IsAlgebraic.isAlgebraic _).algHom ψ

private theorem exists_nonAlg_j : ∃ τ : UpperHalfPlane, ¬ IsAlgebraic ℚ (Jf τ) := by
  by_contra! h
  have hc : Continuous (fun w : UpperHalfPlane => Jf w) :=
    diffOn_Jf.continuousOn.comp_continuous UpperHalfPlane.continuous_coe fun w => w.im_pos
  have hcnt := (Algebraic.countable ℚ ℂ).mono
    (show Set.range (fun w : UpperHalfPlane => Jf w) ⊆ {z | IsAlgebraic ℚ z} from
      fun _ ⟨w, hw⟩ => hw ▸ h w)
  have hEq := const_of_countable hc hcnt UpperHalfPlane.I τρ
  rw [Jf_I, Jf_ρ] at hEq
  norm_num at hEq

/-- For detecting constancy of rational morphisms, it suffices to realize two
parameters: the one with (j=1728), and one with transcendental (j). The two
points lie over a closed point and the generic point of the rational curve. -/
theorem exists_closed_and_generic_atTau (hC : IsCurve X) (hP : TauPts N jX tX) :
    ∃ (τ τ' : UpperHalfPlane) (x x' : CPt X),
      AtTau N jX tX x τ ∧ AtTau N jX tX x' τ' ∧
      IsClosed {x.left (IsLocalRing.closedPoint ℂ)} ∧
      x'.left (IsLocalRing.closedPoint ℂ) = genericPoint X.left := by
  obtain ⟨τ, hτ⟩ := exists_nonAlg_j
  obtain ⟨x, hx⟩ := hP τ
  obtain ⟨y, hy⟩ := hP UpperHalfPlane.I
  have : SmoothOfRelativeDimension 1 X.hom := hC.smooth
  have hb := topologicalKrullDim_le_of_smoothOfRelativeDimension X.hom 1
  have hxg : x.left (IsLocalRing.closedPoint ℂ) = genericPoint X.left :=
    Scheme.eq_genericPoint_of_not_isClosed hb
      (fun h => hτ (isAlgebraic_of_regAt_closed hC h (regAt_j_of_atTau hx)))
  refine ⟨UpperHalfPlane.I, τ, y, x, hy, hx, ?_, hxg⟩
  by_contra h
  have hyg := Scheme.eq_genericPoint_of_not_isClosed hb h
  obtain ⟨f, hf⟩ := eval_generic_of_regAt hyg (regAt_j_of_atTau hy)
  rw [Jf_I] at hf
  have hj : jX = 1728 := f.injective (hf.trans (map_ofNat f 1728).symm)
  obtain ⟨e, he⟩ := eval_generic_of_regAt hxg (regAt_j_of_atTau hx)
  rw [hj, map_ofNat] at he
  exact hτ (he ▸ isAlgebraic_natCast (R := ℚ) (A := ℂ) 1728)

/-- Provided the `AtTau` points exist, the pointed constancy criterion follows
from properness and the two test points. The image of the generic point is
closed, so the morphism factors through the image of the rational base point. -/
theorem constOnTauPoints_of_realization (hP : X1TauPoints) : ConstOnTauPoints := by
  intro N hN X iX jX tX hC hG P₀ J g hg h
  obtain ⟨τ, τ', x, x', hx, hx', hxc, hxg⟩ :=
    exists_closed_and_generic_atTau hC (hP N hN X jX tX hC hG)
  have : IsProper X.hom := hC.proper
  have : IsProper (g.left ≫ J.X.hom) := by rw [Over.w]; infer_instance
  have : IsProper g.left := IsProper.of_comp g.left J.X.hom
  have heq : g.left (x.left (IsLocalRing.closedPoint ℂ)) = g.left (genericPoint X.left) := by
    have he := congrArg (fun v : CPt J.X => v.left (IsLocalRing.closedPoint ℂ))
      (h τ τ' x x' hx hx')
    change g.left (x.left (IsLocalRing.closedPoint ℂ)) =
      g.left (x'.left (IsLocalRing.closedPoint ℂ)) at he
    rw [hxg] at he
    exact he
  have hclosed : IsClosed {g.left (genericPoint X.left)} := by
    rw [← heq, ← Set.image_singleton]
    exact g.left.isClosedMap _ hxc
  have hconst (w : X.left) : g.left w = g.left (genericPoint X.left) := by
    have hw := ((genericPoint_spec X.left).specializes (Set.mem_univ w)).map g.left.continuous
    exact Set.mem_singleton_iff.1 (hclosed.closure_eq ▸ hw.mem_closure)
  let q : SpecQ ⟶ J.X.left := (P₀ ≫ g).left
  have hq : q ≫ J.X.hom = 𝟙 SpecQ := Over.w (P₀ ≫ g)
  have : IsClosedImmersion (q ≫ J.X.hom) := by rw [hq]; infer_instance
  have : IsClosedImmersion q := IsClosedImmersion.of_comp q J.X.hom
  have hsub : Set.range g.left ⊆ Set.range q := by
    rintro _ ⟨w, rfl⟩
    exact ⟨IsLocalRing.closedPoint ℚ, (hconst _).trans (hconst w).symm⟩
  have hrad : g.left.ker.radical = g.left.ker := by
    ext U : 2
    rw [Scheme.IdealSheafData.radical_ideal, g.left.ker_apply U]
    exact Ideal.radical_eq_iff.mpr (Ideal.isRadical_bot.comap _)
  have hle : q.ker ≤ g.left.ker := by
    rw [← hrad, ← Scheme.IdealSheafData.vanishingIdeal_support]
    apply Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp
    change (g.left.ker.support : Set J.X.left) ⊆ q.ker.support
    rw [g.left.support_ker, q.support_ker]
    exact closure_mono hsub
  let u := IsClosedImmersion.lift q g.left hle
  have hu : u ≫ q = g.left := IsClosedImmersion.lift_fac q g.left hle
  have huX : u = X.hom := by
    rw [← Category.comp_id u, ← hq, ← Category.assoc, hu, Over.w]
  apply Over.OverMorphism.ext
  have hq' : q = (η[J.X]).left := by
    change (P₀ ≫ g).left = _
    rw [hg]
    change (toUnit (𝟙_ (Over SpecQ)) ≫ η[J.X]).left = _
    rw [toUnit_unit, Category.id_comp]
  rw [← hu, huX, hq']
  rfl

#print axioms regAt_j_of_atTau
#print axioms regAt_stalk
#print axioms eval_generic_of_regAt
#print axioms isAlgebraic_of_regAt_closed
#print axioms exists_nonAlg_j
#print axioms exists_closed_and_generic_atTau
#print axioms constOnTauPoints_of_realization

end ShimuraSteps.HeckeJ
