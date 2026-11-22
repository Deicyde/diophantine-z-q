import ZInQKernel.Contrib.OneProof.Y3CMPeriodValues
import ZInQKernel.Contrib.OneProof.Y3FibreBound
import ZInQKernel.Contrib.OneProof.Y3ToP1jDescent
import ZInQKernel.Contrib.OneProof.H.TailZ21

/-! The rational projective-line identification and the three rational
distinguished fibres give the original normalized level-three coordinate. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open LeafQM LeafQM.AV Y3Fix
open HDec HDec.QMSplit.Moduli
open HDec.HSyn.G0Split.FibreQM HDec.HSyn.G0Split.FibreQM.PeriodGlue
open HDec.HSyn.G0Split.FibreQM.PeriodMapH

namespace Y3P1j

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

private theorem standard_coordinate : HDec.MCRGlue.IsP1CoordinateQ P1.PQ P1.tau :=
  ⟨AlgebraicGeometry.ProjectiveSpace.isAffineOpen_standardOpen P1.I P1.SQ P1.i0,
    AlgebraicGeometry.ProjectiveSpace.isAffineOpen_standardOpen P1.I P1.SQ P1.i1,
    P1.chart_bijective P1.i0 P1.i1 P1.i0_ne_i1,
    P1.chart_bijective P1.i1 P1.i0 P1.i1_ne_i0⟩

/-- The universal family on the printed model gives a classifying morphism to
each fine witness. Its geometric point bijection lets the coordinate descend
to that witness. -/
theorem y3ToP1j_of_printedOrbitCoordinateAt
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {π : ToP1 Y.left}
    (hΦ : R1fpPropsAbP Y Φ) (hπ : OrbitCoordinateAt Y Φ π) : Y3ToP1j := by
  intro Y' Φ' hΦ'
  obtain ⟨𝒜, h𝒜⟩ := hΦ.2.2.2.1
  have hfib : ∀ (K : Type) [Field K] [Algebra ℚ K] (x : fieldPt K ⟶ Y),
      ∃ P : QML3 K, IsFibreOf 𝒜.toQMFamily x.left P :=
    fun K _ _ x => ⟨Quotient.out (Φ K x), h𝒜 K x _ (Quotient.out_eq _).symm⟩
  obtain ⟨c, hc⟩ := (LeafQM.AV.Pin.R1fpProps.univ hΦ') Y hΦ.1 hΦ.2.1 𝒜.toQMFamily hfib
  have hclass (x : fieldPt Qbar ⟶ Y) : Φ' Qbar (x ≫ c) = Φ Qbar x :=
    (hc Qbar x _ (h𝒜 Qbar x _ (Quotient.out_eq _).symm)).trans (Quotient.out_eq _)
  have hinj : Function.Injective (fun x : fieldPt Qbar ⟶ Y => x ≫ c) := by
    intro x y h
    apply (Φ Qbar).injective
    rw [← hclass x, ← hclass y]
    exact congrArg (Φ' Qbar) h
  have hsurj : ∀ z : fieldPt Qbar ⟶ Y', ∃ x : fieldPt Qbar ⟶ Y, x ≫ c = z := by
    intro z
    let x := (Φ Qbar).symm (Φ' Qbar z)
    exact ⟨x, (Φ' Qbar).injective ((hclass x).trans ((Φ Qbar).apply_symm_apply _))⟩
  obtain ⟨π', hπ'⟩ := Descent.toP1DescendsAlongSurj_proof Y Y' hΦ.1 hΦ.2.1
    hΦ'.1 hΦ'.2.1 c π hsurj (fun x y h => congrArg (fun p : fieldPt Qbar ⟶ Y =>
      π.val (K := Qbar) p.left) (hinj h))
  refine ⟨π', (y3ToP1jAt_iff_orbitCoordinateAt hΦ' π').mpr ?_⟩
  intro z z' P Q hP hQ
  obtain ⟨x, rfl⟩ := hsurj z
  obtain ⟨y, rfl⟩ := hsurj z'
  rw [hπ' x, hπ' y]
  exact hπ x y P Q ((hclass x).symm.trans hP) ((hclass y).symm.trans hQ)

/-- On the actual twist quotient, a rational isomorphism with the projective
line and the three rational distinguished fibres yield the exact coordinate
on all fine models. -/
theorem y3ToP1j_of_quotient_iso_and_CM_fibres
    {Y Z : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} (π : Y ⟶ Z)
    (hΦ : R1fpPropsAbP Y Φ) (e : Z ≅ P1.PQ)
    (hquot : ∀ (y y' : fieldPt Qbar ⟶ Y) (P Q : QML3 Qbar),
      Φ Qbar y = M3.mk P → Φ Qbar y' = M3.mk Q →
        (y ≫ π = y' ≫ π ↔ ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)))
    {x₄ x₃ x₂₄ : fieldPt ℚ ⟶ Z} (h43 : x₄ ≠ x₃) (h424 : x₄ ≠ x₂₄)
    (h324 : x₃ ≠ x₂₄)
    (hCM : ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
      (HasCM4 P.q ↔ y ≫ π = fieldMap (Algebra.ofId ℚ Qbar) ≫ x₄) ∧
      (HasCM3 P.q ↔ y ≫ π = fieldMap (Algebra.ofId ℚ Qbar) ≫ x₃) ∧
      (HasCM24 P.q ↔ y ≫ π = fieldMap (Algebra.ofId ℚ Qbar) ≫ x₂₄)) :
    Y3ToP1j := by
  let τ : ToP1 Z.left := P1.tau.comp e.hom.left
  have hinj {K : Type} [Field K] [Algebra ℚ K] :
      Function.Injective (fun x : fieldPt K ⟶ Z => τ.val (K := K) x.left) := by
    intro x y h
    change (P1.tau.comp e.hom.left).val x.left =
      (P1.tau.comp e.hom.left).val y.left at h
    rw [ToP1.val_comp_right, ToP1.val_comp_right] at h
    have he : x ≫ e.hom = y ≫ e.hom :=
      Over.OverMorphism.ext (Descent.pt_eq_of_val standard_coordinate _ _ h)
    exact (cancel_mono e.hom).mp he
  obtain ⟨g, hg4, hg3, hg24⟩ := exists_mobiusBG (τ.val x₄.left)
    (τ.val x₃.left) (τ.val x₂₄.left) (fun h => h43 (hinj h))
    (fun h => h424 (hinj h)) (fun h => h324 (hinj h))
  obtain ⟨σ, hσ⟩ := mobiusCompose Z τ g
  let ρ : ToP1 Y.left := σ.comp π.left
  have hρ (y : fieldPt Qbar ⟶ Y) : ρ.val y.left =
      Matrix.GeneralLinearGroup.map (algebraMap ℚ Qbar) g • τ.val (y ≫ π).left :=
    (ToP1.val_comp_right σ π.left y.left).trans (hσ (y ≫ π))
  have hval (y : fieldPt Qbar ⟶ Y) (x : fieldPt ℚ ⟶ Z) :
      ρ.val y.left = (g • τ.val x.left).map (algebraMap ℚ Qbar) ↔
        y ≫ π = fieldMap (Algebra.ofId ℚ Qbar) ≫ x := by
    rw [hρ, smul_map_iff]
    have hx : τ.val (fieldMap (Algebra.ofId ℚ Qbar) ≫ x).left =
        (τ.val x.left).map (algebraMap ℚ Qbar) := τ.val_comp (algebraMap ℚ Qbar) x.left
    rw [← hx, hinj.eq_iff]
  apply y3ToP1j_of_printedOrbitCoordinateAt hΦ (π := ρ)
  intro y y' P Q hP hQ
  obtain ⟨h4, h3, h24⟩ := hCM y P hP
  refine ⟨?_, h4.trans ?_, h3.trans ?_, h24.trans ?_⟩
  · rw [hρ, hρ, (MulAction.injective _).eq_iff, hinj.eq_iff]
    exact hquot y y' P Q hP hQ
  · simpa [hg4] using (hval y x₄).symm
  · simpa [hg3] using (hval y x₃).symm
  · simpa [hg24] using (hval y x₂₄).symm

/-- For a quotient with the printed Deligne periods, the three CM-existence
facts and a rational projective-line identification suffice for (Y_3). -/
theorem y3ToP1j_of_quotient_iso_and_periods
    {Y Z : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} (π : Y ⟶ Z)
    (hΦ : R1fpPropsAbP Y Φ) (e : Z ≅ P1.PQ)
    (hquot : ∀ (K : Type) [Field K] [Algebra ℚ K]
      (y y' : fieldPt K ⟶ Y) (P Q : QML3 K),
      Φ K y = M3.mk P → Φ K y' = M3.mk Q →
        (y ≫ π = y' ≫ π ↔ ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)))
    (hD : Y3Hodge.DeligneCanonicalModelY3EveryPrint) (hL : QMTwistLattice)
    (hA : RayClassCFT.CMAnalytic) (hf : PkgI1.QMHauptmodul)
    (hE : (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q)) : Y3ToP1j := by
  obtain ⟨x₄, x₃, x₂₄, h43, h424, h324, hCM⟩ :=
    exists_rational_CM_fibres_of_periods π hΦ hquot hD hL hA hf hE
  exact y3ToP1j_of_quotient_iso_and_CM_fibres π hΦ e (hquot Qbar) h43 h424 h324 hCM

end Y3P1j

#print axioms Y3P1j.y3ToP1j_of_quotient_iso_and_CM_fibres
#print axioms Y3P1j.y3ToP1j_of_quotient_iso_and_periods
