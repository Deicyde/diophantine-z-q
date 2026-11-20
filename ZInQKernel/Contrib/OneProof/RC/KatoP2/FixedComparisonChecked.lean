import ZInQKernel.Contrib.OneProof.RC.KatoP2.FiniteAnchor

/-! The same finite comparison as Appendix E.1, with the finite system
passed directly. The historical interface is needed only to specialize
the statement back to the older consumer, not to use the comparison. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KatoP2.Checked

open CategoryTheory NumberField IsDedekindDomain SelmerComplex CoefModules LambdaCoef
open AppEK1 PrintsArith ZInQ.Contrib.CloudB3RC53 _root_.ZInQ.Manuscript.RC.Even

/-- Exact finite comparison on the retained modules: reduction, trace,
deck action and detection modulo the lattice's possible dyadic torsion. -/
abbrev KatoFiniteComparison {E : WeierstrassCurve ℚ}
    (es : EulerSystemData ℤ_[2]) {N : ℕ} (fam : BinaryFamily N)
    (μ : ∀ m : FamilyIndex fam, HasRootsOfUnity ℚ (familyPlaces fam) (m : ℕ))
    (nested : ∀ (m m' : FamilyIndex fam), (m : ℕ) ∣ (m' : ℕ) →
      cyclotomicKernel (μ m') ≤ cyclotomicKernel (μ m)) : Prop :=
  KatoP2.RetainedFiniteComparison (E := E) es fam μ nested

/-- The same comparison at the fixed curve and newform level. -/
abbrev FixedKatoFiniteComparison (ℓ : ℕ) (es : EulerSystemData ℤ_[2])
    (fam : BinaryFamily (CST.newformLevel (Ecurve ℓ)))
    (μ : ∀ m : FamilyIndex fam, HasRootsOfUnity ℚ (familyPlaces fam) (m : ℕ))
    (nested : ∀ (m m' : FamilyIndex fam), (m : ℕ) ∣ (m' : ℕ) →
      cyclotomicKernel (μ m') ≤ cyclotomicKernel (μ m)) : Prop :=
  Checked.KatoFiniteComparison (E := Ecurve ℓ) es fam μ nested

/-- Finite-coefficient detection of the signed anchor, with no Iwasawa input. -/
theorem exists_nonzero_image_of_anchored_weightedSum_p2 {E : WeierstrassCurve ℚ}
    {Sig Sbad : Finset ℕ} {es : EulerSystemData ℤ_[2]}
    (K : RetainedReciprocity E Sig Sbad es) {N : ℕ} (fam : BinaryFamily N)
    (μ : ∀ m : FamilyIndex fam, HasRootsOfUnity ℚ (familyPlaces fam) (m : ℕ))
    (nested : ∀ (m m' : FamilyIndex fam), (m : ℕ) ∣ (m' : ℕ) →
      cyclotomicKernel (μ m') ≤ cyclotomicKernel (μ m))
    (hcomp : Checked.KatoFiniteComparison (E := E) es fam μ nested)
    (m : FamilyIndex fam) (hm : KatoXi 2 Sig m)
    (χ : DirichletCharacter ℂ (m : ℕ)) (signs : (ZMod (m : ℕ))ˣ → ℤ)
    (hχ : ∀ g, (signs g : ℂ) = χ (g : ZMod (m : ℕ))) (hL : K.Lcont χ 1 ≠ 0) :
    ∃ i, hcomp.choose m i
      (∑ g : (ZMod (m : ℕ))ˣ, signs g • (MonoidAlgebra.of ℤ_[2] _ g • es.z m)) ≠ 0 :=
  KatoP2.exists_nonzero_image_of_anchored_weightedSum_p2 K fam μ nested hcomp m hm χ signs hχ hL

end ZInQ.Manuscript.RC.KatoP2.Checked
