import ZInQKernel.Contrib.OneProof.Y3InvariantAffine
import ZInQKernel.Contrib.OneProof.FiniteSchemeActionQuotient
import ZInQKernel.Contrib.OneProof.InvariantSchemePoints
import ZInQKernel.Contrib.OneProof.FiniteProperDescent

/-! The finite group of level changes and twists has a scheme quotient over
the rational base, with its invariant-function and factorization properties. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open LeafQM LeafQM.AV LeafQM.AV.Pin LeafQM.AV.R1UnivRigid
open Y3Fix Y3RouteA
open scoped CategoryTheory.Obj

namespace Y3P1j

variable {Y : Over (Spec (CommRingCat.of ℚ))} {𝒜 : QMAbSchemeP Y.left}

/-- The group action on schemes underlying the action over `ℚ`. -/
def twistMarkSchemeAction (hU : Represents Y 𝒜) (hN : IsLocallyNoetherian Y.left) :
    twistMarkGroup hU hN →* Aut Y.left :=
  (Functor.mapAut Y (Over.forget _)).comp (twistMarkGroup hU hN).subtype

/-- The scheme quotient of the represented curve by the actual finite group
of twists and changes of level marking. -/
theorem exists_twistMark_scheme_quotient
    (hP : IsProper Y.hom) (hS : SmoothOfRelativeDimension 1 Y.hom)
    (hU : Represents Y 𝒜) (hN : IsLocallyNoetherian Y.left) :
    ∃ (Z : Over (Spec (CommRingCat.of ℚ))) (π : Y ⟶ Z)
      (hπ : ∀ g, (twistMarkSchemeAction hU hN g).asIso.hom ≫ π.left = π.left),
      IsFinite π.left ∧ IsProper Z.hom ∧ Function.Surjective π.left.base ∧
      (∀ x x' : Y.left, π.left.base x = π.left.base x' ↔
        ∃ g, (twistMarkSchemeAction hU hN g).asIso.hom x = x') ∧
      (∀ V : Z.left.Opens, Function.Injective (π.left.app V)) ∧
      (∀ V : Z.left.Opens, Set.range (π.left.app V) =
        {s | ∀ g, (twistMarkSchemeAction hU hN g).asIso.hom.appLE
          (π.left ⁻¹ᵁ V) (π.left ⁻¹ᵁ V)
          (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s}) ∧
      ∀ (W : Over (Spec (CommRingCat.of ℚ))) (f : Y ⟶ W),
        (∀ g : twistMarkGroup hU hN, g.val.asIso.hom ≫ f = f) →
          ∃! f' : Z ⟶ W, π ≫ f' = f := by
  let ρ := twistMarkSchemeAction hU hN
  have : Finite (twistMarkGroup hU hN) := twistMarkGroup_finite hU hN
  obtain ⟨Z, π, hπ, hint, -, hsurj, horb, hinj, hsections, -, huniv⟩ :=
    FiniteSchemeActionQuotient.exists_quotient ρ
      (exists_invariant_isAffineOpen_of_smooth_curve Y.hom ρ)
  have hbase (g : twistMarkGroup hU hN) : (ρ g).asIso.hom ≫ Y.hom = Y.hom :=
    (g.val.asIso.hom).w
  obtain ⟨z, hz, -⟩ := huniv _ Y.hom hbase
  let Z' := Over.mk z
  let π' : Y ⟶ Z' := Over.homMk π hz
  have : LocallyOfFiniteType (π ≫ z) := hz.symm ▸ (inferInstance : LocallyOfFiniteType Y.hom)
  have hfin := (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType π).mpr
    ⟨hint, locallyOfFiniteType_of_comp π z⟩
  have : Surjective π := ⟨hsurj⟩
  have : IsProper (π ≫ z) := hz.symm ▸ hP
  have : IsNoetherianRing Γ(Spec (CommRingCat.of ℚ), ⊤) :=
    isNoetherianRing_of_ringEquiv (↥(CommRingCat.of ℚ))
      (Scheme.ΓSpecIso (CommRingCat.of ℚ)).symm.commRingCatIsoToRingEquiv
  have hzProper := isProper_of_finite_surjective_comp_of_injective_sections π z
    (fun U _ => hinj U)
  refine ⟨Z', π', hπ, hfin, hzProper, hsurj, horb, hinj, hsections, ?_⟩
  intro W f hf
  have hf' (g : twistMarkGroup hU hN) : (ρ g).asIso.hom ≫ f.left = f.left :=
    congrArg CommaMorphism.left (hf g)
  obtain ⟨d, hd, hd_unique⟩ := huniv W.left f.left hf'
  have hdz : d ≫ W.hom = z := by
    obtain ⟨v, hv, hv_unique⟩ := huniv _ Y.hom hbase
    refine (hv_unique _ ?_).trans (hv_unique _ hz).symm
    change π ≫ (d ≫ W.hom) = Y.hom
    rw [← Category.assoc, hd, Over.w]
  refine ⟨Over.homMk d hdz, ?_, ?_⟩
  · exact Over.OverMorphism.ext hd
  · intro d' he
    exact Over.OverMorphism.ext (hd_unique d'.left (congrArg CommaMorphism.left he))

open HDec.QMSplit.Moduli in
/-- The geometric fibres of the finite quotient are precisely the twist
classes of underlying QM pairs. -/
theorem exists_twistMark_quotient_geometric_fibres
    (hP : IsProper Y.hom) (hS : SmoothOfRelativeDimension 1 Y.hom)
    (hU : Represents Y 𝒜) :
    ∃ (Z : Over (Spec (CommRingCat.of ℚ))) (π : Y ⟶ Z), IsFinite π.left ∧ IsProper Z.hom ∧
      Function.Surjective π.left.base ∧
      ∀ (K : Type) [Field K] [Algebra ℚ K] (y y' : fieldPt K ⟶ Y) (P Q : QML3 K),
        IsFibreOf 𝒜.toQMFamily y.left P → IsFibreOf 𝒜.toQMFamily y'.left Q →
          (y ≫ π = y' ≫ π ↔ ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) := by
  have hN := Y3Audit.isLocallyNoetherian_of_smooth_Q Y hS
  have : Finite (twistMarkGroup hU hN) := twistMarkGroup_finite hU hN
  obtain ⟨Z, π, hπ, hfin, hzProper, hsurj, -, -, hsections, -⟩ :=
    exists_twistMark_scheme_quotient hP hS hU hN
  refine ⟨Z, π, hfin, hzProper, hsurj, fun K _ _ y y' P Q hP hQ => ?_⟩
  have hp := InvariantSchemePoints.point_orbit_iff (twistMarkSchemeAction hU hN) Y.hom
    (fun g => g.val.asIso.hom.w) π.left hπ hsections y'.left y.left y'.w y.w
  rw [← twistMarkGroup_orbit_iff hU hN y y' P Q hP hQ]
  constructor
  · intro e
    obtain ⟨g, hg⟩ := hp.mp (congrArg CommaMorphism.left e.symm)
    exact ⟨g, Over.OverMorphism.ext hg⟩
  · rintro ⟨g, hg⟩
    exact Over.OverMorphism.ext (hp.mpr ⟨g, congrArg CommaMorphism.left hg⟩).symm

open HDec.QMSplit.Moduli SGRSplit in
/-- The printed integral representability input suffices for the existence
of a rational finite scheme quotient with the prescribed geometric fibres. -/
theorem exists_twistMark_quotient_of_z30 (h : Y3FullThreeRepZ30) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (𝒜 : QMAbSchemeP Y.left)
      (Z : Over (Spec (CommRingCat.of ℚ))) (π : Y ⟶ Z),
      IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧ Represents Y 𝒜 ∧
      IsFinite π.left ∧ IsProper Z.hom ∧ Function.Surjective π.left.base ∧
      ∀ (K : Type) [Field K] [Algebra ℚ K] (y y' : fieldPt K ⟶ Y) (P Q : QML3 K),
        IsFibreOf 𝒜.toQMFamily y.left P → IsFibreOf 𝒜.toQMFamily y'.left Q →
          (y ≫ π = y' ≫ π ↔ ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) := by
  obtain ⟨Y, 𝒜, hp, hs, hU⟩ := y3RepresentableQ_of_z30 h
  obtain ⟨Z, π, hfin, hproper, hsurj, hfib⟩ := exists_twistMark_quotient_geometric_fibres hp hs hU
  exact ⟨Y, 𝒜, Z, π, hp, hs, hU, hfin, hproper, hsurj, hfib⟩

end Y3P1j

#print axioms Y3P1j.exists_twistMark_scheme_quotient
#print axioms Y3P1j.exists_twistMark_quotient_geometric_fibres
#print axioms Y3P1j.exists_twistMark_quotient_of_z30
