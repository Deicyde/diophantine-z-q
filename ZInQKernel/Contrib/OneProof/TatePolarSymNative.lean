import ZInQKernel.Contrib.OneProof.WeilFormulaTheta
import ZInQKernel.Contrib.OneProof.PhiAmpleIsogenyOpen
import ZInQKernel.Contrib.CloudR2Poincare.L6.NativeSquareProof
import ZInQKernel.Contrib.CloudR2Poincare.L5.C1MultiplicativeSeesaw
import ZInQKernel.Contrib.CloudR2Poincare.L2.QuotientDescentCompatibility
import ZInQKernel.Contrib.CloudR2Poincare.L2.QuotientPointClasses
import ZInQKernel.Contrib.CloudR2Poincare.L4.QuotientExists
import ZInQKernel.Contrib.CloudR2Poincare.ProjectiveEmbedding

/-!
The actual native polarization quotient, read on geometric points in the
coordinates of the existing Weil formula.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 PkgI3.AbVar HDec.WeilPairing PicDict
open ZInQ.Contrib.CloudR2Poincare

namespace HodgeFil1.TatePolar

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
set_option linter.style.haveILetI false

variable {K : Type} [Field K] [CharZero K] {A : AbVar K}

omit [CharZero K] in
private theorem translate_eq_tr (x : AC.Kpt A) : L1.translate A.X x = AC.tr x := by
  rw [L1.translate, mul_comm, CategoryTheory.Hom.mul_def]
  rfl

/-- The class of a translate divided by the original class is translation invariant. -/
theorem phiPt_isTranslInv (c : (AK A).Pic) (x : A.Pt (AlgebraicClosure K)) :
    IsTranslInv (phiPt c x) := by
  apply (isTI_iff _).1
  rw [← phi_pts]
  intro y
  have h := L2.translationClass_invariant_of_nativeSquare
    L6.NativeTheoremOfTheSquare_proof (AKbar A) c (pts x) y
  simpa only [L1.translationClass, translate_eq_tr (A := AKbar A), AC.phi] using h

/-- The polarization class is multiplicative on geometric points. -/
theorem phiPt_mul (c : (AK A).Pic) (x y : A.Pt (AlgebraicClosure K)) :
    phiPt c (x * y) = phiPt c x * phiPt c y := by
  have h := phiPt_isTranslInv c y x
  calc
    phiPt c (x * y) = Scheme.Pic.map (trl x) (phiPt c y) * phiPt c x := by
      simp only [phiPt, Scheme.Pic.map_mul, L1.pic_map_inv, ← Scheme.Pic.map_comp,
        ← Over.comp_left, transl_comp_transl]
      group
    _ = phiPt c x * phiPt c y := by rw [h, mul_comm]

omit [CharZero K] in
/-- Pullback by multiplication on a translation invariant class is its tensor power. -/
theorem mulN_pic_of_invariant (c : (AK A).Pic) (hc : IsTranslInv c) (n : ℕ) :
    Scheme.Pic.map (mlN A n) c = c ^ n := by
  change Scheme.Pic.map (T09Pic.mulN A n).left c = c ^ n
  rw [← mul_AKbar]
  have inv : L3.TranslationInvariant (AKbar A) c := by
    intro x
    rw [translate_eq_tr (A := AKbar A)]
    exact (isTI_iff c).2 hc x
  let X := AKbar A
  have hmul := L5.mul_pullback_class_of_translationInvariant
    L1.ReducedGlobalNormalizedSeesaw_proof X c inv
  change Scheme.Pic.map (AC.mul X n).left c = c ^ n
  induction n with
  | zero =>
    have hz : AC.mul X 0 = toUnit X.X ≫ η[X.X] := by
      simp only [AC.mul, pow_zero]
      rfl
    rw [hz, Over.comp_left, Scheme.Pic.map_comp, pow_zero]
    have e : Scheme.Pic.map η[X.X].left c = 1 :=
      Subsingleton.elim (α := (Spec (CommRingCat.of (AlgebraicClosure K))).Pic) _ _
    rw [e, Scheme.Pic.map_one]
  | succ n ih =>
    have hs : AC.mul X (n + 1) = lift (AC.mul X n) (𝟙 X.X) ≫ μ[X.X] := by
      rw [AC.mul, pow_succ, CategoryTheory.Hom.mul_def]
      rfl
    rw [hs, Over.comp_left, Scheme.Pic.map_comp, hmul, Scheme.Pic.map_mul,
      ← Scheme.Pic.map_comp, ← Scheme.Pic.map_comp, ← Over.comp_left, ← Over.comp_left,
      lift_fst, lift_snd, Over.id_left, Scheme.Pic.map_id, ih, pow_succ]

omit [CharZero K] in
private theorem polarizationFamily_eq_phiPt (L : A.X.left.Pic) (x : A.Pt (AlgebraicClosure K)) :
    L1.polarizationFamily A.X L x = phiPt (bcPic A L) x := by
  rw [← map_mumfordBundle_pt]
  have hμ : JacobianChallenge.baseChangeMap A.X.hom x ≫ (μ[A.X]).left =
      (L1.translationAction A.X x).left := by
    rw [L1.baseChangeMap_eq_tensor, ← Over.comp_left, L1.translationAction, mul_comm,
      CategoryTheory.Hom.mul_def]
    congr 1
  have hfst : JacobianChallenge.baseChangeMap A.X.hom x ≫ pullback.fst A.X.hom A.X.hom =
      pullback.fst A.X.hom (T09Pic.ptK K).hom := pullback.lift_fst _ _ _
  have hsnd : JacobianChallenge.baseChangeMap A.X.hom x ≫ pullback.snd A.X.hom A.X.hom =
      pullback.snd _ _ ≫ x.left := pullback.lift_snd _ _ _
  have hone : Scheme.Pic.map x.left L = 1 :=
    Subsingleton.elim (α := (Spec (CommRingCat.of (AlgebraicClosure K))).Pic) _ _
  simp only [T09Pic.mumfordBundle, Scheme.Pic.map_mul, L1.pic_map_inv, ← Scheme.Pic.map_comp,
    hμ, hfst, hsnd, Scheme.Pic.map_comp (pullback.snd _ _) x.left, hone, Scheme.Pic.map_one,
    inv_one, L1.polarizationFamily]
  rw [_root_.mul_one]
  rfl

/-- Data obtained by specializing the descended bundle on the actual native stabilizer
quotient. The class map is only on geometric points. -/
structure NativePolarization (A : AbVar K) where
  L : A.X.left.Pic
  Q : AbVar K
  q : Hom A Q
  isogeny : IsIsogenyMor q.hom
  dim_eq : Q.dim = A.dim
  cl : Q.Pt (AlgebraicClosure K) →* (AK A).Pic
  injective : Function.Injective cl
  translInv : ∀ y, IsTranslInv (cl y)
  galois : ∀ σ y, cl (Q.galAct σ y) = Scheme.Pic.map (gal A σ) (cl y)
  over_q : ∀ x : A.Pt (AlgebraicClosure K), cl (x ≫ q.hom) = phiPt (bcPic A L) x

/-- The native finite quotient and its descended normalized polarization bundle supply
the point classes used by the Weil formula. -/
theorem exists_nativePolarization (A : AbVar K) : Nonempty (NativePolarization A) := by
  classical
  obtain ⟨I, hI, f, hf, hover⟩ := nativeProjectiveEmbeddingExists_proof K A
  let M := ProjectiveSpace.twistRestrict f 1
  have hM : L2.VeryAmple A.X.hom M := ⟨I, hI, f, hf, hover, ⟨Iso.refl _⟩⟩
  letI : M.IsInvertible := hM.isInvertible
  let L := Scheme.Pic.mk M
  have hsee : L2.ReducedGlobalNormalizedSeesaw := L1.ReducedGlobalNormalizedSeesaw_proof
  obtain ⟨H, Q, q, hflat, hfin, hsurj, hfp, hkp, hdim⟩ :=
    L4.StabilizerAbVarQuotientExists_proof hsee A M hM
  letI := hflat
  letI := hfin
  letI := hsurj
  letI := hfp
  let D : L1.StabilizerQuotient A L H :=
    { Q := Q.X, q := q.hom, kernelPair := hkp }
  obtain ⟨M', hM', _, hP⟩ := L1.exists_quotientPolarizationBundle A L H D
    (L2.nativeQuotientDescentCompatibility_of_seesaw hsee K A L H D)
  let P := @Scheme.Pic.mk _ M' hM'
  let cl (y : Q.Pt (AlgebraicClosure K)) :=
    Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom y) P
  letI : Subsingleton (T09Pic.ptK K).left.Pic :=
    inferInstanceAs (Subsingleton (Spec (.of (AlgebraicClosure K))).Pic)
  have hcl (x : A.Pt (AlgebraicClosure K)) : cl (x ≫ q.hom) = phiPt (bcPic A L) x := by
    change Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom (x ≫ q.hom)) P = _
    rw [L2.quotientBundle_parameter_class A Q L q P hP x,
      L1.normalizedPolarizationFamily_eq_of_subsingletonPic]
    exact polarizationFamily_eq_phiPt L x
  have hlift (y : Q.Pt (AlgebraicClosure K)) : ∃ x : A.Pt (AlgebraicClosure K), x ≫ q.hom = y :=
    L2.exists_fieldPoint_lift_of_finite_surjective q.hom y
  let fpts := IsMonHom.monoidHom q.hom (T09Pic.ptK K)
  have hmul (x y : Q.Pt (AlgebraicClosure K)) : cl (x * y) = cl x * cl y := by
    obtain ⟨x, rfl⟩ := hlift x
    obtain ⟨y, rfl⟩ := hlift y
    change cl (fpts x * fpts y) = cl (fpts x) * cl (fpts y)
    rw [← map_mul]
    change cl ((x * y) ≫ q.hom) = cl (x ≫ q.hom) * cl (y ≫ q.hom)
    rw [hcl, hcl, hcl, phiPt_mul]
  refine ⟨⟨L, Q, q, ⟨hfin, hsurj⟩, hdim, MonoidHom.mk' cl hmul, ?_, ?_, ?_, hcl⟩⟩
  · exact L2.quotientBundle_fieldPoint_injective (Ω := AlgebraicClosure K) A Q L H q hkp P hP
  · intro y
    obtain ⟨x, rfl⟩ := hlift y
    change IsTranslInv (cl (x ≫ q.hom))
    rw [hcl]
    exact phiPt_isTranslInv _ _
  · intro σ y
    change Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom (galHom σ ≫ y)) P =
      Scheme.Pic.map (gal A σ) (Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom y) P)
    rw [JacobianChallenge.baseChangeMap_comp, Scheme.Pic.map_comp]

#print axioms translate_eq_tr
#print axioms polarizationFamily_eq_phiPt
#print axioms phiPt_isTranslInv
#print axioms phiPt_mul
#print axioms mulN_pic_of_invariant
#print axioms exists_nativePolarization

end HodgeFil1.TatePolar
