import ZInQKernel.Contrib.CloudR2Poincare.L2.FpqcNormalizedDetection
import ZInQKernel.Contrib.CloudR2Poincare.L2.GlobalStabilizerLocus
import ZInQKernel.Contrib.CloudR2Poincare.L1.Stabilizer
import ZInQKernel.Contrib.CloudR2Poincare.L1.DualInterface

/-!
# Field-extension detection of the ORIGINAL global triviality locus

The normalized Picard presheaf is a genuine fpqc sheaf. A field extension is
an actual fpqc cover; this detects the residue-fibre class at the IMAGE point
rather than substituting a separately constructed extension-field locus.
The result supplies all-Ω points of the original K and the graph consumer.
No global seesaw, canonical H0 map or pointwise-cover Fact is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- Actual normalized-class restriction stays normalized under parameter change. -/
theorem normalizedPicard_baseChange_normalized
    {k : Type u} [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ π = 𝟙 _)
    {T U : Over (Spec (.of k))} (g : U ⟶ T) (L : (pullback π T.hom).Pic)
    (hn : Scheme.Pic.map (sectionBaseChange π σ hσ T) L = 1) :
    Scheme.Pic.map (sectionBaseChange π σ hσ U)
      (Scheme.Pic.map (JacobianChallenge.baseChangeMap π g) L) = 1 := by
  rw [← Scheme.Pic.map_comp, sectionBaseChange_comp_baseChangeMap,
    Scheme.Pic.map_comp, hn, Scheme.Pic.map_one]

/-- ORIGINAL residue-fibre triviality is detected by ANY extension-field test
point, using a real field fpqc cover and normalized Picard-class descent. -/
theorem fibreTriviality_mem_fieldTest_iff
    {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of k)) [IsProper π] [Flat π] [GeometricallyIntegral π]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ π = 𝟙 _)
    (T : Over (Spec (.of k))) [IsLocallyNoetherian T.left]
    (L : (pullback π T.hom).Pic)
    (hn : Scheme.Pic.map (sectionBaseChange π σ hσ T) L = 1)
    (x : L1.fieldTest k Ω ⟶ T) :
    x.left (IsLocalRing.closedPoint Ω) ∈
      globalFibreTrivialityClosed (pullback.snd π T.hom) L ↔
    Scheme.Pic.map (JacobianChallenge.baseChangeMap π x) L = 1 := by
  let xp : Spec (.of Ω) ⟶ T.left := x.left
  let y : T.left := xp (IsLocalRing.closedPoint Ω)
  let φ : T.left.residueField y ⟶ CommRingCat.of Ω :=
    T.left.descResidueField (Scheme.stalkClosedPointTo xp)
  have hφ : Spec.map φ ≫ T.left.fromSpecResidueField y = x.left :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω T.left xp
  let d : L1.fieldTest k Ω ⟶ residueParameter T y := Over.homMk (Spec.map φ) (by
    change Spec.map φ ≫ (T.left.fromSpecResidueField y ≫ T.hom) =
      Spec.map (CommRingCat.ofHom (algebraMap k Ω))
    rw [← Category.assoc, hφ]
    exact Over.w x)
  have hd : d ≫ residueParameterMap T y = x := by
    apply Over.OverMorphism.ext
    exact hφ
  letI : Algebra (T.left.residueField y) Ω := φ.hom.toAlgebra
  letI : Flat d.left := by
    change Flat (Spec.map φ)
    rw [Flat.SpecMap_iff]
    change (algebraMap (T.left.residueField y) Ω).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  letI : Subsingleton (residueParameter T y).left :=
    inferInstanceAs (Subsingleton (Spec (T.left.residueField y)))
  letI : Surjective d.left := ⟨fun z => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  letI : QuasiCompact d.left := by change QuasiCompact (Spec.map φ); infer_instance
  let r := residueParameterMap T y
  let Lr := Scheme.Pic.map (JacobianChallenge.baseChangeMap π r) L
  have hnr : Scheme.Pic.map (sectionBaseChange π σ hσ (residueParameter T y)) Lr = 1 :=
    normalizedPicard_baseChange_normalized π σ hσ r L hn
  have hdet := normalizedPicard_eq_one_iff_fpqc_pullback π σ hσ d Lr hnr
  dsimp only [Lr, r] at hdet
  rw [← Scheme.Pic.map_comp, ← JacobianChallenge.baseChangeMap_comp, hd] at hdet
  change Scheme.Pic.map ((pullback.snd π T.hom).fiberι y) L = 1 ↔ _
  rw [relativeFibrePicardClass_eq_one_iff]
  exact hdet.symm

/-- All extension-field points of the ORIGINAL normalized K have exactly the
raw stabilizer condition. No identification with a separate Ω-locus is assumed. -/
theorem mem_globalNormalizedKernelClosed_fieldTest_iff
    {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
    (A : PkgI3.AbVar k) (L : A.X.left.Pic) (x : L1.fieldTest k Ω ⟶ A.X) :
    x.left (IsLocalRing.closedPoint Ω) ∈ globalNormalizedKernelClosed A L ↔
      x ∈ L1.stabilizerSubgroup A.X L (L1.fieldTest k Ω) := by
  letI : IsLocallyNoetherian A.X.left := LocallyOfFiniteType.isLocallyNoetherian A.X.hom
  letI : Subsingleton (L1.fieldTest k Ω).left.Pic := inferInstanceAs (Subsingleton (Spec (.of Ω)).Pic)
  have h := fibreTriviality_mem_fieldTest_iff A.X.hom η[A.X].left (L1.groupUnit_over A.X)
    A.X (L1.normalizedPolarizationFamily A.X L (𝟙 A.X))
    (L1.normalizedPolarizationFamily_normalized A.X L (𝟙 A.X)) x
  rw [L1.normalizedPolarizationFamily_parameter, Category.comp_id] at h
  rw [L1.normalizedPolarizationFamily_eq_of_subsingletonPic A.X L x,
    L1.polarizationFamily_eq_one_iff_mem_stabilizer] at h
  exact h

/-- Actual ALL-Ω scheme factorization through the ORIGINAL global K.
This is the missing upstream ABI for L1.FiniteStabilizerScheme.points. -/
theorem globalNormalizedKernel_fieldTest_factor_iff
    {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
    (A : PkgI3.AbVar k) (L : A.X.left.Pic) (x : L1.fieldTest k Ω ⟶ A.X) :
    (∃ z : L1.fieldTest k Ω ⟶ globalNormalizedKernel A L,
      z ≫ globalNormalizedKernelι A L = x) ↔
      x ∈ L1.stabilizerSubgroup A.X L (L1.fieldTest k Ω) := by
  letI : Subsingleton (L1.fieldTest k Ω).left := inferInstanceAs (Subsingleton (Spec (.of Ω)))
  letI : AlgebraicGeometry.IsReduced (L1.fieldTest k Ω).left :=
    inferInstanceAs (AlgebraicGeometry.IsReduced (Spec (.of Ω)))
  constructor
  · rintro ⟨z, hz⟩
    apply (mem_globalNormalizedKernelClosed_fieldTest_iff A L x).mp
    rw [← hz, Over.comp_left, Scheme.Hom.comp_apply]
    change (globalNormalizedKernelι A L).left (z.left (IsLocalRing.closedPoint Ω)) ∈
      (globalNormalizedKernelClosed A L : Set A.X.left)
    rw [← range_globalNormalizedKernelι]
    exact ⟨_, rfl⟩
  · intro hx
    have hm := (mem_globalNormalizedKernelClosed_fieldTest_iff A L x).mpr hx
    change x.left (IsLocalRing.closedPoint Ω) ∈ (globalNormalizedKernelClosed A L : Set A.X.left) at hm
    have hr : Set.range x.left ⊆ globalNormalizedKernelClosed A L := by
      rintro a ⟨t, rfl⟩
      simpa only [Subsingleton.elim t (IsLocalRing.closedPoint Ω)] using hm
    obtain ⟨b, hb⟩ := L1.exists_factor_reducedClosedSupport (globalNormalizedKernelClosed A L) x.left hr
    let z : L1.fieldTest k Ω ⟶ globalNormalizedKernel A L := Over.homMk b (by
      change b ≫ (L1.reducedClosedSupportι A.X.left (globalNormalizedKernelClosed A L) ≫ A.X.hom) =
        Spec.map (CommRingCat.ofHom (algebraMap k Ω))
      rw [← Category.assoc, hb]
      exact Over.w x)
    refine ⟨z, ?_⟩
    apply Over.OverMorphism.ext
    exact hb

/-- Exact original-K ALL-field range equality, in the literal shape of the
finite-stabilizer scheme record (stronger: Ω need not be algebraically closed). -/
theorem range_globalNormalizedKernel_fieldTest
    {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
    (A : PkgI3.AbVar k) (L : A.X.left.Pic) :
    Set.range (fun z : L1.fieldTest k Ω ⟶ globalNormalizedKernel A L =>
      z ≫ globalNormalizedKernelι A L) =
    (L1.stabilizerSubgroup A.X L (L1.fieldTest k Ω) : Set (L1.fieldTest k Ω ⟶ A.X)) := by
  ext x
  exact globalNormalizedKernel_fieldTest_factor_iff A L x

end ZInQ.Contrib.CloudR2Poincare.L2
