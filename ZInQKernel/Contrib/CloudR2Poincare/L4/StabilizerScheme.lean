import ZInQKernel.Contrib.CloudR2Poincare.L4.FiniteReduced
import ZInQKernel.Contrib.CloudR2Poincare.L2.FieldTrivialityDetection
import ZInQKernel.Contrib.CloudR2Poincare.L2.SeesawFiniteness

/-!
# The ORIGINAL global reduced stabilizer as a finite subgroup scheme

The group-object restriction pattern is credited to the unconditional
`grpObjOfMono` / `isMonHom_grpObjOfMono` construction in
`scratch/av-glue/Kernel.lean` at df98652abbeeef78b57f0868f19523a26d811b58.
Finiteness is an explicit (A) input; L2's actual all-field classification detects
the original closed support. No separate extension-field kernel is substituted.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

section MonoTransport
variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {G K : C} [GrpObj G]

/-- Restrict the actual group law through a monomorphism once all operations factor. -/
@[reducible] def grpObjOfMono (j : K ⟶ G) [Mono j]
    (m : K ⊗ K ⟶ K) (hm : m ≫ j = fst K K ≫ j * snd K K ≫ j)
    (e : 𝟙_ C ⟶ K) (he : e ≫ j = η[G])
    (v : K ⟶ K) (hv : v ≫ j = j⁻¹) : GrpObj K where
  one := e
  mul := m
  one_mul := by
    apply (cancel_mono j).1
    simp only [Category.assoc, hm, MonObj.comp_mul, whiskerRight_fst_assoc,
      whiskerRight_snd_assoc, he, leftUnitor_hom]
    rw [show fst (𝟙_ C) K ≫ η[G] = 1 by
      rw [Hom.one_def]; congr 1; exact toUnit_unique _ _, _root_.one_mul]
  mul_one := by
    apply (cancel_mono j).1
    simp only [Category.assoc, hm, MonObj.comp_mul, whiskerLeft_fst_assoc,
      whiskerLeft_snd_assoc, he, rightUnitor_hom]
    rw [show snd K (𝟙_ C) ≫ η[G] = 1 by
      rw [Hom.one_def]; congr 1; exact toUnit_unique _ _, _root_.mul_one]
  mul_assoc := by
    apply (cancel_mono j).1
    simp only [Category.assoc, hm, MonObj.comp_mul, whiskerRight_fst_assoc,
      whiskerRight_snd_assoc, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc,
      associator_hom_fst_assoc, associator_hom_snd_fst_assoc, associator_hom_snd_snd_assoc]
    rw [_root_.mul_assoc]
  inv := v
  left_inv := by
    apply (cancel_mono j).1
    simp only [Category.assoc, hm, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
      hv, he, Category.id_comp]
    rw [inv_mul_cancel, Hom.one_def]
  right_inv := by
    apply (cancel_mono j).1
    simp only [Category.assoc, hm, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
      hv, he, Category.id_comp]
    rw [mul_inv_cancel, Hom.one_def]

theorem isMonHom_grpObjOfMono (j : K ⟶ G) [Mono j]
    (m : K ⊗ K ⟶ K) (hm : m ≫ j = fst K K ≫ j * snd K K ≫ j)
    (e : 𝟙_ C ⟶ K) (he : e ≫ j = η[G])
    (v : K ⟶ K) (hv : v ≫ j = j⁻¹) :
    letI := grpObjOfMono j m hm e he v hv
    IsMonHom j := by
  letI := grpObjOfMono j m hm e he v hv
  refine ⟨he, ?_⟩
  change m ≫ j = _
  rw [hm, Hom.mul_def, ← lift_fst_comp_snd_comp]

end MonoTransport

variable {k : Type} [Field k] (A : PkgI3.AbVar k) (L : A.X.left.Pic)

/-- A reduced test whose every extension-field point is a stabilizer point
factors through the ORIGINAL reduced closed support. -/
theorem factor_originalKernel_of_fieldPoints {T : Over (Spec (.of k))}
    [AlgebraicGeometry.IsReduced T.left] (f : T ⟶ A.X)
    (h : ∀ (Ω : Type) [Field Ω] [Algebra k Ω] (p : L1.fieldTest k Ω ⟶ T),
      p ≫ f ∈ L1.stabilizerSubgroup A.X L (L1.fieldTest k Ω)) :
    ∃ z : T ⟶ L2.globalNormalizedKernel A L, z ≫ L2.globalNormalizedKernelι A L = f := by
  have hr : Set.range f.left ⊆ L2.globalNormalizedKernelClosed A L := by
    rintro _ ⟨x, rfl⟩
    let Ω := T.left.residueField x
    let ρ := T.left.fromSpecResidueField x ≫ T.hom
    let a := Spec.preimage ρ
    letI : Algebra k Ω := a.hom.toAlgebra
    have ha : (L1.fieldTest k Ω).hom = ρ := by
      change Spec.map (CommRingCat.ofHom (algebraMap k Ω)) = ρ
      rw [RingHom.algebraMap_toAlgebra]
      change Spec.map a = ρ
      exact Spec.map_preimage ρ
    let p : L1.fieldTest k Ω ⟶ T := Over.homMk (T.left.fromSpecResidueField x) ha.symm
    have hx := (L2.mem_globalNormalizedKernelClosed_fieldTest_iff A L (p ≫ f)).mpr (h Ω p)
    change f.left (T.left.fromSpecResidueField x (IsLocalRing.closedPoint Ω)) ∈
      L2.globalNormalizedKernelClosed A L at hx
    have hpt : T.left.fromSpecResidueField x (IsLocalRing.closedPoint Ω) = x :=
      Scheme.fromSpecResidueField_apply x (IsLocalRing.closedPoint Ω)
    rw [hpt] at hx
    exact hx
  obtain ⟨z, hz⟩ := L1.exists_factor_reducedClosedSupport
    (L2.globalNormalizedKernelClosed A L) f.left hr
  refine ⟨Over.homMk z ?_, ?_⟩
  · change z ≫ (L1.reducedClosedSupportι A.X.left (L2.globalNormalizedKernelClosed A L) ≫ A.X.hom) = T.hom
    rw [← Category.assoc, hz]
    exact Over.w f
  · exact Over.OverMorphism.ext hz

/-- ORIGINAL K-points belong to the actual stabilizer subgroup for all field tests. -/
theorem originalKernel_point_mem {Ω : Type} [Field Ω] [Algebra k Ω]
    (p : L1.fieldTest k Ω ⟶ L2.globalNormalizedKernel A L) :
    p ≫ L2.globalNormalizedKernelι A L ∈ L1.stabilizerSubgroup A.X L (L1.fieldTest k Ω) :=
  (L2.globalNormalizedKernel_fieldTest_factor_iff A L _).mp ⟨p, rfl⟩

/-- The original reduced K's identity operation factors. -/
theorem exists_originalKernelUnit : ∃ e : 𝟙_ (Over (Spec (.of k))) ⟶ L2.globalNormalizedKernel A L,
    e ≫ L2.globalNormalizedKernelι A L = η[A.X] := by
  haveI : AlgebraicGeometry.IsReduced (𝟙_ (Over (Spec (.of k)))).left :=
    inferInstanceAs (AlgebraicGeometry.IsReduced (Spec (.of k)))
  refine factor_originalKernel_of_fieldPoints A L η[A.X] ?_
  intro Ω _ _ p
  have hp : p = toUnit (L1.fieldTest k Ω) := toUnit_unique _ _
  rw [hp]
  exact (L1.stabilizerSubgroup A.X L (L1.fieldTest k Ω)).one_mem

/-- The original reduced K's inverse operation factors. -/
theorem exists_originalKernelInv : ∃ v : L2.globalNormalizedKernel A L ⟶ L2.globalNormalizedKernel A L,
    v ≫ L2.globalNormalizedKernelι A L = (L2.globalNormalizedKernelι A L)⁻¹ := by
  refine factor_originalKernel_of_fieldPoints A L (L2.globalNormalizedKernelι A L)⁻¹ ?_
  intro Ω _ _ p
  rw [GrpObj.comp_inv]
  exact (L1.stabilizerSubgroup A.X L (L1.fieldTest k Ω)).inv_mem
    (originalKernel_point_mem A L p)

/-- The original reduced K's multiplication factors as soon as its actual self-product is reduced. -/
theorem exists_originalKernelMul
    [AlgebraicGeometry.IsReduced (L2.globalNormalizedKernel A L ⊗ L2.globalNormalizedKernel A L).left] :
    ∃ m : L2.globalNormalizedKernel A L ⊗ L2.globalNormalizedKernel A L ⟶ L2.globalNormalizedKernel A L,
      m ≫ L2.globalNormalizedKernelι A L =
        fst _ _ ≫ L2.globalNormalizedKernelι A L * snd _ _ ≫ L2.globalNormalizedKernelι A L := by
  refine factor_originalKernel_of_fieldPoints A L _ ?_
  intro Ω _ _ p
  rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc]
  exact (L1.stabilizerSubgroup A.X L (L1.fieldTest k Ω)).mul_mem
    (originalKernel_point_mem A L (p ≫ fst _ _))
    (originalKernel_point_mem A L (p ≫ snd _ _))

/-- Finite étale schemes over a field are reduced, independently of any group structure. -/
theorem finite_etale_scheme_reduced {k : Type} [Field k] {X : Scheme}
    (f : X ⟶ Spec (.of k)) [IsFinite f] [Etale f] : AlgebraicGeometry.IsReduced X := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  let e := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  letI : Field Γ(Spec (.of k), ⊤) := (e.isField (Field.toIsField k)).toField
  letI : Algebra Γ(Spec (.of k), ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have he : f.appTop.hom.Etale :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := f)).mp inferInstance
  haveI : Algebra.Etale Γ(Spec (.of k), ⊤) Γ(X, ⊤) := he
  haveI : _root_.IsReduced Γ(X, ⊤) :=
    Algebra.FormallyUnramified.isReduced_of_field Γ(Spec (.of k), ⊤) Γ(X, ⊤)
  exact isReduced_of_isAffine_isReduced X

/-- Finiteness plus reducedness in char0 makes K×K reduced BEFORE its group law is built. -/
theorem originalKernel_selfProduct_reduced [CharZero k]
    (hfin : IsFinite (L2.globalNormalizedKernel A L).hom) :
    AlgebraicGeometry.IsReduced (L2.globalNormalizedKernel A L ⊗ L2.globalNormalizedKernel A L).left := by
  let K := L2.globalNormalizedKernel A L
  haveI := hfin
  haveI : Etale K.hom := finite_reduced_scheme_etale K.hom
  haveI : IsFinite (K ⊗ K).hom := by rw [Over.tensorObj_hom]; infer_instance
  haveI : Etale (K ⊗ K).hom := by rw [Over.tensorObj_hom]; infer_instance
  exact finite_etale_scheme_reduced (K ⊗ K).hom

/-- The ORIGINAL reduced closed K receives its actual subgroup structure. -/
@[reducible] def originalKernelGrp [CharZero k]
    (hfin : IsFinite (L2.globalNormalizedKernel A L).hom) :
    GrpObj (L2.globalNormalizedKernel A L) :=
  haveI : Mono (L2.globalNormalizedKernelι A L) := Over.mono_of_mono_left _
  haveI := originalKernel_selfProduct_reduced A L hfin
  grpObjOfMono (L2.globalNormalizedKernelι A L)
    (exists_originalKernelMul A L).choose (exists_originalKernelMul A L).choose_spec
    (exists_originalKernelUnit A L).choose (exists_originalKernelUnit A L).choose_spec
    (exists_originalKernelInv A L).choose (exists_originalKernelInv A L).choose_spec

theorem originalKernel_isMonHom [CharZero k]
    (hfin : IsFinite (L2.globalNormalizedKernel A L).hom) :
    letI := originalKernelGrp A L hfin
    IsMonHom (L2.globalNormalizedKernelι A L) := by
  haveI : Mono (L2.globalNormalizedKernelι A L) := Over.mono_of_mono_left _
  haveI := originalKernel_selfProduct_reduced A L hfin
  exact isMonHom_grpObjOfMono (L2.globalNormalizedKernelι A L)
    (exists_originalKernelMul A L).choose (exists_originalKernelMul A L).choose_spec
    (exists_originalKernelUnit A L).choose (exists_originalKernelUnit A L).choose_spec
    (exists_originalKernelInv A L).choose (exists_originalKernelInv A L).choose_spec

/-- Package the literal global normalized kernel/inclusion as L1's finite subgroup scheme. -/
def originalFiniteStabilizer [CharZero k]
    (hfin : IsFinite (L2.globalNormalizedKernel A L).hom) : L1.FiniteStabilizerScheme A L where
  K := L2.globalNormalizedKernel A L
  grp := originalKernelGrp A L hfin
  j := L2.globalNormalizedKernelι A L
  monHom := originalKernel_isMonHom A L hfin
  closed := inferInstance
  finite := hfin
  points Ω _ _ _ := L2.range_globalNormalizedKernel_fieldTest A L

@[simp] theorem originalFiniteStabilizer_K [CharZero k]
    (hfin : IsFinite (L2.globalNormalizedKernel A L).hom) :
    (originalFiniteStabilizer A L hfin).K = L2.globalNormalizedKernel A L := rfl

@[simp] theorem originalFiniteStabilizer_j [CharZero k]
    (hfin : IsFinite (L2.globalNormalizedKernel A L).hom) :
    (originalFiniteStabilizer A L hfin).j = L2.globalNormalizedKernelι A L := rfl

end ZInQ.Contrib.CloudR2Poincare.L4
