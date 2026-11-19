import ZInQKernel.Contrib.RC53Assist.CentralKummer.RationalKummer
import ZInQKernel.Contrib.RC53Assist.CentralUniversal.IntegralAlgebra
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The coefficient sequence of the compact Kummer complex

The quotient complex is formed from the canonical scalar-extension map, not
from a choice of cohomology dimensions. Its connecting homomorphism is the
one in the long exact cohomology sequence. The identification of its first
cohomology with the arithmetic Selmer group is a separate comparison.
-/

noncomputable section

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Manuscript.RC53Assist.CentralUniversal

open CategoryTheory CategoryTheory.Limits
open ZInQ.Manuscript.RC53Assist.CentralKummer
open ZInQ.Manuscript.RC53Assist.CentralSelmer
open ZInQ.Manuscript.SelmerTwoPower
open scoped TensorProduct

/-- Rational scalar extension followed by restriction to integral scalars. -/
abbrev rationalFunctor : ModuleCat.{0} ℤ_[2] ⥤ ModuleCat.{0} ℤ_[2] :=
  ModuleCat.extendScalars PadicInt.Coe.ringHom ⋙
    ModuleCat.restrictScalars PadicInt.Coe.ringHom

instance rationalFunctor_preservesFiniteLimits : PreservesFiniteLimits rationalFunctor := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat flat_padicIntCoe
  dsimp [rationalFunctor]
  infer_instance

instance rationalFunctor_preservesFiniteColimits : PreservesFiniteColimits rationalFunctor := by
  have : PreservesFiniteColimits
      (ModuleCat.extendScalars.{0, 0, 0} (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2])) := by
    have := (ModuleCat.extendRestrictScalarsAdj.{0, 0, 0}
      (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2])).leftAdjoint_preservesColimits
    infer_instance
  dsimp [rationalFunctor]
  infer_instance

/-- The canonical unit of scalar extension. -/
def coefficientUnit : 𝟭 (ModuleCat.{0} ℤ_[2]) ⟶ rationalFunctor :=
  (ModuleCat.extendRestrictScalarsAdj PadicInt.Coe.ringHom).unit

variable (C : CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ)

/-- Rational coefficients, regarded as integral modules. -/
def rationalCoefficientComplex : CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ :=
  (rationalFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj C

/-- The coefficient map in every degree is the canonical unit. -/
def coefficientMap : C ⟶ rationalCoefficientComplex C where
  f n := coefficientUnit.app (C.X n)
  comm' i j _ := (coefficientUnit.naturality (C.d i j)).symm

/-- The coefficient quotient is the cokernel complex of the genuine coefficient map. -/
def coefficientQuotientComplex : CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ :=
  cokernel (coefficientMap C)

/-- The coefficient sequence of complexes. -/
def coefficientSequence : ShortComplex (CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ) :=
  ShortComplex.mk (coefficientMap C) (cokernel.π (coefficientMap C))
    (cokernel.condition (coefficientMap C))

/-- Flat scalar extension commutes with cohomology. -/
def coefficientHomologyIso (n : ℤ) :
    (rationalCoefficientComplex C).homology n ≅ rationalFunctor.obj (C.homology n) :=
  ShortComplex.mapHomologyIso (C.sc n) rationalFunctor

/-- The identity-functor cohomology isomorphism. -/
def identityHomologyIso (n : ℤ) : C.homology n ≅ C.homology n :=
  ShortComplex.mapHomologyIso (C.sc n) (𝟭 (ModuleCat.{0} ℤ_[2]))

/-- Naturality identifies the cohomological coefficient map with scalar extension. -/
theorem coefficientHomologyMap_unit (n : ℤ) :
    HomologicalComplex.homologyMap (coefficientMap C) n ≫ (coefficientHomologyIso C n).hom =
      (identityHomologyIso C n).hom ≫ coefficientUnit.app (C.homology n) := by
  change ShortComplex.homologyMap ((C.sc n).mapNatTrans coefficientUnit) ≫
    ((C.sc n).mapHomologyIso rationalFunctor).hom = _
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp [identityHomologyIso]
  rfl

/-- The cohomology of rational coefficients, in the tensor-product realization. -/
def coefficientTensorHomologyEquiv (n : ℤ) :
    (rationalCoefficientComplex C).homology n ≃ₗ[ℤ_[2]]
      ℚ_[2] ⊗[ℤ_[2]] C.homology n :=
  (coefficientHomologyIso C n).toLinearEquiv

/-- The cohomology unit is the tensor unit, through the canonical identity comparison. -/
theorem coefficientTensorHomologyEquiv_map (n : ℤ) (x : C.homology n) :
    coefficientTensorHomologyEquiv C n
        ((HomologicalComplex.homologyMap (coefficientMap C) n).hom x) =
      rationalUnit (C.homology n) ((identityHomologyIso C n).hom.hom x) := by
  exact congrArg (fun f => f.hom x) (coefficientHomologyMap_unit C n)

/-- The integral image in rational cohomology is exactly the tensor-unit lattice. -/
theorem coefficientHomologyMap_range (n : ℤ) :
    LinearMap.range ((coefficientTensorHomologyEquiv C n).toLinearMap.comp
      (HomologicalComplex.homologyMap (coefficientMap C) n).hom) =
        LinearMap.range (rationalUnit (C.homology n)) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(identityHomologyIso C n).hom.hom x,
      (coefficientTensorHomologyEquiv_map C n x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨(identityHomologyIso C n).inv.hom x, ?_⟩
    change coefficientTensorHomologyEquiv C n
      ((HomologicalComplex.homologyMap (coefficientMap C) n).hom
        ((identityHomologyIso C n).inv.hom x)) = _
    rw [coefficientTensorHomologyEquiv_map]
    simp

/-- The kernel of rationalization on cohomology is precisely integral torsion. -/
theorem coefficientHomologyMap_ker (n : ℤ) :
    LinearMap.ker (HomologicalComplex.homologyMap (coefficientMap C) n).hom =
      Submodule.torsion ℤ_[2] (C.homology n) := by
  ext x
  constructor
  · intro hx
    have ht : (identityHomologyIso C n).hom.hom x ∈
        Submodule.torsion ℤ_[2] (C.homology n) := by
      rw [← rationalUnit_ker, LinearMap.mem_ker,
        ← coefficientTensorHomologyEquiv_map, hx, map_zero]
    obtain ⟨a, ha⟩ := ht
    change a.1 • ((identityHomologyIso C n).hom.hom x) = 0 at ha
    refine ⟨a, ?_⟩
    change a.1 • x = 0
    apply (ModuleCat.mono_iff_injective (identityHomologyIso C n).hom).mp inferInstance
    simpa only [map_smul, map_zero] using ha
  · rintro ⟨a, ha⟩
    change a.1 • x = 0 at ha
    have ht : (identityHomologyIso C n).hom.hom x ∈
        Submodule.torsion ℤ_[2] (C.homology n) := by
      refine ⟨a, ?_⟩
      change a.1 • ((identityHomologyIso C n).hom.hom x) = 0
      rw [← map_smul, ha, map_zero]
    apply (coefficientTensorHomologyEquiv C n).injective
    rw [coefficientTensorHomologyEquiv_map, map_zero]
    exact (show (identityHomologyIso C n).hom.hom x ∈
      LinearMap.ker (rationalUnit (C.homology n)) from
        (rationalUnit_ker (C.homology n)).symm ▸ ht)

variable [∀ n : ℤ, Module.IsTorsionFree ℤ_[2] (C.X n)]

/-- Torsion-free cochain terms make the coefficient map degreewise injective. -/
instance coefficientMap_mono : Mono (coefficientMap C) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  rw [ModuleCat.mono_iff_injective]
  change Function.Injective (rationalUnit (C.X n))
  rw [← LinearMap.ker_eq_bot, rationalUnit_ker]
  exact (Submodule.isTorsionFree_iff_torsion_eq_bot).mp inferInstance

/-- The canonical coefficient sequence is short exact. -/
theorem coefficientSequence_shortExact : (coefficientSequence C).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact (coefficientSequence C).exact_of_g_is_cokernel (cokernelIsCokernel (coefficientMap C))
  · change Mono (coefficientMap C)
    infer_instance
  · change Epi (cokernel.π (coefficientMap C))
    infer_instance

/-- The projection on first cohomology in the coefficient sequence. -/
def coefficientProjection : (rationalCoefficientComplex C).homology 1 →ₗ[ℤ_[2]]
    (coefficientQuotientComplex C).homology 1 :=
  (HomologicalComplex.homologyMap (coefficientSequence C).g 1).hom

/-- The rational-cohomology map written in the canonical tensor realization. -/
def rationalToDivisible : ℚ_[2] ⊗[ℤ_[2]] C.homology 1 →ₗ[ℤ_[2]]
    (coefficientQuotientComplex C).homology 1 :=
  (coefficientProjection C).comp (coefficientTensorHomologyEquiv C 1).symm.toLinearMap

/-- Exactness identifies the kernel with the integral image, not an arbitrary lattice. -/
theorem rationalToDivisible_ker : LinearMap.ker (rationalToDivisible C) =
    LinearMap.range (rationalUnit (C.homology 1)) := by
  have hex := (coefficientSequence_shortExact C).homology_exact₂ 1
  have hr := hex.moduleCat_range_eq_ker
  change LinearMap.range (HomologicalComplex.homologyMap (coefficientMap C) 1).hom =
    LinearMap.ker (coefficientProjection C) at hr
  ext z
  constructor
  · intro hz
    have hp : (coefficientTensorHomologyEquiv C 1).symm z ∈
        LinearMap.ker (coefficientProjection C) := hz
    rw [← hr] at hp
    obtain ⟨x, hx⟩ := hp
    rw [← coefficientHomologyMap_range C 1]
    refine ⟨x, ?_⟩
    change coefficientTensorHomologyEquiv C 1
      ((HomologicalComplex.homologyMap (coefficientMap C) 1).hom x) = z
    rw [hx, LinearEquiv.apply_symm_apply]
  · intro hz
    rw [← coefficientHomologyMap_range C 1] at hz
    obtain ⟨x, hx⟩ := hz
    have hp : (HomologicalComplex.homologyMap (coefficientMap C) 1).hom x ∈
        LinearMap.ker (coefficientProjection C) := by
      rw [← hr]
      exact ⟨x, rfl⟩
    change coefficientTensorHomologyEquiv C 1
      ((HomologicalComplex.homologyMap (coefficientMap C) 1).hom x) = z at hx
    change coefficientProjection C ((coefficientTensorHomologyEquiv C 1).symm z) = 0
    rw [← hx, LinearEquiv.symm_apply_apply]
    exact hp

/-- The integral image maps to zero under the rational-cohomology projection. -/
theorem rationalToDivisible_unit (x : C.homology 1) :
    rationalToDivisible C (rationalUnit (C.homology 1) x) = 0 := by
  rw [← LinearMap.mem_ker, rationalToDivisible_ker]
  exact ⟨x, rfl⟩

/-- The universal-coefficient map to the cohomology of the genuine coefficient quotient. -/
def universalCoefficientMap : Q2Z2 ⊗[ℤ_[2]] C.homology 1 →ₗ[ℤ_[2]]
    (coefficientQuotientComplex C).homology 1 :=
  universalTensorMap (C.homology 1) (rationalToDivisible C) (rationalToDivisible_unit C)

/-- The universal-coefficient map is injective. -/
theorem universalCoefficientMap_injective : Function.Injective (universalCoefficientMap C) :=
  universalTensorMap_injective _ _ _ (rationalToDivisible_ker C)

/-- The connecting map is the one furnished by the coefficient long exact sequence. -/
def coefficientConnecting : (coefficientQuotientComplex C).homology 1 →ₗ[ℤ_[2]] C.homology 2 :=
  ((coefficientSequence_shortExact C).δ 1 2 rfl).hom

/-- The connecting map lands in the torsion of second integral cohomology. -/
theorem coefficientConnecting_mem_torsion (y : (coefficientQuotientComplex C).homology 1) :
    coefficientConnecting C y ∈ Submodule.torsion ℤ_[2] (C.homology 2) := by
  have h := congrArg (fun f => f.hom y)
    ((coefficientSequence_shortExact C).δ_comp 1 2 rfl)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at h
  change (HomologicalComplex.homologyMap (coefficientMap C) 2).hom
    (coefficientConnecting C y) = 0 at h
  exact (coefficientHomologyMap_ker C 2) ▸ h

/-- The connecting homomorphism with its exact torsion target. -/
def coefficientTorsionConnecting : (coefficientQuotientComplex C).homology 1 →ₗ[ℤ_[2]]
    Submodule.torsion ℤ_[2] (C.homology 2) :=
  (coefficientConnecting C).codRestrict _ (coefficientConnecting_mem_torsion C)

/-- Every torsion class of second integral cohomology is a connecting class. -/
theorem coefficientTorsionConnecting_surjective :
    Function.Surjective (coefficientTorsionConnecting C) := by
  intro y
  have hy : (y : C.homology 2) ∈
      LinearMap.ker (HomologicalComplex.homologyMap (coefficientMap C) 2).hom :=
    (coefficientHomologyMap_ker C 2).symm ▸ y.2
  have hr := ((coefficientSequence_shortExact C).homology_exact₁ 1 2 rfl).moduleCat_range_eq_ker
  change LinearMap.range (coefficientConnecting C) =
    LinearMap.ker (HomologicalComplex.homologyMap (coefficientMap C) 2).hom at hr
  rw [← hr] at hy
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

/-- The rational projection and the connecting homomorphism are exact. -/
theorem rationalToDivisibleConnecting_exact :
    Function.Exact (rationalToDivisible C) (coefficientTorsionConnecting C) := by
  have hex := (coefficientSequence_shortExact C).homology_exact₃ 1 2 rfl
  have hex' := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hex
  change Function.Exact (coefficientProjection C) (coefficientConnecting C) at hex'
  intro y
  constructor
  · intro hy
    have hy' : coefficientConnecting C y = 0 := congrArg Subtype.val hy
    obtain ⟨z, hz⟩ := (hex' y).mp hy'
    refine ⟨coefficientTensorHomologyEquiv C 1 z, ?_⟩
    change coefficientProjection C ((coefficientTensorHomologyEquiv C 1).symm
      (coefficientTensorHomologyEquiv C 1 z)) = y
    rw [LinearEquiv.symm_apply_apply]
    exact hz
  · rintro ⟨z, rfl⟩
    apply Subtype.ext
    exact (hex' (rationalToDivisible C z)).mpr
      ⟨(coefficientTensorHomologyEquiv C 1).symm z, rfl⟩

/-- The universal-coefficient map on a rationalization class. -/
theorem universalCoefficientMap_quotient (z : ℚ_[2] ⊗[ℤ_[2]] C.homology 1) :
    universalCoefficientMap C
        (tensorQuotientEquiv (C.homology 1) (Submodule.Quotient.mk z)) =
      rationalToDivisible C z :=
  universalTensorMap_quotient _ _ _ z

/-- Its image is exactly the image of rational cohomology. -/
theorem universalCoefficientMap_range :
    LinearMap.range (universalCoefficientMap C) = LinearMap.range (rationalToDivisible C) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := Submodule.mkQ_surjective (LinearMap.range (rationalUnit (C.homology 1)))
      ((tensorQuotientEquiv (C.homology 1)).symm x)
    have hx : tensorQuotientEquiv (C.homology 1) (Submodule.Quotient.mk z) = x := by
      rw [show (Submodule.Quotient.mk z :
        ℚ_[2] ⊗[ℤ_[2]] C.homology 1 ⧸ LinearMap.range (rationalUnit (C.homology 1))) =
          (tensorQuotientEquiv (C.homology 1)).symm x from hz]
      exact LinearEquiv.apply_symm_apply _ _
    refine ⟨z, ?_⟩
    rw [← hx, universalCoefficientMap_quotient]
  · rintro ⟨z, rfl⟩
    exact ⟨tensorQuotientEquiv (C.homology 1) (Submodule.Quotient.mk z),
      universalCoefficientMap_quotient C z⟩

/-- Universal coefficients: the image is the kernel of the torsion connecting map. -/
theorem universalCoefficient_exact :
    Function.Exact (universalCoefficientMap C) (coefficientTorsionConnecting C) := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (rationalToDivisibleConnecting_exact C y).mp hy
    have h : y ∈ LinearMap.range (rationalToDivisible C) := ⟨x, hx⟩
    rw [← universalCoefficientMap_range C] at h
    exact h
  · rintro ⟨x, hx⟩
    have h : y ∈ LinearMap.range (universalCoefficientMap C) := ⟨x, hx⟩
    rw [universalCoefficientMap_range C] at h
    exact (rationalToDivisibleConnecting_exact C y).mpr h

/-- The universal-coefficient short complex. -/
def universalCoefficientSequence : ShortComplex (ModuleCat.{0} ℤ_[2]) :=
  ShortComplex.moduleCatMk (universalCoefficientMap C) (coefficientTorsionConnecting C) (by
    apply LinearMap.ext
    intro x
    exact (universalCoefficient_exact C (universalCoefficientMap C x)).mpr ⟨x, rfl⟩)

/-- The coefficient quotient satisfies the manuscript's universal-coefficient short exact sequence. -/
theorem universalCoefficientSequence_shortExact : (universalCoefficientSequence C).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
      (universalCoefficient_exact C)
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact universalCoefficientMap_injective C
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact coefficientTorsionConnecting_surjective C

/-- A fixed power of two kills the cokernel, directly from degree-two torsion. -/
theorem universalCoefficientMap_coker_two_power [Module.Finite ℤ_[2] (C.homology 2)] :
    ∃ n : ℕ, ∀ y : (coefficientQuotientComplex C).homology 1,
      ∃ x, universalCoefficientMap C x = (2 ^ n : ℕ) • y := by
  obtain ⟨n, hn⟩ := finite_torsion_two_power (C.homology 2)
  refine ⟨n, fun y => ?_⟩
  apply (universalCoefficient_exact C ((2 ^ n : ℕ) • y)).mp
  apply Subtype.ext
  change coefficientConnecting C ((2 ^ n : ℕ) • y) = 0
  rw [map_nsmul]
  exact hn (coefficientConnecting C y) (coefficientConnecting_mem_torsion C y)

/-- Finite generation in degree two gives a fixed integral bound on both defects. -/
theorem universalCoefficientMap_boundedDefects [Module.Finite ℤ_[2] (C.homology 2)] :
    BoundedDefects (universalCoefficientMap C).toAddMonoidHom := by
  obtain ⟨n, hn⟩ := finite_torsion_two_power (C.homology 2)
  refine ⟨1, 2 ^ n, one_ne_zero, pow_ne_zero n two_ne_zero, fun x hx => ?_, fun y => ?_⟩
  · have hx0 : x = 0 := universalCoefficientMap_injective C (hx.trans (map_zero _).symm)
    simpa only [one_nsmul] using hx0
  · apply (universalCoefficient_exact C ((2 ^ n : ℕ) • y)).mp
    apply Subtype.ext
    change coefficientConnecting C ((2 ^ n : ℕ) • y) = 0
    rw [map_nsmul]
    exact hn (coefficientConnecting C y) (coefficientConnecting_mem_torsion C y)

end ZInQ.Manuscript.RC53Assist.CentralUniversal
