import ZInQKernel.Contrib.TYZGenus.RingClass
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField
open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory

namespace ZInQ.Contrib.TYZGenus.RingClass

variable {K : Type} [Field K] [NumberField K]

theorem ker_le_ker_maximal (O : NumberFieldOrder K) :
    (ringClassIdeleQuotient O).ker ≤ (ringClassIdeleQuotient (maximalNumberFieldOrder K)).ker := by
  intro c hc
  rw [ker_ringClassIdeleQuotient_maximalNumberFieldOrder, ← ker_rayClassQuotient, MonoidHom.mem_ker]
  obtain ⟨J, hJ, β, -, hJβ⟩ := (mem_ker_ringClassIdeleQuotient_iff O).1 hc
  rw [← classMap_rayClassQuotient (Modulus.one_dvd O.conductorModulus), ← hJ, classMap_idealClass,
    idealClass_eq_one_iff_exists_generator]
  refine ⟨β, by simp, fun w hw => by simp at hw, ?_⟩
  simpa using hJβ

theorem ringClassField_maximal_le (O : NumberFieldOrder K) :
    ringClassField (maximalNumberFieldOrder K) ≤ ringClassField O := by
  rw [ringClassField_def, ringClassField_def, ← globalClassField_orderReversing]
  change ((ringClassNormSubgroup O).1.toSubgroup ≤ (ringClassNormSubgroup _).1.toSubgroup)
  rw [ringClassNormSubgroup_toSubgroup, ringClassNormSubgroup_toSubgroup]
  exact ker_le_ker_maximal O

theorem ringClassField_maximal_eq_hilbertClassField :
    ringClassField (maximalNumberFieldOrder K) = hilbertClassField K := by
  rw [ringClassField_def, hilbertClassField, rayClassField_def]
  congr 3
  apply Subtype.ext
  apply OpenSubgroup.toSubgroup_injective
  change (ringClassNormSubgroup _).1.toSubgroup = (rayNormSubgroup _).1.toSubgroup
  rw [ringClassNormSubgroup_toSubgroup, rayNormSubgroup_toSubgroup,
    ker_ringClassIdeleQuotient_maximalNumberFieldOrder]

end ZInQ.Contrib.TYZGenus.RingClass
