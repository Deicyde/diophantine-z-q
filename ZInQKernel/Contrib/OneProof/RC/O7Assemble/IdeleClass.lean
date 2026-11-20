import ZInQKernel.Contrib.OneProof.RC.PicardFibers.IdeleClass
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup

/-! Compare the two ideal and class group maps pointwise (on the spot, (c)). -/

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing

namespace ZInQ.Manuscript.RC.O7Assemble

open PicardFibers

/-- The two branches' fractional ideal maps agree on every idele. -/
theorem ideleToIdeal_eq {F : Type} [Field F] [NumberField F]
    (a : (FiniteAdeleRing (𝓞 F) F)ˣ) : ideleToIdeal a = toFractionalIdeal a := by
  apply Units.ext
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' F (ideleToIdeal a).ne_zero,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' F (toFractionalIdeal a).ne_zero]
  refine finprod_congr fun v => ?_
  rw [count_ideleToIdeal, count_coe_toFractionalIdeal]
  rfl

/-- The class-group readings of a finite idele coincide. -/
theorem ideleClass_mk {F : Type} [Field F] [NumberField F]
    (a : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ideleClassEquiv (QuotientGroup.mk a) = toClassGroup (𝓞 F) F a := by
  change ideleClassMap a = toClassGroup (𝓞 F) F a
  rw [toClassGroup_apply]
  apply (ClassGroup.equiv F).injective
  simp only [ideleClassMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self,
    RingEquiv.coe_mulEquiv_refl, ideleToIdeal_eq]
  congr 1

end ZInQ.Manuscript.RC.O7Assemble
