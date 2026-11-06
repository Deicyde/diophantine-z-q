import ZInQKernel.Model.Field
open ZInQ
#check @Ideal.mem_span_pair
#check @Ideal.span_mul_span'
#check @RingHom.ker_isMaximal_of_surjective
#check @Ideal.absNorm_span_singleton
#check @Algebra.norm_algebraMap
#check @MulEquiv.prime_iff
#check @Nat.exists_eq_pow_mul_and_not_dvd
#check @starRingAut
#check @Ideal.map_span
#check @QuadraticAlgebra.finrank_eq_two
#check @Submodule.cardQuot_apply
#check @Ideal.absNorm_apply
#check @Ideal.IsPrime.isMaximal
#check @Zs.isUnit_iff_norm
#check @Zs.norm_eq
example : IsDedekindDomain Zs := inferInstance
example : Module.Free ℤ Zs := inferInstance
example : Module.Finite ℤ Zs := inferInstance
example : Module.finrank ℤ Zs = 2 := QuadraticAlgebra.finrank_eq_two _ _
example (a : Zs) : star a = ⟨a.re, -a.im⟩ := by ext <;> simp
example (a : Zs) : Zs.toK0 (star a) = star (Zs.toK0 a) := by ext <;> simp
