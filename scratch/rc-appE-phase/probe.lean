import Mathlib
abbrev Qbar : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ
example : IsGalois ℚ Qbar := inferInstance
example : IsAlgClosed Qbar := inferInstance
#check @InfiniteGalois.mem_range_algebraMap_iff_fixed
#check @MulChar.ext
#check @ZMod.val_coe_unit_coprime
#check @IsPrimitiveRoot.eq_pow_of_pow_eq_one
#check @IsPrimitiveRoot.map_iff_of_injective
#check @Complex.isPrimitiveRoot_exp
#check @MulChar.coeToFun_mul
#check @MulChar.one_apply
