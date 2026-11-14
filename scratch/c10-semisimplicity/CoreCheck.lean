import S1Twist
import S2RelativeMaschke

/-!
# Standalone checks for the generic S1/S2 representation lemmas

These ascriptions and axiom reports cover the generic representation facts only.
They do not instantiate the global Tate-comparison inputs of the mapped C10 helper.
-/

example {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
    (ρ τ : Representation k G V) (χ : G → k)
    (hχ : ∀ g, χ g ≠ 0) (hρτ : ∀ g, ρ g = χ g • τ g) :
    Representation.IsSemisimpleRepresentation ρ ↔
      Representation.IsSemisimpleRepresentation τ :=
  ScaledS1.isSemisimpleRepresentation_iff_of_smul_twist ρ τ χ hχ hρτ

example {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (H : Subgroup G) (ρ : Representation k G V)
    (hidx : (H.index : k) ≠ 0)
    (hH : Representation.IsSemisimpleRepresentation (ρ.comp H.subtype)) :
    Representation.IsSemisimpleRepresentation ρ :=
  ScaledS2.isSemisimpleRepresentation_of_subgroup H ρ hidx hH

#check @ScaledS1.isSemisimpleRepresentation_iff_of_smul_twist
#check @ScaledS1.scalar_ne_zero_of_group_rep
#check @ScaledS1.isSemisimpleRepresentation_of_comp_surjective
#check @ScaledS2.isSemisimpleRepresentation_of_subgroup
#print axioms ScaledS1.le_comap_smul_iff
#print axioms ScaledS1.forall_le_comap_iff_of_smul_twist
#print axioms ScaledS1.twistOrderIso
#print axioms ScaledS1.isSemisimpleRepresentation_iff_of_smul_twist
#print axioms ScaledS1.isSemisimpleRepresentation_of_smul_twist
#print axioms ScaledS1.scalar_ne_zero_of_group_rep
#print axioms ScaledS1.compOrderIso
#print axioms ScaledS1.isSemisimpleRepresentation_of_comp_surjective
#print axioms ScaledS1.isSemisimpleRepresentation_comp_of_surjective
#print axioms ScaledS1.transport
#print axioms ScaledS1.transport_apply
#print axioms ScaledS2.isSemisimpleRepresentation_of_subgroup
#print axioms ScaledS2.conj_mul_of_mem
#print axioms ScaledS2.cosetConj_mk
#print axioms ScaledS2.conj_cosetConj
#print axioms ScaledS2.avg_comm
