import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Group

/-!
# Separation by quadratic characters

The group-theoretic part of Appendix F, tex 9745–9750.
The basis of the elementary quotient is an on-the-spot proof (provenance (c)).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.TraceLimits

/-- A subgroup containing every square is normal. -/
theorem normal_of_all_squares {G : Type*} [Group G] (H : Subgroup G)
    (hsq : ∀ x : G, x ^ 2 ∈ H) : H.Normal := by
  refine ⟨fun a ha b => ?_⟩
  have h := H.mul_mem (H.mul_mem (hsq (b * a)) (H.inv_mem ha)) (hsq b⁻¹)
  convert h using 1
  simp only [pow_two]
  group

/-- In an elementary quotient, quadratic characters separate all nonidentity
elements. The kernel of every such character on the original group contains
the subgroup used to form the quotient. -/
theorem exists_quadratic_separating {G : Type*} [Group G] (N : Subgroup G)
    {g : G} (hg : g ∉ Subgroup.closure {x | ∃ y : G, x = y ^ 2} ⊔ N) :
    ∃ χ : G →* Multiplicative (ZMod 2), N ≤ χ.ker ∧ χ g ≠ 1 := by
  let H := Subgroup.closure {x | ∃ y : G, x = y ^ 2} ⊔ N
  have hsq (x : G) : x ^ 2 ∈ H :=
    Subgroup.mem_sup_left (Subgroup.subset_closure ⟨x, rfl⟩)
  have : H.Normal := normal_of_all_squares H hsq
  let Q := G ⧸ H
  have hs (x : Q) : x ^ 2 = 1 := by
    obtain ⟨y, rfl⟩ := (QuotientGroup.mk'_surjective H) x
    change (QuotientGroup.mk' H y) ^ 2 = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 (hsq y)
  have hinv (x : Q) : x⁻¹ = x :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hs x)
  let : CommGroup Q :=
    { (inferInstance : Group Q) with
      mul_comm := fun a b => by rw [← hinv (a * b), mul_inv_rev, hinv a, hinv b] }
  let : Module (ZMod 2) (Additive Q) := AddCommGroup.zmodModule fun x =>
    show Additive.ofMul (x.toMul ^ 2) = Additive.ofMul 1 from congrArg Additive.ofMul (hs x.toMul)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let b := Module.Basis.ofVectorSpace (ZMod 2) (Additive Q)
  let x := Additive.ofMul (QuotientGroup.mk' H g)
  have hx : x ≠ 0 := fun hx => hg ((QuotientGroup.eq_one_iff g).mp hx)
  have hbx : b.repr x ≠ 0 := fun e => hx (b.repr.injective (e.trans b.repr.map_zero.symm))
  obtain ⟨i, hi⟩ : ∃ i, b.repr x i ≠ 0 := by
    by_contra! h
    exact hbx (Finsupp.ext (fun i => h i))
  let χ : Q →* Multiplicative (ZMod 2) :=
    { toFun := fun y => Multiplicative.ofAdd (b.repr (Additive.ofMul y) i)
      map_one' := by change Multiplicative.ofAdd (b.repr 0 i) = _; simp
      map_mul' := fun y z => by
        change Multiplicative.ofAdd (b.repr (Additive.ofMul y + Additive.ofMul z) i) = _
        rw [map_add, Finsupp.add_apply]
        rfl }
  refine ⟨χ.comp (QuotientGroup.mk' H), fun a ha => MonoidHom.mem_ker.2 ?_, ?_⟩
  · change χ (QuotientGroup.mk' H a) = 1
    rw [(show QuotientGroup.mk' H a = 1 from (QuotientGroup.eq_one_iff a).2 (Subgroup.mem_sup_right ha : a ∈ H)), map_one]
  · exact hi

#print axioms normal_of_all_squares
#print axioms exists_quadratic_separating

end ZInQ.Manuscript.RC.TraceLimits
