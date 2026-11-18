import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Algebra.Polynomial.Lifts

/-!
# Valuation rings of an algebraically closed field are strictly henselian

Let `Ω` be an algebraically closed field and `w` any valuation subring of `Ω` (no discreteness,
no noetherianity, arbitrary value group). Then

* `w` is a henselian local ring (`henselianLocalRing_of_isAlgClosed`): a monic `f ∈ w[X]` splits
  over `Ω`, its roots are integral over `w` hence lie in `w` (valuation subrings are integrally
  closed), and if `f(a₀) ∈ 𝔪` then `f(a₀) = ∏ (a₀ - yᵢ)` forces some `a₀ - yᵢ ∈ 𝔪`;
* the residue field `κ(w)` is algebraically closed (`isAlgClosed_residueField`): lift a monic
  residue polynomial to a monic polynomial over `w`, take a root in `Ω`, it lies in `w`, reduce;
* hence `κ(w)` is separably closed (`isSepClosed_residueField`).

Neither class is assumed; both are derived from the field and valuation-subring data.

Edition V003: the factorwise identity is closed by an explicit rewrite with the chosen root.
Statements as in V001.
-/

open Polynomial IsLocalRing

namespace HenselDivision

variable {Ω : Type*} [Field Ω] (w : ValuationSubring Ω)

/-- A root in `Ω` of a monic polynomial over `w` lies in `w` and is a root there. -/
theorem exists_root_mem_of_monic {f : w[X]} (hf : f.Monic) {r : Ω}
    (hr : aeval r f = 0) : ∃ y : w, algebraMap w Ω y = r ∧ f.IsRoot y := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (⟨f, hf, hr⟩ : IsIntegral w r)
  refine ⟨y, hy, ?_⟩
  have h2 : algebraMap w Ω (aeval y f) = 0 := by
    rw [← Polynomial.aeval_algebraMap_apply, hy, hr]
  have h3 : aeval y f = 0 := by
    apply IsFractionRing.injective w Ω
    rw [h2, map_zero]
  rw [Polynomial.coe_aeval_eq_eval] at h3
  exact h3

variable [IsAlgClosed Ω]

/-- **Every valuation subring of an algebraically closed field is henselian.** -/
theorem henselianLocalRing_of_isAlgClosed : HenselianLocalRing w := by
  refine ⟨fun f hf a₀ h₁ _ => ?_⟩
  classical
  set F := f.map (algebraMap w Ω) with hF
  have hFm : F.Monic := hf.map _
  have hsplit : F = (F.roots.map fun a => X - C a).prod :=
    (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hFm
      IsAlgClosed.card_roots_eq_natDegree).symm
  have hroot : ∀ r ∈ F.roots, ∃ y : w, algebraMap w Ω y = r ∧ f.IsRoot y := by
    intro r hr
    apply exists_root_mem_of_monic w hf
    rw [aeval_def, ← eval_map]
    exact (mem_roots hFm.ne_zero).mp hr
  let g : Ω → w := fun r =>
    if h : ∃ y : w, algebraMap w Ω y = r ∧ f.IsRoot y then h.choose else 0
  have hg : ∀ r ∈ F.roots, algebraMap w Ω (g r) = r ∧ f.IsRoot (g r) := by
    intro r hr
    have h := hroot r hr
    simp only [g, h, ↓reduceDIte]
    exact h.choose_spec
  have hprod : f.eval a₀ = (F.roots.map fun r => a₀ - g r).prod := by
    apply IsFractionRing.injective w Ω
    rw [map_multiset_prod, Multiset.map_map]
    have he : algebraMap w Ω (f.eval a₀) = F.eval (algebraMap w Ω a₀) := by
      rw [hF, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rw [he]
    conv_lhs => rw [hsplit]
    rw [eval_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro r hr
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C, map_sub]
    rw [(hg r hr).1]
  have hmem : (F.roots.map fun r => a₀ - g r).prod ∈ maximalIdeal w := by
    rw [← hprod]; exact h₁
  obtain ⟨x, hx, hxm⟩ :=
    ((maximalIdeal.isMaximal w).isPrime.multiset_prod_mem_iff_exists_mem _).mp hmem
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
  refine ⟨g r, (hg r hr).2, ?_⟩
  rw [← neg_sub]
  exact neg_mem hxm

/-- **The residue field of a valuation subring of an algebraically closed field is algebraically
closed.** -/
theorem isAlgClosed_residueField : IsAlgClosed (ResidueField w) := by
  refine IsAlgClosed.of_exists_root _ (fun p hp hirr => ?_)
  obtain ⟨f, hfp, hdeg, hfm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective IsLocalRing.residue_surjective p) hp
  have hpos : 0 < (f.map (algebraMap w Ω)).natDegree := by
    rw [hfm.natDegree_map, hdeg]
    exact natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hirr)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root (f.map (algebraMap w Ω))
    (natDegree_pos_iff_degree_pos.mp hpos).ne'
  obtain ⟨y, -, hy⟩ := exists_root_mem_of_monic w hfm (by
    rw [aeval_def, ← eval_map]; exact hr)
  refine ⟨IsLocalRing.residue w y, ?_⟩
  rw [← hfp, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy.eq_zero, map_zero]

/-- Hence the residue field is separably closed. -/
theorem isSepClosed_residueField : IsSepClosed (ResidueField w) :=
  haveI := isAlgClosed_residueField w
  IsSepClosed.of_isAlgClosed (ResidueField w)

end HenselDivision

#check @HenselDivision.henselianLocalRing_of_isAlgClosed
#check @HenselDivision.isAlgClosed_residueField
#check @HenselDivision.isSepClosed_residueField
#print axioms HenselDivision.henselianLocalRing_of_isAlgClosed
#print axioms HenselDivision.isAlgClosed_residueField
#print axioms HenselDivision.isSepClosed_residueField
