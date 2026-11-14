import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Polynomial.Splits
import ZInQKernel.Contrib.DiophantineTate.ActualResidue

/-!
# Henselianity of valuation subrings of algebraically closed fields

Every monic polynomial splits in the actual valuation subring: its ambient-field
roots are integral and therefore belong to the subring. Reducing the resulting
factorization matches any prescribed residue root with one of those roots.
This supplies the actual `HenselianLocalRing V`, without a DVR, Noetherian,
completeness or caller-provided Henselian assumption.

The argument lifts all residue roots of monic polynomials; the derivative-unit
hypothesis in the Henselian interface is consequently not needed by this proof.
AI-assisted proof development; no global instance is registered.
-/

noncomputable section

namespace DiophantineTate.ActualHenselian

open Polynomial IsLocalRing

/-- A valuation subring of an algebraically closed field is Henselian. -/
theorem henselianLocalRing (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (V : ValuationSubring Ω) : HenselianLocalRing V := by
  classical
  refine
    { toIsLocalRing := ValuationSubring.isLocalRing V
      is_henselian := ?_ }
  intro f hf a₀ h₀ _hderivative

  have hs : f.Splits := by
    refine Polynomial.Splits.of_splits_map_of_injective
      (i := V.subtype) (ValuationSubring.subtype_injective V)
      (IsAlgClosed.splits (f.map V.subtype)) ?_
    intro x hx
    have hxV : x ∈ V :=
      DiophantineTate.ActualResidue.monic_root_mem V f hf x
        (Polynomial.isRoot_of_mem_roots hx)
    exact ⟨⟨x, hxV⟩, rfl⟩

  have hfactor_bar :
      f.map (residue V) =
        ((f.roots.map (residue V)).map
          (fun r => (X : Polynomial (ResidueField V)) - C r)).prod := by
    have h := congrArg (Polynomial.map (residue V))
      (hs.eq_prod_roots_of_monic hf)
    simpa only [Polynomial.map_multiset_prod, Multiset.map_map,
      Function.comp_def, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] using h

  have hroots_bar : (f.map (residue V)).roots = f.roots.map (residue V) := by
    rw [hfactor_bar, Polynomial.roots_multiset_prod_X_sub_C]

  have hfbar : (f.map (residue V)).Monic := hf.map (residue V)
  have hroot_bar : residue V a₀ ∈ (f.map (residue V)).roots := by
    apply (Polynomial.mem_roots hfbar.ne_zero).mpr
    change (f.map (residue V)).eval (residue V a₀) = 0
    rw [Polynomial.eval_map_apply]
    exact (IsLocalRing.residue_eq_zero_iff (f.eval a₀)).mpr h₀

  rw [hroots_bar, Multiset.mem_map] at hroot_bar
  obtain ⟨a, ha, hres⟩ := hroot_bar
  refine ⟨a, Polynomial.isRoot_of_mem_roots ha, ?_⟩
  apply (IsLocalRing.residue_eq_zero_iff (a - a₀)).mp
  rw [(residue V).map_sub, hres, sub_self]

end DiophantineTate.ActualHenselian
