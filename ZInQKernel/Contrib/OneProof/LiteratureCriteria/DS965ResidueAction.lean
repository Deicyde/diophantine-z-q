import ZInQKernel.Contrib.OneProof.LiteratureCriteria.DS965Places
import ZInQKernel.Contrib.OneProof.DSCoeffExt

/-! # The residue action on the actual algebraic integers -/

namespace DS965Places

open ZInQ.Contrib.ChebFD.HSyn (Qbar GQ gZ)
open ZInQ.Contrib.ChebFD.C10 (Zbar)

/-- Inertia at the valuation ring acts as the identity modulo its contracted prime. -/
theorem inertia_congr (v : ValuationSubring Qbar) (σ : v.decompositionSubgroup ℚ)
    (hσ : σ ∈ v.inertiaSubgroup ℚ) (x : Zbar) : gZ σ.val x - x ∈ placeIdeal v := by
  have h : MulSemiringAction.toRingAut (v.decompositionSubgroup ℚ)
      (IsLocalRing.ResidueField v) σ = 1 := hσ
  have hfix : σ • IsLocalRing.residue v (toVal v x) = IsLocalRing.residue v (toVal v x) :=
    DFunLike.congr_fun h _
  have hval : toVal v (gZ σ.val x) = σ • toVal v x := Subtype.ext rfl
  change toVal v (gZ σ.val x - x) ∈ IsLocalRing.maximalIdeal v
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, hval,
    IsLocalRing.ResidueField.residue_smul, hfix, sub_self]

/-- A lift of residue Frobenius acts by the pth power modulo the contracted prime. -/
theorem frobenius_congr (v : ValuationSubring Qbar) (p : ℕ) (σ : GQ)
    (hσ : ZInQ.Contrib.G9.PkgI4.IsArithFrob σ v p) (x : Zbar) :
    gZ σ x - x ^ p ∈ placeIdeal v := by
  apply (mem_placeIdeal v _).mpr
  change σ (x : Qbar) - (x : Qbar) ^ p ∈ v.nonunits
  exact hσ.2 _ (int_mem v x)

/-- Either of the two residue congruences used in the book implies preservation of the prime.
The positive exponent is one for inertia and `p` for Frobenius. -/
theorem stabilizes_of_congr (P : Ideal Zbar) [P.IsPrime] (σ : GQ) (n : ℕ) (hn : n ≠ 0)
    (h : ∀ x : Zbar, gZ σ x - x ^ n ∈ P) :
    ∀ x : Zbar, gZ σ x ∈ P ↔ x ∈ P := by
  intro x
  constructor
  · intro hx
    have hy := P.sub_mem hx (h x)
    rw [sub_sub_cancel] at hy
    exact (inferInstance : P.IsPrime).mem_of_pow_mem n hy
  · intro hx
    have hy := P.add_mem (h x) (P.pow_mem_of_mem hx n (Nat.pos_of_ne_zero hn))
    rwa [sub_add_cancel] at hy

end DS965Places
