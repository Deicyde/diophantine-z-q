import ZInQKernel.Contrib.OneProof.BShStandardWeber

/-! ON THE SPOT (provenance (c)): the division polynomial of the normalized
curve sees every nonzero analytic torsion point, modulo sign in the x-coordinate. -/

noncomputable section

namespace BShTraces

open WeierstrassCurve PeriodPair X1Igusa X1Igusa.Weber LeafModCurves

/-- At a generic lattice, the roots of the division polynomial in the normalized
x-coordinate are exactly the normalized Weierstrass values on nonzero
lattice classes killed by the given integer. -/
theorem normalized_torsion_roots (L : PeriodPair) (hΔ : L.DiscriminantNeZero)
    (h₂ : L.g₂ ≠ 0) (h₃ : L.g₃ ≠ 0) (n : ℕ) (x : ℂ) :
    let E := curveG (L.g₂ ^ 3 / L.g₃ ^ 2)
    (E.ΨSq n).eval x = 0 ↔
      ∃ w : ℂ, w ∉ L.lattice ∧ (n : ℂ) * w ∈ L.lattice ∧
        x = (L.g₂ / L.g₃) * L.weierstrassP w := by
  classical
  dsimp only
  let G := L.g₂ ^ 3 / L.g₃ ^ 2
  let E := curveG G
  have hD : E.Δ = G ^ 2 * (G - 27) := by
    simp only [E, curveG, Δ, b₂, b₄, b₆, b₈]
    ring
  have hg : G ≠ 0 := div_ne_zero (pow_ne_zero _ h₂) (pow_ne_zero _ h₃)
  have hg' : G - 27 ≠ 0 := by
    have hh : G - 27 = (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) / L.g₃ ^ 2 := by
      unfold G
      field_simp
    rw [hh]
    exact div_ne_zero hΔ (pow_ne_zero _ h₃)
  have hE : E.Δ ≠ 0 := by rw [hD]; exact mul_ne_zero (pow_ne_zero _ hg) hg'
  obtain ⟨u, hu₂⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₂ / L.g₃) two_pos
  have hu : u ≠ 0 := by
    rintro rfl
    exact div_ne_zero h₂ h₃ (by simpa using hu₂.symm)
  obtain ⟨e, he⟩ := exists_addEquiv_xCoord L.weierstrassCurve E _
    (curveC_smul L h₂ h₃ u hu₂ hu)
  have H (w : ℂ) (hw : w ∉ L.lattice) :
      ∃ a b, ∃ ha : E.toAffine.Nonsingular a b,
        e (L.toPoint hΔ w) = Affine.Point.some a b ha ∧
        a = L.g₂ / L.g₃ * L.weierstrassP w := by
    have h := he (L.toPoint hΔ w) (fun hh => hw ((toPoint_eq_zero_iff L hΔ w).mp hh))
    have hx : xCoord (L.toPoint hΔ w) = L.weierstrassP w := by
      rw [L.toPoint_of_notMem hΔ hw]
      rfl
    rw [hx] at h
    cases hh : e (L.toPoint hΔ w) with
    | zero => exact (hw ((toPoint_eq_zero_iff L hΔ w).mp (e.map_eq_zero_iff.mp hh))).elim
    | some a b hns =>
      refine ⟨a, b, hns, rfl, ?_⟩
      rw [hh] at h
      simpa [xCoord, hu₂] using h
  have torsion (w : ℂ) {a b : ℂ} {ha : E.toAffine.Nonsingular a b}
      (h : e (L.toPoint hΔ w) = Affine.Point.some a b ha) :
      (E.ΨSq n).eval a = 0 ↔ (n : ℂ) * w ∈ L.lattice := by
    rw [eval_ΨSq_eq_zero_iff_zsmul_eq_zero _ ha,
      zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero, ← h, natCast_zsmul, ← map_nsmul,
      e.map_eq_zero_iff, nsmul_toPoint, toPoint_eq_zero_iff]
  constructor
  · intro h
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x ^ 3 + E.a₄ * x + E.a₆) two_pos
    have hns : E.toAffine.Nonsingular x y := by
      apply (Affine.equation_iff_nonsingular_of_Δ_ne_zero hE).mp
      rw [Affine.equation_iff]
      simpa [E, curveG] using hy
    obtain ⟨w, hw⟩ := (e.surjective.comp (L.isUniformization_toPoint hΔ).2.1)
      (Affine.Point.some x y hns)
    change e (L.toPoint hΔ w) = _ at hw
    have hwn : w ∉ L.lattice := by
      intro hm
      rw [L.toPoint_of_mem hΔ hm, map_zero] at hw
      exact Affine.Point.some_ne_zero hns hw.symm
    obtain ⟨x', y', hx', heq, hcoord⟩ := H w hwn
    have hxx : x = x' := congrArg xCoord (hw.symm.trans heq)
    exact ⟨w, hwn, (torsion w hw).mp h, hxx.trans hcoord⟩
  · rintro ⟨w, hw, hn, hcoord⟩
    obtain ⟨x', y', hx', hpt, heq⟩ := H w hw
    have hx : x = x' := hcoord.trans heq.symm
    rw [hx]
    exact (torsion w hpt).mpr hn

#print axioms normalized_torsion_roots

end BShTraces
