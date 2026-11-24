import ZInQKernel.Contrib.OneProof.MumfordTorsionAlgClosed
import ZInQKernel.Contrib.OneProof.FaltingsDict
import Mathlib.AlgebraicGeometry.Artinian

noncomputable section
open CategoryTheory AlgebraicGeometry
open ZInQ.HeightSplit
open scoped CategoryTheory.MonObj

namespace ZInQ.FaltingsRestate

/-- A positive-dimensional abelian variety has nonidentity (n)-torsion
over an algebraically closed field for every invertible (n > 1). -/
theorem exists_nonidentity_torsion_of_positive_dimension
    {k : Type} [Field k] [IsAlgClosed k] (B : PkgI3.AbVar k)
    (g n : ℕ) (hg : topologicalKrullDim B.X.left = (g : WithBot ℕ∞))
    (hDim : 0 < g) (hn : 1 < n) (hnK : (n : k) ≠ 0) :
    ∃ x : algPt k k ⟶ B.X, x ^ n = 1 ∧ x ≠ 1 := by
  let C := Grp.mk B.X
  have : PkgI2.IsAbelianVariety C := ⟨B.proper, B.smooth, B.geomInt⟩
  obtain ⟨e, -⟩ := ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
    k C g n hg (by omega) hnK
  have : Fact (1 < n) := ⟨hn⟩
  have : Nonempty (Fin (2 * g)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (α := Fin (2 * g) → ZMod n)
  by_contra h
  apply hxy
  apply e.symm.injective
  apply Subtype.ext
  have eq_one (u : PkgI2.torsion C k n) : (u : PkgI2.Pts C k) = 1 := by
    by_contra hu
    exact h ⟨u.1, u.2, hu⟩
  exact (eq_one _).trans (eq_one _).symm

private theorem exists_invertible_two_or_three (k : Type) [Field k] :
    ∃ n : ℕ, 1 < n ∧ (n : k) ≠ 0 := by
  by_cases h : (2 : k) = 0
  · refine ⟨3, by decide, ?_⟩
    have he : (3 : k) = 2 + 1 := by norm_num
    have he' : (3 : k) = 1 := by rw [he, h, zero_add]
    simpa only [Nat.cast_ofNat, he'] using (one_ne_zero : (1 : k) ≠ 0)
  · exact ⟨2, by decide, h⟩

/-- A torsion-free abelian variety over an algebraically closed field has at
most one rational point if tested at all orders invertible in the field. -/
theorem subsingleton_abelian_points_of_no_invertible_torsion
    {k : Type} [Field k] [IsAlgClosed k] (B : PkgI3.AbVar k)
    (g : ℕ) (hg : topologicalKrullDim B.X.left = (g : WithBot ℕ∞))
    (ht : ∀ n : ℕ, (n : k) ≠ 0 → ∀ x : algPt k k ⟶ B.X, x ^ n = 1 → x = 1) :
    Subsingleton (algPt k k ⟶ B.X) := by
  have hg0 : g = 0 := by
    by_contra h
    obtain ⟨n, hn, hnK⟩ := exists_invertible_two_or_three k
    obtain ⟨x, hx, hne⟩ := exists_nonidentity_torsion_of_positive_dimension B g n hg
      (Nat.pos_of_ne_zero h) hn hnK
    exact hne (ht n hnK x hx)
  have : Smooth B.X.hom := B.smooth
  have : LocallyOfFiniteType B.X.hom := inferInstance
  have : IsLocallyNoetherian B.X.left := LocallyOfFiniteType.isLocallyNoetherian B.X.hom
  have : IsLocallyArtinian B.X.left :=
    IsLocallyArtinian.of_topologicalKrullDim_le_zero (by rw [hg, hg0]; rfl)
  have : GeometricallyIntegral B.X.hom := B.geomInt
  have : IsIntegral B.X.left := GeometricallyIntegral.isIntegral_of_subsingleton B.X.hom
  have : Subsingleton B.X.left := subsingleton_of_preconnected_totallyDisconnected
  constructor
  intro u v
  apply Over.OverMorphism.ext
  apply ext_of_apply_closedPoint_eq B.X.hom
  · simpa [algPt] using Over.w u
  · simpa [algPt] using Over.w v
  · exact Subsingleton.elim _ _

end ZInQ.FaltingsRestate
