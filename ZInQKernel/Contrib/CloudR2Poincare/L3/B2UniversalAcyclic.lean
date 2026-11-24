import ZInQKernel.Contrib.CloudR2Poincare.L1.NativeCohomologyLocus
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FreeComplexLocus

/-!
# Local universal acyclicity from the actual finite-free fibre model

This is the needed cohomology-and-base-change direction. It constructs a
single open neighborhood and split zero homology AFTER EVERY scheme-valued
base change. The only premise is actual fibre homology dimension zero;
no reducedness, flatness of the base change, or canonical-map Fact is assumed.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits

namespace ZInQ.Contrib.CloudR2Poincare.L3

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

universe u

/-- A bounded termwise free sheaf complex acyclic at one residue field becomes
universally acyclic on a genuine open neighborhood of that point. -/
theorem exists_opens_universally_zero_homology_of_fibre_zero
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (r : ℤ → ℕ)
    (e : ∀ q, P.X q ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin (r q))))
    (bound : ℕ) (hbound : ∀ q : ℤ, q < 0 ∨ (bound : ℤ) < q → r q = 0)
    (y : Y) (hy : ∀ q : ℤ, L1.derivedFiberDimension P q y = 0) :
    ∃ W : Y.Opens, y ∈ W ∧ ∀ {Z : Scheme.{u}} (g : Z ⟶ Y), Set.range g ⊆ W →
      ∀ q : ℤ, IsZero ((((Scheme.Modules.pullback g).mapHomologicalComplex _).obj P).homology q) := by
  classical
  let C (n m : ℤ) : Matrix (ULift.{u} (Fin (r m))) (ULift.{u} (Fin (r n))) Γ(Y, ⊤) :=
    Scheme.Modules.freeMatrix ((e n).inv ≫ P.d n m ≫ (e m).hom)
  have hC : ∀ n m l, C m l * C n m = 0 := by
    intro n m l
    dsimp [C]
    rw [← Scheme.Modules.freeMatrix_comp]
    simp [Category.assoc, Scheme.Modules.freeMatrix_zero]
  have hN : ∀ n : ℤ, n < 0 ∨ (bound : ℤ) < n → IsEmpty (ULift.{u} (Fin (r n))) := by
    intro n hn
    rw [hbound n hn]
    infer_instance
  have hr : Scheme.RankCondition C 0 0 y := by
    intro q
    have h := Scheme.Modules.finrank_homology_pullback_add_rank_add_rank e
      (Field.toIsField (Y.residueField y)) (Y.fromSpecResidueField y) q
    change L1.derivedFiberDimension P q y +
      ((C q (q + 1)).map (Y.fromSpecResidueField y).appTop).rank +
        ((C (q - 1) q).map (Y.fromSpecResidueField y).appTop).rank = r q at h
    rw [hy q] at h
    change ((C (q - 1) q).map (Y.fromSpecResidueField y).appTop).rank +
      ((C q (q + 1)).map (Y.fromSpecResidueField y).appTop).rank +
        (if q = 0 then 0 else 0) = Fintype.card (ULift.{u} (Fin (r q)))
    simp only [ite_self, add_zero, Fintype.card_ulift, Fintype.card_fin]
    exact (add_comm _ _).trans (by simpa only [zero_add] using h)
  obtain ⟨W, hyW, split⟩ := Scheme.exists_opens_hasSplitHomology hC bound hN hr
  refine ⟨W, hyW, fun {Z} g hg q => ?_⟩
  have hs := split g hg q
  have hz : (if q = 0 then 0 else 0 : ℕ) = 0 := by split_ifs <;> rfl
  rw [hz] at hs
  have hsU := hs.of_equiv (Equiv.ulift.symm : Fin 0 ≃ ULift.{u} (Fin 0))
  obtain ⟨I, Q, σ, τ, hQI, hAI, hQzero, hsum⟩ := hsU
  let P' := ((Scheme.Modules.pullback g).mapHomologicalComplex _).obj P
  let e' (n : ℤ) : P'.X n ≅
      SheafOfModules.free (R := Z.ringCatSheaf) (ULift.{u} (Fin (r n))) :=
    (Scheme.Modules.pullback g).mapIso (e n) ≪≫ Scheme.Modules.pullbackFreeIso g _
  have incoming : Scheme.Modules.freeMatrix ((e' (q - 1)).inv ≫ P'.d (q - 1) q ≫ (e' q).hom) =
      (C (q - 1) q).map g.appTop := Scheme.Modules.freeMatrix_pullback_d g P (e (q - 1)) (e q)
  have outgoing : Scheme.Modules.freeMatrix ((e' q).inv ≫ P'.d q (q + 1) ≫ (e' (q + 1)).hom) =
      (C q (q + 1)).map g.appTop := Scheme.Modules.freeMatrix_pullback_d g P (e q) (e (q + 1))
  obtain ⟨iso⟩ := Scheme.Modules.nonempty_homology_iso_free_of_split P' q
    (e' (q - 1)) (e' q) (e' (q + 1)) σ τ I Q hQI
    (by rw [outgoing]; exact hAI) (by rw [incoming]; exact hQzero)
    (by rw [incoming, outgoing]; exact hsum)
  exact (Scheme.Modules.isZero_free_of_isEmpty (X := Z) (ULift.{u} (Fin 0))).of_iso iso

end ZInQ.Contrib.CloudR2Poincare.L3
