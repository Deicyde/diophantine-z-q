import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.HDecomp.Conductor.I6Base
import ZInQKernel.Contrib.G15.LadicD1

/-!
# g8-local, part C: the local field `F` of G15's local data

Task g8-local (2026-11-13). The field `F ⊆ ℚ̄_p` of g8-object's `LocalDataS` (N5 L797-798,
L814-815): "for a finite extension of `ℚ_p` of degree at most `a`, its normal closure has degree
at most `a!`".

* `ramCard_le_finrank`: `e(F/ℚ_p) = ramCard F 0 ≤ [F:ℚ_p]` for `F` finite Galois.
* `exists_galois_closure`: for `M ⊆ ℚ̄` finite over `ℚ` and any embedding `jQ : ℚ̄ → ℚ̄_p`, the
  normal closure `F` of `ℚ_p(jQ M)` (the splitting field of the minimal polynomial of a primitive
  element) is finite Galois, contains `jQ M`, and `e(F/ℚ_p) ≤ [M:ℚ]!`. No Krasner argument is
  needed: `F` is built inside `ℚ̄_p`, and its degree is bounded through the minimal polynomial.
* `ramCard_Lj_le_finrank`: `e(ℚ_p(j L)/ℚ_p) ≤ [L:ℚ]` for the kernel's `Lj` (g15-decomp).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.G8Local

open PkgI4 LadicCond Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- **`e(F/ℚ_p) ≤ [F:ℚ_p]`.** Restrictions of `G_{ℚ_p}` to a finite Galois `F` are elements of
`Gal(F/ℚ_p)`. -/
theorem ramCard_le_finrank (F : Fld p) (hF : IsFinGal F) :
    ramCard F 0 ≤ Module.finrank ℚ_[p] F := by
  haveI := hF.1
  haveI : IsGalois ℚ_[p] F := hF.2
  haveI : Normal ℚ_[p] F := inferInstance
  set φ : (F ≃ₐ[ℚ_[p]] F) → (F → Kbar p) := fun s x => ((s x : F) : Kbar p) with hφ
  have hsub : restr F '' ramSet F 0 ⊆ Set.range φ := by
    rintro _ ⟨σ, -, rfl⟩
    refine ⟨σ.restrictNormal F, ?_⟩
    funext x
    exact AlgEquiv.restrictNormal_commutes σ F x
  have hfin : (Set.range φ).Finite := Set.finite_range φ
  calc ramCard F 0 = Nat.card (restr F '' ramSet F 0) := rfl
    _ ≤ Nat.card (Set.range φ) := Nat.card_mono hfin hsub
    _ ≤ Nat.card (F ≃ₐ[ℚ_[p]] F) :=
        Nat.card_le_card_of_surjective (Set.rangeFactorization φ) Set.rangeFactorization_surjective
    _ = Module.finrank ℚ_[p] F := IsGalois.card_aut_eq_finrank ℚ_[p] F

/-- **The normal closure of `ℚ_p(jQ M)` (proved).** For `M ⊆ ℚ̄` finite over `ℚ` and a ring map
`jQ : ℚ̄ → ℚ̄_p`, some finite Galois `F ⊆ ℚ̄_p` contains `jQ M` and has `e(F/ℚ_p) ≤ [M:ℚ]!`. -/
theorem exists_galois_closure (jQ : AlgebraicClosure ℚ →+* Kbar p)
    (M : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ M] :
    ∃ F : Fld p, IsFinGal F ∧ (∀ x ∈ M, jQ x ∈ F) ∧
      ramCard F 0 ≤ (Module.finrank ℚ M).factorial := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ M
  set a : AlgebraicClosure ℚ := (α : AlgebraicClosure ℚ) with ha
  set y : Kbar p := jQ a with hy
  have hyi : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral y
  have hai : IsIntegral ℚ a := Algebra.IsIntegral.isIntegral a
  set f := minpoly ℚ_[p] y with hf
  have hf0 : f ≠ 0 := minpoly.ne_zero hyi
  let F : Fld p := IntermediateField.adjoin ℚ_[p] (f.rootSet (Kbar p))
  haveI hspl : f.IsSplittingField ℚ_[p] F :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  haveI : FiniteDimensional ℚ_[p] F := IsSplittingField.finiteDimensional F f
  have hsep : f.Separable := (minpoly.irreducible hyi).separable
  haveI : IsGalois ℚ_[p] F := IsGalois.of_separable_splitting_field hsep
  have hFG : IsFinGal F := ⟨inferInstance, inferInstance⟩
  have hyF : y ∈ F := IntermediateField.subset_adjoin ℚ_[p] _
    ((mem_rootSet_of_ne hf0).mpr (minpoly.aeval ℚ_[p] y))
  -- degree bound
  have hdvd : f ∣ (minpoly ℚ a).map (algebraMap ℚ ℚ_[p]) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, hy, ← jQ.toRatAlgHom_apply, aeval_algHom_apply, minpoly.aeval,
      map_zero]
  have hdeg : f.natDegree ≤ Module.finrank ℚ M := by
    have h1 := natDegree_le_of_dvd hdvd (map_ne_zero (minpoly.ne_zero hai))
    rw [natDegree_map] at h1
    have h2 : (minpoly ℚ a).natDegree ≤ Module.finrank ℚ M := by
      have := minpoly.natDegree_le (A := ℚ) α
      rwa [IntermediateField.minpoly_eq] at this
    omega
  refine ⟨F, hFG, ?_, ?_⟩
  · -- `jQ M ⊆ F`
    let G : IntermediateField ℚ (AlgebraicClosure ℚ) :=
      (F.restrictScalars ℚ).comap jQ.toRatAlgHom
    have haG : a ∈ G := hyF
    have hle : IntermediateField.adjoin ℚ {a} ≤ G :=
      IntermediateField.adjoin_simple_le_iff.mpr haG
    intro x hx
    have hx' : x ∈ (IntermediateField.adjoin ℚ ({α} : Set M)).map M.val := by
      rw [hα]
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at hx'
    exact hle hx'
  · calc ramCard F 0 ≤ Module.finrank ℚ_[p] F := ramCard_le_finrank F hFG
      _ ≤ f.natDegree.factorial := PkgI6.finrank_isSplittingField_le_factorial f hsep
      _ ≤ (Module.finrank ℚ M).factorial := Nat.factorial_le hdeg

/-- **`e(ℚ_p(j L)/ℚ_p) ≤ [L:ℚ]`** for the kernel's `Lj` (g15-decomp's local field). -/
theorem ramCard_Lj_le_finrank {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (j : L →+* Kbar p) :
    ramCard (ZInQ.Contrib.G15.Ladic.Lj j) 0 ≤ Module.finrank ℚ L := by
  have := ZInQ.Contrib.G15.Ladic.primeOf_liesOver j
  rw [ZInQ.Contrib.G15.Ladic.ramCard_Lj_zero]
  exact PkgI6.ramificationIdx_le_finrank_of_numberField L _

end ZInQ.Contrib.G8Local

end
