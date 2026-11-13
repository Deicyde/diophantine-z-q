import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.HDecomp.Conductor.I6Base

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
  If `M` is Galois over `ℚ`, then `[F:ℚ_p] ≤ [M:ℚ]` and `F` lies in every `F' ⊇ jQ M`.
* `decomp_spec`: the embedding `ℚ̄ → ℚ̄_p` underlying `PkgI4.decomp` (copied from g15-decomp's
  `ZInQ.Contrib.G15.Ladic.decomp_spec`; this file does not import `ZInQKernel.Contrib.G15`, whose
  `Contrib.Different.Local` clashes with `HDecomp.Textbook.Different` in the scratch assembly).

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
`jQ : ℚ̄ → ℚ̄_p`, some finite Galois `F ⊆ ℚ̄_p` contains `jQ M` and has `e(F/ℚ_p) ≤ [M:ℚ]!`; if
`M/ℚ` is Galois, `[F:ℚ_p] ≤ [M:ℚ]` and `F` lies in every subfield containing `jQ M`. -/
theorem exists_galois_closure (jQ : AlgebraicClosure ℚ →+* Kbar p)
    (M : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ M] :
    ∃ F : Fld p, IsFinGal F ∧ (∀ x ∈ M, jQ x ∈ F) ∧
      ramCard F 0 ≤ (Module.finrank ℚ M).factorial ∧
      (IsGalois ℚ M → Module.finrank ℚ_[p] F ≤ Module.finrank ℚ M ∧
        ∀ F' : Fld p, (∀ x ∈ M, jQ x ∈ F') → ∀ z ∈ F, z ∈ F') := by
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
  -- `M` maps into any `ℚ_p`-subfield containing `y`
  have hMin : ∀ E : Fld p, y ∈ E → ∀ x ∈ M, jQ x ∈ E := by
    intro E hyE
    let G : IntermediateField ℚ (AlgebraicClosure ℚ) :=
      (E.restrictScalars ℚ).comap jQ.toRatAlgHom
    have haG : a ∈ G := hyE
    have hle : IntermediateField.adjoin ℚ {a} ≤ G :=
      IntermediateField.adjoin_simple_le_iff.mpr haG
    intro x hx
    have hx' : x ∈ (IntermediateField.adjoin ℚ ({α} : Set M)).map M.val := by
      rw [hα]
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at hx'
    exact hle hx'
  refine ⟨F, hFG, hMin F hyF, ?_, ?_⟩
  · calc ramCard F 0 ≤ Module.finrank ℚ_[p] F := ramCard_le_finrank F hFG
      _ ≤ f.natDegree.factorial := PkgI6.finrank_isSplittingField_le_factorial f hsep
      _ ≤ (Module.finrank ℚ M).factorial := Nat.factorial_le hdeg
  · intro hMgal
    -- every root of `f` is `jQ b` with `b ∈ M`
    have hroots : ∀ r ∈ f.rootSet (Kbar p), ∃ b ∈ M, jQ b = r := by
      intro r hr
      have hr0 : aeval r f = 0 := ((mem_rootSet_of_ne hf0).mp hr)
      have hr1 : aeval r (minpoly ℚ a) = 0 := by
        obtain ⟨g, hg⟩ := hdvd
        have := congrArg (aeval r) hg
        rw [aeval_map_algebraMap, map_mul, hr0, zero_mul] at this
        exact this
      have hspl : ((minpoly ℚ α).map (algebraMap ℚ M)).Splits :=
        Normal.splits (IsGalois.to_normal) α
      have hne : (minpoly ℚ α).map (algebraMap ℚ M) ≠ 0 := map_ne_zero (minpoly.ne_zero
        (Algebra.IsIntegral.isIntegral α))
      have hroot : (((minpoly ℚ α).map (algebraMap ℚ M)).map (jQ.comp M.val.toRingHom)).IsRoot r := by
        rw [Polynomial.map_map, IsRoot, IntermediateField.minpoly_eq,
          show (jQ.comp M.val.toRingHom).comp (algebraMap ℚ M) = algebraMap ℚ (Kbar p) from
            RingHom.ext_rat _ _, eval_map_algebraMap]
        exact hr1
      obtain ⟨b, hb⟩ := hspl.mem_range_of_isRoot hne hroot
      exact ⟨b, b.2, hb⟩
    have hFle : ∀ F' : Fld p, (∀ x ∈ M, jQ x ∈ F') → F ≤ F' := by
      intro F' hF'
      rw [IntermediateField.adjoin_le_iff]
      intro r hr
      obtain ⟨b, hbM, rfl⟩ := hroots r hr
      exact hF' b hbM
    refine ⟨?_, fun F' hF' z hz => hFle F' hF' hz⟩
    have hFy : F ≤ IntermediateField.adjoin ℚ_[p] {y} :=
      hFle _ (hMin _ (IntermediateField.mem_adjoin_simple_self ℚ_[p] y))
    haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] {y}) :=
      IntermediateField.adjoin.finiteDimensional hyi
    calc Module.finrank ℚ_[p] F ≤ Module.finrank ℚ_[p] (IntermediateField.adjoin ℚ_[p] {y}) :=
          IntermediateField.finrank_le_of_le_right hFy
      _ = f.natDegree := IntermediateField.adjoin.finrank hyi
      _ ≤ Module.finrank ℚ M := hdeg

/-- The embedding `ℚ̄ → ℚ̄_p` underlying `PkgI4.decomp p` (copied from g15-decomp's
`ZInQ.Contrib.G15.Ladic.decomp_spec`): it intertwines `decomp p σ` with `σ`. -/
theorem decomp_spec (p : ℕ) [Fact p.Prime] : ∃ jQ : PkgI4.Qbar →+* PadicAlgCl p,
    ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) x, jQ (PkgI4.decomp p σ x) = σ (jQ x) := by
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  letI g : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p] := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[p]) := g.toAlgebra
  refine ⟨g.toRingHom, fun σ x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes ((AlgEquiv.restrictScalarsHom ℚ) σ)
    (AlgebraicClosure ℚ) x

end ZInQ.Contrib.G8Local

end
