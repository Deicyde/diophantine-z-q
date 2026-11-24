import ZInQKernel.Contrib.CloudR2Poincare.L4.DimensionTopology

/-!
# Finite dimension of a compact scheme locally of finite type over a field

H-72 round 2, lane L4. Mathlib-only input: an affine finite-type `k`-algebra is a
quotient of a polynomial ring in finitely many variables. A finite affine open
cover of the compact scheme then gives a finite global dimension bound.

SOURCE / CHANGE NOTICE: the finite-type ring bound follows the proof in
AxiomMath/Stacks `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
`StacksFrontier/RingTheory/KrullDimension/FiniteTypeNeTop.lean` (Apache-2.0;
`LICENSE.Stacks` accompanies this contribution). We inline that elementary
Mathlib-only ring argument in an affine-open lemma and prove the global open-cover
bound directly using Mathlib's irreducible-closed-set order isomorphism.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Set Order

noncomputable section

namespace ZInQ.Contrib.CloudR2Poincare.L4

set_option linter.style.haveILetI false

/-- An open cover whose members all have dimension at most `n` bounds the dimension of the space. -/
theorem dimension_le_of_open_cover {X : Type*} [TopologicalSpace X] {ι : Type*}
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcov : ∀ x, ∃ i, x ∈ U i)
    {n : WithBot ℕ∞} (hn : ∀ i, topologicalKrullDim (U i) ≤ n) :
    topologicalKrullDim X ≤ n := by
  unfold topologicalKrullDim krullDim
  refine iSup_le fun p => ?_
  obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
  obtain ⟨i, hxi⟩ := hcov x
  let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding (Subtype.val : U i → X)
    (hU i).isOpenEmbedding_subtypeVal
  have hmem (j : Fin (p.length + 1)) :
      ((Subtype.val : U i → X) ⁻¹' (p j : Set X)).Nonempty :=
    ⟨⟨x, hxi⟩, p.monotone (Fin.zero_le j) hx⟩
  let q : LTSeries (IrreducibleCloseds (U i)) :=
    ⟨p.length, fun j => e.symm ⟨p j, hmem j⟩,
      fun j => e.symm.strictMono (show
        (⟨p j.castSucc, hmem j.castSucc⟩ : {C : IrreducibleCloseds X |
          ((Subtype.val : U i → X) ⁻¹' (C : Set X)).Nonempty}) <
          ⟨p j.succ, hmem j.succ⟩ from p.step j)⟩
  exact (LTSeries.length_le_krullDim q).trans (hn i)

/-- Every affine open of a scheme locally of finite type over a field has finite dimension. -/
theorem affineOpen_dimension_ne_top {k : Type} [Field k] {X : Scheme}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (U : X.affineOpens) :
    topologicalKrullDim (U.1 : Set X) ≠ ⊤ := by
  let g := (f.appLE ⊤ U.1 (by simp)).hom
  letI : Algebra k Γ(X, U.1) :=
    (g.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  haveI : Algebra.FiniteType k Γ(X, U.1) := by
    apply RingHom.FiniteType.comp
      (f.finiteType_appLE (isAffineOpen_top (Spec (.of k))) U.2 (by simp))
    exact RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective
  have hring : ringKrullDim Γ(X, U.1) ≠ ⊤ := by
    obtain ⟨ι, _, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp
      (inferInstance : Algebra.FiniteType k Γ(X, U.1))
    have h := ringKrullDim_le_of_surjective φ.toRingHom hφ
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      zero_add] at h
    refine ne_top_of_le_ne_top ?_ h
    rw [ENat.card_eq_coe_natCard]
    change ((Nat.card ι : ℕ∞) : WithBot ℕ∞) ≠ ((⊤ : ℕ∞) : WithBot ℕ∞)
    exact fun he => ENat.natCast_ne_top _ (WithBot.coe_eq_coe.mp he)
  have he : topologicalKrullDim (U.1 : Set X) = ringKrullDim Γ(X, U.1) := by
    calc
      topologicalKrullDim (U.1 : Set X) = topologicalKrullDim (Spec Γ(X, U.1)) :=
        IsHomeomorph.topologicalKrullDim_eq _ U.2.isoSpec.hom.homeomorph.isHomeomorph
      _ = ringKrullDim Γ(X, U.1) := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
  rw [he]
  exact hring

/-- A compact scheme locally of finite type over a field has finite topological Krull dimension. -/
theorem scheme_dimension_ne_top {k : Type} [Field k] {X : Scheme}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [CompactSpace X] :
    topologicalKrullDim X ≠ ⊤ := by
  classical
  obtain ⟨s, hs, hcov⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
    (show IsCompact (Set.univ : Set X) ∧ IsOpen (Set.univ : Set X) from
      ⟨isCompact_univ, isOpen_univ⟩)
  haveI : Finite s := hs.to_subtype
  letI := Fintype.ofFinite s
  have hn : ∀ U : s, ∃ n : ℕ, topologicalKrullDim (U.1.1 : Set X) ≤ (n : WithBot ℕ∞) := by
    intro U
    cases he : topologicalKrullDim (U.1.1 : Set X) with
    | bot => exact ⟨0, by simpa only [he] using
        (bot_le : (⊥ : WithBot ℕ∞) ≤ ((0 : ℕ) : WithBot ℕ∞))⟩
    | coe e =>
      cases e with
      | top => exact (affineOpen_dimension_ne_top f U.1 he).elim
      | coe n => exact ⟨n, le_rfl⟩
  choose n hn using hn
  let m := Finset.univ.sup n
  have hbound : topologicalKrullDim X ≤ (m : WithBot ℕ∞) := by
    refine dimension_le_of_open_cover (fun U : s => (U.1.1 : Set X))
      (fun U => U.1.1.isOpen) ?_ ?_
    · intro x
      have hx : x ∈ (⋃ U ∈ s, (U.1 : Set X)) := by rw [← hcov]; trivial
      obtain ⟨U, hUs, hxU⟩ := Set.mem_iUnion₂.mp hx
      exact ⟨⟨U, hUs⟩, hxU⟩
    · intro U
      exact (hn U).trans (by exact_mod_cast (Finset.le_sup (Finset.mem_univ U) : n U ≤ m))
  refine ne_top_of_le_ne_top ?_ hbound
  change ((m : ℕ∞) : WithBot ℕ∞) ≠ ((⊤ : ℕ∞) : WithBot ℕ∞)
  exact fun he => ENat.natCast_ne_top m (WithBot.coe_eq_coe.mp he)

end ZInQ.Contrib.CloudR2Poincare.L4
