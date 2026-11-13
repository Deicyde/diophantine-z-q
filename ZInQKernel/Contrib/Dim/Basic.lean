import Mathlib

/-!
# Krull dimension of spaces and schemes: covers, isomorphisms, specializing maps

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task dim-contrib, 2026-11-13,
adopting tasks g0-dim, g0-reverseisog, infra-smooth-dim and curve-infra). Mathlib only.

## Main results

* `ZInQ.Contrib.Dim.topologicalKrullDim_eq_iSup_of_isOpenEmbedding`: the Krull dimension of a
  space covered by open embeddings is the supremum of the dimensions of the pieces.
* `ZInQ.Contrib.Dim.topologicalKrullDim_scheme_eq_iSup_cover`: the same for an open cover of a
  scheme.
* `ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_iso`, `ZInQ.Contrib.Dim.topologicalKrullDim_spec`.
* `ZInQ.Contrib.Dim.topologicalKrullDim_le_of_specializingMap`: a continuous, specializing,
  surjective map to a quasi-sober space does not lower the Krull dimension.
-/

namespace ZInQ.Contrib.Dim

open Order TopologicalSpace Topology

/-- The Krull dimension of a space is the supremum of the dimensions of the members of a cover
by open embeddings (Stacks 0055 for open covers; tag UNVERIFIED). -/
theorem topologicalKrullDim_eq_iSup_of_isOpenEmbedding {X : Type*} [TopologicalSpace X]
    {ι : Type*} {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] (f : ∀ i, Y i → X)
    (hf : ∀ i, IsOpenEmbedding (f i)) (hcov : ∀ x, ∃ i, x ∈ Set.range (f i)) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (Y i) := by
  apply le_antisymm
  · refine iSup_le fun p => ?_
    obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
    obtain ⟨i, y, rfl⟩ := hcov x
    let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding (f i) (hf i)
    have hmem : ∀ j, (f i ⁻¹' (p j : Set X)).Nonempty := fun j =>
      ⟨y, p.monotone (Fin.zero_le j) hx⟩
    let q : LTSeries {V : IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} :=
      { length := p.length
        toFun := fun j => ⟨p j, hmem j⟩
        step := fun j => p.step j }
    calc (p.length : WithBot ℕ∞) = q.length := rfl
      _ ≤ krullDim {V : IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} := q.length_le_krullDim
      _ = topologicalKrullDim (Y i) := (Order.krullDim_eq_of_orderIso e).symm
      _ ≤ ⨆ i, topologicalKrullDim (Y i) := le_iSup (fun i => topologicalKrullDim (Y i)) i
  · exact iSup_le fun i => (hf i).isInducing.topologicalKrullDim_le

section Specializing

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- `closure {x}` as an irreducible closed set. -/
def closureIrreducibleCloseds (x : X) : IrreducibleCloseds X :=
  ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩

/-- Chains of irreducible closed sets lift along a continuous, specializing map, ending at the
closure of any point over the generic point of the last member. -/
theorem exists_ltSeries_lift_of_specializingMap [QuasiSober Y] (f : X → Y) (hc : Continuous f)
    (hs : SpecializingMap f) (p : LTSeries (IrreducibleCloseds Y)) :
    ∀ x : X, IsGenericPoint (f x) (p.last : Set Y) →
      ∃ q : LTSeries (IrreducibleCloseds X), q.length = p.length ∧
        q.last = closureIrreducibleCloseds x := by
  induction p using RelSeries.inductionOn' with
  | singleton W =>
    intro x _
    exact ⟨RelSeries.singleton _ (closureIrreducibleCloseds x), rfl, rfl⟩
  | snoc p W hW ih =>
    intro x hx
    rw [RelSeries.last_snoc] at hx
    obtain ⟨w', hw'⟩ := QuasiSober.sober p.last.isIrreducible p.last.isClosed
    have hsub : (p.last : Set Y) ⊆ W := SetLike.coe_subset_coe.mpr hW.le
    have hspec : f x ⤳ w' := hx.specializes (hsub hw'.mem)
    obtain ⟨x', hxx', hfx'⟩ := hs hspec
    obtain ⟨q, hql, hqlast⟩ := ih x' (hfx' ▸ hw')
    have hlt : q.last < closureIrreducibleCloseds x := by
      rw [hqlast]
      refine lt_of_le_of_ne ?_ ?_
      · show closure {x'} ⊆ closure {x}
        exact specializes_iff_closure_subset.mp hxx'
      · intro heq
        have h1 : closure ({x'} : Set X) = closure {x} := congrArg SetLike.coe heq
        have h2 : x' ⤳ x := specializes_iff_closure_subset.mpr h1.symm.le
        have h3 : w' ⤳ f x := hfx' ▸ h2.map hc
        have h4 : (W : Set Y) ⊆ p.last := by
          rw [← hx.def, ← hw'.def]
          exact specializes_iff_closure_subset.mp h3
        exact hW.ne (SetLike.coe_injective (subset_antisymm hsub h4))
    refine ⟨q.snoc (closureIrreducibleCloseds x) hlt, ?_, RelSeries.last_snoc _ _ _⟩
    simp [hql]

/-- A continuous, specializing (for example closed), surjective map `f : X → Y` to a quasi-sober
space does not lower the Krull dimension: `dim Y ≤ dim X`. -/
theorem topologicalKrullDim_le_of_specializingMap [QuasiSober Y] (f : X → Y) (hc : Continuous f)
    (hs : SpecializingMap f) (hsurj : Function.Surjective f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  unfold topologicalKrullDim Order.krullDim
  refine iSup_le fun p => ?_
  obtain ⟨y, hy⟩ := QuasiSober.sober p.last.isIrreducible p.last.isClosed
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨q, hql, -⟩ := exists_ltSeries_lift_of_specializingMap f hc hs p x hy
  rw [← hql]
  exact le_iSup (fun q : LTSeries (IrreducibleCloseds X) =>
    ((q.length : ℕ∞) : WithBot ℕ∞)) q

end Specializing

section Scheme

open AlgebraicGeometry CategoryTheory

/-- The dimension of a scheme is the supremum of the dimensions of the members of an open
cover. -/
theorem topologicalKrullDim_scheme_eq_iSup_cover {X : Scheme} (𝒰 : X.OpenCover) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (𝒰.X i) :=
  topologicalKrullDim_eq_iSup_of_isOpenEmbedding (fun i => 𝒰.f i)
    (fun i => (𝒰.f i).isOpenEmbedding) (fun x => ⟨𝒰.idx x, 𝒰.covers x⟩)

/-- Isomorphic schemes have the same dimension. -/
theorem topologicalKrullDim_eq_of_iso {X Y : Scheme} (e : X ≅ Y) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph

/-- `dim Spec R = dim R`. -/
theorem topologicalKrullDim_spec (R : CommRingCat) :
    topologicalKrullDim (Spec R) = ringKrullDim R :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R

end Scheme

end ZInQ.Contrib.Dim
