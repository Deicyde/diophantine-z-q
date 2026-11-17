import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# A discrete subgroup with compact quotient is a full lattice

Pure Mathlib. For a finite-dimensional real normed space `E` and a `ℤ`-submodule `Λ ⊆ E`, compactness of
`E ⧸ Λ` forces `Λ` to span `E` over `ℝ`; with `DiscreteTopology Λ` this is `IsZLattice ℝ Λ`.

Mathlib has the converse (`IsZLattice.isCompact_range_of_periodic`, and `BPAnalytic.compactSpace_torus` in this
repository) but not this direction: `Mathlib/Algebra/Module/ZLattice/Basic.lean` produces `IsZLattice` only from
a basis (`instIsZLatticeRealSpan`).

* `CloudB3W17Lattice.span_top_of_compactSpace_quotient` — the span statement (no discreteness needed).
* `CloudB3W17Lattice.isZLattice_of_compactSpace_quotient` — the lattice form.
* `CloudB3W17Lattice.isZLattice_of_isOpenMap` — the supplier a uniformization route needs: a continuous, open,
  surjective additive homomorphism `π : E → X` onto a compact group, with kernel `Λ`, makes `Λ` a full lattice.
* `CloudB3W17Lattice.discreteTopology_of_injOn` — the kernel of such a `π` is discrete as soon as `π` is injective
  on a neighbourhood of `0` (the case of a local homeomorphism, e.g. a local biholomorphism at `0`).
* `CloudB3W17Lattice.quotientContinuousAddEquiv` — the induced isomorphism of topological groups `E ⧸ Λ ≃ₜ+ X`.

Proof of the main statement: if `W = span ℝ Λ < ⊤`, a nonzero functional `f : E →ₗ[ℝ] ℝ` kills `W`
(`Submodule.exists_le_ker_of_lt_top`), hence kills `Λ` and descends to a continuous `F : E ⧸ Λ → ℝ`; `f ≠ 0` makes
`F` surjective, so `ℝ` is a continuous image of a compact space, contradicting `NoncompactSpace ℝ`.
-/

set_option linter.unusedSectionVars false

namespace CloudB3W17Lattice

open Set Submodule

section SpanTop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A nonzero `ℝ`-linear functional on a real vector space is surjective. -/
theorem surjective_of_ne_zero {f : E →ₗ[ℝ] ℝ} (hf : f ≠ 0) : Function.Surjective f := by
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hf
  simp only [LinearMap.zero_apply] at hv
  intro r
  exact ⟨(r / f v) • v, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]⟩

/-- **A submodule with compact quotient spans.** If the quotient of a finite-dimensional real normed space
`E` by a `ℤ`-submodule `Λ` is compact, then `Λ` spans `E` over `ℝ`. Discreteness is not needed. -/
theorem span_top_of_compactSpace_quotient (Λ : Submodule ℤ E)
    [CompactSpace (E ⧸ Λ.toAddSubgroup)] : span ℝ (Λ : Set E) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hker⟩ :=
    Submodule.exists_le_ker_of_lt_top (span ℝ (Λ : Set E)) (lt_top_iff_ne_top.mpr hne)
  have hvanish : ∀ x ∈ Λ.toAddSubgroup, f.toAddMonoidHom x = 0 := by
    intro x hx
    have hxΛ : x ∈ (Λ : Set E) := by simpa using hx
    exact hker (Submodule.subset_span hxΛ)
  set F : (E ⧸ Λ.toAddSubgroup) →+ ℝ :=
    QuotientAddGroup.lift Λ.toAddSubgroup f.toAddMonoidHom hvanish with hFdef
  have hFmk : ∀ x : E, F (QuotientAddGroup.mk x) = f x := fun _ => rfl
  have hFcont : Continuous F := by
    rw [(QuotientAddGroup.isQuotientMap_mk Λ.toAddSubgroup).continuous_iff]
    exact f.continuous_of_finiteDimensional
  have hFsurj : Function.Surjective F := by
    intro r
    obtain ⟨x, hx⟩ := surjective_of_ne_zero hf0 r
    exact ⟨QuotientAddGroup.mk x, by rw [hFmk, hx]⟩
  have hcomp : IsCompact (range F) := isCompact_range hFcont
  rw [hFsurj.range_eq] at hcomp
  exact noncompact_univ ℝ hcomp

/-- **A discrete subgroup with compact quotient is a full lattice.** -/
theorem isZLattice_of_compactSpace_quotient (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [CompactSpace (E ⧸ Λ.toAddSubgroup)] : IsZLattice ℝ Λ :=
  ⟨span_top_of_compactSpace_quotient Λ⟩

end SpanTop

section Supplier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : Type*} [TopologicalSpace X] [AddGroup X]
  (Λ : Submodule ℤ E) (π : E →+ X) (hker : ∀ x, π x = 0 ↔ x ∈ Λ)

include hker

/-- The map `E ⧸ Λ → X` induced by a homomorphism `π` whose kernel is `Λ`. -/
def liftKer : (E ⧸ Λ.toAddSubgroup) →+ X :=
  QuotientAddGroup.lift Λ.toAddSubgroup π (fun x hx => (hker x).mpr (by simpa using hx))

@[simp] theorem liftKer_mk (x : E) : liftKer Λ π hker (QuotientAddGroup.mk x) = π x := rfl

theorem liftKer_injective : Function.Injective (liftKer Λ π hker) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [liftKer_mk] at hq
  exact (QuotientAddGroup.eq_zero_iff x).mpr (by simpa using (hker x).mp hq)

theorem liftKer_surjective (hsurj : Function.Surjective π) :
    Function.Surjective (liftKer Λ π hker) := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  exact ⟨QuotientAddGroup.mk x, rfl⟩

theorem liftKer_bijective (hsurj : Function.Surjective π) :
    Function.Bijective (liftKer Λ π hker) :=
  ⟨liftKer_injective Λ π hker, liftKer_surjective Λ π hker hsurj⟩

theorem liftKer_continuous (hcont : Continuous π) : Continuous (liftKer Λ π hker) := by
  rw [(QuotientAddGroup.isQuotientMap_mk Λ.toAddSubgroup).continuous_iff]
  exact hcont

theorem liftKer_isOpenMap (hopen : IsOpenMap π) : IsOpenMap (liftKer Λ π hker) := by
  intro U hU
  have himg : liftKer Λ π hker '' U
      = π '' ((QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) ⁻¹' U) := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
      exact ⟨x, hq, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨QuotientAddGroup.mk x, hx, rfl⟩
  rw [himg]
  exact hopen _ (hU.preimage QuotientAddGroup.continuous_mk)

/-- `E ⧸ Λ ≃ₜ X` for a continuous open surjective `π : E → X` with kernel `Λ`. -/
noncomputable def liftKerHomeomorph (hcont : Continuous π) (hopen : IsOpenMap π)
    (hsurj : Function.Surjective π) : (E ⧸ Λ.toAddSubgroup) ≃ₜ X :=
  (Equiv.ofBijective _ (liftKer_bijective Λ π hker hsurj)).toHomeomorphOfContinuousOpen
    (liftKer_continuous Λ π hker hcont) (liftKer_isOpenMap Λ π hker hopen)

/-- **The induced isomorphism of topological groups** `E ⧸ Λ ≃ₜ+ X`. -/
noncomputable def quotientContinuousAddEquiv (hcont : Continuous π) (hopen : IsOpenMap π)
    (hsurj : Function.Surjective π) : (E ⧸ Λ.toAddSubgroup) ≃ₜ+ X where
  toEquiv := Equiv.ofBijective _ (liftKer_bijective Λ π hker hsurj)
  map_add' a b := map_add (liftKer Λ π hker) a b
  continuous_toFun := (liftKerHomeomorph Λ π hker hcont hopen hsurj).continuous_toFun
  continuous_invFun := (liftKerHomeomorph Λ π hker hcont hopen hsurj).continuous_invFun

/-- The quotient is compact when the target is. -/
theorem compactSpace_quotient [CompactSpace X] (hcont : Continuous π) (hopen : IsOpenMap π)
    (hsurj : Function.Surjective π) : CompactSpace (E ⧸ Λ.toAddSubgroup) :=
  (liftKerHomeomorph Λ π hker hcont hopen hsurj).symm.compactSpace

/-- **Supplier for a uniformization route.** If `π : E → X` is a continuous, open, surjective homomorphism
onto a compact group and its kernel is the discrete submodule `Λ`, then `Λ` is a full lattice. -/
theorem isZLattice_of_isOpenMap [DiscreteTopology Λ] [CompactSpace X] (hcont : Continuous π)
    (hopen : IsOpenMap π) (hsurj : Function.Surjective π) : IsZLattice ℝ Λ := by
  have : CompactSpace (E ⧸ Λ.toAddSubgroup) := compactSpace_quotient Λ π hker hcont hopen hsurj
  exact isZLattice_of_compactSpace_quotient Λ

/-- **The kernel is discrete** as soon as `π` is injective on a neighbourhood of `0`. -/
theorem discreteTopology_of_injOn {U : Set E} (hU : U ∈ nhds (0 : E)) (hinj : Set.InjOn π U) :
    DiscreteTopology Λ := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  obtain ⟨V, hVU, hVopen, hV0⟩ := mem_nhds_iff.mp hU
  refine ⟨V, hVopen, ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hxV
    have hx0 : π (x : E) = 0 := (hker (x : E)).mpr x.2
    have hxz : (x : E) = (0 : E) := hinj (hVU hxV) (hVU hV0) (by rw [hx0, map_zero])
    exact Subtype.ext hxz
  · rintro rfl
    simpa using hV0

end Supplier

end CloudB3W17Lattice
