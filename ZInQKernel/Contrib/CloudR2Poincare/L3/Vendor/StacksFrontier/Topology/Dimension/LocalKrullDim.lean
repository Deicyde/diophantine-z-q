import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.Topology.Dimension.CodimensionOpen
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.Topology.Dimension.Krull

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.Topology.Dimension.LocalKrullDim`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory



/-!
# Local Krull dimension at a point (Stacks 0B7I)

Mathlib's `topologicalKrullDim X` is the supremum of the lengths of chains
`Z₀ ⊊ Z₁ ⊊ ⋯ ⊊ Zₙ` of irreducible closed subsets of `X`, taken in
`WithBot ℕ∞ ≃ {-∞} ∪ ℤ≥0 ∪ {+∞}` (so `topologicalKrullDim ∅ = ⊥ = -∞`).

This file introduces the *local* dimension of `X` at a point `x`, namely
`TopologicalSpace.localKrullDim X x = ⨅ {topologicalKrullDim U | U open, x ∈ U}`,
and proves the Stacks Project's identity
`topologicalKrullDim X = ⨆ x, localKrullDim X x`.

The `≤` direction is the only substantial one: given a chain `p` of irreducible
closed subsets of `X`, any point `x` of its bottom member lies in every member,
so intersecting the chain with an open neighbourhood `U` of `x` produces a chain
of irreducible closed subsets of `U` *of the same length* — the strictness of each
inclusion survives because an irreducible set meets every pair of open sets it
meets separately. The `≥` direction is `U := Set.univ`. No separation or
finiteness hypotheses are needed, and the empty space is covered automatically:
both sides are then `⊥`, the supremum over an empty index type.

`localKrullDim` and `topologicalKrullDimAt` (Stacks 0055 (4), in
`StacksFrontier.Topology.Dimension.Krull`) are two encodings of one infimum: the first is an
iterated infimum over an open set together with its two defining properties, the second an
infimum over the subtype of open neighbourhoods. `topologicalKrullDimAt_eq_localKrullDim`
identifies them, and is why this file imports that one.
-/


namespace TopologicalSpace
#cloudR2Vendor localKrullDim in

/-- The *local Krull dimension* of a topological space `X` at a point `x`, defined
as the infimum of `topologicalKrullDim U` over all open neighbourhoods `U` of `x`.
The value lives in `WithBot ℕ∞ ≃ {-∞} ∪ ℤ≥0 ∪ {+∞}`. -/

noncomputable def localKrullDim (X : Type*) [TopologicalSpace X] (x : X) : WithBot ℕ∞ :=
  ⨅ (U : Set X) (_ : IsOpen U) (_ : x ∈ U), topologicalKrullDim U
#cloudR2Vendor topologicalKrullDimAt_eq_localKrullDim in

/-- `topologicalKrullDimAt` and `localKrullDim` are the same infimum, written once as an
infimum over the subtype of open neighbourhoods of `x` and once as an iterated infimum over an
open set together with its two defining properties. Each side is below the other because each
index of one infimum supplies an index of the other. -/
theorem topologicalKrullDimAt_eq_localKrullDim (X : Type*) [TopologicalSpace X] (x : X) :
    topologicalKrullDimAt X x = localKrullDim X x :=
  le_antisymm
    (le_iInf fun U => le_iInf fun hU => le_iInf fun hxU =>
      iInf_le (fun V : {V : Set X // x ∈ V ∧ IsOpen V} => topologicalKrullDim (↥V.val))
        ⟨U, hxU, hU⟩)
    (le_iInf fun U => iInf_le_of_le U.1 (iInf_le_of_le U.2.2 (iInf_le _ U.2.1)))
#cloudR2Vendor restrictOpen_carrier_ssubset in

/-- Restriction to an open subset is strictly monotone on irreducible closed subsets that meet it:
if `Z₁ ⊊ Z₂` and both meet `U`, the restrictions are again strictly nested. Since `Z₁` is a proper
closed subset of the irreducible `Z₂`, the set `Z₂ \ Z₁` is a nonempty open subset of `Z₂`; as
`Z₂ ∩ U` is another one, preirreducibility of `Z₂` makes them meet, and a common point witnesses
the strict inclusion. -/
private lemma restrictOpen_carrier_ssubset {X : Type*} [TopologicalSpace X]
    (Z₁ Z₂ : IrreducibleCloseds X) {U : Set X} (hU : IsOpen U)
    (h12 : Z₁.carrier ⊂ Z₂.carrier)
    (hZ₁U : (Z₁.carrier ∩ U).Nonempty) (hZ₂U : (Z₂.carrier ∩ U).Nonempty) :
    (Z₁.restrictOpen hU hZ₁U).carrier ⊂ (Z₂.restrictOpen hU hZ₂U).carrier := by
  simp only [IrreducibleCloseds.restrictOpen]
  constructor
  · intro ⟨y, hy_in_U⟩ hy₁
    exact h12.subset hy₁
  · have hpre := Z₂.isIrreducible'.isPreirreducible
    have hopen_compl : IsOpen Z₁.carrier.compl := Z₁.isClosed'.isOpen_compl
    have hZ₂_compl_ne : (Z₂.carrier ∩ Z₁.carrier.compl).Nonempty := by
      obtain ⟨y, hy₂, hy₁⟩ := Set.exists_of_ssubset h12
      exact ⟨y, hy₂, hy₁⟩
    have hmeet := hpre U Z₁.carrier.compl hU hopen_compl hZ₂U hZ₂_compl_ne
    obtain ⟨y, hy₂, hyU, hy_not_Z₁⟩ := hmeet
    intro h_sub
    have : (⟨y, hyU⟩ : ↥U) ∈ Subtype.val ⁻¹' Z₂.carrier := hy₂
    have : (⟨y, hyU⟩ : ↥U) ∈ Subtype.val ⁻¹' Z₁.carrier := h_sub this
    exact hy_not_Z₁ this
#cloudR2Vendor length_le_topologicalKrullDim_of_mem in

/-- Restricting a chain of irreducible closed subsets to an open set containing a point
of its bottom member gives a chain of the same length in the subspace, so the chain's
length bounds the dimension of the subspace. -/
lemma length_le_topologicalKrullDim_of_mem {X : Type*} [TopologicalSpace X]
    (p : LTSeries (IrreducibleCloseds X))
    (U : Set X) (hU : IsOpen U) (x : X) (hxU : x ∈ U)
    (hx : x ∈ (RelSeries.head p).carrier) :
    (p.length : WithBot ℕ∞) ≤ topologicalKrullDim ↥U := by
  have hx_in_all : ∀ i : Fin (p.length + 1), x ∈ (p.toFun i).carrier :=
    fun i => (LTSeries.monotone p (Fin.zero_le i)) hx
  have hU_meet : ∀ i : Fin (p.length + 1), ((p.toFun i).carrier ∩ U).Nonempty :=
    fun i => ⟨x, hx_in_all i, hxU⟩
  let q : LTSeries (IrreducibleCloseds ↥U) :=
    { length := p.length
      toFun := fun i => (p.toFun i).restrictOpen hU (hU_meet i)
      step := fun i =>
        restrictOpen_carrier_ssubset (p.toFun i.castSucc) (p.toFun i.succ) hU
          (p.step i) (hU_meet i.castSucc) (hU_meet i.succ) }
  calc (p.length : WithBot ℕ∞) = (q.length : WithBot ℕ∞) := rfl
    _ ≤ topologicalKrullDim ↥U := by
        unfold topologicalKrullDim Order.krullDim
        exact le_iSup (fun (s : LTSeries (IrreducibleCloseds ↥U)) =>
          (s.length : WithBot ℕ∞)) q
#cloudR2Vendor topologicalKrullDim_eq_iSup_localKrullDim in

/-- **Stacks 0B7I.** The Krull dimension of a topological space is the supremum of its
local Krull dimensions over all of its points. When `X` is empty both sides are `⊥ = -∞`. -/

theorem topologicalKrullDim_eq_iSup_localKrullDim (X : Type*) [TopologicalSpace X] :
    topologicalKrullDim X = ⨆ x : X, localKrullDim X x := by
  apply le_antisymm
  · -- Every chain lives in every open neighbourhood of a point of its bottom member.
    unfold topologicalKrullDim Order.krullDim
    apply iSup_le
    intro p
    obtain ⟨x, hx⟩ := p.head.isIrreducible'.nonempty
    apply le_trans _ (le_iSup (localKrullDim X) x)
    unfold localKrullDim
    apply le_iInf; intro U
    apply le_iInf; intro hU
    apply le_iInf; intro hxU
    exact length_le_topologicalKrullDim_of_mem p U hU x hxU hx
  · -- `Set.univ` is an open neighbourhood of every point.
    apply iSup_le
    intro x
    unfold localKrullDim
    apply iInf_le_of_le Set.univ
    apply iInf_le_of_le isOpen_univ
    apply iInf_le_of_le (Set.mem_univ x)
    exact topologicalKrullDim_subspace_le X Set.univ

end TopologicalSpace


/-!
# Local dimension of a scheme at a point

`Scheme.localKrullDim X x` is the Krull dimension of the local ring `𝒪_{X,x}`. This is not
the Stacks notion `dim_x X` of Topology, Definition 0055 (4), which is the topological
`TopologicalSpace.localKrullDim` above. For `X = Spec S` and `x` the point of a maximal ideal
`m ⊆ S` it is `dim S_m` for every commutative ring `S`: the stalk of the structure sheaf at `m` is
the localization `S_m`, so `RingEquiv.ringKrullDim` applied to
`AlgebraicGeometry.StructureSheaf.stalkIso` transports the dimension across. Stacks 00OU, which
compares the topological `dim_x X` with `dim S_m` for `S` of finite type over a field, is
`PrimeSpectrum.localKrullDim_eq_ringKrullDim_localization_of_isMaximal` in
`StacksFrontier.RingTheory.Spectrum.Prime.LocalDimensionClosedPoint`.
-/


open _root_.AlgebraicGeometry _root_.CategoryTheory
open AlgebraicGeometry CategoryTheory
#cloudR2Vendor Scheme.localKrullDim in

/-- The Krull dimension of the local ring of a scheme `X` at a point `x`. This is not the
topological local dimension `dim_x X` of Stacks, Topology, Definition 0055 (4), which is
`TopologicalSpace.localKrullDim`. -/

noncomputable def Scheme.localKrullDim (X : Scheme) (x : X) : WithBot ℕ∞ :=
  ringKrullDim (X.presheaf.stalk x)
#cloudR2Vendor specClosedPoint in

/-- The closed point of `Spec S` associated to a maximal ideal `m ⊆ S`. -/

def specClosedPoint {S : Type*} [CommRing S] (m : Ideal S) [hm : m.IsMaximal] :
    (Spec (CommRingCat.of S) : Scheme) :=
  (⟨m, hm.isPrime⟩ : PrimeSpectrum S)
#cloudR2Vendor Scheme.localKrullDim_specClosedPoint in

/-- For a maximal ideal `m ⊆ S`, the Krull dimension of the stalk of `Spec S` at the closed point
of `m` equals the Krull dimension of `S_m`, the stalk being `S_m`. The hypothesis that `S` is of
finite type over a field `k` is not used. This is not Stacks 00OU, which concerns the topological
local dimension; that is
`PrimeSpectrum.localKrullDim_eq_ringKrullDim_localization_of_isMaximal`. -/
theorem Scheme.localKrullDim_specClosedPoint
    (k : Type*) [Field k]
    (S : Type*) [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (m : Ideal S) [hm : m.IsMaximal] :
    Scheme.localKrullDim (Spec (CommRingCat.of S)) (specClosedPoint m)
      = ringKrullDim (Localization.AtPrime m) :=
  (StructureSheaf.stalkIso S ⟨m, hm.isPrime⟩).toRingEquiv.ringKrullDim.symm


end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
