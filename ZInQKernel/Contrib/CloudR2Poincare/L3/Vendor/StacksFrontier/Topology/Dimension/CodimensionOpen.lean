import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.Topology.Dimension.CodimensionOpen`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory



/-!
# Codimension of an irreducible closed subset is local on an open subset

Let `X` be a topological space, let `Y ⊆ X` be an irreducible closed subset, and let `U ⊆ X` be
open with `Y ∩ U ≠ ∅`. Then `Y ∩ U` is an irreducible closed subset of the subspace `U`, and

    codim (Y, X) = codim (Y ∩ U, U).

## The encoding of codimension

There is no `codim` in Mathlib. Following Stacks 02I3, the codimension of an irreducible closed
subset `Y ⊆ X` is the supremum of the lengths `e` of strict chains

    Y = Y₀ ⊊ Y₁ ⊊ … ⊊ Y_e

of irreducible closed subsets of `X` starting at `Y`. That is exactly the *coheight* of `Y` in the
poset `TopologicalSpace.IrreducibleCloseds X`, ordered by inclusion: `Order.coheight` of an element
of a preorder is the supremum of the lengths of strict chains ascending from it. So throughout,
`codim (Y, X)` is spelled `Order.coheight (Y : TopologicalSpace.IrreducibleCloseds X)`.

Irreducible closed subsets of the subspace `U` are, via `Subtype.val ⁻¹' ·` and `closure`, in
inclusion-preserving bijection with the irreducible closed subsets of `X` that meet `U`
(`TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding`). Under that bijection `Y`
corresponds to `Y ∩ U`, and the statement above is the invariance of coheight under an order
isomorphism onto an upward-closed piece of the poset.

## Main definitions

* `TopologicalSpace.IrreducibleCloseds.comapOpenEmbedding`: the irreducible closed subset
  `f ⁻¹' Y` of `W`, for `f : W → X` an open embedding whose image meets the irreducible closed
  subset `Y` of `X`.
* `TopologicalSpace.IrreducibleCloseds.restrictOpen`: the irreducible closed subset `Y ∩ U` of the
  subspace `U`, for `Y` an irreducible closed subset of `X` meeting the open set `U`. It is the
  case `f = Subtype.val` of the previous one.

## Main results

* `TopologicalSpace.IrreducibleCloseds.coheight_comapOpenEmbedding` and
  `TopologicalSpace.IrreducibleCloseds.coheight_restrictOpen`: Stacks 02I4, the equality
  `codim (Y, X) = codim (Y ∩ U, U)`, for an arbitrary open embedding and for a subspace.

## Implementation notes

The proof goes through `Topology.IsOpenEmbedding.coheight_map`, which carries no separation or
sobriety hypotheses; this matches Stacks, which imposes none. The variant
`Topology.IsOpenEmbedding.coheight_eq` needs `[QuasiSober] [T0Space]` on both spaces because it
speaks about *points* under the specialization order, and is not used here.

Mathlib's `AlgebraicGeometry.coheight_eq_of_isOpenImmersion` is the scheme-level corollary,
about the coheight of a *point* of a scheme in the specialization order along an open immersion.
The topological statement of 02I4 — about irreducible closed subsets of an arbitrary topological
space — is the one proved here.
-/


open _root_.Set _root_.Topology _root_.TopologicalSpace
open Set Topology TopologicalSpace

namespace TopologicalSpace.IrreducibleCloseds

variable {X : Type*} [TopologicalSpace X] {U : Set X}

section OpenEmbedding

variable {W : Type*} [TopologicalSpace W] {f : W → X}
#cloudR2Vendor comapOpenEmbedding in

/-- For `Y` an irreducible closed subset of `X` and `f : W → X` an open embedding whose image
meets `Y`, the trace `f ⁻¹' Y`, viewed as an irreducible closed subset of `W`.

It is closed because `Y` is closed and `f` is continuous, and irreducible because a nonempty
preimage of an irreducible set under an open embedding is preirreducible. -/
def comapOpenEmbedding (Y : IrreducibleCloseds X) (hf : IsOpenEmbedding f)
    (h : (f ⁻¹' (Y : Set X)).Nonempty) : IrreducibleCloseds W where
  carrier := f ⁻¹' (Y : Set X)
  isIrreducible' := ⟨h, Y.isIrreducible.isPreirreducible.preimage hf⟩
  isClosed' := Y.isClosed.preimage hf.continuous
#cloudR2Vendor coe_comapOpenEmbedding in

/-- The underlying set of `Y.comapOpenEmbedding hf h` is the preimage `f ⁻¹' Y`. -/
@[simp]
lemma coe_comapOpenEmbedding (Y : IrreducibleCloseds X) (hf : IsOpenEmbedding f)
    (h : (f ⁻¹' (Y : Set X)).Nonempty) :
    (Y.comapOpenEmbedding hf h : Set W) = f ⁻¹' (Y : Set X) :=
  rfl
#cloudR2Vendor map_comapOpenEmbedding in

/-- The closure in `X` of the trace of `Y` is `Y` again: an irreducible closed set is the closure
of its intersection with any open set meeting it. -/
lemma map_comapOpenEmbedding (Y : IrreducibleCloseds X) (hf : IsOpenEmbedding f)
    (h : (f ⁻¹' (Y : Set X)).Nonempty) :
    map f hf.continuous (Y.comapOpenEmbedding hf h) = Y :=
  SetLike.coe_injective <| closure_image_preimage_of_isPreirreducible f hf.isOpenMap
    (Y : Set X) h Y.isIrreducible.isPreirreducible Y.isClosed
#cloudR2Vendor coheight_comapOpenEmbedding in

/-- For an open embedding `f : W → X`, the codimension of an irreducible closed subset `Y ⊆ X`
meeting the image of `f` equals the codimension of its trace `f ⁻¹' Y` in `W`. No sobriety
or separation hypothesis is needed. -/

theorem coheight_comapOpenEmbedding (Y : IrreducibleCloseds X) (hf : IsOpenEmbedding f)
    (h : (f ⁻¹' (Y : Set X)).Nonempty) :
    Order.coheight Y = Order.coheight (Y.comapOpenEmbedding hf h) := by
  conv_lhs => rw [← Y.map_comapOpenEmbedding hf h]
  exact hf.coheight_map (Y.comapOpenEmbedding hf h)

end OpenEmbedding

omit [TopologicalSpace X] in
#cloudR2Vendor nonempty_preimage_val_of_inter_nonempty in
/-- A point of `Y ∩ U` is a point of the subspace `U` lying in `Y`, so `Y ∩ U ≠ ∅` says exactly
that the trace of `Y` on `U` is nonempty. -/
lemma nonempty_preimage_val_of_inter_nonempty {Y : Set X}
    (h : (Y ∩ U).Nonempty) : (Subtype.val ⁻¹' Y : Set U).Nonempty :=
  let ⟨_, hxY, hxU⟩ := h; ⟨⟨_, hxU⟩, hxY⟩
#cloudR2Vendor restrictOpen in

/-- For `Y` an irreducible closed subset of `X` and `U ⊆ X` open with `Y ∩ U` nonempty, the
intersection `Y ∩ U`, viewed as an irreducible closed subset of the subspace `U`.

Concretely the carrier is `Subtype.val ⁻¹' Y`, whose image in `X` is `Y ∩ U`
(`IrreducibleCloseds.image_coe_restrictOpen`). It is closed in `U` because `Y` is closed in `X`,
and irreducible because the preimage of an irreducible set under an open embedding is
preirreducible once it is nonempty. -/

def restrictOpen (Y : IrreducibleCloseds X) (hU : IsOpen U)
    (h : ((Y : Set X) ∩ U).Nonempty) : IrreducibleCloseds U :=
  Y.comapOpenEmbedding hU.isOpenEmbedding_subtypeVal
    (nonempty_preimage_val_of_inter_nonempty h)
#cloudR2Vendor coe_restrictOpen in

/-- The underlying set of `Y.restrictOpen hU h` is the preimage `Subtype.val ⁻¹' Y` in `U`. -/
@[simp]
lemma coe_restrictOpen (Y : IrreducibleCloseds X) (hU : IsOpen U)
    (h : ((Y : Set X) ∩ U).Nonempty) :
    (Y.restrictOpen hU h : Set U) = Subtype.val ⁻¹' (Y : Set X) :=
  rfl
#cloudR2Vendor image_coe_restrictOpen in

/-- The image of `Y.restrictOpen hU h` in `X` is `Y ∩ U`. -/
@[simp]
lemma image_coe_restrictOpen (Y : IrreducibleCloseds X) (hU : IsOpen U)
    (h : ((Y : Set X) ∩ U).Nonempty) :
    Subtype.val '' (Y.restrictOpen hU h : Set U) = (Y : Set X) ∩ U := by
  simp [inter_comm]
#cloudR2Vendor map_subtypeVal_restrictOpen in

/-- The closure in `X` of `Y ∩ U` is `Y`, for `Y` irreducible closed in `X` and `U ⊆ X` open
meeting `Y`. -/
lemma map_subtypeVal_restrictOpen (Y : IrreducibleCloseds X) (hU : IsOpen U)
    (h : ((Y : Set X) ∩ U).Nonempty) :
    map (Subtype.val : U → X) continuous_subtype_val (Y.restrictOpen hU h) = Y :=
  Y.map_comapOpenEmbedding hU.isOpenEmbedding_subtypeVal _
#cloudR2Vendor coheight_restrictOpen in

/-- **Stacks 02I4**.
Let `X` be a topological space, `Y ⊆ X` an irreducible closed subset and `U ⊆ X` an open subset
with `Y ∩ U ≠ ∅`. Then the codimension of `Y` in `X` equals the codimension of `Y ∩ U` in `U`:

    codim (Y, X) = codim (Y ∩ U, U).

Codimension is `Order.coheight` in the poset of irreducible closed subsets; see the module
docstring. No sobriety or separation hypothesis is needed. -/

theorem coheight_restrictOpen (Y : IrreducibleCloseds X) (hU : IsOpen U)
    (h : ((Y : Set X) ∩ U).Nonempty) :
    Order.coheight Y = Order.coheight (Y.restrictOpen hU h) :=
  Y.coheight_comapOpenEmbedding hU.isOpenEmbedding_subtypeVal _

end TopologicalSpace.IrreducibleCloseds

end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
