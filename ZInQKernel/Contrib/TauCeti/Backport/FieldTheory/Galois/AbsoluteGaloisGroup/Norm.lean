/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Norm), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Norm` (task ring-class).
module

public import ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Norm
public import ZInQKernel.Contrib.TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex
public import Mathlib.FieldTheory.IsAlgClosed.Basic

public section

noncomputable section

namespace TauCeti

open IntermediateField

variable (K : Type*) [Field K]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section Relative

variable {K} {E E' : IntermediateField K (SeparableClosure K)} [Algebra E E']
  [IsScalarTower E E' (SeparableClosure K)] [FiniteDimensional E E']
  {W W' : OpenSubgroup (AbsoluteGaloisGroup K)}


/-- **The relative norm of `E'/E` is the product of the conjugates over `G_E`**: if `W` and `W'`
are open subgroups of `G_K` with fixed fields `E ⊆ E'`, then the norm `N_{E'/E} x`, read in `Kˢ`,
is the product of the translates of `x` by representatives of the cosets of `W'` in `W`. The
extension `E'/E` need not be normal. -/
theorem coe_norm_eq_prod_quotient_out (hW : fixedField W.toSubgroup = E)
    (hW' : fixedField W'.toSubgroup = E') (x : E') :
    ((Algebra.norm E x : E) : SeparableClosure K) =
      ∏ q : W.toSubgroup ⧸ W'.toSubgroup.subgroupOf W.toSubgroup,
        (q.out : AbsoluteGaloisGroup K) (x : SeparableClosure K) := by
  let φ := IsScalarTower.toAlgHom E E' (SeparableClosure K)
  have : IsGalois E (SeparableClosure K) := IsGalois.tower_top_of_isGalois K E _
  have := Algebra.IsSeparable.of_algHom E (SeparableClosure K) φ
  have hsplits : ∀ y : E', ((minpoly E y).map (algebraMap E (SeparableClosure K))).Splits :=
    fun y => IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable E y)
  -- `W` is `Gal(Kˢ/E)`, and under this identification `W'` is the subgroup fixing `φ(E') = E'`.
  let e : W.toSubgroup ≃* (SeparableClosure K ≃ₐ[E] SeparableClosure K) :=
    (MulEquiv.subgroupCongr (toSubgroup_eq_fixingSubgroup_of_fixedField_eq hW)).trans
      E.fixingSubgroupEquiv
  have he (g : W.toSubgroup) (y : SeparableClosure K) : e g y = (g : AbsoluteGaloisGroup K) y := by
    rw [MulEquiv.trans_apply, IntermediateField.coe_fixingSubgroupEquiv_apply,
      MulEquiv.subgroupCongr_apply]
  have hmem (g : W.toSubgroup) :
      g ∈ W'.toSubgroup.subgroupOf W.toSubgroup ↔ e g ∈ φ.fieldRange.fixingSubgroup := by
    rw [Subgroup.mem_subgroupOf, toSubgroup_eq_fixingSubgroup_of_fixedField_eq hW',
      IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
    refine ⟨fun h ↦ ?_, fun h y hy ↦ h y ⟨⟨y, hy⟩, rfl⟩⟩
    rintro _ ⟨y, rfl⟩
    exact h _ y.2
  -- The cosets of `W'` in `W` are the `E`-embeddings of `E'` in `Kˢ`, and those in an algebraic
  -- closure of `Kˢ`.
  let f : W.toSubgroup ⧸ W'.toSubgroup.subgroupOf W.toSubgroup ≃
      (E' →ₐ[E] AlgebraicClosure (SeparableClosure K)) := (Quotient.congr e.toEquiv fun a b ↦ by
      rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, hmem, map_mul, map_inv]
      -- `e.toEquiv` is `e` as a function.
      rfl).trans
    ((FieldTheory.fixingSubgroupQuotientEquivAlgHom φ).trans
      (Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits (AlgebraicClosure (SeparableClosure K))
        (SeparableClosure K) hsplits))
  refine (algebraMap (SeparableClosure K) (AlgebraicClosure (SeparableClosure K))).injective ?_
  rw [map_prod, ← IntermediateField.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply E (SeparableClosure K),
    Algebra.norm_eq_prod_embeddings (K := E) (L := E') (E := AlgebraicClosure (SeparableClosure K))]
  refine (Fintype.prod_equiv f _ _ fun q ↦ ?_).symm
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  -- `f` sends the coset of `g` to the embedding `e g ∘ φ`, read in the algebraic closure; the
  -- first step, the coset of `g` to the coset of `e g`, is `Quotient.congr` on a representative,
  -- and `e g` acts on `Kˢ` as `g` by `he`.
  rw [Equiv.trans_apply, Equiv.trans_apply,
    Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits_apply_apply]
  exact congrArg (algebraMap _ _) ((congrArg (· x)
    (FieldTheory.fixingSubgroupQuotientEquivAlgHom_mk φ (e q.out))).trans (he q.out x)).symm

end Relative

end TauCeti
