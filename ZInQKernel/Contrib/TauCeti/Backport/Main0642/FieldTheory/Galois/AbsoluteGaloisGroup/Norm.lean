/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 0642eae29e0a, module
-- TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Norm), Apache-2.0: declarations of that module absent from its commit-5a01f5fe version, which
-- is vendored as `ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Norm, ZInQKernel.Contrib.TauCeti.Backport.FieldTheory.Galois.AbsoluteGaloisGroup.Norm` (task selmer-2infty).
-- Modified for the Z-in-Q kernel: declarations already in the vendored module removed; imports rewritten.
module

public import ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Norm
public import ZInQKernel.Contrib.TauCeti.Backport.FieldTheory.Galois.AbsoluteGaloisGroup.Norm
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import ZInQKernel.Contrib.TauCeti.FieldTheory.Normal.Embeddings
public import ZInQKernel.Contrib.TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# The norm of a finite subextension as a product over the absolute Galois group

Let `K` be a field, `Kˢ` a separable closure, `L/K` a finite extension and `σ : L →ₐ[K] Kˢ` a
`K`-embedding. Composing with `σ` identifies the coset space of the open subgroup
`Gal(Kˢ/σ(L))` cut out by `σ` with the set of `K`-embeddings of `L` into `Kˢ`,

```text
G_K ⧸ Gal(Kˢ/σ(L)) ≃ (L →ₐ[K] Kˢ),    g ↦ g ∘ σ,
```

which is `TauCeti.FieldTheory.fixingSubgroupQuotientEquivAlgHom` for the normal extension
`Kˢ / K`. Under that identification the classical formula "the norm is the product of the
conjugates" becomes a product over a system `t` of coset representatives:

```text
algebraMap K Kˢ (N_{L/K} b) = ∏ u : G_K ⧸ Gal(Kˢ/σ(L)), t u (σ b).
```

This is the shape in which the norm of a finite extension meets the cohomology of `G_K`, where a
sum `x ↦ ∑ u, t u • x` over a transversal is the standard degree-zero corestriction: on units of
`Kˢ` fixed by `Gal(Kˢ/σ(L))`, that sum is the norm of `L/K`.

Separability of `L/K` is not assumed. An embedding of `L` into a separable closure of `K` forces
it by Mathlib's `Algebra.IsSeparable.of_algHom`. Finiteness of `L/K` is used twice: it bounds the
index of `Gal(Kˢ/σ(L))` by `[L : K]`, so that the coset space is a finite index set, and it is the
hypothesis of Mathlib's product formula for the norm, `Algebra.norm_eq_prod_embeddings`.

The same holds relatively. For open subgroups `W` and `W'` of `G_K` with fixed fields `E ⊆ E'`,
the cosets of `W'` in `W` are the `E`-embeddings of `E'` into `Kˢ`, so the norm of `E'/E` is the
product of the translates by representatives of these cosets. This is the form in which the norm
`x ↦ ∑ q, q.out • x` between the levels of `W'` and `W` of a discrete `G_K`-module is compared with
the norm of the extension `E'/E`.

## Main results

* `TauCeti.algebraMap_norm_eq_prod_transversal`: the norm of `L/K` is the product of the
  conjugates of `σ`, indexed by a transversal of `Gal(Kˢ/σ(L))`.
* `TauCeti.algebraMap_norm_eq_prod_algHom`: the norm of a finite separable `L/K` is the product
  of the images under all `K`-embeddings of `L` into `Kˢ`.
* `TauCeti.coe_norm_eq_prod_quotient_out`: the norm of `E'/E` is the product of the translates by
  representatives of the cosets of `W'` in `W`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I §5, where
  the degree-zero corestriction along a finite extension of fields is the norm.
-/

public section

noncomputable section

namespace TauCeti

open IntermediateField

variable (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K)

include σ

variable [FiniteDimensional K L]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

omit σ in
/-- **The norm of a finite separable extension is the product of its conjugates in `Kˢ`**: the
image of `N_{L/K} b` in `Kˢ` is the product of `τ b` over all `K`-embeddings `τ : L →ₐ[K] Kˢ`.
This is Mathlib's `Algebra.norm_eq_prod_embeddings` with the separable closure of `K` in place of
an algebraically closed field. -/
theorem algebraMap_norm_eq_prod_algHom [Algebra.IsSeparable K L] (b : L) :
    algebraMap K (SeparableClosure K) (Algebra.norm K b) =
      ∏ τ : L →ₐ[K] SeparableClosure K, τ b := by
  let σ : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  rw [algebraMap_norm_eq_prod_transversal K L σ Quotient.out (fun u ↦ QuotientGroup.out_eq' u) b]
  refine Fintype.prod_equiv (FieldTheory.fixingSubgroupQuotientEquivAlgHom σ) _ _ fun u ↦ ?_
  conv_rhs => rw [← QuotientGroup.out_eq' u, FieldTheory.fixingSubgroupQuotientEquivAlgHom_mk]
  rfl

section Relative

variable {K} {E E' : IntermediateField K (SeparableClosure K)} [Algebra E E']
  [IsScalarTower E E' (SeparableClosure K)]
  {W W' : OpenSubgroup (AbsoluteGaloisGroup K)}

end Relative

end TauCeti
