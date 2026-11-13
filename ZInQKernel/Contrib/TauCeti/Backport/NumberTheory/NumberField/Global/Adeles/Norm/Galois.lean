/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.NumberField.Global.Adeles.Norm.Galois), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Adeles.Norm.Galois` (task ring-class).
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Adeles.Norm.Galois

public section

open IsDedekindDomain NumberField

namespace TauCeti.GlobalNumberFields

section Transfer

variable (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M]

/-- **A product formula for the norm transfers to finite adeles.** Let `L/K` be an extension of
number fields and `M` an extension of both. If for some ring automorphisms `σ i` of `M` the norm
`N_{L/K}(x)` of every `x ∈ L`, read in `M`, is `∏ i, σ i x`, then the same holds for the finite
adele norm: extended to `M`, the norm of a finite adele `a` of `L` is `∏ i, σ i a`. -/
theorem finiteAdeleExtension_finiteAdeleNorm_of_algebraMap_norm_eq_prod {ι : Type*} [Fintype ι]
    (σ : ι → M ≃+* M)
    (hσ : ∀ x : L, algebraMap K M (Algebra.norm K x) = ∏ i, σ i (algebraMap L M x))
    (a : FiniteAdeleRing (𝓞 L) L) :
    finiteAdeleExtension (𝓞 K) K (𝓞 M) M (finiteAdeleNorm K L a) =
      ∏ i, finiteAdeleEquiv M M (σ i) (finiteAdeleExtension (𝓞 L) L (𝓞 M) M a) := by
  -- Both sides are continuous in `a` and agree on the dense diagonal `L`.
  refine congrFun ((FiniteAdeleRing.denseRange_algebraMap (𝓞 L) L).equalizer
    ((continuous_finiteAdeleExtension (𝓞 K) K (𝓞 M) M).comp (continuous_finiteAdeleNorm K L))
    (continuous_finsetProd _ fun i _ ↦ (continuous_finiteAdeleEquiv M M (σ i)).comp
      (continuous_finiteAdeleExtension (𝓞 L) L (𝓞 M) M))
    (funext fun x ↦ ?_)) a
  simp only [Function.comp_apply, finiteAdeleNorm_algebraMap, finiteAdeleExtension_algebraMap,
    finiteAdeleEquiv_algebraMap, hσ, map_prod]

omit [NumberField M] in
/-- **A product formula for the norm transfers to infinite adeles.** If for some ring
automorphisms `σ i` of `M` the norm `N_{L/K}(x)` of every `x ∈ L`, read in `M`, is `∏ i, σ i x`,
then extended to `M`, the norm of an infinite adele `a` of `L` is `∏ i, σ i a`. -/
theorem infiniteAdeleExtension_infiniteAdeleNorm_of_algebraMap_norm_eq_prod {ι : Type*}
    [Fintype ι] (σ : ι → M ≃+* M)
    (hσ : ∀ x : L, algebraMap K M (Algebra.norm K x) = ∏ i, σ i (algebraMap L M x))
    (a : InfiniteAdeleRing L) :
    infiniteAdeleExtension K M (infiniteAdeleNorm K L a) =
      ∏ i, infiniteAdeleEquiv M M (σ i) (infiniteAdeleExtension L M a) := by
  -- Both sides are continuous in `a` and agree on the dense diagonal `L`.
  refine congrFun ((InfiniteAdeleRing.denseRange_algebraMap L).equalizer
    ((continuous_infiniteAdeleExtension K M).comp (continuous_infiniteAdeleNorm K L))
    (continuous_finsetProd _ fun i _ ↦ (continuous_infiniteAdeleEquiv M M (σ i)).comp
      (continuous_infiniteAdeleExtension L M))
    (funext fun x ↦ ?_)) a
  simp only [Function.comp_apply, infiniteAdeleNorm_algebraMap, infiniteAdeleExtension_algebraMap,
    infiniteAdeleEquiv_algebraMap, hσ, map_prod]

/-- **A product formula for the norm transfers to adeles.** If for some ring automorphisms `σ i`
of `M` the norm `N_{L/K}(x)` of every `x ∈ L`, read in `M`, is `∏ i, σ i x`, then extended to
`M`, the adele norm `N_{L/K}(a)` of an adele `a` of `L` is `∏ i, σ i a`. The extension `L/K` need
not be normal: `M` may be a Galois extension of `K` containing `L`, and the `σ i` representatives
of the cosets of `Gal(M/L)` in `Gal(M/K)`. -/
theorem adeleExtension_adeleNorm_of_algebraMap_norm_eq_prod {ι : Type*} [Fintype ι]
    (σ : ι → M ≃+* M)
    (hσ : ∀ x : L, algebraMap K M (Algebra.norm K x) = ∏ i, σ i (algebraMap L M x))
    (a : AdeleRing (𝓞 L) L) :
    adeleExtension (𝓞 K) K (𝓞 M) M (adeleNorm K L a) =
      ∏ i, adeleEquiv M M (σ i) (adeleExtension (𝓞 L) L (𝓞 M) M a) := by
  -- Apply the infinite and finite formulas to the two factors. `AdeleRing` is a type synonym
  -- for the product, so its projections are `RingHom.fst` and `RingHom.snd`.
  refine Prod.ext ?_ ?_
  · rw [adeleExtension_fst, adeleNorm_fst,
      infiniteAdeleExtension_infiniteAdeleNorm_of_algebraMap_norm_eq_prod K L M σ hσ]
    refine Eq.trans ?_ (map_prod (RingHom.fst (InfiniteAdeleRing M) (FiniteAdeleRing (𝓞 M) M))
      (fun i ↦ adeleEquiv M M (σ i) (adeleExtension (𝓞 L) L (𝓞 M) M a)) Finset.univ).symm
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← adeleExtension_fst (R := 𝓞 L) (B := 𝓞 M) a]
    exact (adeleEquiv_fst M M (σ i) _).symm
  · rw [adeleExtension_snd, adeleNorm_snd,
      finiteAdeleExtension_finiteAdeleNorm_of_algebraMap_norm_eq_prod K L M σ hσ]
    refine Eq.trans ?_ (map_prod (RingHom.snd (InfiniteAdeleRing M) (FiniteAdeleRing (𝓞 M) M))
      (fun i ↦ adeleEquiv M M (σ i) (adeleExtension (𝓞 L) L (𝓞 M) M a)) Finset.univ).symm
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← adeleExtension_snd (R := 𝓞 L) (B := 𝓞 M) a]
    exact (adeleEquiv_snd M M (σ i) _).symm

end Transfer

end TauCeti.GlobalNumberFields
