-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.Algebra.Homology.ShortComplex.Finite), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite modules in exact sequences

Over a Noetherian ring, the middle term of an exact sequence is finite when
both outer terms are finite.
-/

open CategoryTheory

universe u v

namespace CategoryTheory.ShortComplex

variable {baseRing : Type u} [CommRing baseRing] [IsNoetherianRing baseRing]
  {shortComplex : ShortComplex (ModuleCat.{v} baseRing)}

/-- Finiteness of the outer terms of an exact sequence implies finiteness of its middle term. -/
lemma Exact.moduleFinite_X₂ (exact_sequence : shortComplex.Exact)
    [Module.Finite baseRing shortComplex.X₁] [Module.Finite baseRing shortComplex.X₃] :
    Module.Finite baseRing shortComplex.X₂ := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at exact_sequence
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker shortComplex.g.hom
    (IsNoetherian.noetherian _) ?_⟩
  rw [top_inf_eq, ← exact_sequence, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map _

end CategoryTheory.ShortComplex
