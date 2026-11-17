-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Modules.DescentIsomorphism), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FpqcFullyFaithful

/-!
# Isomorphisms from fpqc descent data

Full faithfulness of quasi-coherent module descent lifts isomorphisms of descent data to isomorphisms of sheaves.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe w u
open CategoryTheory Opposite
namespace AlgebraicGeometry
variable {T : Scheme.{u}} {ι : Type w} {T' : ι → Scheme.{u}} (g : ∀ i, T' i ⟶ T)

/-- Quasi-coherent modules whose descent data relative to an fpqc covering are isomorphic are
isomorphic: the comparison functor is fully faithful on quasi-coherent modules. -/
theorem nonempty_iso_of_toDescentData_iso (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    {M N : modulesPseudofunctor.obj (.mk (op T))} (hM : (M : T.Modules).IsQuasicoherent)
    (hN : (N : T.Modules).IsQuasicoherent)
    (e : (modulesPseudofunctor.toDescentData g).obj M ≅
      (modulesPseudofunctor.toDescentData g).obj N) :
    Nonempty (M ≅ N) := by
  obtain ⟨φ, hφ⟩ := (bijective_toDescentData_map_of_mem_fpqcTopology g hg M N hM hN).2 e.hom
  obtain ⟨ψ, hψ⟩ := (bijective_toDescentData_map_of_mem_fpqcTopology g hg N M hN hM).2 e.inv
  refine ⟨⟨φ, ψ, (bijective_toDescentData_map_of_mem_fpqcTopology g hg M M hM hM).1 ?_,
    (bijective_toDescentData_map_of_mem_fpqcTopology g hg N N hN hN).1 ?_⟩⟩
  · rw [Functor.map_comp, hφ, hψ, e.hom_inv_id, CategoryTheory.Functor.map_id]
  · rw [Functor.map_comp, hφ, hψ, e.inv_hom_id, CategoryTheory.Functor.map_id]

end AlgebraicGeometry
