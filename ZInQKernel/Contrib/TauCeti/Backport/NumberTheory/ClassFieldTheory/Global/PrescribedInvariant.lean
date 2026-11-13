/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.ClassFieldTheory.Global.PrescribedInvariant), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.PrescribedInvariant`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.PrescribedInvariant
public import ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.ClassFieldTheory.Global.PrimeDegreeDecomposition

public section
noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField ContCohomology
open _root_.ValuativeRel
open scoped AdicCompletionExtension _root_.IntermediateField
variable {K : Type} [Field K] [NumberField K]
local notation "Ω" => FiniteGaloisIntermediateField K (SeparableClosure K)

/-- **A prime-degree layer carries a class of invariant `1 / [U : V]`.** A layer `V ◁ U` of prime
degree has a finite place whose decomposition map onto `U ⧸ V` is surjective, and its Galois group
is cyclic, so the prescribed-invariant construction applies at that place. -/
theorem exists_ideleSumLocalInv_eq_one_div_degree_of_prime
    (L : NormalLayer (AbsoluteGaloisGroup K)) (hL : L.degree.Prime) :
    ∃ y : L.H (ideleFormation K) 2,
      ideleSumLocalInv K L y = ((1 / L.degree : ℚ) : AddCircle (1 : ℚ)) := by
  have := NormalLayer.isCyclic_gal_of_prime_degree hL
  obtain ⟨v, τ, hτ⟩ := L.exists_surjective_absoluteGaloisGroupMap_of_degree_prime hL
  exact exists_ideleSumLocalInv_eq_one_div_degree_of_isCyclic L τ hτ

end TauCeti.ClassFieldTheory

end
end
