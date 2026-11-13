/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Galois), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Galois` (task ring-class).
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Galois
public import ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.NumberField.Global.Adeles.Norm.Galois

public section

open IsDedekindDomain NumberField

namespace TauCeti.GlobalNumberFields


/-- **A product formula for the norm transfers to ideles.** Let `L/K` be an extension of number
fields and `M` an extension of both. If for some ring automorphisms `σ i` of `M` the norm
`N_{L/K}(y)` of every `y ∈ L`, read in `M`, is `∏ i, σ i y`, then extended to `M`, the idele norm
`N_{L/K}(x)` of an idele `x` of `L` is `∏ i, σ i x`. -/
theorem ideleExtension_ideleNormMap_of_algebraMap_norm_eq_prod (K L M : Type*) [Field K]
    [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M] [Algebra K L]
    [Algebra K M] [Algebra L M] {ι : Type*} [Fintype ι] (σ : ι → M ≃+* M)
    (hσ : ∀ y : L, algebraMap K M (Algebra.norm K y) = ∏ i, σ i (algebraMap L M y))
    (x : IdeleGroup (𝓞 L) L) :
    ideleExtension K M (ideleNormMap K L x) =
      ∏ i, Units.map (adeleEquiv M M (σ i)).toMonoidHom (ideleExtension L M x) := by
  apply Units.ext
  rw [coe_ideleExtension, coe_ideleNormMap,
    adeleExtension_adeleNorm_of_algebraMap_norm_eq_prod K L M σ hσ, Units.coe_prod]
  simp only [Units.coe_map, coe_ideleExtension]
  -- `RingEquiv.toMonoidHom` is an abbreviation, with the same underlying function.
  rfl


end TauCeti.GlobalNumberFields
