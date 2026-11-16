/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier.lean, lines 184-237
                   (sections `SatGates` and `TeethGate`, verbatim)
  Copyright      : 2026 Anthropic, PBC
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)), H5 lane4, 2026-11-14. The published H76 port
`ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier`
deleted these two self-test sections (6 lemmas on ℤ_[p]) because its closure never used them.
Several files of the lane4 closure DO use them (e.g. Def_AlgebraicGeometry_NeronModelEndomorphismExtension,
Def_AlgebraicGeometry_NeronModelUniquenessUpToIsomorphism, Def_AlgebraicGeometry_NeronSpecialFibreRestriction),
so this module restores exactly those source lines, unchanged, in the same namespace
`ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra` and with the source file's own context
(`noncomputable section`, `universe u`, the same `open`s), importing the H76 copy for everything else.
No other change.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry"

namespace NeronModelInfra
r2nos_namespace_dual

section SatGates

theorem gate_neronModelPropertyBundle_trivialGroupScheme_zp (p : ℕ) [Fact p.Prime] :
    NeronModelPropertyBundle ℤ_[p] ℚ_[p] (𝟙 (Spec (CommRingCat.of ℤ_[p]))) :=
  neronModelPropertyBundle_id ℤ_[p] ℚ_[p]

theorem gate_neronModelPropertyBundle_trivialGroupScheme_z3 :
    NeronModelPropertyBundle ℤ_[3] ℚ_[3] (𝟙 (Spec (CommRingCat.of ℤ_[3]))) :=
  gate_neronModelPropertyBundle_trivialGroupScheme_zp 3

end SatGates

section TeethGate

theorem isEmpty_schemeHomOver_id_specGenericFibreInclusion_zp (p : ℕ) [Fact p.Prime] :
    IsEmpty (SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ_[p])))
      (specGenericFibreInclusion ℤ_[p] ℚ_[p])) := by
  constructor
  rintro ⟨s, hs⟩
  obtain ⟨σ, rfl⟩ := Spec.map_surjective s
  rw [specGenericFibreInclusion_eq, ← Spec.map_comp, Spec.map_eq_id] at hs
  have h2 : σ.hom.comp (algebraMap ℤ_[p] ℚ_[p]) = RingHom.id ℤ_[p] := by
    have h3 := congrArg CommRingCat.Hom.hom hs
    simpa [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_id] using h3
  have happ : σ.hom (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p])) = (p : ℤ_[p]) := by
    have h4 := RingHom.congr_fun h2 (p : ℤ_[p])
    rw [RingHom.comp_apply, RingHom.id_apply] at h4
    exact h4
  have hunitK : IsUnit (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p])) := by
    refine isUnit_iff_ne_zero.mpr ?_
    rw [PadicInt.algebraMap_apply, PadicInt.coe_ne_zero]
    exact PadicInt.prime_p.ne_zero
  have hunit : IsUnit ((p : ℤ_[p])) := happ ▸ hunitK.map σ.hom
  exact (mem_nonunits_iff.mp (PadicInt.p_nonunit (p := p))) hunit

theorem gate_neronUniqueExtension_fails_genericFibreOnly (p : ℕ) [Fact p.Prime] :
    ¬ NeronUniqueExtension ℤ_[p] ℚ_[p] (specGenericFibreInclusion ℤ_[p] ℚ_[p]) := by
  intro h
  obtain ⟨φ, -⟩ := (h (Spec (CommRingCat.of ℤ_[p])) (𝟙 (Spec (CommRingCat.of ℤ_[p])))
    inferInstance).2
    ⟨pullback.snd (𝟙 (Spec (CommRingCat.of ℤ_[p]))) (specGenericFibreInclusion ℤ_[p] ℚ_[p]) ≫
        pullback.lift (𝟙 (Spec (CommRingCat.of ℚ_[p]))) (𝟙 (Spec (CommRingCat.of ℚ_[p]))) rfl,
      by simp [pullback.lift_snd]⟩
  exact (isEmpty_schemeHomOver_id_specGenericFibreInclusion_zp p).false φ

theorem gate_neronModelPropertyBundle_not_genericFibreOnly (p : ℕ) [Fact p.Prime] :
    ¬ NeronModelPropertyBundle ℤ_[p] ℚ_[p] (specGenericFibreInclusion ℤ_[p] ℚ_[p]) :=
  fun h => gate_neronUniqueExtension_fails_genericFibreOnly p h.neronMapping

theorem gate_neronUniqueExtension_fails_genericFibreOnly_three :
    ¬ NeronUniqueExtension ℤ_[3] ℚ_[3] (specGenericFibreInclusion ℤ_[3] ℚ_[3]) :=
  gate_neronUniqueExtension_fails_genericFibreOnly 3

end TeethGate

end NeronModelInfra

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
