/-
NOS-CORE PROBE STAGING COPY (lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.lean
  Source sha256  : 9ba940a358b7f05f84629d65f3c0f0c2ca984f7e894a60991c22e32b4ca54d7c
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 23 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 8 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 3 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 multi-command source line(s) split into one command per line (no change of commands).
  * REMOVED source option(s) (default-options rule): `set_option linter.unusedSectionVars false`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 3 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_ModularCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
r2nos_namespace_dual

set_option autoImplicit false
noncomputable section

set_option autoImplicit false

open KaehlerDifferential Algebra IntermediateField
r2nos_open_dual "KaehlerDifferential Algebra IntermediateField"

namespace AlgebraicCurve
r2nos_namespace_dual
w03_export "AlgebraicCurve" "IsCurveOver IsCurveOver.finrank_kaehler"
w03_open "AlgebraicCurve"

namespace IsCurveOver
r2nos_namespace_dual
w03_export "AlgebraicCurve.IsCurveOver" "finrank_kaehler instNontrivialKaehler"
w03_open "AlgebraicCurve.IsCurveOver"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem not_isSeparable [IsCurveOver K F] : ¬ Algebra.IsSeparable K F := by
  intro hsep
  haveI : Algebra.FormallyUnramified K F := Algebra.FormallyUnramified.of_isSeparable K F
  exact false_of_nontrivial_of_subsingleton Ω[F⁄K]

theorem not_isAlgebraic [PerfectField K] [IsCurveOver K F] :
    ¬ Algebra.IsAlgebraic K F := by
  intro halg
  exact not_isSeparable (K := K) (F := F) Algebra.IsAlgebraic.isSeparable_of_perfectField

scoped instance instTranscendental [PerfectField K] [IsCurveOver K F] :
    Algebra.Transcendental K F :=
  Algebra.transcendental_iff_not_isAlgebraic.mpr not_isAlgebraic

theorem exists_transcendental [PerfectField K] [IsCurveOver K F] :
    ∃ t : F, Transcendental K t :=
  Algebra.Transcendental.transcendental

theorem trdeg_pos [PerfectField K] [IsCurveOver K F] :
    0 < Algebra.trdeg K F :=
  _root_.trdeg_pos K F

theorem trdeg_ne_zero [PerfectField K] [IsCurveOver K F] :
    Algebra.trdeg K F ≠ 0 :=
  trdeg_pos.ne'

theorem one_le_trdeg [PerfectField K] [IsCurveOver K F] :
    1 ≤ Algebra.trdeg K F :=
  Cardinal.one_le_iff_pos.mpr trdeg_pos

end IsCurveOver
w03_reactivate "P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve.IsCurveOver"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace IsCurveOver
r2nos_namespace_dual
w03_export "AlgebraicCurve.IsCurveOver" "finrank_kaehler instNontrivialKaehler"
end IsCurveOver
r2nos_open_scoped "AlgebraicCurve.IsCurveOver" in

theorem IsCurveOver.trdeg_eq_one [PerfectField K] [IsCurveOver K F]
    (htrdeg : Algebra.trdeg K F ≤ 1) :
    Algebra.trdeg K F = 1 :=
  le_antisymm htrdeg IsCurveOver.one_le_trdeg

end AlgebraicCurve
w03_reactivate "P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve.IsCurveOver P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve"

set_option autoImplicit false

noncomputable section

w03_open "KaehlerDifferential IntermediateField TensorProduct Algebra.TensorProduct Module"
open scoped IntermediateField.algebraAdjoinAdjoin
r2nos_open_scoped_dual "IntermediateField.algebraAdjoinAdjoin"

namespace AlgebraicCurve
r2nos_namespace_dual
w03_export "AlgebraicCurve" "IsCurveOver IsCurveOver.finrank_kaehler"
w03_open "AlgebraicCurve"

universe u₁ u₂

variable {K : Type u₁} {F : Type u₂} [Field K] [Field F] [Algebra K F]

variable {ι : Type*} {v : ι → F}

def kaehlerAdjoinBasis (hv : AlgebraicIndependent K v) :
    Basis ι (IntermediateField.adjoin K (Set.range v))
      Ω[(IntermediateField.adjoin K (Set.range v))⁄K] := by

  let Kv : IntermediateField K F := IntermediateField.adjoin K (Set.range v)

  letI : Algebra (MvPolynomial ι K) Kv :=
    ((algebraMap (Algebra.adjoin K (Set.range v)) Kv).comp
      (hv.aevalEquiv : MvPolynomial ι K →+* Algebra.adjoin K (Set.range v))).toAlgebra

  haveI : IsScalarTower K (MvPolynomial ι K) Kv :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K Kv a
        = algebraMap (Algebra.adjoin K (Set.range v)) Kv (hv.aevalEquiv (algebraMap K _ a))
      rw [AlgEquiv.commutes]; rfl

  haveI : IsFractionRing (MvPolynomial ι K) Kv :=
    IsFractionRing.of_ringEquiv_left hv.aevalEquiv.toRingEquiv (fun _ => rfl)

  haveI : Algebra.FormallyEtale (MvPolynomial ι K) Kv :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (MvPolynomial ι K))

  exact ((KaehlerDifferential.mvPolynomialBasis K ι).baseChange Kv).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (MvPolynomial ι K) Kv)

def kaehlerOfSeparatingTranscendentalBasis (hv : AlgebraicIndependent K v)
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) F] : Basis ι F Ω[F⁄K] :=
  haveI : Algebra.FormallyEtale (IntermediateField.adjoin K (Set.range v)) F :=
    Algebra.FormallyEtale.of_isSeparable _ _
  ((kaehlerAdjoinBasis hv).baseChange F).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K
      (IntermediateField.adjoin K (Set.range v)) F)

theorem finrank_kaehler_eq_card_of_separating {s : Finset F}
    (hs : AlgebraicIndependent K ((↑) : s → F))
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range ((↑) : s → F))) F] :
    Module.finrank F Ω[F⁄K] = s.card := by
  rw [Module.finrank_eq_card_basis (kaehlerOfSeparatingTranscendentalBasis hs),
    Fintype.card_coe]

theorem finrank_kaehler_eq_card_of_separating' {s : Finset F}
    (hs : AlgebraicIndependent K ((↑) : s → F))
    [hsep : Algebra.IsSeparable (IntermediateField.adjoin K (s : Set F)) F] :
    Module.finrank F Ω[F⁄K] = s.card := by

  have heq : IntermediateField.adjoin K (s : Set F)
      = IntermediateField.adjoin K (Set.range ((↑) : s → F)) := by
    rw [Subtype.range_coe]
  let e : (IntermediateField.adjoin K (s : Set F)) ≃ₐ[K]
      (IntermediateField.adjoin K (Set.range ((↑) : s → F))) :=
    IntermediateField.equivOfEq heq

  haveI : Algebra.IsSeparable (IntermediateField.adjoin K (Set.range ((↑) : s → F))) F :=
    Algebra.IsSeparable.of_equiv_equiv e.toRingEquiv (RingEquiv.refl F)
      (RingHom.ext fun x => rfl)
  exact finrank_kaehler_eq_card_of_separating hs

namespace IsCurveOver
r2nos_namespace_dual
w03_export "AlgebraicCurve.IsCurveOver" "finrank_kaehler instNontrivialKaehler"
w03_open "AlgebraicCurve.IsCurveOver"

theorem trdeg_le_one [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    Algebra.trdeg K F ≤ 1 := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K F

  haveI := hsep
  have hcard : s.card = 1 := by
    rw [← finrank_kaehler_eq_card_of_separating' hs.1, IsCurveOver.finrank_kaehler]

  have htr := hs.cardinalMk_eq_trdeg
  rw [Cardinal.mk_coe_finset, hcard, Nat.cast_one] at htr
  exact htr.symm.le

theorem trdeg_eq_one_of_perfectField [PerfectField K] [Algebra.EssFiniteType K F]
    [IsCurveOver K F] : Algebra.trdeg K F = 1 :=
  IsCurveOver.trdeg_eq_one trdeg_le_one

end IsCurveOver
w03_reactivate "P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve.IsCurveOver P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve"

end AlgebraicCurve
w03_reactivate "P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve.IsCurveOver P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve"

set_option autoImplicit false

w03_open "IntermediateField Algebra TensorProduct.Algebra Algebra.TensorProduct.Algebra"

namespace AlgebraicCurve
r2nos_namespace_dual
w03_export "AlgebraicCurve" "IsCurveOver IsCurveOver.finrank_kaehler"
w03_open "AlgebraicCurve"

universe u₁ u₂

variable {K : Type u₁} {F : Type u₂} [Field K] [Field F] [Algebra K F]

namespace IsCurveOver
r2nos_namespace_dual
w03_export "AlgebraicCurve.IsCurveOver" "finrank_kaehler instNontrivialKaehler"
w03_open "AlgebraicCurve.IsCurveOver"

theorem exists_separating_transcendental_s6 [PerfectField K] [Algebra.EssFiniteType K F]
    [IsCurveOver K F] :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F := by

  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K F

  have hcard : s.card = 1 := by
    have htr := hs.cardinalMk_eq_trdeg
    rw [Cardinal.mk_coe_finset, IsCurveOver.trdeg_eq_one_of_perfectField] at htr
    exact_mod_cast htr

  obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hcard

  have htr : Transcendental K t := by
    have h1 := hs.1
    rw [show ((↑) : (↑({t} : Finset F)) → F) = fun _ => t from
      funext fun x => (Finset.mem_singleton.mp x.2).symm ▸ rfl] at h1
    exact (algebraicIndependent_unique_type_iff (ι := (↑({t} : Finset F)))).mp h1

  have heq : IntermediateField.adjoin K (↑({t} : Finset F) : Set F) = K⟮t⟯ := by
    rw [Finset.coe_singleton]
  haveI hsep' : Algebra.IsSeparable K⟮t⟯ F :=
    Algebra.IsSeparable.of_equiv_equiv
      (IntermediateField.equivOfEq heq).toRingEquiv (RingEquiv.refl F)
      (RingHom.ext fun _ => rfl)

  haveI : Algebra.EssFiniteType K⟮t⟯ F := Algebra.EssFiniteType.of_comp K K⟮t⟯ F
  exact ⟨t, htr, Algebra.finite_of_essFiniteType_of_isAlgebraic, hsep'⟩

end IsCurveOver
w03_reactivate "P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve.IsCurveOver P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve"

end AlgebraicCurve
w03_reactivate "P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve.IsCurveOver P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve"

open IntermediateField _root_.Algebra _root_.TensorProduct.Algebra _root_.Algebra.TensorProduct.Algebra in
r2nos_open_dual "IntermediateField _root_.Algebra _root_.TensorProduct.Algebra _root_.Algebra.TensorProduct.Algebra" in
theorem _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.solution {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F] :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F :=
  AlgebraicCurve.IsCurveOver.exists_separating_transcendental_s6

end
w03_reactivate "P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve.IsCurveOver P2MW.S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.AlgebraicCurve"
end
end S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
