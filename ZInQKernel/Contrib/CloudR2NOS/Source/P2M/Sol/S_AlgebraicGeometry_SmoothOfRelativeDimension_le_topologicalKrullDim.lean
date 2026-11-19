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
  Source file    : P2M/Sol/S_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim.lean
  Source sha256  : 6002ab7be98e6db0b5493901e73199d56efbc7d7b72fc523c75a5d81bda08423
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: R10×1; rule citations in the batch ledger.
  * BATCH-3 (lane4): ; hand repairs: ringKrullDim of MvPolynomial now yields ENat.card σ (a Parent compile probe l.66 goal `0 + ↑(ENat.card (Fin… (×1)
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
r2nos_namespace_dual

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
r2nos_open_dual "CategoryTheory AlgebraicGeometry TopologicalSpace"

namespace P2mSmoothDimGe
r2nos_namespace_dual

theorem height_eq_of_isMaximal_mvPolynomial (L : Type u) [Field L] (n : ℕ)
    (𝔭 : Ideal (MvPolynomial (Fin n) L)) [h𝔭 : 𝔭.IsMaximal] : 𝔭.height = n := by
  have hform := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType L 𝔭
  have hquot : ringKrullDim (MvPolynomial (Fin n) L ⧸ 𝔭) = 0 :=
    ringKrullDim_eq_zero_of_isField (Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔭 |>.mp h𝔭)
  have hP : ringKrullDim (MvPolynomial (Fin n) L) = n := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_fintype_card,
      Fintype.card_fin, zero_add]
    all_goals norm_cast
  rw [hquot, hP, add_zero] at hform
  exact_mod_cast hform

theorem le_ringKrullDim_of_isStandardSmoothOfRelativeDimension {L R : Type u} [CommRing L] (hL : IsField L)
    [CommRing R] [Nontrivial R] (φ : L →+* R) (n : ℕ) (hφ : φ.IsStandardSmoothOfRelativeDimension n) :
    (n : WithBot ℕ∞) ≤ ringKrullDim R := by
  letI : Field L := hL.toField
  obtain ⟨g, -, hg⟩ := hφ.exists_etale_mvPolynomial

  algebraize [g]

  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal R
  let 𝔭 : Ideal (MvPolynomial (Fin n) L) := 𝔪.comap g

  haveI : 𝔭.IsMaximal := by
    letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    haveI : Algebra.FiniteType (MvPolynomial (Fin n) L) (R ⧸ 𝔪) :=
      Algebra.FiniteType.trans (S := R) inferInstance inferInstance
    haveI : Module.Finite (MvPolynomial (Fin n) L) (R ⧸ 𝔪) :=
      finite_of_finite_type_of_isJacobsonRing (MvPolynomial (Fin n) L) (R ⧸ 𝔪)
    haveI : Algebra.IsIntegral (MvPolynomial (Fin n) L) (R ⧸ 𝔪) := inferInstance
    have hbot : (⊥ : Ideal (R ⧸ 𝔪)).IsMaximal := Ideal.bot_isMaximal
    have hcomap : ((⊥ : Ideal (R ⧸ 𝔪)).comap (algebraMap (MvPolynomial (Fin n) L) (R ⧸ 𝔪))).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal ⊥
    have heq : (⊥ : Ideal (R ⧸ 𝔪)).comap (algebraMap (MvPolynomial (Fin n) L) (R ⧸ 𝔪)) = 𝔭 := by
      rw [show algebraMap (MvPolynomial (Fin n) L) (R ⧸ 𝔪) = (Ideal.Quotient.mk 𝔪).comp g from rfl,
        ← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    rwa [heq] at hcomap

  have hht : 𝔭.height = n := height_eq_of_isMaximal_mvPolynomial L n 𝔭

  have hle : (n : ℕ∞) ≤ Order.height (⟨𝔭, inferInstance⟩ : PrimeSpectrum (MvPolynomial (Fin n) L)) := by
    rw [← PrimeSpectrum.height_eq_orderHeight, hht]
  obtain ⟨l, hlast, hlen⟩ := Order.exists_series_of_le_height _ hle

  haveI : 𝔪.LiesOver l.last.asIdeal := ⟨by rw [hlast]; rfl⟩
  obtain ⟨l', hl'len, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l 𝔪
  calc (n : WithBot ℕ∞) = (l'.length : WithBot ℕ∞) := by rw [hl'len, hlen]
    _ ≤ ringKrullDim R := Order.LTSeries.length_le_krullDim l'

theorem le_topologicalKrullDim {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f] [Nonempty X] :
    (n : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨U, hU, V, hV, hxV, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x

  have hU' : U = ⊤ := by
    haveI : Subsingleton (Spec (CommRingCat.of K)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum K))
    ext y
    simp only [Opens.coe_top, Set.mem_univ, iff_true]
    have hx : f.base x ∈ U := e hxV
    rwa [Subsingleton.elim y (f.base x)]
  subst hU'
  have hK : IsField Γ(Spec (CommRingCat.of K), ⊤) :=
    MulEquiv.isField (Field.toIsField K)
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv

  have hne : Nonempty (PrimeSpectrum Γ(X, V)) := ⟨(hV.isoSpec.hom.base ⟨x, hxV⟩ : PrimeSpectrum Γ(X, V))⟩
  haveI : Nontrivial Γ(X, V) := PrimeSpectrum.nonempty_iff_nontrivial.mp hne

  have hring : (n : WithBot ℕ∞) ≤ ringKrullDim Γ(X, V) :=
    le_ringKrullDim_of_isStandardSmoothOfRelativeDimension hK _ n hf
  have hSpec : (n : WithBot ℕ∞) ≤ topologicalKrullDim (Spec Γ(X, V)) := by
    change (n : WithBot ℕ∞) ≤ topologicalKrullDim (PrimeSpectrum Γ(X, V))
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  rw [← IsHomeomorph.topologicalKrullDim_eq _ hV.isoSpec.hom.homeomorph.isHomeomorph] at hSpec
  exact hSpec.trans (topologicalKrullDim_subspace_le X (V : Set X))

end P2mSmoothDimGe

theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [Nonempty X] :
    (n : WithBot ℕ∞) ≤ topologicalKrullDim X :=
  P2mSmoothDimGe.le_topologicalKrullDim f n
end S_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
