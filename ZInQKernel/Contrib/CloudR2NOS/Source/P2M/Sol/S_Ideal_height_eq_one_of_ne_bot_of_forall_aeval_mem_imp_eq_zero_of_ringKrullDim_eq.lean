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
  Source file    : P2M/Sol/S_Ideal_height_eq_one_of_ne_bot_of_forall_aeval_mem_imp_eq_zero_of_ringKrullDim_eq.lean
  Source sha256  : 6f611c507cbd8d9c86037749e3158a195b08988633b9d3b208f53ce090197b0f
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_Algebra_ringKrullDim_eq_toENat_trdeg_of_finiteType
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_Ideal_height_eq_one_of_ne_bot_of_forall_aeval_mem_imp_eq_zero_of_ringKrullDim_eq
r2nos_namespace_dual

set_option autoImplicit false

universe u v

namespace Ideal
r2nos_namespace_dual
w03_export "Ideal" "height Quotient.eq_zero_iff_mem Quotient.mkₐ isDomain Quotient.isDomain Quotient.mk height_eq_zero_iff IsPrime height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType"
namespace HeightOneOfIndependentResidues
r2nos_namespace_dual
w03_open "Ideal"

theorem algebraicIndependent_mk (k : Type u) [Field k] {A : Type v} [CommRing A] [Algebra k A]
    (p : Ideal A) {d : ℕ} (f : Fin d → A)
    (hind : ∀ Q : MvPolynomial (Fin d) k, MvPolynomial.aeval f Q ∈ p → Q = 0) :
    AlgebraicIndependent k (fun i => Ideal.Quotient.mk p (f i)) := by
  rw [AlgebraicIndependent]
  intro Q₁ Q₂ hQ
  have h1 : ∀ Q : MvPolynomial (Fin d) k,
      MvPolynomial.aeval (fun i => Ideal.Quotient.mk p (f i)) Q =
        Ideal.Quotient.mkₐ k p (MvPolynomial.aeval f Q) := by
    intro Q
    rw [MvPolynomial.comp_aeval_apply]
    rfl
  have h2 : MvPolynomial.aeval f (Q₁ - Q₂) ∈ p := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have := hQ
    rw [h1, h1] at this
    change Ideal.Quotient.mk p (MvPolynomial.aeval f Q₁) = Ideal.Quotient.mk p (MvPolynomial.aeval f Q₂)
      at this
    rw [map_sub, map_sub, this, sub_self]
  exact sub_eq_zero.mp (hind _ h2)

theorem natCast_le_ringKrullDim_of_algebraicIndependent (k : Type u) [Field k] {B : Type v} [CommRing B]
    [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] {d : ℕ} {x : Fin d → B}
    (hx : AlgebraicIndependent k x) : ((d : ℕ) : WithBot ℕ∞) ≤ ringKrullDim B := by
  have h1 := Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k B
  have h2 : Cardinal.lift.{v} (Cardinal.mk (Fin d)) ≤ Cardinal.lift.{0} (Algebra.trdeg k B) :=
    hx.lift_cardinalMk_le_trdeg
  rw [Cardinal.mk_fin] at h2
  have h3 : (d : ℕ∞) ≤ Cardinal.toENat (Algebra.trdeg k B) := by
    have := (OrderHomClass.mono Cardinal.toENat) h2
    simpa using this
  rw [h1]
  exact_mod_cast h3

theorem enat_eq_one_of_add_eq_of_le {h : ℕ∞} {x : WithBot ℕ∞} {d : ℕ}
    (hsum : (h : WithBot ℕ∞) + x = ((d + 1 : ℕ) : WithBot ℕ∞)) (hle : ((d : ℕ) : WithBot ℕ∞) ≤ x)
    (hne : h ≠ 0) : h = 1 := by
  induction x using WithBot.recBotCoe with
  | bot =>
    exfalso
    rw [WithBot.add_bot] at hsum
    exact WithBot.bot_ne_coe (hsum.trans (WithBot.coe_natCast _).symm)
  | coe y =>
    have hsum' : h + y = ((d + 1 : ℕ) : ℕ∞) := by
      have : ((h + y : ℕ∞) : WithBot ℕ∞) = (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add]
        exact hsum.trans (WithBot.coe_natCast _).symm
      exact WithBot.coe_inj.mp this
    have hle' : (d : ℕ∞) ≤ y := by
      have : (((d : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (y : WithBot ℕ∞) := by
        rw [WithBot.coe_natCast]; exact hle
      exact WithBot.coe_le_coe.mp this
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      rw [add_top] at hsum'
      exact ENat.top_ne_coe _ hsum'
    | coe m =>
      induction h using ENat.recTopCoe with
      | top =>
        exfalso
        rw [top_add] at hsum'
        exact ENat.top_ne_coe _ hsum'
      | coe n =>
        have e1 : n + m = d + 1 := by exact_mod_cast hsum'
        have e2 : d ≤ m := by exact_mod_cast hle'
        have e3 : n ≠ 0 := by exact_mod_cast hne
        have : n = 1 := by omega
        subst this
        rfl

end Ideal.HeightOneOfIndependentResidues

open Ideal.HeightOneOfIndependentResidues in
r2nos_open_dual "Ideal.HeightOneOfIndependentResidues" in
theorem solution
    (k : Type u) [Field k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥)
    (d : ℕ) (hd : ((d + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim A)
    (f : Fin d → A) (hind : ∀ Q : MvPolynomial (Fin d) k, MvPolynomial.aeval f Q ∈ p → Q = 0) :
    p.height = 1 := by
  haveI : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p

  have hind' := algebraicIndependent_mk k p f hind
  have hle : ((d : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p) :=
    natCast_le_ringKrullDim_of_algebraicIndependent k hind'

  have hsum := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k p
  rw [← hd] at hsum

  have hne : p.height ≠ 0 := by
    intro h0
    rw [Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] at h0
    exact hp h0
  exact enat_eq_one_of_add_eq_of_le hsum hle hne
end S_Ideal_height_eq_one_of_ne_bot_of_forall_aeval_mem_imp_eq_zero_of_ringKrullDim_eq
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
