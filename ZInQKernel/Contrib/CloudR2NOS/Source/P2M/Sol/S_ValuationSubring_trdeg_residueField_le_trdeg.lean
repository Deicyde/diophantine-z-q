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
  Source file    : P2M/Sol/S_ValuationSubring_trdeg_residueField_le_trdeg.lean
  Source sha256  : e57df16b372a620d89a32c22181ec3fb863d2c7b7d93709fbe13dd19ce50f4c8
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: R1×2; rule citations in the batch ledger.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_ValuationSubring_trdeg_residueField_le_trdeg
r2nos_namespace_dual

set_option autoImplicit false

open Cardinal
r2nos_open_dual "Cardinal"

namespace ValuationSubring
r2nos_namespace_dual
w03_export "ValuationSubring" "comap mem_comap toSubring ext valuation_le_one_iff algebra valuation inclusion"
namespace ResidueTrdeg
r2nos_namespace_dual
w03_open "ValuationSubring"

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

abbrev B : ValuationSubring K := A.comap (algebraMap K L)

def resHom : B K A →+* A :=
  (algebraMap K L).restrict (B K A).toSubring A.toSubring (fun _ hx => hx)

@[scoped simp] lemma coe_resHom_apply (b : B K A) : ((resHom K A b : A) : L) = algebraMap K L (b : K) := rfl

lemma algebraMap_comp_resHom :
    (algebraMap A L).comp (resHom K A) = (algebraMap K L).comp (algebraMap (B K A) K) := by
  ext b
  rfl

theorem algebraicIndependent_lift
    [Algebra (IsLocalRing.ResidueField (B K A)) (IsLocalRing.ResidueField A)]
    (hcompat : ∀ b : B K A,
      algebraMap (IsLocalRing.ResidueField (B K A)) (IsLocalRing.ResidueField A)
        (IsLocalRing.residue _ b) =
          IsLocalRing.residue A ⟨algebraMap K L (b : K), ValuationSubring.mem_comap.mp b.2⟩)
    {ι : Type*} (y : ι → A)
    (hind : AlgebraicIndependent (IsLocalRing.ResidueField (B K A))
      (fun i => IsLocalRing.residue A (y i))) :
    AlgebraicIndependent K (fun i => ((y i : A) : L)) := by
  classical
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hP0

  have hsupp : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hP0
  obtain ⟨m₀, hm₀, hmax⟩ := Finset.exists_max_image P.support
    (fun m => A.valuation (algebraMap K L (P.coeff m))) hsupp
  set c : K := P.coeff m₀ with hc
  have hc0 : c ≠ 0 := MvPolynomial.mem_support_iff.mp hm₀

  set Q : MvPolynomial ι K := MvPolynomial.C c⁻¹ * P with hQ
  have hQcoeff : ∀ m, Q.coeff m = c⁻¹ * P.coeff m := fun m => by
    rw [hQ, MvPolynomial.coeff_C_mul]
  have hQm₀ : Q.coeff m₀ = 1 := by rw [hQcoeff, ← hc, inv_mul_cancel₀ hc0]
  have hQeval : MvPolynomial.aeval (fun i => ((y i : A) : L)) Q = 0 := by
    rw [hQ, map_mul, hP, mul_zero]

  have hQmem : ∀ m, algebraMap K L (Q.coeff m) ∈ A := by
    intro m
    rw [← A.valuation_le_one_iff, hQcoeff, map_mul, map_mul, map_inv₀, map_inv₀]
    by_cases hm : m ∈ P.support
    · have hle := hmax m hm
      have hcv : A.valuation (algebraMap K L c) ≠ 0 := by
        rw [Ne, Valuation.zero_iff, map_eq_zero]
        exact hc0
      calc (A.valuation (algebraMap K L c))⁻¹ * A.valuation (algebraMap K L (P.coeff m))
          ≤ (A.valuation (algebraMap K L c))⁻¹ * A.valuation (algebraMap K L c) := by
            gcongr
        _ = 1 := inv_mul_cancel₀ hcv
    · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero, map_zero, mul_zero]
      exact zero_le_one

  obtain ⟨QB, hQB⟩ : Q ∈ Set.range (MvPolynomial.map (algebraMap (B K A) K)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro d hd
    obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hd
    exact ⟨⟨Q.coeff m, hQmem m⟩, rfl⟩

  have heval : MvPolynomial.eval₂ (resHom K A) y QB = 0 := by
    have h : algebraMap A L (MvPolynomial.eval₂ (resHom K A) y QB) = 0 := by
      rw [MvPolynomial.eval₂_comp_left, algebraMap_comp_resHom, ← MvPolynomial.eval₂_map, hQB]
      exact hQeval
    apply Subtype.val_injective
    show algebraMap A L (MvPolynomial.eval₂ (resHom K A) y QB) = algebraMap A L 0
    rw [h, map_zero]

  have hres : MvPolynomial.aeval (fun i => IsLocalRing.residue A (y i))
      (MvPolynomial.map (IsLocalRing.residue (B K A)) QB) = 0 := by
    have h1 := congrArg (IsLocalRing.residue A) heval
    rw [map_zero, MvPolynomial.eval₂_comp_left] at h1
    have h2 : (IsLocalRing.residue A).comp (resHom K A) =
        (algebraMap (IsLocalRing.ResidueField (B K A)) (IsLocalRing.ResidueField A)).comp
          (IsLocalRing.residue (B K A)) := by
      ext b
      simp only [RingHom.comp_apply]
      rw [hcompat b]
      rfl
    rw [h2, ← MvPolynomial.eval₂_map] at h1
    rw [MvPolynomial.aeval_def]
    exact h1
  have hzero : MvPolynomial.map (IsLocalRing.residue (B K A)) QB = 0 :=
    (algebraicIndependent_iff.mp hind) _ hres

  have h1 : QB.coeff m₀ = 1 := by
    have h : algebraMap (B K A) K (QB.coeff m₀) = algebraMap (B K A) K 1 := by
      rw [← MvPolynomial.coeff_map, hQB, hQm₀, map_one]
    exact Subtype.val_injective h
  have h2 := congrArg (AddMonoidAlgebra.coeff · m₀) hzero
  rw [MvPolynomial.coeff_map, h1, map_one, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h2
  exact one_ne_zero h2

theorem main
    [Algebra (IsLocalRing.ResidueField (A.comap (algebraMap K L))) (IsLocalRing.ResidueField A)]
    (hcompat : ∀ b : A.comap (algebraMap K L),
      algebraMap (IsLocalRing.ResidueField (A.comap (algebraMap K L))) (IsLocalRing.ResidueField A)
        (IsLocalRing.residue _ b) =
          IsLocalRing.residue A ⟨algebraMap K L (b : K), ValuationSubring.mem_comap.mp b.2⟩) :
    Algebra.trdeg (IsLocalRing.ResidueField (A.comap (algebraMap K L)))
        (IsLocalRing.ResidueField A) ≤ Algebra.trdeg K L := by
  classical
  rw [Algebra.trdeg]
  refine ciSup_le' fun s => ?_

  choose y hy using fun i : s.1 => IsLocalRing.residue_surjective (R := A) (i : IsLocalRing.ResidueField A)
  have hind : AlgebraicIndependent (IsLocalRing.ResidueField (B K A))
      (fun i : s.1 => IsLocalRing.residue A (y i)) := by
    have : (fun i : s.1 => IsLocalRing.residue A (y i)) = fun i : s.1 => (i : IsLocalRing.ResidueField A) :=
      funext hy
    rw [this]
    exact s.2
  have hK := algebraicIndependent_lift K A hcompat y hind
  exact hK.cardinalMk_le_trdeg

end ValuationSubring.ResidueTrdeg
w03_reactivate "P2MW.S_ValuationSubring_trdeg_residueField_le_trdeg.ValuationSubring P2MW.S_ValuationSubring_trdeg_residueField_le_trdeg.ValuationSubring.ResidueTrdeg"
w03_reactivate "P2MW.S_ValuationSubring_trdeg_residueField_le_trdeg.ValuationSubring"

theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    [Algebra (IsLocalRing.ResidueField (A.comap (algebraMap K L))) (IsLocalRing.ResidueField A)]
    (hcompat : ∀ b : A.comap (algebraMap K L),
      algebraMap (IsLocalRing.ResidueField (A.comap (algebraMap K L))) (IsLocalRing.ResidueField A)
        (IsLocalRing.residue _ b) =
          IsLocalRing.residue A ⟨algebraMap K L (b : K), ValuationSubring.mem_comap.mp b.2⟩) :
    Algebra.trdeg (IsLocalRing.ResidueField (A.comap (algebraMap K L)))
        (IsLocalRing.ResidueField A) ≤ Algebra.trdeg K L :=
  ValuationSubring.ResidueTrdeg.main K A hcompat
end S_ValuationSubring_trdeg_residueField_le_trdeg
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
