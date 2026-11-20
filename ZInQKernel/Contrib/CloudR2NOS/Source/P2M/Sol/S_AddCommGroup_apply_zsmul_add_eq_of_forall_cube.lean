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
  Source file    : P2M/Sol/S_AddCommGroup_apply_zsmul_add_eq_of_forall_cube.lean
  Source sha256  : ae2f5bfdb7e5e0ae2e73d5e3198e03579937e3e08002fd4f3ec8d6fc19c39fff
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
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

namespace P2MW.S_AddCommGroup_apply_zsmul_add_eq_of_forall_cube
r2nos_namespace_dual

set_option autoImplicit false

namespace P2mQuad
r2nos_namespace_dual

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

theorem tri_succ (n : ℤ) : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
  have h : (n + 1) * (n + 1 - 1) = n * (n - 1) + n * 2 := by ring
  rw [h, Int.add_mul_ediv_right _ _ two_ne_zero]

theorem tri_zero : (0 : ℤ) * (0 - 1) / 2 = 0 := by norm_num

theorem eq_of_second_difference (g : ℤ → N) (D : N)
    (h : ∀ n : ℤ, g (n + 2) - 2 • g (n + 1) + g n = D) (n : ℤ) :
    g n = g 0 + n • (g 1 - g 0) + (n * (n - 1) / 2) • D := by

  have h1 : ∀ n : ℤ, g (n + 1) - g n = (g 1 - g 0) + n • D := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih =>
      have hk := h k
      have e : (k : ℤ) + 1 + 1 = k + 2 := by ring
      rw [e]

      have : g (k + 2) - g (k + 1) = (g (k + 1) - g k) + D := by
        rw [← hk]; abel
      rw [this, ih, add_smul, one_smul]
      abel
    | pred k ih =>

      have hk := h (-(k : ℤ) - 1)
      have e1 : (-(k : ℤ) - 1 + 2) = -k + 1 := by ring
      have e2 : (-(k : ℤ) - 1 + 1) = -k := by ring
      rw [e1, e2] at hk
      rw [e2]
      have : g (-(k : ℤ)) - g (-k - 1) = (g (-k + 1) - g (-k)) - D := by
        rw [← hk]; abel
      rw [this, ih, sub_smul, one_smul]
      abel
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have := h1 k
    rw [tri_succ, add_smul, eq_add_of_sub_eq' this |>.trans (by rfl), ih, add_smul, one_smul]
    abel
  | pred k ih =>
    have hk := h1 (-(k : ℤ) - 1)
    have e2 : (-(k : ℤ) - 1 + 1) = -k := by ring
    rw [e2] at hk

    have : g (-(k : ℤ) - 1) = g (-k) - ((g 1 - g 0) + (-(k : ℤ) - 1) • D) := by
      rw [← hk]; abel
    rw [this, ih]
    have ht : (-(k : ℤ)) * (-(k : ℤ) - 1) / 2 = (-(k : ℤ) - 1) * (-(k : ℤ) - 1 - 1) / 2 + (-(k : ℤ) - 1) := by
      have := tri_succ (-(k : ℤ) - 1)
      rw [e2] at this
      exact this
    rw [ht, add_smul, sub_smul, sub_smul, one_smul]
    abel

theorem main (Λ : M → N)
    (hΛ : ∀ x y z : M, Λ (x + y + z) - Λ (x + y) - Λ (x + z) - Λ (y + z) + Λ x + Λ y + Λ z = Λ 0)
    (x y : M) (n : ℤ) :
    Λ (n • x + y) = Λ y + n • (Λ (x + y) - Λ y) + (n * (n - 1) / 2) • (Λ (2 • x) - 2 • Λ x + Λ 0) := by
  set g : ℤ → M := fun n => n • x + y with hg
  have h2 : ∀ n : ℤ, Λ (g (n + 2)) - 2 • Λ (g (n + 1)) + Λ (g n) = Λ (2 • x) - 2 • Λ x + Λ 0 := by
    intro n
    have hc := hΛ (n • x + y) x x
    have e1 : n • x + y + x + x = g (n + 2) := by simp only [hg]; module
    have e2 : n • x + y + x = g (n + 1) := by simp only [hg]; module
    have e3 : x + x = 2 • x := (two_nsmul x).symm
    rw [e1, e2, e3] at hc
    have e4 : Λ (g n) = Λ (n • x + y) := rfl

    rw [two_nsmul (Λ (g (n + 1))), two_nsmul (Λ x)]
    have := hc

    calc Λ (g (n + 2)) - (Λ (g (n + 1)) + Λ (g (n + 1))) + Λ (g n)
        = (Λ (g (n + 2)) - Λ (g (n + 1)) - Λ (g (n + 1)) - Λ (2 • x) + Λ (n • x + y) + Λ x + Λ x)
            + (Λ (2 • x) - (Λ x + Λ x)) := by rw [e4]; abel
      _ = Λ 0 + (Λ (2 • x) - (Λ x + Λ x)) := by rw [this]
      _ = Λ (2 • x) - (Λ x + Λ x) + Λ 0 := by abel
  have hmain := eq_of_second_difference (fun n => Λ (g n)) _ h2 n
  have g0 : g 0 = y := by simp [hg]
  have g1 : g 1 = x + y := by simp [hg]
  simp only [g0, g1] at hmain
  exact hmain

end P2mQuad

theorem solution
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] (Λ : M → N)
    (hΛ : ∀ x y z : M,
      Λ (x + y + z) - Λ (x + y) - Λ (x + z) - Λ (y + z) + Λ x + Λ y + Λ z = Λ 0)
    (x y : M) (n : ℤ) :
    Λ (n • x + y) =
      Λ y + n • (Λ (x + y) - Λ y) + (n * (n - 1) / 2) • (Λ (2 • x) - 2 • Λ x + Λ 0) :=
  P2mQuad.main Λ hΛ x y n
end S_AddCommGroup_apply_zsmul_add_eq_of_forall_cube
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
