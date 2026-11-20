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
  Source file    : P2M/Sol/S_DoubleComplex_Convergence_finite_E2_q0.lean
  Source sha256  : 318305e003edf47a55e968d77e1979c1839a52eb2d41e86c4d10184038009cc4
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 multi-command source line(s) split into one command per line (no change of commands).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_DoubleComplex
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_DoubleComplex_Convergence_finite_E2_q0
r2nos_namespace_dual

set_option autoImplicit false

universe u

noncomputable section

namespace DoubleComplex
r2nos_namespace_dual
w03_export "DoubleComplex" "E₂I SubQuot Convergence"
w03_open "DoubleComplex"

section Extract

variable {R : Type u} [CommRing R]

theorem subquot_finite [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (s : SubQuot R M) : Module.Finite R s.carrier := by
  haveI : IsNoetherian R M := isNoetherian_of_isNoetherianRing_of_finite R M
  haveI : Module.Finite R ↥s.Z := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  exact Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.Quotient.mk_surjective _)

theorem filt_finite [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] {N : ℕ} (F : Fin (N + 1) → Submodule R M)
    (hF₀ : F 0 = ⊥) (hFmono : Monotone F)
    (hFgr : ∀ i : Fin N,
      Module.Finite R (↥(F i.succ) ⧸ (F i.castSucc).comap (F i.succ).subtype)) :
    ∀ i, Module.Finite R ↥(F i) := by
  intro i
  induction i using Fin.induction with
  | zero => rw [hF₀]; exact Module.Finite.iff_fg.mpr Submodule.fg_bot
  | succ j ih =>
    haveI := ih
    haveI hS : Module.Finite R ↥((F j.castSucc).comap (F j.succ).subtype) :=
      Module.Finite.equiv
        (Submodule.comapSubtypeEquivOfLe (hFmono (Fin.castSucc_le_succ j))).symm
    haveI hQ : Module.Finite R (↥(F j.succ) ⧸ (F j.castSucc).comap (F j.succ).subtype) := hFgr j
    exact Module.Finite.of_submodule_quotient ((F j.castSucc).comap (F j.succ).subtype)

namespace Convergence
r2nos_namespace_dual
w03_export "DoubleComplex.Convergence" "Bfilt_mono Einf Hfilt hZ0 Bfilt_gr Bfilt_top Bfilt_bot Hfilt_gr Bfilt"
end Convergence
r2nos_open_scoped "DoubleComplex.Convergence" in

theorem Convergence.finite_E2_q0 [IsNoetherianRing R]
    {E₂ : ℕ → ℕ → Type u} [∀ p q, AddCommGroup (E₂ p q)] [∀ p q, Module R (E₂ p q)]
    {H : ℕ → Type u} [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)] {N : ℕ}
    (conv : Convergence R E₂ H N)
    (hH : ∀ n, Module.Finite R (H n)) (hE₂ : ∀ p q, 1 ≤ q → Module.Finite R (E₂ p q))
    (p : ℕ) (hp : p ≤ N) : Module.Finite R (E₂ p 0) := by

  have hBfilt : ∀ i, Module.Finite R ↥(conv.Bfilt p i) := by
    refine filt_finite (conv.Bfilt p) (conv.Bfilt_bot p)
      (conv.Bfilt_mono p) (fun i => ?_)
    obtain ⟨p', q', hq', s, ⟨e⟩⟩ := conv.Bfilt_gr p i
    haveI := hE₂ p' q' hq'
    haveI := subquot_finite s
    exact Module.Finite.equiv e.symm

  haveI hEinf : Module.Finite R (conv.Einf p 0).carrier := by
    let pF : Fin (N + 1) := ⟨p, Nat.lt_succ_of_le hp⟩
    obtain ⟨e⟩ := conv.Hfilt_gr pF
    haveI := hH p
    haveI : IsNoetherian R (H p) := isNoetherian_of_isNoetherianRing_of_finite R (H p)
    haveI : Module.Finite R ↥(conv.Hfilt p pF.succ) :=
      Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
    haveI hgrH : Module.Finite R
        (↥(conv.Hfilt p pF.succ) ⧸
          (conv.Hfilt p pF.castSucc).comap (conv.Hfilt p pF.succ).subtype) :=
      Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.Quotient.mk_surjective _)
    exact Module.Finite.equiv e

  haveI hB : Module.Finite R ↥(conv.Einf p 0).B := conv.Bfilt_top p ▸ hBfilt (Fin.last N)
  haveI hBc : Module.Finite R ↥((conv.Einf p 0).B.comap (conv.Einf p 0).Z.subtype) :=
    Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe (conv.Einf p 0).hBZ).symm
  haveI hZ : Module.Finite R ↥(conv.Einf p 0).Z :=
    Module.Finite.of_submodule_quotient ((conv.Einf p 0).B.comap (conv.Einf p 0).Z.subtype)
  haveI : Module.Finite R ↥(⊤ : Submodule R (E₂ p 0)) := conv.hZ0 p ▸ hZ
  exact Module.Finite.equiv Submodule.topEquiv

end Extract

end DoubleComplex

theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R]
    {E₂ : ℕ → ℕ → Type u} [∀ p q, AddCommGroup (E₂ p q)] [∀ p q, Module R (E₂ p q)]
    {H : ℕ → Type u} [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)] {N : ℕ}
    (conv : DoubleComplex.Convergence R E₂ H N)
    (hH : ∀ n, Module.Finite R (H n)) (hE₂ : ∀ p q, 1 ≤ q → Module.Finite R (E₂ p q))
    (p : ℕ) (hp : p ≤ N) : Module.Finite R (E₂ p 0) :=
  DoubleComplex.Convergence.finite_E2_q0 conv hH hE₂ p hp

end
end S_DoubleComplex_Convergence_finite_E2_q0
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
