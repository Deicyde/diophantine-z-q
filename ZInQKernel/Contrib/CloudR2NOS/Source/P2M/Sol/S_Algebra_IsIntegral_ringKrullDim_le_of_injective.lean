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
  Source file    : P2M/Sol/S_Algebra_IsIntegral_ringKrullDim_le_of_injective.lean
  Source sha256  : 1fb09410d26426e399af42cdc8474f2bf48285214ff2582f331bd98687ccae98
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * BATCH-2 HAND REPAIRS (lane4, recorded): Mathlib 56a0058 states `Ideal.exists_ideal_over_prime_of_isIntegral` with `Ideal.under` (a… (×1)
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

namespace P2MW.S_Algebra_IsIntegral_ringKrullDim_le_of_injective
r2nos_namespace_dual

set_option autoImplicit false

theorem solution
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R ≤ ringKrullDim S := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [ringKrullDim_eq_bot_of_subsingleton]; exact bot_le
  haveI : Nontrivial S := hinj.nontrivial

  have hbot : ∀ P : Ideal R, (⊥ : Ideal S).comap (algebraMap R S) ≤ P := by
    intro P x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    have : x = 0 := hinj (by rw [hx, map_zero])
    rw [this]; exact zero_mem _

  have key : ∀ n : ℕ, ∀ l : LTSeries (PrimeSpectrum R), l.length = n →
      ∃ l' : LTSeries (PrimeSpectrum S), l'.length = n ∧
        l'.last.asIdeal.comap (algebraMap R S) = l.last.asIdeal := by
    intro n
    induction n with
    | zero =>
      intro l hl
      obtain ⟨Q, -, hQ, hQc⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral l.last.asIdeal (⊥ : Ideal S) (hbot _)
      exact ⟨RelSeries.singleton _ ⟨Q, hQ⟩, rfl, by simpa using hQc⟩
    | succ n ih =>
      intro l hl
      have hne : l.length ≠ 0 := by omega
      obtain ⟨l'', hl'', hc⟩ := ih l.eraseLast (by simp [RelSeries.eraseLast_length, hl])
      have hrel : l.eraseLast.last < l.last := l.eraseLast_last_rel_last hne
      obtain ⟨Q, hQge, hQ, hQc⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral l.last.asIdeal l''.last.asIdeal
          (by rw [Ideal.under_def, hc]; exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hrel.le)
      have hlt : l''.last < ⟨Q, hQ⟩ := by
        refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hQge) ?_
        intro heq
        have h1 : l''.last.asIdeal = Q := by rw [heq]
        have h2 : l.eraseLast.last.asIdeal = l.last.asIdeal := by rw [← hc, ← hQc, h1]
        exact (ne_of_lt hrel) (PrimeSpectrum.ext h2)
      refine ⟨l''.snoc ⟨Q, hQ⟩ hlt, by simp [RelSeries.snoc_length, hl''], ?_⟩
      simpa [RelSeries.last_snoc] using hQc
  rw [ringKrullDim, ringKrullDim, Order.krullDim_eq_iSup_length, Order.krullDim_eq_iSup_length]
  refine WithBot.coe_le_coe.mpr (iSup_le fun l => ?_)
  obtain ⟨l', hl', -⟩ := key l.length l rfl
  exact le_iSup_of_le l' (by rw [hl'])
end S_Algebra_IsIntegral_ringKrullDim_le_of_injective
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
