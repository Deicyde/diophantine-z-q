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
  Source file    : P2M/Sol/S_PrimeSpectrum_eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal.lean
  Source sha256  : b6be0b5fa8908eb9f4ccfaedf8d60aa46b418ded8c3f90b6ebe07f1ab1fa29d2
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
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

namespace P2MW.S_PrimeSpectrum_eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal
r2nos_namespace_dual

set_option autoImplicit false

open scoped TensorProduct
r2nos_open_scoped_dual "TensorProduct"

universe u v w

theorem solution
    {A : Type u} [CommRing A] [IsJacobsonRing A]
    (U : Set (PrimeSpectrum A)) (hU : IsOpen U) (hne : U.Nonempty)
    (htrans : ∀ P Q : PrimeSpectrum A, P.asIdeal.IsMaximal → Q.asIdeal.IsMaximal → P ∈ U → Q ∈ U) :
    U = Set.univ := by
  classical
  obtain ⟨P, hP⟩ := hne
  obtain ⟨s, hs⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus _).mp (isClosed_compl_iff.mpr hU)

  have hPnot : ¬ (s ⊆ (P.asIdeal : Set A)) := by
    intro h
    have : P ∈ Uᶜ := by rw [hs]; exact (PrimeSpectrum.mem_zeroLocus _ _).mpr h
    exact this hP
  rw [Set.not_subset] at hPnot
  obtain ⟨f, hfs, hfP⟩ := hPnot

  have hfrad : f ∉ (⊥ : Ideal A).radical := fun h => hfP (by
    have h' : f ∈ nilradical A := h
    exact nilradical_le_prime P.asIdeal h')
  rw [Ideal.radical_eq_jacobson, Ideal.jacobson, Submodule.mem_sInf] at hfrad
  push_neg at hfrad
  obtain ⟨M, ⟨-, hM⟩, hfM⟩ := hfrad
  have hMU : (⟨M, hM.isPrime⟩ : PrimeSpectrum A) ∈ U := by
    by_contra h
    have h' : (⟨M, hM.isPrime⟩ : PrimeSpectrum A) ∈ Uᶜ := h
    rw [hs, PrimeSpectrum.mem_zeroLocus] at h'
    exact hfM (h' hfs)

  apply Set.eq_univ_of_forall
  intro Q
  by_contra hQ
  have hQz : s ⊆ (Q.asIdeal : Set A) := by
    have h' : Q ∈ Uᶜ := hQ
    rw [hs, PrimeSpectrum.mem_zeroLocus] at h'
    exact h'
  obtain ⟨M', hM', hQM'⟩ := Q.asIdeal.exists_le_maximal Q.isPrime.ne_top
  have hM'U : (⟨M', hM'.isPrime⟩ : PrimeSpectrum A) ∈ U :=
    htrans ⟨M, hM.isPrime⟩ ⟨M', hM'.isPrime⟩ hM hM' hMU
  have hM'c : (⟨M', hM'.isPrime⟩ : PrimeSpectrum A) ∈ Uᶜ := by
    rw [hs, PrimeSpectrum.mem_zeroLocus]
    intro a ha
    exact hQM' (hQz ha)
  exact hM'c hM'U
end S_PrimeSpectrum_eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
