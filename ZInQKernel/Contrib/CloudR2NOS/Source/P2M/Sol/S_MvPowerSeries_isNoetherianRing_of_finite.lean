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
  Source file    : P2M/Sol/S_MvPowerSeries_isNoetherianRing_of_finite.lean
  Source sha256  : f2b39d9bef28c99912db0b3b4ddec0d1324d1acee5f739e489cccb138eacd1ba
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * BATCH-2 HAND REPAIRS (lane4, recorded): Mathlib 56a0058 adds a 3-argument `Finset.mem_antidiagonal` (sets s t); the source means `… (×6)
-/

import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.Data.Finsupp.Option
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_MvPowerSeries_isNoetherianRing_of_finite
r2nos_namespace_dual

universe u v w

noncomputable section

namespace M4cP1PS
r2nos_namespace_dual

open Finsupp Finset
r2nos_open_dual "Finsupp Finset"

section Equiv

variable {σ : Type*} {R : Type*} [CommSemiring R]

def optFun (φ : MvPowerSeries (Option σ) R) : PowerSeries (MvPowerSeries σ R) :=
  PowerSeries.mk fun n => fun d => MvPowerSeries.coeff (d.optionElim n) φ

def optInv (ψ : PowerSeries (MvPowerSeries σ R)) : MvPowerSeries (Option σ) R :=
  fun m => MvPowerSeries.coeff m.some (PowerSeries.coeff (m none) ψ)

@[scoped simp]
theorem coeff_coeff_optFun (φ : MvPowerSeries (Option σ) R) (n : ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (PowerSeries.coeff n (optFun φ)) = MvPowerSeries.coeff (d.optionElim n) φ := by
  rw [optFun, PowerSeries.coeff_mk]; rfl

@[scoped simp]
theorem coeff_optInv (ψ : PowerSeries (MvPowerSeries σ R)) (m : Option σ →₀ ℕ) :
    MvPowerSeries.coeff m (optInv ψ) = MvPowerSeries.coeff m.some (PowerSeries.coeff (m none) ψ) :=
  rfl

theorem optInv_optFun (φ : MvPowerSeries (Option σ) R) : optInv (optFun φ) = φ := by
  ext m
  rw [coeff_optInv, coeff_coeff_optFun, optionElim_some]

theorem optFun_optInv (ψ : PowerSeries (MvPowerSeries σ R)) : optFun (optInv ψ) = ψ := by
  ext n d
  rw [coeff_coeff_optFun, coeff_optInv, some_optionElim, optionElim_apply_none]

theorem optFun_add (φ ψ : MvPowerSeries (Option σ) R) : optFun (φ + ψ) = optFun φ + optFun ψ := by
  ext n d
  simp only [map_add, coeff_coeff_optFun]

theorem optFun_mul (φ ψ : MvPowerSeries (Option σ) R) : optFun (φ * ψ) = optFun φ * optFun ψ := by
  classical
  ext n d
  rw [coeff_coeff_optFun, MvPowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum]
  simp_rw [MvPowerSeries.coeff_mul, coeff_coeff_optFun]
  rw [← sum_product']
  refine sum_nbij' (fun p => ((p.1 none, p.2 none), (p.1.some, p.2.some)))
    (fun q => (q.2.1.optionElim q.1.1, q.2.2.optionElim q.1.2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [mem_product, Finset.HasAntidiagonal.mem_antidiagonal, Finset.HasAntidiagonal.mem_antidiagonal, ← Finsupp.add_apply, hp, ← some_add, hp,
      optionElim_apply_none, some_optionElim]
    exact ⟨rfl, rfl⟩
  · intro q hq
    rw [mem_product, Finset.HasAntidiagonal.mem_antidiagonal, Finset.HasAntidiagonal.mem_antidiagonal] at hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal, ← optionElim_add, hq.1, hq.2]
  · intro p _
    simp only [optionElim_some]
  · intro q _
    simp only [some_optionElim, optionElim_apply_none, Prod.mk.eta]
  · intro p _
    simp only [optionElim_some]

def optRingEquiv : MvPowerSeries (Option σ) R ≃+* PowerSeries (MvPowerSeries σ R) where
  toFun := optFun
  invFun := optInv
  left_inv := optInv_optFun
  right_inv := optFun_optInv
  map_mul' := optFun_mul
  map_add' := optFun_add

end Equiv

section Noetherian

variable (R : Type*) [CommRing R] [IsNoetherianRing R]

theorem isNoetherianRing_fin : ∀ n : ℕ, IsNoetherianRing (MvPowerSeries (Fin n) R)
  | 0 => isNoetherianRing_of_surjective R _ MvPowerSeries.C MvPowerSeries.C_surjective
  | n + 1 => by
    haveI := isNoetherianRing_fin n
    exact isNoetherianRing_of_ringEquiv (PowerSeries (MvPowerSeries (Fin n) R))
      (optRingEquiv.symm.trans (MvPowerSeries.renameEquiv R (finSuccEquiv n).symm).toRingEquiv)

theorem isNoetherianRing_of_finite (σ : Type*) [Finite σ] : IsNoetherianRing (MvPowerSeries σ R) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  haveI := isNoetherianRing_fin R n
  exact isNoetherianRing_of_ringEquiv (MvPowerSeries (Fin n) R)
    (MvPowerSeries.renameEquiv R e.symm).toRingEquiv

end Noetherian

end M4cP1PS
w03_reactivate "P2MW.S_MvPowerSeries_isNoetherianRing_of_finite.M4cP1PS"

end
w03_reactivate "P2MW.S_MvPowerSeries_isNoetherianRing_of_finite.M4cP1PS"

theorem solution {σ : Type u} {R : Type v} [Finite σ] [CommRing R]
    [IsNoetherianRing R] : IsNoetherianRing (MvPowerSeries σ R) :=
  M4cP1PS.isNoetherianRing_of_finite R σ
end S_MvPowerSeries_isNoetherianRing_of_finite
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
