/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_ModularCurve_AbelFibreSum (git blob df6255413cae52e1153acc5bdb9a977132893b31, sha256 0670220cc77d01fff96decd2573541a4c1e4c7266aa3b96665e008bd4f193bcf).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups

namespace ModularCurve

noncomputable def valueMultiplicity (F : ℍ → ℂ) (t : ℂ) (τ : ℍ) : ℕ :=
  (meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ)).untop₀.toNat

noncomputable def orbifoldIndex (N : ℕ) (τ : ℍ) : ℕ :=
  Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) / 2

noncomputable def abelFibreSum (N : ℕ) (F : ℍ → ℂ) (t : ℂ) :
    Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
  ∑ᶠ ξ : Quotient (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ),
    ((valueMultiplicity F t ξ.out : ℂ) / (orbifoldIndex N ξ.out : ℂ)) •
      periodAlong N UpperHalfPlane.I ξ.out

theorem valueMultiplicity_def (F : ℍ → ℂ) (t : ℂ) (τ : ℍ) :
    valueMultiplicity F t τ =
      (meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ)).untop₀.toNat :=
  rfl

theorem orbifoldIndex_def (N : ℕ) (τ : ℍ) :
    orbifoldIndex N τ = Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) / 2 :=
  rfl

theorem abelFibreSum_def (N : ℕ) (F : ℍ → ℂ) (t : ℂ) :
    abelFibreSum N F t =
      ∑ᶠ ξ : Quotient (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ),
        ((valueMultiplicity F t ξ.out : ℂ) / (orbifoldIndex N ξ.out : ℂ)) •
          periodAlong N UpperHalfPlane.I ξ.out :=
  rfl

theorem valueMultiplicity_of_eq_top {F : ℍ → ℂ} {t : ℂ} {τ : ℍ}
    (h : meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) = ⊤) :
    valueMultiplicity F t τ = 0 := by
  simp [valueMultiplicity, h]

theorem valueMultiplicity_of_eq_coe {F : ℍ → ℂ} {t : ℂ} {τ : ℍ} {n : ℕ}
    (h : meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) = ((n : ℤ) : WithTop ℤ)) :
    valueMultiplicity F t τ = n := by
  simp [valueMultiplicity, h]

end ModularCurve
