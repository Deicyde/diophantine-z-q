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
  Source file    : Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean
  Source sha256  : a4ee8d71aba6d46cea6a7d856214c63fc80a9a38787a54325bf0dd31b7b18a2f
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 10 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 10 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 1600000`; `set_option linter.unusedSectionVars false`; `set_option linter.unusedSectionVars false`; `set_option synthInstance.maxHeartbeats 800000`; `set_option maxHeartbeats 1600000`; `set_option maxHeartbeats 1600000`; `set_option synthInstance.maxHeartbeats 800000`; `set_option linter.unusedSectionVars false`; `set_option maxHeartbeats 1600000`; `set_option synthInstance.maxHeartbeats 800000`; `set_option linter.unusedSectionVars false`; `set_option maxHeartbeats 1600000`; `set_option synthInstance.maxHeartbeats 800000`; `set_option linter.unusedSectionVars false`; `set_option maxHeartbeats 1600000`; `set_option linter.unusedSectionVars false`; `set_option maxHeartbeats 1600000`; `set_option linter.unusedSectionVars false`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 9 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_ModularCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_LocalResidue
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_PlaceCompletion
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

set_option autoImplicit false

open LinearMap Submodule
r2nos_open_dual "LinearMap Submodule"

noncomputable section

namespace ModularCurve.KwF4gRRTate
r2nos_namespace_dual

section FinrankTrace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def finrankTrace (φ : V →ₗ[K] V) [FiniteDimensional K (LinearMap.range φ)] : K :=
  LinearMap.trace K (LinearMap.range φ)
    (φ.restrict (fun x _ => LinearMap.mem_range_self φ x))

end FinrankTrace

section TateComm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def tateComm (pA φ ψ : V →ₗ[K] V) : V →ₗ[K] V :=
  pA ∘ₗ φ ∘ₗ pA ∘ₗ ψ - pA ∘ₗ ψ ∘ₗ pA ∘ₗ φ

theorem tateComm_apply (pA φ ψ : V →ₗ[K] V) (x : V) :
    tateComm pA φ ψ x = pA (φ (pA (ψ x))) - pA (ψ (pA (φ x))) := rfl

theorem tateComm_mem_range (pA φ ψ : V →ₗ[K] V) (x : V) :
    tateComm pA φ ψ x ∈ LinearMap.range pA :=
  sub_mem (LinearMap.mem_range_self pA _) (LinearMap.mem_range_self pA _)

theorem tateComm_antisymm (pA φ ψ : V →ₗ[K] V) :
    tateComm pA φ ψ = - tateComm pA ψ φ := by
  unfold tateComm; rw [neg_sub]

def tateCommRestrict (pA φ ψ : V →ₗ[K] V) :
    LinearMap.range pA →ₗ[K] LinearMap.range pA :=
  (tateComm pA φ ψ).restrict (fun x _ => tateComm_mem_range pA φ ψ x)

theorem tateCommRestrict_apply (pA φ ψ : V →ₗ[K] V) (a : LinearMap.range pA) :
    (tateCommRestrict pA φ ψ a : V) = tateComm pA φ ψ (a : V) := rfl

def tateCommTrace (pA φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range (tateCommRestrict pA φ ψ))] : K :=
  finrankTrace (tateCommRestrict pA φ ψ)

end TateComm

section TateFactoring

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem tateComm_eq_of_commute {pA φ ψ : V →ₗ[K] V}
    (hcomm : φ ∘ₗ ψ = ψ ∘ₗ φ) (a : V) :
    tateComm pA φ ψ a
      = pA (ψ (φ a - pA (φ a))) - pA (φ (ψ a - pA (ψ a))) := by
  have hφψ : φ (ψ a) = ψ (φ a) := by
    have := congrArg (fun f => f a) (congrArg DFunLike.coe hcomm)
    simpa using this
  rw [tateComm_apply, map_sub, map_sub, map_sub, map_sub, hφψ]
  abel

end TateFactoring

end ModularCurve.KwF4gRRTate

end

set_option autoImplicit false


noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing
r2nos_open_dual "IsDedekindDomain WithZero Module IsLocalRing"

namespace AlgebraicCurve
r2nos_namespace_dual

section CorrectedCarrier

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]

def kaehlerPullback (ωE : Ω[E⁄K]) : Ω[F⁄K] :=
  KaehlerDifferential.map K K E F ωE

variable {K F E}

variable (K F E)
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

end CorrectedCarrier

end AlgebraicCurve

end

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing
r2nos_open_dual "IsDedekindDomain WithZero Module IsLocalRing"

namespace AlgebraicCurve
r2nos_namespace_dual

namespace Place
r2nos_namespace_dual

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def regularSubmodule (w : Place K F) (ωF : Ω[F⁄K]) : Submodule K F where
  carrier := {f : F | f * w.differentialCoeff ωF ∈ w.toValuationSubring}
  zero_mem' := by simp only [Set.mem_setOf_eq, zero_mul]; exact zero_mem _
  add_mem' {f g} hf hg := by
    simp only [Set.mem_setOf_eq, add_mul]; exact add_mem hf hg
  smul_mem' c f hf := by
    simp only [Set.mem_setOf_eq, Algebra.smul_def, mul_assoc]
    exact mul_mem (w.algebraMap_mem' c) hf

end Place

end AlgebraicCurve

end

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing
r2nos_open_dual "IsDedekindDomain WithZero Module IsLocalRing"

namespace AlgebraicCurve
r2nos_namespace_dual

section KaehlerCotrace

variable (K E F : Type*) [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

abbrev kaehlerCotrace : Ω[E⁄K] →ₗ[E] Ω[F⁄K] :=
  KaehlerDifferential.map K K E F

variable {K E F}

end KaehlerCotrace

end AlgebraicCurve

end

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place IsDedekindDomain
r2nos_open_dual "AlgebraicCurve AlgebraicCurve.Place IsDedekindDomain"

noncomputable section

namespace AlgebraicCurve
r2nos_namespace_dual

section LocalResidueCompletion

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

variable [HasCanonicalLocalResidueKStar K E]

def kwHgfV352_localResidueCompletion (v : Place K E) (xh : v.adicCompletion) :
    v.ResidueField :=
  v.localResidue (kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh).choose

end LocalResidueCompletion

section CompletionTraceAt

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]

def kwHgfV352_completionTraceAt [FiniteDimensional E F]
    (v : Place K E) (w' : Place K F) (hw' : w' ∈ v.fiber F) (g : F) :
    v.adicCompletion :=
  Place.mem_fiber.mp hw' ▸ kw_ffgc_completionTraceF' E w' g

end CompletionTraceAt

section MPGKPowBasisLocalMint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

def KwHgfV352R3MPGKPowBasisLocal : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [∀ w : Place K F, w.FiniteResidue]
    [FiniteDimensional E F]
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0)
    (v : Place K E) (w : Place K F) (hw : w ∈ v.fiber F)
    (_ : ∀ w'' ∈ v.fiber F,
      w''.differentialCoeff (kaehlerPullback K F E ωE) ∈ w''.toValuationSubring)
    (θ : F) (_ : ∀ w' ∈ v.fiber F, θ ∈ w'.toValuationSubring)
    (π : F) (_ : π ≠ 0) (_ : w.ord π = 1)
    (_ : ∀ w' ∈ v.fiber F, w' ≠ w → w'.ord π = 0)
    (j : ℕ) (_ : j < Module.finrank K w.ResidueField) (k : ℕ),
    kaehlerResidueTerm (kaehlerPullback K F E ωE)
        (diagonalHom K F (θ ^ j * (π ^ (k + 1))⁻¹)) w
      = Algebra.trace K v.ResidueField
          (kwHgfV352_localResidueCompletion v
            (kwHgfV352_completionTraceAt v w hw (θ ^ j * (π ^ (k + 1))⁻¹)
              * algebraMap E v.adicCompletion (v.differentialCoeff ωE)))

end MPGKPowBasisLocalMint

section CompletionTraceSumMint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

def KwHgfV352CompletionTraceSum : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (g : F),
    algebraMap E v.adicCompletion (Algebra.trace E F g)
      = ∑ w' ∈ (v.fiber F).attach, kwHgfV352_completionTraceAt v w'.1 w'.2 g

end CompletionTraceSumMint

end AlgebraicCurve

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place LinearMap Submodule
r2nos_open_dual "AlgebraicCurve AlgebraicCurve.Place LinearMap Submodule"
open ModularCurve.KwF4gRRTate
r2nos_open_dual "ModularCurve.KwF4gRRTate"

noncomputable section

namespace ModularCurve.KwF4gRRTate
r2nos_namespace_dual

section TateProj

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

def adicIntegersKSubmod : Submodule K u.adicCompletion where
  carrier := u.adicCompletionIntegers
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' c x hx := by
    rw [Algebra.smul_def]
    exact mul_mem (by
      rw [IsScalarTower.algebraMap_apply K L u.adicCompletion]
      exact (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff u _).mpr
        (u.algebraMap_mem' c)) hx

def tateProj : u.adicCompletion →ₗ[K] u.adicCompletion :=
  letI B := Classical.choose (Submodule.exists_isCompl (adicIntegersKSubmod u))
  (adicIntegersKSubmod u).subtype ∘ₗ
    Submodule.projectionOnto (adicIntegersKSubmod u) B
      (Classical.choose_spec (Submodule.exists_isCompl (adicIntegersKSubmod u)))

end TateProj

section TateResDef

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

abbrev lmulK (fh : u.adicCompletion) : u.adicCompletion →ₗ[K] u.adicCompletion :=
  (Algebra.lmul K u.adicCompletion) fh

def tateRes (fh gh : u.adicCompletion)
    [FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh) (lmulK u gh)))] : K :=
  tateCommTrace (tateProj u) (lmulK u fh) (lmulK u gh)

end TateResDef

section TateAtoms

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

def KwF4gRRTateCommFinite : Prop :=
  ∀ (u : Place K L) (fh gh : u.adicCompletion),
    FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh) (lmulK u gh)))

variable [HasCanonicalLocalResidueKStar K L]

def KwF4gRRTateAgreement (hfin : KwF4gRRTateCommFinite K L) : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue] (fh : u.adicCompletion),
    haveI := hfin u fh (algebraMap L u.adicCompletion u.uniformizer)
    tateRes u fh (algebraMap L u.adicCompletion u.uniformizer)
      = Algebra.trace K u.ResidueField (kwHgfV352_localResidueCompletion u fh)

variable (F E : Type*) [Field F] [Algebra K F] [Field E] [Algebra K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]

def KwF4gRRTateChainRule (hfinF : KwF4gRRTateCommFinite K F) : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    [Nontrivial Ω[E⁄K]] [Nontrivial Ω[F⁄K]]
    (v : Place K E) [v.DCoordGenerates] (w : Place K F) [w.DCoordGenerates]
    (_ : w ∈ v.fiber F) (fh : w.adicCompletion),
    haveI := hfinF w fh (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
    haveI := hfinF w (fh * algebraMap F w.adicCompletion
      (w.differentialCoeff (kaehlerPullback K F E v.dCoord)))
      (algebraMap F w.adicCompletion w.uniformizer)
    tateRes w fh (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
      = tateRes w (fh * algebraMap F w.adicCompletion
          (w.differentialCoeff (kaehlerPullback K F E v.dCoord)))
          (algebraMap F w.adicCompletion w.uniformizer)

def KwF4gRRTateTraceCompat (hfinF : KwF4gRRTateCommFinite K F)
    (hfinE : KwF4gRRTateCommFinite K E) : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w : Place K F) (hw : w ∈ v.fiber F) (g : F),
    haveI := hfinF w (algebraMap F w.adicCompletion g)
      (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
    haveI := hfinE v (kwHgfV352_completionTraceAt v w hw g)
      (algebraMap E v.adicCompletion v.uniformizer)
    tateRes w (algebraMap F w.adicCompletion g)
        (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
      = tateRes v (kwHgfV352_completionTraceAt v w hw g)
          (algebraMap E v.adicCompletion v.uniformizer)

end TateAtoms

end ModularCurve.KwF4gRRTate

end

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place FunctionField KaehlerDifferential
r2nos_open_dual "AlgebraicCurve AlgebraicCurve.Place FunctionField KaehlerDifferential"

noncomputable section

namespace ModularCurve.KwF4R1V391a
r2nos_namespace_dual

section Mint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

def KwF4R1V391aResidueTraceCompletionCommute : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    [∀ w : Place K F, w.FiniteResidue] [FiniteDimensional E F]
    [Nontrivial Ω[E⁄K]] (v : Place K E) [v.DCoordGenerates]
    (w : Place K F) [w.DCoordGenerates] (_ : w ∈ v.fiber F) (g : F),
    kaehlerResidueTerm (kaehlerPullback K F E v.dCoord) (diagonalHom K F g) w
      = Algebra.trace K v.ResidueField
          (kwHgfV352_localResidueCompletion v
            (kwHgfV352_completionTraceAt v w ‹w ∈ v.fiber F› g))

end Mint

end ModularCurve.KwF4R1V391a

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve
r2nos_namespace_dual

open scoped Polynomial
r2nos_open_scoped_dual "Polynomial"

section KCurrencyRow

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

def FiberKaehlerCotraceResidueIdentityK : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (RfamF : ∀ w : Place K F, w.CanonicalLocalResidueDataK)
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0),
    ∃ RfamE : ∀ v : Place K E, v.CanonicalLocalResidueDataK,
      ∀ (v : Place K E) (f : F),
        ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F f) w
          = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F f)) v

end KCurrencyRow

end AlgebraicCurve

end

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve
r2nos_namespace_dual

open scoped Polynomial
r2nos_open_scoped_dual "Polynomial"

section KCurrencyRowA

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

def CotraceResidueIdentityOnFiberLocalizedK : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (RfamF : ∀ w : Place K F, w.CanonicalLocalResidueDataK)
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0),
    ∃ RfamE : ∀ v : Place K E, v.CanonicalLocalResidueDataK,
      ∀ (v : Place K E) (p : F),
        (∀ w₁ ∈ v.fiber F, ∀ w₂ ∈ v.fiber F,
          p ∉ w₁.regularSubmodule (kaehlerPullback K F E ωE) →
          p ∉ w₂.regularSubmodule (kaehlerPullback K F E ωE) → w₁ = w₂) →
        ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F p) w
          = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F p)) v

end KCurrencyRowA

end AlgebraicCurve

end
end
end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
