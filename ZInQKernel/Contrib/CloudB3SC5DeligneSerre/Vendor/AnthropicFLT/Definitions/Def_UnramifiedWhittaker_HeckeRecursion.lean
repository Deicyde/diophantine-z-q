/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_UnramifiedWhittaker_HeckeRecursion (git blob ea072921880c0001c48091f33bc3e982cb001267, sha256 54ef35f26287d6b84e518c8564a595caa1ec37ec08ba58aa39f928e1c6b4835c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open Matrix

namespace UnramifiedWhittaker

def heckeRecursionSeq (N lam om : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => lam / N
  | m + 2 => (lam * heckeRecursionSeq N lam om (m + 1) - om * heckeRecursionSeq N lam om m) / N

def torusFactor (N lam om : ℂ) (m : ℤ) : ℂ :=
  if 0 ≤ m then heckeRecursionSeq N lam om m.toNat else 0

section Matrices

variable {K : Type*} [Field K]

def unipotent (x : K) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![1, x; 0, 1] (by simp [det_fin_two_of])

def diagZ (π : K) (hπ : π ≠ 0) (m : ℤ) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![π ^ m, 0; 0, 1] (by simp [det_fin_two_of, zpow_ne_zero m hπ])

def repSome (π : K) (hπ : π ≠ 0) (β : K) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![π, β; 0, 1] (by simp [det_fin_two_of, hπ])

def repInf (π : K) (hπ : π ≠ 0) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, π] (by simp [det_fin_two_of, hπ])

def scalarPi (π : K) (hπ : π ≠ 0) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![π, 0; 0, π] (by simp [det_fin_two_of, hπ])

end Matrices

section Adelic

open IsDedekindDomain NumberField AdelicDock

variable {R : Type*} (K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def placeEmbed (v : HeightOneSpectrum R) :
    GL (Fin 2) (v.adicCompletion K) →* GL (Fin 2) (AdeleRing R K) :=
  (finEmbed R K).comp (localEmbed R K v)

end Adelic

end UnramifiedWhittaker

end
