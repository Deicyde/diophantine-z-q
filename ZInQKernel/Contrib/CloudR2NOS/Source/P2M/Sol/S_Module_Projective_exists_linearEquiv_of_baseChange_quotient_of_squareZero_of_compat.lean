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
  Source file    : P2M/Sol/S_Module_Projective_exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat.lean
  Source sha256  : c03b256c7be832dd21fb2f1d106a4ffb5ef861bb4dee703e9c36478ea91d7efc
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 multi-command source line(s) split into one command per line (no change of commands).
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

namespace P2MW.S_Module_Projective_exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat
r2nos_namespace_dual

universe u

set_option autoImplicit false

open TensorProduct
r2nos_open_dual "TensorProduct"

namespace Module
r2nos_namespace_dual
w03_export "Module" "Injective mk restrictScalars Finite.fg_top jacobson Projective projective_lifting_property"
namespace Projective
r2nos_namespace_dual
w03_export "Module.Projective" "mk"
end Module.Projective
r2nos_open_scoped "Module Module.Projective" in

private lemma Module.Projective.le_jacobson_bot_of_sq_eq_bot_aux
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥) :
    I ≤ (⊥ : Ideal R).jacobson := by
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  have hxx : x * x = 0 := by
    have hmem : x * x ∈ I ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul hx hx
    rw [hI] at hmem
    simpa using hmem
  have hxy : IsNilpotent (x * y) := ⟨2, by
    calc (x * y) ^ 2 = (x * x) * (y * y) := by ring
      _ = 0 := by rw [hxx, zero_mul]⟩
  exact hxy.isUnit_add_one

r2nos_open_scoped "Module Module.Projective" in

private lemma Module.Projective.surjective_of_one_tmul_aux
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    {N M : Type u} [AddCommGroup N] [AddCommGroup M] [Module R N] [Module R M]
    [Module.Finite R M] (f : N →ₗ[R] M)
    (hf : ∀ m : M, ∃ n : N, (1 : R ⧸ I) ⊗ₜ[R] f n = (1 : R ⧸ I) ⊗ₜ[R] m) :
    Function.Surjective f := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI ?_
  intro m _
  obtain ⟨n, hn⟩ := hf m
  have key : ∀ x : M, quotTensorEquivQuotSMul M I ((1 : R ⧸ I) ⊗ₜ[R] x) =
      Submodule.Quotient.mk x := by
    intro x
    rw [← map_one (Ideal.Quotient.mk I), quotTensorEquivQuotSMul_mk_tmul, one_smul]
  have hq : (Submodule.Quotient.mk (f n) : M ⧸ (I • ⊤ : Submodule R M)) =
      Submodule.Quotient.mk m := by
    rw [← key, ← key, hn]
  have hmem : f n - m ∈ I • (⊤ : Submodule R M) := (Submodule.Quotient.eq _).mp hq
  have hsplit : m = f n - (f n - m) := by abel
  rw [hsplit]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left (LinearMap.mem_range_self f n))
    (Submodule.mem_sup_right hmem)

theorem solution
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    (P₁ P₂ : Type u) [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₁] [Module R P₂]
    [Module.Projective R P₁] [Module.Finite R P₁]
    [Module.Projective R P₂] [Module.Finite R P₂]
    (e : ((R ⧸ I) ⊗[R] P₁) ≃ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] P₂)) :
    ∃ σ' : P₁ ≃ₗ[R] P₂, ∀ p : P₁, (1 : R ⧸ I) ⊗ₜ[R] σ' p = e ((1 : R ⧸ I) ⊗ₜ[R] p) := by

  have hmk₁ : Function.Surjective (TensorProduct.mk R (R ⧸ I) P₁ 1) :=
    TensorProduct.mk_surjective R P₁ (R ⧸ I) Ideal.Quotient.mk_surjective
  have hmk₂ : Function.Surjective (TensorProduct.mk R (R ⧸ I) P₂ 1) :=
    TensorProduct.mk_surjective R P₂ (R ⧸ I) Ideal.Quotient.mk_surjective

  obtain ⟨f, hf⟩ := Module.projective_lifting_property (TensorProduct.mk R (R ⧸ I) P₂ 1)
    ((e.restrictScalars R).toLinearMap ∘ₗ TensorProduct.mk R (R ⧸ I) P₁ 1) hmk₂
  obtain ⟨g, hg⟩ := Module.projective_lifting_property (TensorProduct.mk R (R ⧸ I) P₁ 1)
    ((e.symm.restrictScalars R).toLinearMap ∘ₗ TensorProduct.mk R (R ⧸ I) P₂ 1) hmk₁
  have hf' : ∀ p : P₁, (1 : R ⧸ I) ⊗ₜ[R] f p = e ((1 : R ⧸ I) ⊗ₜ[R] p) := fun p =>
    LinearMap.congr_fun hf p
  have hg' : ∀ q : P₂, (1 : R ⧸ I) ⊗ₜ[R] g q = e.symm ((1 : R ⧸ I) ⊗ₜ[R] q) := fun q =>
    LinearMap.congr_fun hg q

  have hgf : ∀ p : P₁, (1 : R ⧸ I) ⊗ₜ[R] (g ∘ₗ f) p = (1 : R ⧸ I) ⊗ₜ[R] p := fun p => by
    rw [LinearMap.comp_apply, hg', hf', LinearEquiv.symm_apply_apply]
  have hfg : ∀ q : P₂, (1 : R ⧸ I) ⊗ₜ[R] (f ∘ₗ g) q = (1 : R ⧸ I) ⊗ₜ[R] q := fun q => by
    rw [LinearMap.comp_apply, hf', hg', LinearEquiv.apply_symm_apply]

  have hJ := Module.Projective.le_jacobson_bot_of_sq_eq_bot_aux I hI
  have sgf : Function.Surjective (g ∘ₗ f) :=
    Module.Projective.surjective_of_one_tmul_aux I hJ (g ∘ₗ f) fun p => ⟨p, hgf p⟩
  have sfg : Function.Surjective (f ∘ₗ g) :=
    Module.Projective.surjective_of_one_tmul_aux I hJ (f ∘ₗ g) fun q => ⟨q, hfg q⟩

  have igf : Function.Injective (g ∘ₗ f) :=
    OrzechProperty.injective_of_surjective_endomorphism _ sgf
  rw [LinearMap.coe_comp] at igf sfg
  have hbij : Function.Bijective f := ⟨igf.of_comp, sfg.of_comp⟩
  exact ⟨LinearEquiv.ofBijective f hbij, fun p => hf' p⟩
end S_Module_Projective_exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
