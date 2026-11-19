/-
NOS-CORE PROBE STAGING COPY (nos-core-probe-001, lane4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_Subalgebra_faithfullyFlat_of_faithfullyFlat_range_baseChange.lean
  Source sha256  : 01b08f68e7c02539e07ab49ff4ba2e90f366d3a004bf44686f6c4bcc348bd2fd
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option synthInstance.maxHeartbeats 1600000`; `set_option maxHeartbeats 3200000`; `set_option maxHeartbeats 16000000 in`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * H4 lane 1 default-limit edition (2026-11-17, for H5 C4): the single declaration `solution`
    is split into the new helpers `algKK'` (the local algebra structure, as an abbrev),
    `towerk_K'`, `faithfullyFlat_K_K'` and `faithfullyFlat_K'_tensor` (the two halves of the
    original proof, verbatim); `solution` keeps its statement and assembles them. No option,
    import or budget added.
  * DRIFT/PORT-PITFALL RULES v1, applied: R3×9; rule citations in the batch ledger.
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

namespace P2MW.S_Subalgebra_faithfullyFlat_of_faithfullyFlat_range_baseChange
r2nos_namespace_dual

set_option autoImplicit false

open scoped TensorProduct
r2nos_open_scoped_dual "TensorProduct"

universe u v w

namespace S17Ta
r2nos_namespace_dual

universe u₁ u₂ u₃

section Descent

variable (R : Type u₁) [CommRing R] (S : Type u₂) [CommRing S] [Algebra R S]
variable (M : Type u₃) [AddCommGroup M] [Module R M]

noncomputable def cancelIso (N : Type*) [AddCommGroup N] [Module R N] :
    (S ⊗[R] M) ⊗[S] (S ⊗[R] N) ≃ₗ[S] S ⊗[R] (M ⊗[R] N) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S (S ⊗[R] M) N).trans
    (TensorProduct.AlgebraTensorModule.assoc R R S S M N)

theorem cancelIso_tmul {N : Type*} [AddCommGroup N] [Module R N] (s s' : S) (m : M) (n : N) :
    cancelIso R S M N ((s ⊗ₜ[R] m) ⊗ₜ[S] (s' ⊗ₜ[R] n)) = (s' * s) ⊗ₜ[R] (m ⊗ₜ[R] n) := by
  simp [cancelIso, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    TensorProduct.AlgebraTensorModule.assoc_tmul, TensorProduct.smul_tmul', smul_eq_mul]

theorem cancelIso_naturality {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddCommGroup N'] [Module R N']
    (f : N →ₗ[R] N') (z : (S ⊗[R] M) ⊗[S] (S ⊗[R] N)) :
    cancelIso R S M N' (((f.baseChange S).lTensor (S ⊗[R] M)) z)
      = (f.lTensor M).lTensor S (cancelIso R S M N z) := by
  induction z with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      induction x with
      | add x₁ x₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add, h₁, h₂]
      | tmul s m =>
          induction y with
          | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
          | tmul s' n =>
              rw [LinearMap.lTensor_tmul, LinearMap.baseChange_tmul, cancelIso_tmul, cancelIso_tmul,
                LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]

theorem faithfullyFlat_of_faithfullyFlat_baseChange [Module.FaithfullyFlat R S]
    [Module.FaithfullyFlat S (S ⊗[R] M)] : Module.FaithfullyFlat R M := by
  rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
  constructor
  ·
    rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
    intro N N' _ _ _ _ f hf
    rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective R S]
    have hfS : Function.Injective (f.baseChange S) := Module.Flat.lTensor_preserves_injective_linearMap f hf
    have hg : Function.Injective ((f.baseChange S).lTensor (S ⊗[R] M)) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hfS
    have hcomp : ((f.lTensor M).lTensor S : S ⊗[R] (M ⊗[R] N) → S ⊗[R] (M ⊗[R] N'))
        = (cancelIso R S M N') ∘ ((f.baseChange S).lTensor (S ⊗[R] M)) ∘ (cancelIso R S M N).symm := by
      funext z
      simp only [Function.comp_apply]
      rw [cancelIso_naturality, LinearEquiv.apply_symm_apply]
    rw [hcomp]
    exact (cancelIso R S M N').injective.comp (hg.comp (cancelIso R S M N).symm.injective)
  ·
    intro I hI hIM
    let J : Ideal S := I.map (algebraMap R S)
    have hJ : J ≠ ⊤ := by
      intro hJ
      have h1 := ((Module.FaithfullyFlat.iff_flat_and_proper_ideal R S).mp inferInstance).2 I hI
      apply h1
      have hJ' : Ideal.map (algebraMap R S) I = ⊤ := hJ
      rw [Ideal.smul_top_eq_map, hJ']
      rfl
    have h2 := ((Module.FaithfullyFlat.iff_flat_and_proper_ideal S (S ⊗[R] M)).mp inferInstance).2 J hJ
    apply h2

    have hone : ∀ m : M, (1 : S) ⊗ₜ[R] m ∈ J • (⊤ : Submodule S (S ⊗[R] M)) := by
      intro m
      have hm : m ∈ I • (⊤ : Submodule R M) := by rw [hIM]; exact Submodule.mem_top
      refine Submodule.smul_induction_on hm ?_ ?_
      · intro i hi n _
        have : (1 : S) ⊗ₜ[R] (i • n) = (algebraMap R S i) • ((1 : S) ⊗ₜ[R] n) := by
          rw [TensorProduct.tmul_smul, algebraMap_smul]
        rw [this]
        exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hi) Submodule.mem_top
      · intro x y hx hy
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ hx hy
    rw [eq_top_iff]
    rintro z -
    induction z with
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul s m =>
        have : s ⊗ₜ[R] m = s • ((1 : S) ⊗ₜ[R] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        exact Submodule.smul_mem _ s (hone m)

end Descent

end S17Ta

namespace S17Ta
r2nos_namespace_dual

section Plumbing

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [Algebra k H] (K : Subalgebra k H)
variable (k' : Type w) [Field k'] [Algebra k k']

noncomputable abbrev φ : k' ⊗[k] ↥K →ₐ[k'] k' ⊗[k] H := Algebra.TensorProduct.map (AlgHom.id k' k') K.val

noncomputable abbrev K' : Subalgebra k' (k' ⊗[k] H) := (φ K k').range

theorem φ_tmul (c : k') (x : ↥K) : φ K k' (c ⊗ₜ[k] x) = c ⊗ₜ[k] (x : H) := by
  rw [Algebra.TensorProduct.map_tmul]; rfl

theorem tmul_mem (c : k') {y : H} (hy : y ∈ K) : c ⊗ₜ[k] y ∈ K' K k' :=
  ⟨c ⊗ₜ[k] ⟨y, hy⟩, φ_tmul K k' c ⟨y, hy⟩⟩

noncomputable def ι : ↥K →ₐ[k] ↥(K' K k') :=
  (((φ K k').rangeRestrict).restrictScalars k).comp Algebra.TensorProduct.includeRight

theorem ι_apply_coe (x : ↥K) : ((ι K k' x : ↥(K' K k')) : k' ⊗[k] H) = (1 : k') ⊗ₜ[k] (x : H) := by
  show φ K k' ((1 : k') ⊗ₜ[k] x) = _
  exact φ_tmul K k' 1 x

end Plumbing

end S17Ta

open S17Ta in
r2nos_open_dual "S17Ta" in
/-- (H4 L1 edition) the `↥K`-algebra structure on `K'` used throughout `solution`. -/
noncomputable abbrev algKK' {k : Type u} [Field k] {H : Type v} [CommRing H] [Algebra k H]
    (K : Subalgebra k H) (k' : Type w) [Field k'] [Algebra k k'] : Algebra ↥K ↥(K' K k') :=
  (ι K k').toRingHom.toAlgebra

open S17Ta in
r2nos_open_dual "S17Ta" in
theorem towerk_K' {k : Type u} [Field k] {H : Type v} [CommRing H] [Algebra k H]
    (K : Subalgebra k H) (k' : Type w) [Field k'] [Algebra k k'] :
    letI := algKK' K k'
    IsScalarTower k ↥K ↥(K' K k') := by
  letI := algKK' K k'
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  apply Subtype.ext
  show algebraMap k (k' ⊗[k] H) c = ((ι K k' (algebraMap k ↥K c) : ↥(K' K k')) : k' ⊗[k] H)
  rw [ι_apply_coe, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
    Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]


open S17Ta in
r2nos_open_dual "S17Ta" in
/-- (H4 L1 edition) first half of `solution`: `K'` is faithfully flat over `K` (original steps). -/
theorem faithfullyFlat_K_K' {k : Type u} [Field k] {H : Type v} [CommRing H] [Algebra k H]
    (K : Subalgebra k H) (k' : Type w) [Field k'] [Algebra k k'] :
    letI := algKK' K k'
    Module.FaithfullyFlat ↥K ↥(K' K k') := by
  classical
  letI algKK' : Algebra ↥K ↥(K' K k') := algKK' K k'
  have hsmulK' : ∀ (x : ↥K) (κ : ↥(K' K k')), x • κ = ι K k' x * κ := fun _ _ => rfl
  haveI towerk : IsScalarTower k ↥K ↥(K' K k') := towerk_K' K k'
  let g : ↥K →ₗ[↥K] k' →ₗ[k] ↥(K' K k') :=
    LinearMap.mk₂' ↥K k (fun x c => ⟨c ⊗ₜ[k] (x : H), tmul_mem K k' c x.2⟩)
      (fun x y c => Subtype.ext (by
        show c ⊗ₜ[k] ((x + y : ↥K) : H) = c ⊗ₜ[k] (x : H) + c ⊗ₜ[k] (y : H)
        rw [Subalgebra.coe_add, TensorProduct.tmul_add]))
      (fun y x c => Subtype.ext (by
        show c ⊗ₜ[k] ((y • x : ↥K) : H) = ((ι K k' y * ⟨c ⊗ₜ[k] (x : H), tmul_mem K k' c x.2⟩ : ↥(K' K k')) : k' ⊗[k] H)
        rw [Subalgebra.coe_mul, ι_apply_coe, Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_eq_mul,
          Subalgebra.coe_mul]))
      (fun x c₁ c₂ => Subtype.ext (by
        show (c₁ + c₂) ⊗ₜ[k] (x : H) = c₁ ⊗ₜ[k] (x : H) + c₂ ⊗ₜ[k] (x : H)
        rw [TensorProduct.add_tmul]))
      (fun a x c => Subtype.ext (by
        show (a • c) ⊗ₜ[k] (x : H) = a • (c ⊗ₜ[k] (x : H))
        rw [TensorProduct.smul_tmul']))
  let f : ↥K ⊗[k] k' →ₗ[↥K] ↥(K' K k') := TensorProduct.AlgebraTensorModule.lift g
  have hf : ∀ (x : ↥K) (c : k'), f (x ⊗ₜ[k] c) = ⟨c ⊗ₜ[k] (x : H), tmul_mem K k' c x.2⟩ := fun x c => by
    rw [TensorProduct.AlgebraTensorModule.lift_tmul]; rfl
  have hfsurj : Function.Surjective f := by
    have key : ∀ t : k' ⊗[k] ↥K, ∃ s, f s = ⟨φ K k' t, t, rfl⟩ := by
      intro t
      induction t with
      | tmul c x => exact ⟨x ⊗ₜ[k] c, by rw [hf]; exact Subtype.ext (φ_tmul K k' c x).symm⟩
      | add t₁ t₂ h₁ h₂ =>
          obtain ⟨s₁, hs₁⟩ := h₁
          obtain ⟨s₂, hs₂⟩ := h₂
          exact ⟨s₁ + s₂, by
            rw [map_add, hs₁, hs₂]
            exact Subtype.ext (show φ K k' t₁ + φ K k' t₂ = φ K k' (t₁ + t₂) by rw [map_add])⟩
    rintro ⟨y, t, rfl⟩
    obtain ⟨s, hs⟩ := key t
    exact ⟨s, hs⟩
  have hfval : ∀ s, ((f s : ↥(K' K k')) : k' ⊗[k] H)
      = (K.val.toLinearMap.lTensor k') (TensorProduct.comm k ↥K k' s) := by
    intro s
    induction s with
    | add x y hx hy => rw [map_add, Subalgebra.coe_add, hx, hy, map_add, map_add]
    | tmul x c => rw [hf, TensorProduct.comm_tmul, LinearMap.lTensor_tmul]; rfl
  have hfinj : Function.Injective f := by
    intro s₁ s₂ h
    have h' : ((f s₁ : ↥(K' K k')) : k' ⊗[k] H) = f s₂ := congrArg Subtype.val h
    rw [hfval, hfval] at h'
    exact (TensorProduct.comm k ↥K k').injective
      (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective h')
  let e : ↥K ⊗[k] k' ≃ₗ[↥K] ↥(K' K k') := LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  exact Module.FaithfullyFlat.of_linearEquiv ↥K (↥K ⊗[k] k') e.symm

open S17Ta in
r2nos_open_dual "S17Ta" in
/-- (H4 L1 edition) second half of `solution`: `K' ⊗[K] H ≅ k' ⊗[k] H` is faithfully flat over `K'`
(original steps). -/
theorem faithfullyFlat_K'_tensor {k : Type u} [Field k] {H : Type v} [CommRing H] [Algebra k H]
    (K : Subalgebra k H) (k' : Type w) [Field k'] [Algebra k k']
    (hff : Module.FaithfullyFlat ↥(K' K k') (k' ⊗[k] H)) :
    letI := algKK' K k'
    Module.FaithfullyFlat ↥(K' K k') (↥(K' K k') ⊗[↥K] H) := by
  classical
  haveI := hff
  letI algKK' : Algebra ↥K ↥(K' K k') := algKK' K k'
  have hsmulK' : ∀ (x : ↥K) (κ : ↥(K' K k')), x • κ = ι K k' x * κ := fun _ _ => rfl
  haveI towerk : IsScalarTower k ↥K ↥(K' K k') := towerk_K' K k'
  letI modKH' : Module ↥K (k' ⊗[k] H) := Module.compHom (k' ⊗[k] H) (ι K k').toRingHom
  have hsmulH' : ∀ (x : ↥K) (z : k' ⊗[k] H), x • z = ((ι K k' x : ↥(K' K k')) : k' ⊗[k] H) * z := fun _ _ => rfl
  haveI : IsScalarTower ↥K ↥(K' K k') (k' ⊗[k] H) :=
    ⟨fun x κ z => by
      show (((ι K k' x * κ : ↥(K' K k')) : k' ⊗[k] H)) * z = ((ι K k' x : ↥(K' K k')) : k' ⊗[k] H) * ((κ : k' ⊗[k] H) * z)
      rw [Subalgebra.coe_mul, mul_assoc]⟩
  let g' : ↥(K' K k') →ₗ[↥(K' K k')] H →ₗ[↥K] (k' ⊗[k] H) :=
    LinearMap.mk₂' ↥(K' K k') ↥K (fun κ h => (κ : k' ⊗[k] H) * ((1 : k') ⊗ₜ[k] h))
      (fun κ₁ κ₂ h => by rw [Subalgebra.coe_add, add_mul])
      (fun κ' κ h => by
        show ((κ' * κ : ↥(K' K k')) : k' ⊗[k] H) * _ = (κ' : k' ⊗[k] H) * ((κ : k' ⊗[k] H) * _)
        rw [Subalgebra.coe_mul, mul_assoc])
      (fun κ h₁ h₂ => by rw [TensorProduct.tmul_add, mul_add])
      (fun x κ h => by
        show (κ : k' ⊗[k] H) * ((1 : k') ⊗ₜ[k] ((x : H) * h)) = ((ι K k' x : ↥(K' K k')) : k' ⊗[k] H) * ((κ : k' ⊗[k] H) * _)
        rw [ι_apply_coe, ← mul_one (1 : k'), ← Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        ring)
  let Φ₀ : ↥(K' K k') ⊗[↥K] H →ₗ[↥(K' K k')] (k' ⊗[k] H) := TensorProduct.AlgebraTensorModule.lift g'
  have hΦ₀ : ∀ (κ : ↥(K' K k')) (h : H), Φ₀ (κ ⊗ₜ[↥K] h) = (κ : k' ⊗[k] H) * ((1 : k') ⊗ₜ[k] h) := fun κ h => by
    rw [TensorProduct.AlgebraTensorModule.lift_tmul]; rfl
  have hΦ₀surj : Function.Surjective Φ₀ := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    rintro z -
    induction z with
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul c h =>
        refine ⟨(⟨c ⊗ₜ[k] (1 : H), tmul_mem K k' c K.one_mem⟩ : ↥(K' K k')) ⊗ₜ[↥K] h, ?_⟩
        rw [hΦ₀]
        show (c ⊗ₜ[k] (1 : H)) * ((1 : k') ⊗ₜ[k] h) = c ⊗ₜ[k] h
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

  let cK : k' → ↥(K' K k') := fun c => ⟨c ⊗ₜ[k] (1 : H), tmul_mem K k' c K.one_mem⟩
  have cK_zero : cK 0 = 0 := Subtype.ext (TensorProduct.zero_tmul _ (1 : H))
  have cK_add : ∀ c₁ c₂, cK (c₁ + c₂) = cK c₁ + cK c₂ := fun c₁ c₂ => Subtype.ext (TensorProduct.add_tmul c₁ c₂ (1 : H))
  let ψ₂ : k' →+ H →+ (↥(K' K k') ⊗[↥K] H) :=
    { toFun := fun c => (TensorProduct.mk ↥K ↥(K' K k') H (cK c)).toAddMonoidHom
      map_zero' := by
        ext h
        show cK 0 ⊗ₜ[↥K] h = 0
        rw [cK_zero, TensorProduct.zero_tmul]
      map_add' := fun c₁ c₂ => by
        ext h
        show cK (c₁ + c₂) ⊗ₜ[↥K] h = cK c₁ ⊗ₜ[↥K] h + cK c₂ ⊗ₜ[↥K] h
        rw [cK_add, TensorProduct.add_tmul] }
  have cK_smul : ∀ (a : k) (c : k'), (algebraMap k ↥K a) • cK c = cK (a • c) := by
    intro a c
    apply Subtype.ext
    show ((ι K k' (algebraMap k ↥K a) : ↥(K' K k')) : k' ⊗[k] H) * (c ⊗ₜ[k] (1 : H)) = (a • c) ⊗ₜ[k] (1 : H)
    rw [TensorProduct.smul_tmul, ι_apply_coe, Subalgebra.coe_algebraMap, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_one, Algebra.algebraMap_eq_smul_one]
  let Ψ : k' ⊗[k] H →+ (↥(K' K k') ⊗[↥K] H) := TensorProduct.liftAddHom ψ₂ (fun a c h => by
    show cK (a • c) ⊗ₜ[↥K] h = cK c ⊗ₜ[↥K] (a • h)
    have e1 : ((algebraMap k ↥K a) • cK c) ⊗ₜ[↥K] h = cK c ⊗ₜ[↥K] ((algebraMap k ↥K a) • h) :=
      TensorProduct.smul_tmul _ _ _
    have e2 : (algebraMap k ↥K a) • h = a • h := algebraMap_smul (↥K) a h
    rw [← e2, ← e1, cK_smul])
  have hΨ : ∀ (c : k') (h : H), Ψ (c ⊗ₜ[k] h) = cK c ⊗ₜ[↥K] h := fun c h =>
    TensorProduct.liftAddHom_tmul _ _ _ _
  have hL : ∀ (t : k' ⊗[k] ↥K) (h : H),
      Ψ (φ K k' t * ((1 : k') ⊗ₜ[k] h)) = (⟨φ K k' t, t, rfl⟩ : ↥(K' K k')) ⊗ₜ[↥K] h := by
    intro t h
    induction t with
    | tmul c x =>
        have h1 : (⟨φ K k' (c ⊗ₜ[k] x), c ⊗ₜ[k] x, rfl⟩ : ↥(K' K k')) = x • cK c := by
          apply Subtype.ext
          show φ K k' (c ⊗ₜ[k] x) = ((ι K k' x : ↥(K' K k')) : k' ⊗[k] H) * (c ⊗ₜ[k] (1 : H))
          rw [φ_tmul, ι_apply_coe, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
        rw [h1, φ_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hΨ, TensorProduct.smul_tmul]
        rfl
    | add t₁ t₂ h₁ h₂ =>
        have h2 : (⟨φ K k' (t₁ + t₂), t₁ + t₂, rfl⟩ : ↥(K' K k'))
            = ⟨φ K k' t₁, t₁, rfl⟩ + ⟨φ K k' t₂, t₂, rfl⟩ := Subtype.ext (map_add _ _ _)
        rw [h2, TensorProduct.add_tmul, map_add, add_mul, map_add, h₁, h₂]
  have hΨΦ : ∀ w, Ψ (Φ₀ w) = w := by
    intro w
    induction w with
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul κ h =>
        obtain ⟨t, ht⟩ := κ.2
        have hκ : κ = ⟨φ K k' t, t, rfl⟩ := Subtype.ext ht.symm
        rw [hκ, hΦ₀]
        exact hL t h
  have hΦ₀inj : Function.Injective Φ₀ := fun w₁ w₂ h => by
    rw [← hΨΦ w₁, ← hΨΦ w₂, h]
  let Φ : ↥(K' K k') ⊗[↥K] H ≃ₗ[↥(K' K k')] (k' ⊗[k] H) := LinearEquiv.ofBijective Φ₀ ⟨hΦ₀inj, hΦ₀surj⟩
  exact Module.FaithfullyFlat.of_linearEquiv ↥(K' K k') (k' ⊗[k] H) Φ

open S17Ta in
r2nos_open_dual "S17Ta" in
theorem solution
    {k : Type u} [Field k] {H : Type v} [CommRing H] [Algebra k H] (K : Subalgebra k H)
    (k' : Type w) [Field k'] [Algebra k k']
    (hff : Module.FaithfullyFlat
      ↥((Algebra.TensorProduct.map (AlgHom.id k' k') K.val).range) (k' ⊗[k] H)) :
    Module.FaithfullyFlat ↥K H := by
  classical
  letI : Algebra ↥K ↥(K' K k') := algKK' K k'
  haveI : Module.FaithfullyFlat ↥K ↥(K' K k') := faithfullyFlat_K_K' K k'
  haveI : Module.FaithfullyFlat ↥(K' K k') (↥(K' K k') ⊗[↥K] H) := faithfullyFlat_K'_tensor K k' hff
  exact faithfullyFlat_of_faithfullyFlat_baseChange ↥K ↥(K' K k') H
end S_Subalgebra_faithfullyFlat_of_faithfullyFlat_range_baseChange
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
