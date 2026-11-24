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
  Source file    : P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_connectedSpace_pullback_of_comp_eq_one_iff.lean
  Source sha256  : 7b7b3cc41a8fbc5da2ab7e4ffde7d93a9e2de2d3ac7ed155509eb29fc48a00e7
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 4 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_connectedSpace_pullback_of_comp_eq_one_iff
r2nos_namespace_dual

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian"

universe u

namespace LiftConn
r2nos_namespace_dual

variable {k : Type u} [Field k]

section grp

variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))

lemma mul_inv_mul_cancel (x y : SchemeHomOver t f) :
    L.mul t x (L.mul t (L.inv t x) y) = y := by
  rw [← L.mul_assoc, L.mul_inv_cancel, L.one_mul]

lemma eq_one_of_mul_self (a : SchemeHomOver t f) (h : L.mul t a a = a) : a = L.one t := by
  calc a = L.mul t (L.one t) a := (L.one_mul t a).symm
    _ = L.mul t (L.mul t (L.inv t a) a) a := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t a) (L.mul t a a) := by rw [L.mul_assoc]
    _ = L.mul t (L.inv t a) a := by rw [h]
    _ = L.one t := L.inv_mul_cancel t a

end grp

section main

variable {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G)
  {Q : Scheme.{u}} {fQ : Q ⟶ Spec (CommRingCat.of k)} (LQ : RelativeGroupLaw k fQ)
  (q : SchemeHomOver f fQ)
  (hq : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
      LQ.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q))
  (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp x q = LQ.one t ↔
      ∃ y : SchemeHomOver t (i ≫ f),
        NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = x)

include hq in

lemma comp_one_eq_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    NeronModelInfra.schemeHomOverComp (L.one t) q = LQ.one t := by
  apply eq_one_of_mul_self LQ t
  rw [← hq, L.one_mul]

include hq in

lemma comp_inv_mul_eq_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver t f)
    (h : NeronModelInfra.schemeHomOverComp x q = NeronModelInfra.schemeHomOverComp y q) :
    NeronModelInfra.schemeHomOverComp (L.mul t (L.inv t x) y) q = LQ.one t := by
  rw [hq, ← h, ← hq, L.inv_mul_cancel, comp_one_eq_one L LQ q hq]

include hq hker in

theorem connectedSpace_pullback [GeometricallyConnected (i ≫ f)] [Surjective q.1]
    {K : Type u} [Field K] (y : Spec (CommRingCat.of K) ⟶ Q) :
    ConnectedSpace ↑(pullback q.1 y) := by
  classical
  let F : Scheme.{u} := pullback q.1 y
  let prG : F ⟶ G := pullback.fst q.1 y
  let prK : F ⟶ Spec (CommRingCat.of K) := pullback.snd q.1 y
  have hcond : prG ≫ q.1 = prK ≫ y := pullback.condition
  have hqf : q.1 ≫ fQ = f := q.2

  obtain ⟨s0⟩ : Nonempty ↑(Spec (CommRingCat.of K)) := inferInstance
  obtain ⟨p, -⟩ := prK.surjective s0

  let pt : Spec (F.residueField p) ⟶ F := F.fromSpecResidueField p
  let σ : Spec (F.residueField p) ⟶ Spec (CommRingCat.of k) := pt ≫ prK ≫ y ≫ fQ

  let NK : Scheme.{u} := pullback (i ≫ f) σ
  have hNK : ConnectedSpace ↑NK :=
    pullback_of_geometrically (GeometricallyConnected.geometrically_connectedSpace (f := i ≫ f))
      _ σ
  let tN : NK ⟶ Spec (CommRingCat.of k) := pullback.snd (i ≫ f) σ ≫ σ
  have hNcond : pullback.fst (i ≫ f) σ ≫ i ≫ f = pullback.snd (i ≫ f) σ ≫ σ := by
    simpa only [Category.assoc] using (pullback.condition (f := i ≫ f) (g := σ))
  let x1 : SchemeHomOver tN f :=
    ⟨pullback.snd (i ≫ f) σ ≫ pt ≫ prG, by
      simp only [tN, σ, Category.assoc, ← hqf]
      rw [reassoc_of% hcond]⟩
  let x2 : SchemeHomOver tN f := ⟨pullback.fst (i ≫ f) σ ≫ i, by
      simp only [tN, Category.assoc]; exact hNcond⟩
  have hx2 : NeronModelInfra.schemeHomOverComp x2 q = LQ.one tN := by
    refine (hker tN x2).mpr ⟨⟨pullback.fst (i ≫ f) σ, hNcond⟩, ?_⟩
    exact Subtype.ext rfl

  let θG : NK ⟶ G := (L.mul tN x1 x2).1
  have hθG : θG ≫ q.1 = (pullback.snd (i ≫ f) σ ≫ pt ≫ prK) ≫ y := by
    have h1 : θG ≫ q.1 = (NeronModelInfra.schemeHomOverComp (L.mul tN x1 x2) q).1 := rfl
    rw [h1, hq, hx2, LQ.mul_one]
    show (pullback.snd (i ≫ f) σ ≫ pt ≫ prG) ≫ q.1 = _
    simp only [Category.assoc, hcond]
  let θ : NK ⟶ F := pullback.lift θG (pullback.snd (i ≫ f) σ ≫ pt ≫ prK) hθG

  let FK : Scheme.{u} := pullback prK (pt ≫ prK)
  let π : FK ⟶ F := pullback.fst prK (pt ≫ prK)
  have hFKcond : π ≫ prK = pullback.snd prK (pt ≫ prK) ≫ pt ≫ prK := pullback.condition
  have hπ : Function.Surjective π := π.surjective
  let tF : FK ⟶ Spec (CommRingCat.of k) := π ≫ prK ≫ y ≫ fQ
  let uu : SchemeHomOver tF f := ⟨π ≫ prG, by
      simp only [tF, Category.assoc, ← hqf]
      rw [reassoc_of% hcond]⟩
  let pK : SchemeHomOver tF f := ⟨pullback.snd prK (pt ≫ prK) ≫ pt ≫ prG, by
      simp only [tF, Category.assoc, ← hqf]
      rw [reassoc_of% hcond, ← reassoc_of% hFKcond]⟩
  have hpu : NeronModelInfra.schemeHomOverComp pK q = NeronModelInfra.schemeHomOverComp uu q := by
    apply Subtype.ext
    show (pullback.snd prK (pt ≫ prK) ≫ pt ≫ prG) ≫ q.1 = (π ≫ prG) ≫ q.1
    simp only [Category.assoc, hcond]
    rw [← reassoc_of% hFKcond]
  have hx : NeronModelInfra.schemeHomOverComp (L.mul tF (L.inv tF pK) uu) q = LQ.one tF :=
    comp_inv_mul_eq_one L LQ q hq tF pK uu hpu
  obtain ⟨n, hn⟩ := (hker tF _).mp hx
  have hn1 : n.1 ≫ i = (L.mul tF (L.inv tF pK) uu).1 := congrArg Subtype.val hn
  have hψw : n.1 ≫ i ≫ f = pullback.snd prK (pt ≫ prK) ≫ σ := by
    rw [n.2]
    simp only [tF, σ]
    rw [← reassoc_of% hFKcond]
  let ψ : FK ⟶ NK := pullback.lift n.1 (pullback.snd prK (pt ≫ prK)) hψw
  have hψt : ψ ≫ tN = tF := by
    simp only [ψ, tN, pullback.lift_snd_assoc, tF, σ]
    rw [← reassoc_of% hFKcond]
  have hψθG : ψ ≫ θG = π ≫ prG := by
    have hnat := L.mul_natural tN tF ψ hψt x1 x2
    have e1 : GoodReductionJacobian.schemeHomOverComp ψ hψt x1 = pK := by
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, x1, pK, ψ, pullback.lift_snd_assoc]
    have e2 : GoodReductionJacobian.schemeHomOverComp ψ hψt x2 = L.mul tF (L.inv tF pK) uu := by
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, x2, ψ, pullback.lift_fst_assoc]
      exact hn1
    have hval := congrArg Subtype.val hnat
    rw [e1, e2, mul_inv_mul_cancel L tF pK uu] at hval
    simpa only [GoodReductionJacobian.schemeHomOverComp_coe] using hval
  have hψθ : ψ ≫ θ = π := by
    apply pullback.hom_ext
    · simp only [θ, Category.assoc, pullback.lift_fst]
      exact hψθG
    · simp only [θ, Category.assoc, pullback.lift_snd]
      simp only [ψ, pullback.lift_snd_assoc]
      exact hFKcond.symm
  have hθ : Function.Surjective θ := by
    intro z
    obtain ⟨w, rfl⟩ := hπ z
    exact ⟨ψ w, by rw [← Scheme.Hom.comp_apply, hψθ]⟩
  exact hθ.connectedSpace θ.continuous

include hq hker in
theorem geometricallyConnected [GeometricallyConnected (i ≫ f)] [Surjective q.1] :
    GeometricallyConnected q.1 := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have : ConnectedSpace ↑(pullback q.1 y) := connectedSpace_pullback L i LQ q hq hker y
  exact (h.isoPullback.inv.surjective).connectedSpace h.isoPullback.inv.continuous

include hq hker in
theorem connectedSpace_preimage [GeometricallyConnected (i ≫ f)] [Surjective q.1]
    (h : ℕ) [SmoothOfRelativeDimension h q.1]
    {M : Scheme.{u}} (j : M ⟶ Q) [ConnectedSpace ↑M] :
    ConnectedSpace ↑(pullback j q.1) := by
  have : GeometricallyConnected q.1 := geometricallyConnected L i LQ q hq hker
  have : Smooth q.1 := SmoothOfRelativeDimension.smooth h q.1
  have : UniversallyOpen q.1 := inferInstance
  infer_instance

end main

end LiftConn

theorem solution
    (k : Type u) [Field k]
    {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i]
    {Q : Scheme.{u}} (fQ : Q ⟶ Spec (CommRingCat.of k)) (LQ : RelativeGroupLaw k fQ)
    (q : SchemeHomOver f fQ)
    (hq : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
        LQ.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q))
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp x q = LQ.one t ↔
        ∃ y : SchemeHomOver t (i ≫ f),
          NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = x)
    [IsAffine N] [GeometricallyConnected (i ≫ f)]
    (h : ℕ) [SmoothOfRelativeDimension h q.1] [Surjective q.1] [QuasiCompact q.1]
    {M : Scheme.{u}} (j : M ⟶ Q) [IsClosedImmersion j] [ConnectedSpace M] :
    ConnectedSpace ↥(pullback q.1 j) := by
  have : GeometricallyConnected q.1 := LiftConn.geometricallyConnected L i LQ q hq hker
  have : Smooth q.1 := SmoothOfRelativeDimension.smooth h q.1
  have : UniversallyOpen q.1 := inferInstance
  infer_instance
end S_GoodReductionJacobian_RelativeGroupLaw_connectedSpace_pullback_of_comp_eq_one_iff
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
