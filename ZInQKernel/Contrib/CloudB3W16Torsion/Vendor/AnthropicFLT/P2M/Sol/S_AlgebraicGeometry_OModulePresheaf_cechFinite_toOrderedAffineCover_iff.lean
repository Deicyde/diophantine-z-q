/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff

set_option autoImplicit false

noncomputable section

universe u
open CategoryTheory
open Opposite
open AlgebraicGeometry
-- Source P2M scope referred to a not-yet-declared local namespace; root scope retained.

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Surjective Spec Scheme Scheme.OrderedAffineCover Scheme.OrderedAffineCover.Idx OModulePresheaf Scheme.TwoAffineOpenCover)
open AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) {c : X ⟶ Spec (.of R)}
variable (F : OModulePresheaf c)

namespace Scheme
export _root_.AlgebraicGeometry.Scheme (mk empty Opens OrderedAffineCover OrderedAffineCover.Idx TwoAffineOpenCover)
namespace TwoAffineOpenCover
export _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover (toOrderedAffineCover cover res_res U1 U0 mk)
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme

-- CloudW16 port: expanded the source-local shorthand in its original lexical scope.

private def _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.idx0 (i : ULift.{u} (Fin 2)) : ((𝒱.toOrderedAffineCover)).Idx 0 := ⟨fun _ => i, fun a b h => absurd h (by omega)⟩
export _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover (idx0)
private def _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.idx01 : ((𝒱.toOrderedAffineCover)).Idx 1 :=
  ⟨fun j => ⟨j⟩, fun a b h => by
    change (⟨a⟩ : ULift.{u} (Fin 2)) < ⟨b⟩
    exact h⟩
export _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover (idx01)
theorem idx0_val (i : ULift.{u} (Fin 2)) (j : Fin 1) : (𝒱.idx0 i).1 j = i := rfl

private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.eq_idx0 (s : ((𝒱.toOrderedAffineCover)).Idx 0) : s = 𝒱.idx0 (s.1 0) :=
  Subtype.ext (funext fun j => by fin_cases j; rfl)
export _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover (eq_idx0)
def idxZeroEquiv : ((𝒱.toOrderedAffineCover)).Idx 0 ≃ ULift.{u} (Fin 2) where
  toFun s := s.1 0
  invFun := 𝒱.idx0
  left_inv s := (𝒱.eq_idx0 s).symm
  right_inv _ := rfl

private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.eq_idx01 (s : ((𝒱.toOrderedAffineCover)).Idx 1) : s = 𝒱.idx01 := by
  apply Subtype.ext; funext j
  have hs := s.2
  have h01 : s.1 0 < s.1 1 := hs (by decide)

  have hlt : (s.1 0).down < (s.1 1).down := h01
  have h0 : (s.1 0).down = 0 := by omega
  have h1 : (s.1 1).down = 1 := by omega
  fin_cases j
  · exact ULift.ext h0
  · exact ULift.ext h1
export _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover (eq_idx01)
scoped instance uniqueIdxOne : Unique (((𝒱.toOrderedAffineCover)).Idx 1) where
  default := 𝒱.idx01
  uniq := 𝒱.eq_idx01

private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.isEmpty_Idx_add_two (i : ℕ) : IsEmpty (((𝒱.toOrderedAffineCover)).Idx (i + 2)) := by
  rw [Scheme.OrderedAffineCover.Idx, isEmpty_subtype]
  intro s hs
  have := Fintype.card_le_of_injective s hs.injective
  simp only [Fintype.card_fin] at this
  change i + 2 + 1 ≤ Fintype.card (ULift.{u} (Fin 2)) at this
  simp at this
export _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover (isEmpty_Idx_add_two)
private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.inter_idx0 (i : ULift.{u} (Fin 2)) : ((𝒱.toOrderedAffineCover)).inter (𝒱.idx0 i) = ((𝒱.toOrderedAffineCover)).U i :=
  le_antisymm (iInf_le _ 0) (le_iInf fun _ => le_rfl)
export _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover (inter_idx0)
private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.inter_idx01 : ((𝒱.toOrderedAffineCover)).inter 𝒱.idx01 = 𝒱.U0 ⊓ 𝒱.U1 :=
  le_antisymm (le_inf (iInf_le _ 0) (iInf_le _ 1))
    (le_iInf fun j => by fin_cases j <;> [exact inf_le_left; exact inf_le_right])
export _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover (inter_idx01)
end Scheme.TwoAffineOpenCover


namespace OModulePresheaf
export _root_.AlgebraicGeometry.OModulePresheaf (res_refl_apply res_res cochain d d_apply H0 HSucc CechFinite twoChartSections res mk obj)
open _root_.AlgebraicGeometry.OModulePresheaf

private def _root_.AlgebraicGeometry.OModulePresheaf.resEq {U U' : X.Opens} (h : U = U') : F.obj U' ≃ₗ[R] F.obj U where
  toLinearMap := F.res h.le
  invFun := F.res h.ge
  left_inv x := by
    show F.res h.ge (F.res h.le x) = x
    rw [F.res_res]; exact F.res_refl_apply _ x
  right_inv x := by
    show F.res h.le (F.res h.ge x) = x
    rw [F.res_res]; exact F.res_refl_apply _ x
export _root_.AlgebraicGeometry.OModulePresheaf (resEq)
theorem resEq_apply {U U' : X.Opens} (h : U = U') (x : F.obj U') : F.resEq h x = F.res h.le x := rfl

theorem res_resEq {U U' W : X.Opens} (h : U = U') (hW : W ≤ U) (x : F.obj U') :
    F.res hW (F.resEq h x) = F.res (hW.trans h.le) x := by
  rw [resEq_apply, F.res_res]

-- CloudW16 port: expanded the source-local shorthand in its original lexical scope.

private def _root_.AlgebraicGeometry.OModulePresheaf.pick (p : F.obj 𝒱.U0 × F.obj 𝒱.U1) : ∀ i : ULift.{u} (Fin 2), F.obj (((𝒱.toOrderedAffineCover)).U i)
  | ⟨⟨0, _⟩⟩ => p.1
  | ⟨⟨1, _⟩⟩ => p.2
export _root_.AlgebraicGeometry.OModulePresheaf (pick)
theorem pick_zero (p : F.obj 𝒱.U0 × F.obj 𝒱.U1) : F.pick 𝒱 p ⟨0⟩ = p.1 := rfl
theorem pick_one (p : F.obj 𝒱.U0 × F.obj 𝒱.U1) : F.pick 𝒱 p ⟨1⟩ = p.2 := rfl

private theorem _root_.AlgebraicGeometry.OModulePresheaf.pick_add (p q : F.obj 𝒱.U0 × F.obj 𝒱.U1) (i : ULift.{u} (Fin 2)) :
    F.pick 𝒱 (p + q) i = F.pick 𝒱 p i + F.pick 𝒱 q i := by
  rcases i with ⟨⟨_ | _ | n, hn⟩⟩
  · rfl
  · rfl
  · omega
export _root_.AlgebraicGeometry.OModulePresheaf (pick_add)
private theorem _root_.AlgebraicGeometry.OModulePresheaf.pick_smul (r : R) (p : F.obj 𝒱.U0 × F.obj 𝒱.U1) (i : ULift.{u} (Fin 2)) :
    F.pick 𝒱 (r • p) i = r • F.pick 𝒱 p i := by
  rcases i with ⟨⟨_ | _ | n, hn⟩⟩
  · rfl
  · rfl
  · omega
export _root_.AlgebraicGeometry.OModulePresheaf (pick_smul)
private def _root_.AlgebraicGeometry.OModulePresheaf.pickₗ (i : ULift.{u} (Fin 2)) : F.obj 𝒱.U0 × F.obj 𝒱.U1 →ₗ[R] F.obj (((𝒱.toOrderedAffineCover)).U i) where
  toFun p := F.pick 𝒱 p i
  map_add' p q := F.pick_add 𝒱 p q i
  map_smul' r p := F.pick_smul 𝒱 r p i
export _root_.AlgebraicGeometry.OModulePresheaf (pickₗ)
private def _root_.AlgebraicGeometry.OModulePresheaf.cochainZeroTo : F.cochain (𝒱.toOrderedAffineCover) 0 →ₗ[R] F.obj 𝒱.U0 × F.obj 𝒱.U1 :=
  ((F.resEq (𝒱.inter_idx0 ⟨0⟩)).symm.toLinearMap.comp (LinearMap.proj (𝒱.idx0 ⟨0⟩))).prod
    ((F.resEq (𝒱.inter_idx0 ⟨1⟩)).symm.toLinearMap.comp (LinearMap.proj (𝒱.idx0 ⟨1⟩)))
export _root_.AlgebraicGeometry.OModulePresheaf (cochainZeroTo)
private def _root_.AlgebraicGeometry.OModulePresheaf.cochainZeroOf : F.obj 𝒱.U0 × F.obj 𝒱.U1 →ₗ[R] F.cochain (𝒱.toOrderedAffineCover) 0 :=
  LinearMap.pi fun s => (F.res (((𝒱.toOrderedAffineCover)).inter_le s 0)).comp (F.pickₗ 𝒱 (s.1 0))
export _root_.AlgebraicGeometry.OModulePresheaf (cochainZeroOf)
theorem cochainZeroTo_apply (f : F.cochain (𝒱.toOrderedAffineCover) 0) :
    F.cochainZeroTo 𝒱 f
      = (F.res (𝒱.inter_idx0 ⟨0⟩).ge (f (𝒱.idx0 ⟨0⟩)), F.res (𝒱.inter_idx0 ⟨1⟩).ge (f (𝒱.idx0 ⟨1⟩))) :=
  rfl

theorem cochainZeroOf_apply (p : F.obj 𝒱.U0 × F.obj 𝒱.U1) (s : ((𝒱.toOrderedAffineCover)).Idx 0) :
    F.cochainZeroOf 𝒱 p s = F.res (((𝒱.toOrderedAffineCover)).inter_le s 0) (F.pick 𝒱 p (s.1 0)) := rfl

private theorem _root_.AlgebraicGeometry.OModulePresheaf.cochainZeroTo_cochainZeroOf (p : F.obj 𝒱.U0 × F.obj 𝒱.U1) :
    F.cochainZeroTo 𝒱 (F.cochainZeroOf 𝒱 p) = p := by
  rw [cochainZeroTo_apply]
  refine Prod.ext ?_ ?_
  · show F.res _ (F.res _ (F.pick 𝒱 p ⟨0⟩)) = p.1
    rw [F.res_res, pick_zero]; exact F.res_refl_apply _ _
  · show F.res _ (F.res _ (F.pick 𝒱 p ⟨1⟩)) = p.2
    rw [F.res_res, pick_one]; exact F.res_refl_apply _ _
export _root_.AlgebraicGeometry.OModulePresheaf (cochainZeroTo_cochainZeroOf)
private theorem _root_.AlgebraicGeometry.OModulePresheaf.cochainZeroOf_cochainZeroTo (f : F.cochain (𝒱.toOrderedAffineCover) 0) :
    F.cochainZeroOf 𝒱 (F.cochainZeroTo 𝒱 f) = f := by
  funext s
  rw [cochainZeroOf_apply, cochainZeroTo_apply]
  obtain ⟨i, rfl⟩ : ∃ i, s = 𝒱.idx0 i := ⟨_, 𝒱.eq_idx0 s⟩
  rcases i with ⟨⟨_ | _ | n, hn⟩⟩
  · show F.res _ (F.res _ (f _)) = f _
    rw [F.res_res]; exact F.res_refl_apply _ _
  · show F.res _ (F.res _ (f _)) = f _
    rw [F.res_res]; exact F.res_refl_apply _ _
  · omega
export _root_.AlgebraicGeometry.OModulePresheaf (cochainZeroOf_cochainZeroTo)
private def _root_.AlgebraicGeometry.OModulePresheaf.cochainZeroEquiv : F.cochain (𝒱.toOrderedAffineCover) 0 ≃ₗ[R] F.obj 𝒱.U0 × F.obj 𝒱.U1 :=
  LinearEquiv.ofLinear (F.cochainZeroTo 𝒱) (F.cochainZeroOf 𝒱)
    (LinearMap.ext (F.cochainZeroTo_cochainZeroOf 𝒱)) (LinearMap.ext (F.cochainZeroOf_cochainZeroTo 𝒱))
export _root_.AlgebraicGeometry.OModulePresheaf (cochainZeroEquiv)
private theorem _root_.AlgebraicGeometry.OModulePresheaf.finite_HSucc_succ (i : ℕ) : Module.Finite R (F.HSucc (𝒱.toOrderedAffineCover) (i + 1)) := by
  haveI := 𝒱.isEmpty_Idx_add_two i
  haveI : Subsingleton (F.cochain (𝒱.toOrderedAffineCover) (i + 1 + 1)) := inferInstance
  haveI : Subsingleton (F.HSucc (𝒱.toOrderedAffineCover) (i + 1)) := Quot.Subsingleton
  exact Module.Finite.of_finite
export _root_.AlgebraicGeometry.OModulePresheaf (finite_HSucc_succ)
end OModulePresheaf

end AlgebraicGeometry

end

noncomputable section

namespace TwoChartCech
export _root_.TwoChartCech (Sections Sections.cechDiff_apply kerMap cokerMap)
open _root_.TwoChartCech

universe uR uK uC

variable {R : Type uR} [CommRing R]
variable {K0 K1 : Type uK} [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1]
variable {C0 C1 : Type uK} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

theorem kerMap_bijective_of_bijective (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0)
    (ι1 : K1 →ₗ[R] C1) (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (h0 : Function.Bijective ι0)
    (h1 : Function.Injective ι1) : Function.Bijective (kerMap dK d ι0 ι1 comm) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply h0.1
    exact congrArg Subtype.val hxy
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := h0.2 y
    have hx : x ∈ LinearMap.ker dK := by
      rw [LinearMap.mem_ker] at hy ⊢
      apply h1
      rw [map_zero, ← LinearMap.comp_apply, ← comm, LinearMap.comp_apply, hy]
    exact ⟨⟨x, hx⟩, rfl⟩

theorem cokerMap_bijective_of_bijective (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0)
    (ι1 : K1 →ₗ[R] C1) (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (h0 : Function.Surjective ι0)
    (h1 : Function.Bijective ι1) : Function.Bijective (cokerMap dK d ι0 ι1 comm) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.mem_ker] at hq
    change Submodule.Quotient.mk (ι1 y) = 0 at hq
    rw [Submodule.Quotient.mk_eq_zero] at hq ⊢
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hq
    obtain ⟨x, rfl⟩ := h0 c
    refine ⟨x, h1.1 ?_⟩
    rw [← hc, ← LinearMap.comp_apply, ← comm, LinearMap.comp_apply]
  · intro q
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨y, rfl⟩ := h1.2 c
    exact ⟨Submodule.Quotient.mk y, rfl⟩

end TwoChartCech

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Surjective Spec Scheme Scheme.OrderedAffineCover Scheme.OrderedAffineCover.Idx OModulePresheaf Scheme.TwoAffineOpenCover)
open _root_.AlgebraicGeometry

universe u

open CategoryTheory Opposite

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) {c : X ⟶ Spec (.of R)}
variable (F : OModulePresheaf c)

namespace Scheme
export _root_.AlgebraicGeometry.Scheme (mk empty Opens OrderedAffineCover OrderedAffineCover.Idx TwoAffineOpenCover)
namespace TwoAffineOpenCover
export _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover (toOrderedAffineCover cover res_res U1 U0 mk)
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme

-- CloudW16 port: expanded the source-local shorthand in its original lexical scope.

private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.face_idx01_zero : ((𝒱.toOrderedAffineCover)).face 𝒱.idx01 0 = 𝒱.idx0 ⟨1⟩ :=
  Subtype.ext (funext fun j => by fin_cases j; rfl)
export _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover (face_idx01_zero)
private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.face_idx01_one : ((𝒱.toOrderedAffineCover)).face 𝒱.idx01 1 = 𝒱.idx0 ⟨0⟩ :=
  Subtype.ext (funext fun j => by fin_cases j; rfl)
export _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover (face_idx01_one)
private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.inter_le_inf (s : ((𝒱.toOrderedAffineCover)).Idx 1) : ((𝒱.toOrderedAffineCover)).inter s ≤ 𝒱.U0 ⊓ 𝒱.U1 := by
  rw [𝒱.eq_idx01 s, 𝒱.inter_idx01]
export _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover (inter_le_inf)
private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.inf_le_inter (s : ((𝒱.toOrderedAffineCover)).Idx 1) : 𝒱.U0 ⊓ 𝒱.U1 ≤ ((𝒱.toOrderedAffineCover)).inter s := by
  rw [𝒱.eq_idx01 s, 𝒱.inter_idx01]
export _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover (inf_le_inter)
end Scheme.TwoAffineOpenCover


namespace OModulePresheaf
export _root_.AlgebraicGeometry.OModulePresheaf (res_refl_apply res_res cochain d d_apply H0 HSucc CechFinite twoChartSections res mk obj)
open _root_.AlgebraicGeometry.OModulePresheaf

-- CloudW16 port: expanded the source-local shorthand in its original lexical scope.

private theorem _root_.AlgebraicGeometry.OModulePresheaf.res_congr_idx {i : ℕ} (co : F.cochain (𝒱.toOrderedAffineCover) i) {s s' : ((𝒱.toOrderedAffineCover)).Idx i} (e : s = s') {W : X.Opens}
    (p : W ≤ ((𝒱.toOrderedAffineCover)).inter s) (p' : W ≤ ((𝒱.toOrderedAffineCover)).inter s') : F.res p (co s) = F.res p' (co s') := by
  subst e; rfl
export _root_.AlgebraicGeometry.OModulePresheaf (res_congr_idx)
private def _root_.AlgebraicGeometry.OModulePresheaf.cochainOneTo : F.cochain (𝒱.toOrderedAffineCover) 1 →ₗ[R] F.obj (𝒱.U0 ⊓ 𝒱.U1) :=
  (F.res (𝒱.inf_le_inter 𝒱.idx01)).comp (LinearMap.proj 𝒱.idx01)
export _root_.AlgebraicGeometry.OModulePresheaf (cochainOneTo)
private def _root_.AlgebraicGeometry.OModulePresheaf.cochainOneOf : F.obj (𝒱.U0 ⊓ 𝒱.U1) →ₗ[R] F.cochain (𝒱.toOrderedAffineCover) 1 :=
  LinearMap.pi fun s => F.res (𝒱.inter_le_inf s)
export _root_.AlgebraicGeometry.OModulePresheaf (cochainOneOf)
theorem cochainOneTo_apply (co : F.cochain (𝒱.toOrderedAffineCover) 1) :
    F.cochainOneTo 𝒱 co = F.res (𝒱.inf_le_inter 𝒱.idx01) (co 𝒱.idx01) := rfl

theorem cochainOneOf_apply (x : F.obj (𝒱.U0 ⊓ 𝒱.U1)) (s : ((𝒱.toOrderedAffineCover)).Idx 1) :
    F.cochainOneOf 𝒱 x s = F.res (𝒱.inter_le_inf s) x := rfl

private theorem _root_.AlgebraicGeometry.OModulePresheaf.cochainOneTo_cochainOneOf (x : F.obj (𝒱.U0 ⊓ 𝒱.U1)) :
    F.cochainOneTo 𝒱 (F.cochainOneOf 𝒱 x) = x := by
  rw [cochainOneTo_apply, cochainOneOf_apply, F.res_res]
  exact F.res_refl_apply _ x
export _root_.AlgebraicGeometry.OModulePresheaf (cochainOneTo_cochainOneOf)
private theorem _root_.AlgebraicGeometry.OModulePresheaf.cochainOneOf_cochainOneTo (co : F.cochain (𝒱.toOrderedAffineCover) 1) :
    F.cochainOneOf 𝒱 (F.cochainOneTo 𝒱 co) = co := by
  funext s
  rw [cochainOneOf_apply, cochainOneTo_apply, F.res_res]
  have hs := 𝒱.eq_idx01 s
  subst hs
  exact F.res_refl_apply _ _
export _root_.AlgebraicGeometry.OModulePresheaf (cochainOneOf_cochainOneTo)
private def _root_.AlgebraicGeometry.OModulePresheaf.cochainOneEquiv : F.cochain (𝒱.toOrderedAffineCover) 1 ≃ₗ[R] F.obj (𝒱.U0 ⊓ 𝒱.U1) :=
  LinearEquiv.ofLinear (F.cochainOneTo 𝒱) (F.cochainOneOf 𝒱)
    (LinearMap.ext (F.cochainOneTo_cochainOneOf 𝒱)) (LinearMap.ext (F.cochainOneOf_cochainOneTo 𝒱))
export _root_.AlgebraicGeometry.OModulePresheaf (cochainOneEquiv)
private theorem _root_.AlgebraicGeometry.OModulePresheaf.cochainOneTo_d (co : F.cochain (𝒱.toOrderedAffineCover) 0) :
    F.cochainOneTo 𝒱 (F.d (𝒱.toOrderedAffineCover) 0 co) = (F.twoChartSections 𝒱).cechDiff (F.cochainZeroTo 𝒱 co) := by
  rw [cochainOneTo_apply, F.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, ← sub_eq_add_neg,
    map_sub]
  rw [TwoChartCech.Sections.cechDiff_apply, cochainZeroTo_apply]

  change F.res _ (F.res _ (co (((𝒱.toOrderedAffineCover)).face 𝒱.idx01 0))) - F.res _ (F.res _ (co (((𝒱.toOrderedAffineCover)).face 𝒱.idx01 1)))
    = F.res (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1) (F.res _ (co (𝒱.idx0 ⟨1⟩)))
      - F.res (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0) (F.res _ (co (𝒱.idx0 ⟨0⟩)))
  rw [F.res_res, F.res_res, F.res_res, F.res_res]
  rw [F.res_congr_idx 𝒱 co (𝒱.face_idx01_zero) _
      ((inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1).trans (𝒱.inter_idx0 ⟨1⟩).ge),
    F.res_congr_idx 𝒱 co (𝒱.face_idx01_one) _
      ((inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0).trans (𝒱.inter_idx0 ⟨0⟩).ge)]
export _root_.AlgebraicGeometry.OModulePresheaf (cochainOneTo_d)
private theorem _root_.AlgebraicGeometry.OModulePresheaf.cechDiff_comp_cochainZeroEquiv :
    (F.twoChartSections 𝒱).cechDiff ∘ₗ (F.cochainZeroEquiv 𝒱).toLinearMap
      = (F.cochainOneEquiv 𝒱).toLinearMap ∘ₗ F.d (𝒱.toOrderedAffineCover) 0 := by
  apply LinearMap.ext
  intro co
  exact (F.cochainOneTo_d 𝒱 co).symm
export _root_.AlgebraicGeometry.OModulePresheaf (cechDiff_comp_cochainZeroEquiv)
private def _root_.AlgebraicGeometry.OModulePresheaf.H0Equiv : F.H0 (𝒱.toOrderedAffineCover) ≃ₗ[R] (F.twoChartSections 𝒱).H0 :=
  LinearEquiv.ofBijective _
    (TwoChartCech.kerMap_bijective_of_bijective (F.d (𝒱.toOrderedAffineCover) 0) (F.twoChartSections 𝒱).cechDiff
      (F.cochainZeroEquiv 𝒱).toLinearMap (F.cochainOneEquiv 𝒱).toLinearMap
      (F.cechDiff_comp_cochainZeroEquiv 𝒱) (F.cochainZeroEquiv 𝒱).bijective
      (F.cochainOneEquiv 𝒱).injective)
export _root_.AlgebraicGeometry.OModulePresheaf (H0Equiv)
private theorem _root_.AlgebraicGeometry.OModulePresheaf.d_one_eq_zero : F.d (𝒱.toOrderedAffineCover) 1 = 0 := by
  haveI := 𝒱.isEmpty_Idx_add_two 0
  apply LinearMap.ext
  intro co
  exact Subsingleton.elim _ _
export _root_.AlgebraicGeometry.OModulePresheaf (d_one_eq_zero)
private theorem _root_.AlgebraicGeometry.OModulePresheaf.ker_d_one_eq_top : LinearMap.ker (F.d (𝒱.toOrderedAffineCover) 1) = ⊤ := by
  rw [F.d_one_eq_zero 𝒱, LinearMap.ker_zero]
export _root_.AlgebraicGeometry.OModulePresheaf (ker_d_one_eq_top)
private def _root_.AlgebraicGeometry.OModulePresheaf.HSuccZeroEquivCoker : F.HSucc (𝒱.toOrderedAffineCover) 0 ≃ₗ[R] (F.cochain (𝒱.toOrderedAffineCover) 1 ⧸ LinearMap.range (F.d (𝒱.toOrderedAffineCover) 0)) :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofTop _ (F.ker_d_one_eq_top 𝒱)) (by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy
    · intro y hy
      refine ⟨⟨y, by rw [F.ker_d_one_eq_top 𝒱]; trivial⟩, hy, rfl⟩)
export _root_.AlgebraicGeometry.OModulePresheaf (HSuccZeroEquivCoker)
private def _root_.AlgebraicGeometry.OModulePresheaf.HSuccZeroEquiv : F.HSucc (𝒱.toOrderedAffineCover) 0 ≃ₗ[R] (F.twoChartSections 𝒱).H1 :=
  (F.HSuccZeroEquivCoker 𝒱).trans (LinearEquiv.ofBijective _
    (TwoChartCech.cokerMap_bijective_of_bijective (F.d (𝒱.toOrderedAffineCover) 0) (F.twoChartSections 𝒱).cechDiff
      (F.cochainZeroEquiv 𝒱).toLinearMap (F.cochainOneEquiv 𝒱).toLinearMap
      (F.cechDiff_comp_cochainZeroEquiv 𝒱) (F.cochainZeroEquiv 𝒱).surjective
      (F.cochainOneEquiv 𝒱).bijective))
export _root_.AlgebraicGeometry.OModulePresheaf (HSuccZeroEquiv)
theorem cechFinite_toOrderedAffineCover_iff' :
    F.CechFinite (𝒱.toOrderedAffineCover) ↔
      Module.Finite R (F.twoChartSections 𝒱).H0 ∧ Module.Finite R (F.twoChartSections 𝒱).H1 := by
  constructor
  · rintro ⟨h0, hS⟩
    exact ⟨Module.Finite.equiv (F.H0Equiv 𝒱), by
      haveI := hS 0; exact Module.Finite.equiv (F.HSuccZeroEquiv 𝒱)⟩
  · rintro ⟨h0, h1⟩
    refine ⟨Module.Finite.equiv (F.H0Equiv 𝒱).symm, fun i => ?_⟩
    cases i with
    | zero => exact Module.Finite.equiv (F.HSuccZeroEquiv 𝒱).symm
    | succ i => exact F.finite_HSucc_succ 𝒱 i

end OModulePresheaf

end AlgebraicGeometry

end

universe u

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff.AlgebraicGeometry in
theorem solution {R : Type u} [CommRing R] {X : Scheme.{u}} {c : X ⟶ Spec (.of R)}
    (F : OModulePresheaf c) (𝒱 : X.TwoAffineOpenCover) :
    F.CechFinite 𝒱.toOrderedAffineCover ↔
      Module.Finite R (F.twoChartSections 𝒱).H0 ∧ Module.Finite R (F.twoChartSections 𝒱).H1 :=
  AlgebraicGeometry.OModulePresheaf.cechFinite_toOrderedAffineCover_iff' 𝒱 F
