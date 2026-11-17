import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_NeronModelInfra_TopFormOrder_topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq.lean
Original Git blob: e3c81b09b501a447e1449eecbca976a473bdff54
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_NeronModelInfra_TopFormOrder_topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open NeronModelInfra.TopFormOrder

namespace BenchLTopLine
h77_bridge_namespace

theorem subsingleton_kaehler_of_isFractionRing (R K : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] : Subsingleton (Ω[K⁄R]) := by
  haveI : IsLocalizedModule (nonZeroDivisors R) (KaehlerDifferential.map R R R K) :=
    KaehlerDifferential.isLocalizedModule_map R R K (nonZeroDivisors R)
  haveI : Subsingleton (Ω[R⁄R]) := KaehlerDifferential.subsingleton_of_surjective R R Function.surjective_id
  refine ⟨fun x y => ?_⟩
  obtain ⟨⟨mx, sx⟩, hx⟩ := IsLocalizedModule.surj (nonZeroDivisors R) (KaehlerDifferential.map R R R K) x
  obtain ⟨⟨my, sy⟩, hy⟩ := IsLocalizedModule.surj (nonZeroDivisors R) (KaehlerDifferential.map R R R K) y
  have hmx : mx = 0 := Subsingleton.elim _ _
  have hmy : my = 0 := Subsingleton.elim _ _
  simp only [hmx, hmy, map_zero] at hx hy
  have hux : IsUnit (algebraMap R K sx) := IsLocalization.map_units K sx
  have huy : IsUnit (algebraMap R K sy) := IsLocalization.map_units K sy
  have ex : x = 0 := by
    have : algebraMap R K sx • x = 0 := by rw [algebraMap_smul]; exact hx
    exact (hux.smul_left_cancel).mp (this.trans (smul_zero _).symm)
  have ey : y = 0 := by
    have : algebraMap R K sy • y = 0 := by rw [algebraMap_smul]; exact hy
    exact (huy.smul_left_cancel).mp (this.trans (smul_zero _).symm)
  rw [ex, ey]

theorem orderEmbedding_fin_eq_id {d : ℕ} (f : Fin d ↪o Fin d) : (f : Fin d → Fin d) = id := by
  have hs : Function.Surjective f := Finite.surjective_of_injective f.injective
  have h1 : Set.range (f : Fin d → Fin d) = Set.range (id : Fin d → Fin d) := by
    rw [Set.range_id, Set.range_eq_univ.mpr hs]
  exact (f.strictMono.range_inj strictMono_id).mp h1

end BenchLTopLine
theorem solution
    (R K O F : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing O] [IsDomain O] [Algebra R O] [Field F] [Algebra O F] [IsFractionRing O F]
    [Algebra K F] [Algebra R F] [IsScalarTower R O F] [IsScalarTower R K F]
    (d : ℕ) (b : Module.Basis (Fin d) O (Ω[O⁄R])) :
    letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K]))
    topFormMap R K O F d (exteriorPower.ιMulti O d b) ≠ 0 ∧
      ∀ ω : ⋀[F]^d (Ω[F⁄K]), ∃ a : F, ω = a • topFormMap R K O F d (exteriorPower.ιMulti O d b) := by
  letI instO := moduleAlong O F (⋀[F]^d (Ω[F⁄K]))

  set v : Fin d → Ω[F⁄K] := fun i => KaehlerDifferential.map R K O F (b i) with hv
  have hρ : topFormMap R K O F d (exteriorPower.ιMulti O d b) = exteriorPower.ιMulti F d v := by
    show exteriorPower.alternatingMapLinearEquiv (ιMultiAlong R K O F d) (exteriorPower.ιMulti O d b) = _
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    rfl

  haveI : IsLocalizedModule (nonZeroDivisors O) (KaehlerDifferential.map R R O F) :=
    KaehlerDifferential.isLocalizedModule_map R O F (nonZeroDivisors O)
  let b₁ : Module.Basis (Fin d) F (Ω[F⁄R]) :=
    b.ofIsLocalizedModule F (nonZeroDivisors O) (KaehlerDifferential.map R R O F)
  have hinj : Function.Injective (KaehlerDifferential.map R K F F) := by
    haveI := BenchLTopLine.subsingleton_kaehler_of_isFractionRing R K
    rw [← LinearMap.ker_eq_bot, LinearMap.exact_iff.mp (KaehlerDifferential.exact_mapBaseChange_map R K F),
      LinearMap.range_eq_bot]
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => rw [Subsingleton.elim y 0, TensorProduct.tmul_zero, map_zero, LinearMap.zero_apply]
    | add x y hx hy => simp only [map_add, hx, hy, LinearMap.zero_apply, add_zero]
  let e : Ω[F⁄R] ≃ₗ[F] Ω[F⁄K] :=
    LinearEquiv.ofBijective (KaehlerDifferential.map R K F F) ⟨hinj, KaehlerDifferential.map_surjective R K F⟩
  let b₂ : Module.Basis (Fin d) F (Ω[F⁄K]) := b₁.map e
  have hcomp : ∀ x : Ω[O⁄R], KaehlerDifferential.map R K F F (KaehlerDifferential.map R R O F x) =
      KaehlerDifferential.map R K O F x := by
    intro x
    have hx : x ∈ Submodule.span O (Set.range (KaehlerDifferential.D R O)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨o, rfl⟩ := hx
        rw [KaehlerDifferential.map_D, KaehlerDifferential.map_D, KaehlerDifferential.map_D]
        rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
    | smul o x _ hx =>
        rw [LinearMap.map_smul, LinearMap.map_smul, ← hx, ← algebraMap_smul F o (KaehlerDifferential.map R R O F x),
          LinearMap.map_smul, algebraMap_smul]
  have hb₂ : (b₂ : Fin d → Ω[F⁄K]) = v := by
    funext i
    simp only [b₂, b₁, Module.Basis.map_apply, Module.Basis.ofIsLocalizedModule_apply]
    exact hcomp (b i)

  let B := b₂.exteriorPower d
  let s₀ : Set.powersetCard (Fin d) d := ⟨Finset.univ, by simp [Set.powersetCard]⟩
  have hs : ∀ s : Set.powersetCard (Fin d) d, s = s₀ := by
    intro s
    apply Subtype.ext
    show s.val = Finset.univ
    exact Finset.eq_univ_of_card s.val (by rw [Fintype.card_fin]; exact s.prop)
  have hB : B s₀ = exteriorPower.ιMulti F d v := by
    rw [show B s₀ = exteriorPower.ιMulti_family F d b₂ s₀ from exteriorPower.basis_apply F d b₂ s₀]
    unfold exteriorPower.ιMulti_family
    rw [hb₂]
    congr 1
    funext i
    show v ((Set.powersetCard.ofFinEmbEquiv.symm s₀ : Fin d ↪o Fin d) i) = v i
    rw [BenchLTopLine.orderEmbedding_fin_eq_id]
    rfl
  rw [hρ]
  refine ⟨?_, fun ω => ?_⟩
  · rw [← hB]; exact B.ne_zero s₀
  · refine ⟨B.repr ω s₀, ?_⟩
    rw [← hB]
    conv_lhs => rw [← B.sum_repr ω]
    rw [Fintype.sum_eq_single s₀ (fun s hs' => absurd (hs s) hs')]


end P2MW.S_NeronModelInfra_TopFormOrder_topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
