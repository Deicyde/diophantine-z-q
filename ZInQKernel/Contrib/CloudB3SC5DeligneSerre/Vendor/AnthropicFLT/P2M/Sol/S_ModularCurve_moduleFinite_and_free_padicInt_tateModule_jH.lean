/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_moduleFinite_and_free_padicInt_tateModule_jH (git blob e8079947f9db2210218f2c8b29ab3b600076cf3a, sha256 0ca8158ed2fa2c6b0fc6f73002ce8bb80e052f1653a3fb0e8b0a7695ac8d737a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_TateModule
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Pic0_abelJacobiCard_genus
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace TateModule
end TateModule

namespace P2MW.S_ModularCurve_moduleFinite_and_free_padicInt_tateModule_jH

open Submodule

namespace TateModule
export _root_.TateModule (torsion compat compat_pow coe_zero natCast_smul_eq_of_zmod_eq toZModPow_eq_appr smul_apply proj proj_apply proj_mem_torsionBy smul_eq_zero_of_mem_torsionBy_one finite_torsionBy mulP kerMulPEquiv mulP_surjective liftFun liftFun_of_le coe_liftAux_congr liftFun_mem proj_surjective dvd_of_rel_apply levelMap levelMap_injective levelMap_bijective linearIndependent_pair basisOfCard free finite)
namespace RankDBasis
open _root_.TateModule

variable {p : ℕ} {M : Type} [AddCommGroup M] [Fact p.Prime] {d : ℕ}

theorem finite_torsionBy
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) (n : ℕ) :
    Finite (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) :=
  Nat.finite_of_card_ne_zero (by
    rw [hcard n]; exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))

theorem mulP_surjective
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) (n : ℕ) :
    Function.Surjective (mulP p M n) := by
  haveI := finite_torsionBy hcard (n + 1)
  haveI := finite_torsionBy hcard n
  have hp : p.Prime := Fact.out
  have hker : Nat.card (mulP p M n).ker = p ^ d := by
    rw [Nat.card_congr (kerMulPEquiv p M n), hcard 1, pow_one]
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (mulP p M n).ker
  rw [hcard (n + 1), Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (mulP p M n)).toEquiv,
    hker] at h
  have hrange : Nat.card (mulP p M n).range = Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) := by
    rw [hcard n]
    refine Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos d) ?_
    rw [← h, ← mul_pow, ← pow_succ]
  rw [← AddMonoidHom.range_eq_top]
  exact AddSubgroup.eq_top_of_card_eq _ hrange

theorem proj_surjective
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) (n : ℕ) :
    ∀ m ∈ torsionBy ℤ M ((p ^ n : ℕ) : ℤ), ∃ x : TateModule p M, proj p M n x = m := by
  intro m hm
  choose next hnext using fun k (m : torsionBy ℤ M ((p ^ k : ℕ) : ℤ)) => mulP_surjective hcard k m
  refine ⟨⟨liftFun next n ⟨m, hm⟩,
    liftFun_mem (fun k m => congrArg Subtype.val (hnext k m)) n ⟨m, hm⟩⟩, ?_⟩
  rw [proj_apply]
  change liftFun next n ⟨m, hm⟩ n = m
  rw [liftFun_of_le le_rfl, coe_liftAux_congr (Nat.sub_self n)]
  rfl

theorem exists_family_of_card_eq_pow {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (hV : Nat.card V = p ^ d) :
    ∃ e : Fin d → V, ∀ a : Fin d → ℤ, ∑ i, a i • e i = 0 → ∀ i, (p : ℤ) ∣ a i := by
  have hp : p.Prime := Fact.out
  have hrank : Module.finrank (ZMod p) V = d := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [hV, Nat.card_zmod] at h
    exact (Nat.pow_right_injective hp.two_le h).symm
  let b := Module.finBasisOfFinrankEq (ZMod p) V hrank
  refine ⟨b, fun a h i => ?_⟩
  have h' : ∑ j, (a j : ZMod p) • b j = 0 := by
    simpa only [Int.cast_smul_eq_zsmul] using h
  have hli := Fintype.linearIndependent_iff.mp b.linearIndependent (fun j => (a j : ZMod p)) h' i
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a i) p).mp hli

theorem exists_indep_family
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) :
    ∃ e : Fin d → M, (∀ i, e i ∈ torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ)) ∧
      ∀ a : Fin d → ℤ, ∑ i, a i • e i = 0 → ∀ i, (p : ℤ) ∣ a i := by
  haveI := finite_torsionBy hcard 1
  have hmod : ∀ m : torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ), p • m = 0 := fun m =>
    Subtype.ext (by
      rw [coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul ℤ, Submodule.coe_zero]
      exact smul_eq_zero_of_mem_torsionBy_one m.2)
  letI : Module (ZMod p) (torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ)) := AddCommGroup.zmodModule hmod
  have h1 : Nat.card (torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ)) = p ^ d := by rw [hcard 1, pow_one]
  obtain ⟨e, he⟩ := exists_family_of_card_eq_pow (p := p) h1
  refine ⟨fun i => (e i : M), fun i => (e i).2, fun a ha => he a (Subtype.ext ?_)⟩
  rw [Submodule.coe_sum, Submodule.coe_zero, ← ha]
  exact Finset.sum_congr rfl fun i _ => coe_smul_of_tower _ _

omit [Fact p.Prime] in
theorem dvd_of_rel_apply {x : Fin d → TateModule p M}
    (h1 : ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i) :
    ∀ (n : ℕ) (a : Fin d → ℤ), ∑ i, a i • (x i : ℕ → M) n = 0 →
      ∀ i, ((p ^ n : ℕ) : ℤ) ∣ a i := by
  intro n
  induction n with
  | zero => intro a _ i; simp
  | succ n ih =>
    intro a hab
    have hab1 : ∑ i, a i • (x i : ℕ → M) 1 = 0 := by
      have key : ∀ i, ((p ^ n : ℕ) : ℤ) • (a i • (x i : ℕ → M) (n + 1)) = a i • (x i : ℕ → M) 1 :=
        fun i => by
          rw [smul_comm, ← compat_pow (x i) 1 n, Nat.add_comm 1 n]
      have := congrArg (((p ^ n : ℕ) : ℤ) • ·) hab
      simp only [smul_zero, Finset.smul_sum, key] at this
      exact this
    have hdvd := h1 a hab1
    choose a' ha' using hdvd
    have hab' : ∑ i, a' i • (x i : ℕ → M) n = 0 := by
      have key : ∀ i, a i • (x i : ℕ → M) (n + 1) = a' i • (x i : ℕ → M) n := fun i => by
        rw [ha' i, mul_comm, mul_smul, compat]
      simpa only [key] using hab
    intro i
    rw [ha' i, pow_succ', Nat.cast_mul]
    exact mul_dvd_mul_left _ (ih a' hab' i)

noncomputable def levelMap (x : Fin d → TateModule p M) (n : ℕ) (c : Fin d → ZMod (p ^ n)) :
    torsionBy ℤ M ((p ^ n : ℕ) : ℤ) :=
  ⟨∑ i, ((c i).val : ℤ) • (x i : ℕ → M) n,
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (proj_mem_torsionBy n (x i))⟩

theorem levelMap_injective {x : Fin d → TateModule p M}
    (h1 : ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i) (n : ℕ) :
    Function.Injective (levelMap x n) := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  intro c c' h
  have h' : ∑ i, (((c i).val : ℤ) - (c' i).val) • (x i : ℕ → M) n = 0 := by
    have := sub_eq_zero.mpr (congrArg Subtype.val h)
    simp only [levelMap] at this
    rw [← Finset.sum_sub_distrib] at this
    simpa only [sub_smul] using this
  have hdvd := dvd_of_rel_apply h1 n _ h'
  funext i
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub ((c' i).val : ℤ) ((c i).val : ℤ) (p ^ n)).mpr
    (hdvd i)
  rwa [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
    eq_comm] at this

theorem levelMap_bijective
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d)
    {x : Fin d → TateModule p M}
    (h1 : ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i) (n : ℕ) :
    Function.Bijective (levelMap x n) := by
  haveI := finite_torsionBy hcard n
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  refine (levelMap_injective h1 n).bijective_of_nat_card_le ?_
  rw [hcard n, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem exists_coeffs
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d)
    {x : Fin d → TateModule p M}
    (h1 : ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i) (n : ℕ)
    {m : M} (hm : m ∈ torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) :
    ∃ a : Fin d → ℕ, ∑ i, (a i : ℤ) • (x i : ℕ → M) n = m := by
  obtain ⟨c, hc⟩ := (levelMap_bijective hcard h1 n).2 ⟨m, hm⟩
  exact ⟨fun i => (c i).val, congrArg Subtype.val hc⟩

theorem exists_eq_sum_smul
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d)
    {x : Fin d → TateModule p M}
    (h1 : ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i)
    (z : TateModule p M) : ∃ s : Fin d → ℤ_[p], ∑ i, s i • x i = z := by
  choose a ha using fun n => exists_coeffs hcard h1 n (proj_mem_torsionBy n z)
  have hcompat : ∀ n i, ((p ^ n : ℕ) : ℤ) ∣ (a (n + 1) i : ℤ) - a n i := fun n =>
    dvd_of_rel_apply h1 n _ (by
      rw [Finset.sum_congr rfl fun i _ => sub_smul _ _ ((x i : ℕ → M) n),
        Finset.sum_sub_distrib, ha n, sub_eq_zero, proj_apply, ← compat z n,
        ← proj_apply (n + 1) z, ← ha (n + 1), Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm, compat])
  have hca : ∀ i k, (p : ℤ) ^ k ∣ (fun k => (a k i : ℤ)) (k + 1) - (fun k => (a k i : ℤ)) k :=
    fun i k => by rw [← Nat.cast_pow]; exact hcompat k i
  refine ⟨fun i => PadicInt.ofIntSeq (fun k => (a k i : ℤ))
      (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ p (hca i)),
    Subtype.ext (funext fun n => ?_)⟩
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, ← proj_apply n z, ← ha n]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_apply]
  refine natCast_smul_eq_of_zmod_eq (torsion (x i) n) ?_
  rw [← toZModPow_eq_appr,
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun k => (a k i : ℤ)) p (hca i) n, Int.cast_natCast]

theorem exists_family
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) :
    ∃ x : Fin d → TateModule p M,
      ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i := by
  obtain ⟨e, he, h1⟩ := exists_indep_family hcard
  choose x hx using fun i => proj_surjective hcard 1 (e i) (he i)
  refine ⟨x, ?_⟩
  have hx' : ∀ i, (x i : ℕ → M) 1 = e i := fun i => by rw [← proj_apply]; exact hx i
  simp_rw [hx']
  exact h1

theorem top_le_span
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d)
    {x : Fin d → TateModule p M}
    (h1 : ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i) :
    ⊤ ≤ span ℤ_[p] (Set.range x) := by
  rintro z -
  obtain ⟨s, hs⟩ := exists_eq_sum_smul hcard h1 z
  rw [← hs]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

theorem coe_sum_smul_apply (s : Fin d → ℤ_[p]) (x : Fin d → TateModule p M) (n : ℕ) :
    ((∑ i, s i • x i : TateModule p M) : ℕ → M) n = ∑ i, (((s i).appr n : ℕ) : ℤ) • (x i : ℕ → M) n := by
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => smul_apply _ _ _

theorem linearIndependent_family {x : Fin d → TateModule p M}
    (h1 : ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i) :
    LinearIndependent ℤ_[p] x := by
  refine Fintype.linearIndependent_iff.mpr fun s hs i => ?_
  have hlev : ∀ n, ((p ^ n : ℕ) : ℤ) ∣ (((s i).appr n : ℕ) : ℤ) := fun n =>
    dvd_of_rel_apply h1 n (fun j => (((s j).appr n : ℕ) : ℤ)) (by
      rw [← coe_sum_smul_apply, hs]; rfl) i
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  rw [map_zero, toZModPow_eq_appr, ZMod.natCast_eq_zero_iff]
  exact Int.natCast_dvd_natCast.mp (hlev n)

noncomputable def basisOfCard
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) :
    Module.Basis (Fin d) ℤ_[p] (TateModule p M) :=
  Module.Basis.mk (v := (exists_family hcard).choose)
    (linearIndependent_family (exists_family hcard).choose_spec)
    (top_le_span hcard (exists_family hcard).choose_spec)

theorem moduleFinite_and_free
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) :
    Module.Finite ℤ_[p] (TateModule p M) ∧ Module.Free ℤ_[p] (TateModule p M) :=
  ⟨Module.Finite.of_basis (basisOfCard hcard), Module.Free.of_basis (basisOfCard hcard)⟩

theorem finrank_eq
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) :
    Module.finrank ℤ_[p] (TateModule p M) = d := by
  rw [Module.finrank_eq_card_basis (basisOfCard hcard), Fintype.card_fin]

end TateModule.RankDBasis

namespace JHPort

open AlgebraicCurve ModularCurve
open scoped MatrixGroups

theorem finiteIndex_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)

theorem exists_transcendental_finiteDimensional_xHFunctionFieldBar (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) :
    ∃ x : xHFunctionFieldBar M H, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional
        (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (xHFunctionFieldBar M H)))
        (xHFunctionFieldBar M H) := by
  haveI := finiteIndex_GammaH M H
  exact ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH M H)

theorem essFiniteType_of_presentation {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Algebra.EssFiniteType K F := by
  classical
  haveI := hfin
  let K₀ := IntermediateField.adjoin K ({x} : Set F)
  haveI : Module.Free K₀ F := Module.Free.of_divisionRing _ _
  let b := Module.finBasis K₀ F
  rw [← IntermediateField.fg_top_iff, IntermediateField.fg_def]
  refine ⟨insert x (Set.range b), (Set.finite_range b).insert x, ?_⟩
  refine le_antisymm le_top ?_
  intro y _
  have hy := b.sum_repr y
  rw [← hy]
  refine sum_mem fun j _ => ?_
  rw [Algebra.smul_def, IntermediateField.algebraMap_apply]
  refine mul_mem ?_ (IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem _ ⟨j, rfl⟩))
  exact IntermediateField.adjoin.mono K _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
    (b.repr y j).2

theorem isCurveOver_xHFunctionFieldBar (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    IsCurveOver (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) := by
  obtain ⟨x, hx, hfin⟩ := exists_transcendental_finiteDimensional_xHFunctionFieldBar M H
  haveI := hfin
  haveI : PerfectField
      (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (xHFunctionFieldBar M H))) :=
    PerfectField.ofCharZero
  haveI : Algebra.IsSeparable
      (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (xHFunctionFieldBar M H)))
      (xHFunctionFieldBar M H) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact AlgebraicCurve.isCurveOver_of_transcendental hx hfin inferInstance

theorem hasCanonicalDivisor_xHFunctionFieldBar (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := xHFunctionFieldBar M H) := by
  obtain ⟨x, hx, hfin⟩ := exists_transcendental_finiteDimensional_xHFunctionFieldBar M H
  haveI := isCurveOver_xHFunctionFieldBar M H
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) :=
    essFiniteType_of_presentation hfin
  haveI : PerfectField (AlgebraicClosure ℚ) := PerfectField.ofCharZero
  exact AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver

theorem card_torsionBy_jH (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (n : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (ModularCurve.JH M H) ((p ^ n : ℕ) : ℤ)) =
      (p ^ n) ^ (2 * @AlgebraicCurve.genus (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H)
        _ _ _ (hasCanonicalDivisor_xHFunctionFieldBar M H)) := by
  haveI := isCurveOver_xHFunctionFieldBar M H
  haveI := hasCanonicalDivisor_xHFunctionFieldBar M H
  have hAJ := AlgebraicCurve.Pic0.abelJacobiCard_genus (AlgebraicClosure ℚ)
    (ModularCurve.xHFunctionFieldBar M H)
    (exists_transcendental_finiteDimensional_xHFunctionFieldBar M H) p
  have h := hAJ n
  have e : Nat.card (Submodule.torsionBy ℤ (ModularCurve.JH M H) ((p ^ n : ℕ) : ℤ)) =
      Nat.card (AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
        (ModularCurve.xHFunctionFieldBar M H) (p ^ n)) := rfl
  rw [e, h, mul_comm (2 * _) n, pow_mul]

end JHPort

theorem solution (M p : ℕ) [NeZero M] [Fact p.Prime]
    (H : Subgroup (ZMod M)ˣ) :
    Module.Finite ℤ_[p] (TateModule p (ModularCurve.JH M H)) ∧
      Module.Free ℤ_[p] (TateModule p (ModularCurve.JH M H)) :=
  TateModule.RankDBasis.moduleFinite_and_free (JHPort.card_torsionBy_jH M p H)
