/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_DeligneSerre_exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen (git blob 96465fde620a16a318252607e66d5dabb31c3786, sha256 f93d13ca6585caa87063dfcffad7a787722026d788bd5470b098205edd156505).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_DeligneSerre_exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_DeligneSerre_exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_DeligneSerre_exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen

set_option autoImplicit false

open scoped BigOperators

namespace DeligneSerre55

theorem isIntegral_of_mem (R : Subalgebra ℤ ℂ) [Module.Finite ℤ R] {x : ℂ} (hx : x ∈ R) :
    IsIntegral ℤ x := by
  have h : IsIntegral ℤ (⟨x, hx⟩ : R) := Algebra.IsIntegral.isIntegral _
  simpa using h.map R.val

theorem exists_intermediateField (R : Subalgebra ℤ ℂ) [Module.Finite ℤ R] :
    ∃ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K ∧ (R : Set ℂ) ⊆ K := by
  classical
  obtain ⟨s, hs⟩ := Module.finite_def.mp (inferInstance : Module.Finite ℤ R)
  let S : Set ℂ := (s.image (fun x : R => (x : ℂ)) : Finset ℂ)
  haveI : Finite S := Finset.finite_toSet _ |>.to_subtype
  have hSint : ∀ x ∈ S, IsIntegral ℚ x := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    exact (isIntegral_of_mem R y.2).tower_top
  refine ⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin hSint, ?_⟩
  intro x hx
  have hxs : (⟨x, hx⟩ : R) ∈ Submodule.span ℤ (s : Set R) := by rw [hs]; trivial
  suffices h : ∀ y : R, y ∈ Submodule.span ℤ (s : Set R) →
      (y : ℂ) ∈ IntermediateField.adjoin ℚ S from h _ hxs
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
      exact IntermediateField.subset_adjoin ℚ S
        (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨z, hz, rfl⟩))
  | zero => simp
  | add a b _ _ ha hb => simpa using (IntermediateField.adjoin ℚ S).add_mem ha hb
  | smul n a _ ha => simpa using zsmul_mem ha n

theorem isIntegral_coe_intermediateField (K : IntermediateField ℚ ℂ) (x : K)
    (hx : IsIntegral ℤ (x : ℂ)) : IsIntegral ℤ x := by
  obtain ⟨q, hqm, hq⟩ := hx
  refine ⟨q, hqm, ?_⟩
  have h := Polynomial.hom_eval₂ q (algebraMap ℤ K) (K.val.toRingHom) x
  have h1 : (K.val.toRingHom).comp (algebraMap ℤ K) = algebraMap ℤ ℂ := Subsingleton.elim _ _
  rw [h1] at h
  have h2 : (K.val.toRingHom) (Polynomial.eval₂ (algebraMap ℤ K) x q) = 0 := by
    rw [h]; exact hq
  exact (map_eq_zero_iff _ Subtype.val_injective).mp h2

theorem lt_log_one_div_sub_one {M s : ℝ} (hs1 : 1 < s) (hs : s < 1 + Real.exp (-M)) :
    M < Real.log (1 / (s - 1)) := by
  have hpos : 0 < s - 1 := by linarith
  have hlt : s - 1 < Real.exp (-M) := by linarith
  have hlog : Real.log (s - 1) < -M := (Real.log_lt_iff_lt_exp hpos).mpr hlt
  rw [one_div, Real.log_inv]
  linarith

theorem log_one_div_sub_one_pos {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2) :
    0 < Real.log (1 / (s - 1)) := by
  apply Real.log_pos
  rw [lt_div_iff₀ (by linarith)]
  linarith

open ModularFormClass CongruenceSubgroup
open scoped MatrixGroups

theorem main
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) :
    ∃ R : Subalgebra ℤ ℂ, Module.Finite ℤ R ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N → ModularFormClass.qCoeff f p ∈ R) ∧
      ∀ η : ℝ, 0 < η → ∃ (Y : Finset ℂ) (X : Set ℕ),
        (∀ δ : ℝ, 0 < δ → ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
          ∑' p : {p : ℕ // p.Prime ∧ p ∈ X}, ((p : ℕ) : ℝ) ^ (-s) ≤
            (η + δ) * Real.log (1 / (s - 1))) ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N → p ∉ X → ModularFormClass.qCoeff f p ∈ Y := by
  classical

  obtain ⟨R, hfin, hR, hε, hconj⟩ :=
    DeligneSerre.exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen
      N ε f hf₁ hT
  haveI : Module.Finite ℤ R := hfin

  obtain ⟨K, hKfd, hRK⟩ := exists_intermediateField R
  haveI : FiniteDimensional ℚ K := hKfd
  haveI : NumberField K := NumberField.mk

  let ι : R →+* K :=
    { toFun := fun x => ⟨x.1, hRK x.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl }
  have hι : ∀ x : R, ((ι x : K) : ℂ) = (x : ℂ) := fun x => rfl

  choose ε' g hε' hg₁ hgp hgT using fun φ : K →+* ℂ => hconj (φ.comp ι)

  choose C hC using fun φ : K →+* ℂ =>
    DeligneSerre.exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen
      N (ε' φ) (g φ) (hg₁ φ) (hgT φ)

  have haK : ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) (φ : K →+* ℂ),
      φ ⟨qCoeff f p, hRK (hR p hp hpN)⟩ = qCoeff (g φ) p := by
    intro p hp hpN φ
    rw [hgp φ p hp hpN]
    rfl
  refine ⟨R, hfin, hR, fun η hη => ?_⟩

  set r : ℕ := Fintype.card (K →+* ℂ) with hr_def
  have hr : 0 < r := Fintype.card_pos
  set c : ℝ := r / η with hc_def
  have hc : 0 < c := div_pos (Nat.cast_pos.mpr hr) hη
  have hrc : (r : ℝ) / c = η := by
    rw [hc_def]; field_simp
  set B : ℝ := Real.sqrt c with hB_def

  let F : Finset K := (NumberField.Embeddings.finite_of_norm_le K ℂ B).toFinset
  let Y : Finset ℂ := F.image (fun x : K => (x : ℂ))

  let X : Set ℕ := {p | p.Prime ∧ ¬ p ∣ N ∧ ∃ φ : K →+* ℂ, c < ‖qCoeff (g φ) p‖ ^ 2}
  refine ⟨Y, X, ?_, ?_⟩
  ·
    intro δ hδ
    set Ctot : ℝ := ∑ φ : K →+* ℂ, C φ with hCtot_def
    set M : ℝ := max Ctot 0 / (c * δ) with hM_def
    have hM0 : 0 ≤ M := div_nonneg (le_max_right _ _) (mul_pos hc hδ).le
    refine ⟨1 + Real.exp (-M), by linarith [Real.exp_pos (-M)], fun s hs1 hs0 => ?_⟩
    have hexp1 : Real.exp (-M) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hM0)
    have hs2 : s < 2 := by linarith
    set L : ℝ := Real.log (1 / (s - 1)) with hL_def
    have hML : M < L := lt_log_one_div_sub_one hs1 hs0
    have hL0 : 0 < L := log_one_div_sub_one_pos hs1 hs2

    let PN := {p : ℕ // p.Prime ∧ ¬ p ∣ N}
    let PX := {p : ℕ // p.Prime ∧ p ∈ X}

    let G : PN → ℝ := fun p => ∑ φ : K →+* ℂ, ‖qCoeff (g φ) (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s)
    have hGs : Summable G := summable_sum fun φ _ => (hC φ s hs1 hs2).1
    have hGt : ∑' p, G p = ∑ φ : K →+* ℂ,
        ∑' p : PN, ‖qCoeff (g φ) (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s) :=
      Summable.tsum_finsetSum fun φ _ => (hC φ s hs1 hs2).1
    have hGle : ∑' p, G p ≤ r * L + Ctot := by
      rw [hGt]
      calc ∑ φ : K →+* ℂ, ∑' p : PN, ‖qCoeff (g φ) (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s)
          ≤ ∑ φ : K →+* ℂ, (L + C φ) := Finset.sum_le_sum fun φ _ => (hC φ s hs1 hs2).2
        _ = r * L + Ctot := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

    let e : PX → PN := fun p => ⟨p.1, p.2.1, p.2.2.2.1⟩
    have he : Function.Injective e := by
      intro p q hpq
      apply Subtype.ext
      have := congrArg Subtype.val hpq
      exact this
    have hsumX : Summable (fun p : PX => c * ((p : ℕ) : ℝ) ^ (-s)) := by
      have h0 : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
        Real.summable_nat_rpow.mpr (by linarith)
      exact (h0.subtype {p : ℕ | p.Prime ∧ p ∈ X}).mul_left c
    have hGnonneg : ∀ q : PN, 0 ≤ G q := fun q =>
      Finset.sum_nonneg fun φ _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hterm : ∀ p : PX, c * ((p : ℕ) : ℝ) ^ (-s) ≤ G (e p) := by
      intro p
      obtain ⟨hp, hpN, φ₀, hφ₀⟩ := p.2.2
      show c * ((p : ℕ) : ℝ) ^ (-s) ≤
        ∑ φ : K →+* ℂ, ‖qCoeff (g φ) (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s)
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      refine hφ₀.le.trans ?_
      exact Finset.single_le_sum (f := fun φ : K →+* ℂ => ‖qCoeff (g φ) (p : ℕ)‖ ^ 2)
        (fun φ _ => sq_nonneg _) (Finset.mem_univ φ₀)
    have hcmp : ∑' p : PX, c * ((p : ℕ) : ℝ) ^ (-s) ≤ ∑' q, G q :=
      Summable.tsum_le_tsum_of_inj e he (fun q _ => hGnonneg q) hterm hsumX hGs
    rw [tsum_mul_left] at hcmp

    have hmain : c * ∑' p : PX, ((p : ℕ) : ℝ) ^ (-s) ≤ r * L + Ctot := hcmp.trans hGle
    have h1 : ∑' p : PX, ((p : ℕ) : ℝ) ^ (-s) ≤ η * L + Ctot / c := by
      have h1' : ∑' p : PX, ((p : ℕ) : ℝ) ^ (-s) ≤ (r * L + Ctot) / c := by
        rw [le_div_iff₀ hc]; linarith [hmain]
      calc ∑' p : PX, ((p : ℕ) : ℝ) ^ (-s) ≤ (r * L + Ctot) / c := h1'
        _ = (r : ℝ) / c * L + Ctot / c := by ring
        _ = η * L + Ctot / c := by rw [hrc]
    have h2 : Ctot / c ≤ δ * L := by
      have h3 : Ctot / c ≤ max Ctot 0 / c := div_le_div_of_nonneg_right (le_max_left _ _) hc.le
      have h4 : max Ctot 0 / c = δ * M := by
        rw [hM_def]; field_simp
      rw [h4] at h3
      exact h3.trans (mul_le_mul_of_nonneg_left hML.le hδ.le)
    calc ∑' p : PX, ((p : ℕ) : ℝ) ^ (-s) ≤ η * L + Ctot / c := h1
      _ ≤ η * L + δ * L := by linarith
      _ = (η + δ) * L := by ring
  ·
    intro p hp hpN hpX
    have hall : ∀ φ : K →+* ℂ, ‖qCoeff (g φ) p‖ ^ 2 ≤ c := by
      intro φ
      by_contra h
      exact hpX ⟨hp, hpN, φ, lt_of_not_ge h⟩
    let x : K := ⟨qCoeff f p, hRK (hR p hp hpN)⟩
    have hxint : IsIntegral ℤ x :=
      isIntegral_coe_intermediateField K x (isIntegral_of_mem R (hR p hp hpN))
    have hxB : ∀ φ : K →+* ℂ, ‖φ x‖ ≤ B := by
      intro φ
      rw [haK p hp hpN φ, hB_def]
      exact Real.le_sqrt_of_sq_le (hall φ)
    have hxF : x ∈ F := (Set.Finite.mem_toFinset (hs := _)).mpr ⟨hxint, hxB⟩
    exact Finset.mem_image.mpr ⟨x, hxF, rfl⟩

end DeligneSerre55

open CongruenceSubgroup
open scoped MatrixGroups

theorem solution
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) :
    ∃ R : Subalgebra ℤ ℂ, Module.Finite ℤ R ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N → ModularFormClass.qCoeff f p ∈ R) ∧
      ∀ η : ℝ, 0 < η → ∃ (Y : Finset ℂ) (X : Set ℕ),
        (∀ δ : ℝ, 0 < δ → ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
          ∑' p : {p : ℕ // p.Prime ∧ p ∈ X}, ((p : ℕ) : ℝ) ^ (-s) ≤
            (η + δ) * Real.log (1 / (s - 1))) ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N → p ∉ X → ModularFormClass.qCoeff f p ∈ Y :=
  DeligneSerre55.main N ε f hf₁ hT
