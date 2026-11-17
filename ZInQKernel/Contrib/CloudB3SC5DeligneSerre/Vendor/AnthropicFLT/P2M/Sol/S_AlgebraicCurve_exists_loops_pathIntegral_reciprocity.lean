/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity (git blob e1da60a250fa9306c56f5a0f733d4aad340d7c76, sha256 230e607fc9c8789141f89a39d5435daffc8903bde8480f80c41de8150db24788).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_Matrix_exists_transpose_mul_mul_eq_J
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_path_forall_pathIntegral_eq_sum_mul
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity

open scoped Manifold ContDiff Topology
open Set Filter AlgebraicCurve

namespace ReciprocityAssembly

section PlaceAlgebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have := congrArg (fun x : v.toValuationSubring => (x : F)) hu
    simpa using this
  rw [hcoe, v.ord_unit_smul_zpow u hπ]
  exact Int.natCast_nonneg n

theorem ordDifferential_nonneg (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {θ : Ω[F⁄K]} (hθ : θ ∈ regularDifferentials K F) : 0 ≤ v.ordDifferential θ := by
  obtain ⟨f, hf, hfe⟩ := (mem_regularDifferentials_iff (K := K) (F := F)).1 hθ v
  have h : v.differentialCoeff θ = f := v.differentialCoeff_unique hfe
  unfold Place.ordDifferential
  rw [h]
  exact ord_nonneg_of_mem v hf

theorem isRational_of_isAlgClosed [IsAlgClosed K] (w : Place K F) [w.FiniteResidue] :
    w.IsRational := by
  haveI : Module.Finite K w.ResidueField := Place.FiniteResidue.finite
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2

theorem ordDifferential_nonneg_of_evalAt_eq_zero (v : Place K F) (hv : v.IsRational)
    [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] {θ : Ω[F⁄K]} (hθ : -1 ≤ v.ordDifferential θ)
    (hres : v.evalAt (v.dCoordFn * v.differentialCoeff θ) = 0) :
    0 ≤ v.ordDifferential θ := by
  set h := v.differentialCoeff θ with hh
  have hgoal : 0 ≤ v.ord h → 0 ≤ v.ordDifferential θ := fun h' => h'
  apply hgoal
  by_cases h0 : h = 0
  · rw [h0, v.ord_zero]
  have hπ0 : v.dCoordFn ≠ 0 := by
    intro h0'
    have := v.ord_dCoordFn
    rw [h0', v.ord_zero] at this
    exact zero_ne_one this
  have hθ' : -1 ≤ v.ord h := hθ
  rcases hθ'.lt_or_eq with hlt | heq
  · omega
  · exfalso
    have hord0 : v.ord (v.dCoordFn * h) = 0 := by
      rw [v.ord_mul hπ0 h0, v.ord_dCoordFn, ← heq]; norm_num
    exact v.evalAt_ne_zero_of_ord_eq_zero hv (mul_ne_zero hπ0 h0) hord0 hres

end PlaceAlgebra

section Places

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem infinite_place (P₀ : Place ℂ F) : Infinite (Place ℂ F) := by
  have h1 : ((extChartAt 𝓘(ℂ, ℂ) P₀).target).Infinite :=
    infinite_of_mem_nhds (extChartAt 𝓘(ℂ, ℂ) P₀ P₀) (extChartAt_target_mem_nhds P₀)
  have h2 : ((extChartAt 𝓘(ℂ, ℂ) P₀).symm '' (extChartAt 𝓘(ℂ, ℂ) P₀).target).Infinite :=
    h1.image (extChartAt 𝓘(ℂ, ℂ) P₀).symm.injOn
  exact Set.infinite_univ_iff.1 (h2.mono (Set.subset_univ _))

theorem exists_not_mem (P₀ : Place ℂ F) (T : Finset (Place ℂ F)) : ∃ Q : Place ℂ F, Q ∉ T := by
  haveI := infinite_place P₀
  exact Infinite.exists_notMem_finset T

end Places

section MatrixAlgebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem bilin_transfer (X S Q : Matrix ι ι ℤ)
    (h : ∀ k l, Q k l = ∑ s, ∑ s', X s k * S s s' * X s' l) (z z' y y' : ι → ℂ)
    (hy : ∀ s, y s = ∑ k, (X s k : ℂ) * z k) (hy' : ∀ s, y' s = ∑ k, (X s k : ℂ) * z' k) :
    ∑ s, ∑ s', (S s s' : ℂ) * y s * y' s' = ∑ k, ∑ l, (Q k l : ℂ) * z k * z' l := by

  have hL : ∑ s, ∑ s', (S s s' : ℂ) * y s * y' s' =
      ∑ s, ∑ s', ∑ k, ∑ l, (S s s' : ℂ) * (X s k : ℂ) * (X s' l : ℂ) * z k * z' l := by
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    rw [hy s, hy' s', mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hR : ∑ k, ∑ l, (Q k l : ℂ) * z k * z' l =
      ∑ k, ∑ l, ∑ s, ∑ s', (S s s' : ℂ) * (X s k : ℂ) * (X s' l : ℂ) * z k * z' l := by
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [h k l]
    push_cast
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s' _ => ?_
    ring
  rw [hL, hR]

  calc ∑ s, ∑ s', ∑ k, ∑ l, (S s s' : ℂ) * (X s k : ℂ) * (X s' l : ℂ) * z k * z' l
      = ∑ s, ∑ k, ∑ s', ∑ l, (S s s' : ℂ) * (X s k : ℂ) * (X s' l : ℂ) * z k * z' l :=
        Finset.sum_congr rfl fun s _ => Finset.sum_comm
    _ = ∑ k, ∑ s, ∑ s', ∑ l, (S s s' : ℂ) * (X s k : ℂ) * (X s' l : ℂ) * z k * z' l :=
        Finset.sum_comm
    _ = ∑ k, ∑ s, ∑ l, ∑ s', (S s s' : ℂ) * (X s k : ℂ) * (X s' l : ℂ) * z k * z' l :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ s, ∑ s', (S s s' : ℂ) * (X s k : ℂ) * (X s' l : ℂ) * z k * z' l :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm

omit [DecidableEq ι] in

theorem coeff_transfer (P : Matrix ι ι ℤ) (κ : ι → ℤ) (y z : ι → ℂ)
    (hz : ∀ k, z k = ∑ s, (P k s : ℂ) * y s) :
    ∑ k, (κ k : ℂ) * z k = ∑ s, ((∑ k, P k s * κ k : ℤ) : ℂ) * y s := by
  simp_rw [hz, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem vec_invert (X P : Matrix ι ι ℤ) (hPX : P * X = 1) (z y : ι → ℂ)
    (hy : ∀ s, y s = ∑ k, (X s k : ℂ) * z k) : ∀ k, z k = ∑ s, (P k s : ℂ) * y s := by
  intro k
  simp_rw [hy, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hPX' : ∀ l, (∑ s, P k s * X s l : ℤ) = if k = l then 1 else 0 := by
    intro l
    have := congrFun (congrFun hPX k) l
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  symm
  calc ∑ l, ∑ s, (P k s : ℂ) * ((X s l : ℂ) * z l)
      = ∑ l, ((∑ s, P k s * X s l : ℤ) : ℂ) * z l := by
        refine Finset.sum_congr rfl fun l _ => ?_
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun s _ => ?_
        ring
    _ = z k := by
        simp_rw [hPX']
        simp [Finset.sum_ite_eq]

theorem negJ_form (n : ℕ) (y y' : Fin n ⊕ Fin n → ℂ) :
    ∑ s, ∑ s', ((-Matrix.J (Fin n) ℤ) s s' : ℂ) * y s * y' s' =
      ∑ j, (y (Sum.inl j) * y' (Sum.inr j) - y (Sum.inr j) * y' (Sum.inl j)) := by
  classical
  simp only [Fintype.sum_sum_type, Matrix.neg_apply, Matrix.J, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, Matrix.one_apply, neg_zero, Int.cast_zero, zero_mul,
    Finset.sum_const_zero, zero_add, add_zero, neg_neg]
  rw [← Finset.sum_add_distrib, ]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [Ne.symm hk]) (by simp),
    Finset.sum_eq_single j (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
  simp
  ring

end MatrixAlgebra

end ReciprocityAssembly

open ReciprocityAssembly in

theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] [HasCanonicalDivisor (K := ℂ) (F := F)]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    {n : ℕ} (b : Module.Basis (Fin n) ℂ ↥(regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (S : Finset (Place ℂ F)) :
    ∃ (Pα Pβ : Fin n → Place ℂ F) (α : ∀ j, Path (Pα j) (Pα j)) (β : ∀ j, Path (Pβ j) (Pβ j)),
      (∀ j t, α j t ∉ S ∧ α j t ≠ P₀ ∧ β j t ∉ S ∧ β j t ≠ P₀) ∧
      (∀ (Q : Place ℂ F) (δ : Path Q Q), ∃ κ μ : Fin n → ℤ,
        ∀ ξ ∈ regularDifferentials ℂ F,
          pathIntegral ξ δ =
            ∑ j, ((κ j : ℂ) * pathIntegral ξ (α j) + (μ j : ℂ) * pathIntegral ξ (β j))) ∧
      (∀ (Q : Place ℂ F) (δ : Path Q Q), (∀ t, δ t ∉ S) →
        ∃ (κ μ : Fin n → ℤ) (w : Place ℂ F → ℤ), ∀ θ : Ω[F⁄ℂ],
          (∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ) →
          (∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential θ) →
          pathIntegral θ δ =
            ∑ j, ((κ j : ℂ) * pathIntegral θ (α j) + (μ j : ℂ) * pathIntegral θ (β j)) +
              2 * Real.pi * Complex.I *
                ∑ v ∈ S, (w v : ℂ) * Place.evalAt v (v.dCoordFn * v.differentialCoeff θ)) ∧
      (∀ ξ ∈ regularDifferentials ℂ F, ∀ ξ' ∈ regularDifferentials ℂ F,
        ∑ j, (pathIntegral ξ (α j) * pathIntegral ξ' (β j) -
          pathIntegral ξ (β j) * pathIntegral ξ' (α j)) = 0) ∧
      (∀ (E : Divisor ℂ F) (θ : Ω[F⁄ℂ]),
        (∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ) →
        (∀ v : Place ℂ F, Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) = (E v : ℂ)) →
        (∀ v : Place ℂ F, E v ≠ 0 → v ∈ S) →
        ∃ κ μ : Fin n → ℤ, ∀ i : Fin n,
          ∑ j, (pathIntegral (b i : Ω[F⁄ℂ]) (α j) * pathIntegral θ (β j) -
              pathIntegral (b i : Ω[F⁄ℂ]) (β j) * pathIntegral θ (α j)) =
            2 * Real.pi * Complex.I *
              (abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ E i +
                ∑ j, ((κ j : ℂ) * pathIntegral (b i : Ω[F⁄ℂ]) (α j) +
                  (μ j : ℂ) * pathIntegral (b i : Ω[F⁄ℂ]) (β j)))) := by
  classical

  have hgen : ∀ v : Place ℂ F, v.DCoordGenerates := by
    obtain ⟨x, hx, hfd⟩ := hfg
    haveI := AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hfd
    exact fun v => AlgebraicCurve.dCoordGenerates_of_isCurveOver (K := ℂ) (F := F) v
  haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler (K := ℂ) (F := F)
  have hreg : ∀ ξ ∈ regularDifferentials ℂ F, ∀ v : Place ℂ F, 0 ≤ v.ordDifferential ξ :=
    fun ξ hξ v => by haveI := hgen v; exact ordDifferential_nonneg v hξ

  obtain ⟨Pz, Z, Q, hZav, hQt, hQdet, hG1, hG2, hRR, hR3⟩ :=
    AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw F hfg hF b P₀ S

  have hQt' : (-Q).transpose = -(-Q) := by rw [Matrix.transpose_neg, hQt]
  have hdet' : IsUnit (-Q).det := by
    rw [Matrix.det_neg]
    exact ((isUnit_one.neg).pow _).mul hQdet
  obtain ⟨P, hPdet, hPQ⟩ := Matrix.exists_transpose_mul_mul_eq_J (-Q) hQt' hdet'
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hPdet
  set X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ := ↑u⁻¹ with hX
  have hPX : P * X = 1 := by
    rw [← hu, hX, Units.mul_inv]

  have hkey : X.transpose * (-Matrix.J (Fin n) ℤ) * X = Q := by
    have h1 : X.transpose * Matrix.J (Fin n) ℤ * X = -Q := by
      rw [← hPQ]
      calc X.transpose * (P.transpose * -Q * P) * X
          = (P * X).transpose * -Q * (P * X) := by
            rw [Matrix.transpose_mul]
            simp only [Matrix.mul_assoc]
        _ = -Q := by rw [hPX, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.mul_neg, Matrix.neg_mul, h1, neg_neg]
  have hkey' : ∀ k l, Q k l = ∑ s, ∑ s', X s k * (-Matrix.J (Fin n) ℤ) s s' * X s' l := by
    intro k l
    rw [← hkey]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]

  set T : Finset (Place ℂ F) := insert P₀ S with hT
  have hZT : ∀ k t, Z k t ∉ T := by
    intro k t
    rw [hT, Finset.mem_insert, not_or]
    exact ⟨(hZav k t).2, (hZav k t).1⟩
  obtain ⟨Q₀, hQ₀⟩ := exists_not_mem P₀ T
  have hN2 := fun s : Fin n ⊕ Fin n =>
    AlgebraicCurve.exists_path_forall_pathIntegral_eq_sum_mul F hfg hF T Z hZT (fun k => X s k)
      Q₀ hQ₀
  choose Y hYav hYint using hN2
  have hYS : ∀ s t, Y s t ∉ S ∧ Y s t ≠ P₀ := by
    intro s t
    have h := hYav s t
    rw [hT, Finset.mem_insert, not_or] at h
    exact ⟨h.2, h.1⟩

  have hy_of_z : ∀ θ : Ω[F⁄ℂ], (∀ v : Place ℂ F, v ∉ T → 0 ≤ v.ordDifferential θ) →
      ∀ s, pathIntegral θ (Y s) = ∑ k, (X s k : ℂ) * pathIntegral θ (Z k) :=
    fun θ hθ s => hYint s θ hθ
  have hz_of_y : ∀ θ : Ω[F⁄ℂ], (∀ v : Place ℂ F, v ∉ T → 0 ≤ v.ordDifferential θ) →
      ∀ k, pathIntegral θ (Z k) =
        ∑ s, (P k s : ℂ) * pathIntegral θ (Y s) :=
    fun θ hθ => vec_invert X P hPX _ _ (hy_of_z θ hθ)
  have hregT : ∀ ξ ∈ regularDifferentials ℂ F, ∀ v : Place ℂ F, v ∉ T → 0 ≤ v.ordDifferential ξ :=
    fun ξ hξ v _ => hreg ξ hξ v
  have hthirdT : ∀ θ : Ω[F⁄ℂ], (∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential θ) →
      ∀ v : Place ℂ F, v ∉ T → 0 ≤ v.ordDifferential θ := by
    intro θ hθ v hv
    rw [hT, Finset.mem_insert, not_or] at hv
    exact hθ v hv.2

  have hform : ∀ θ θ' : Ω[F⁄ℂ], (∀ v : Place ℂ F, v ∉ T → 0 ≤ v.ordDifferential θ) →
      (∀ v : Place ℂ F, v ∉ T → 0 ≤ v.ordDifferential θ') →
      ∑ j, (pathIntegral θ (Y (Sum.inl j)) * pathIntegral θ' (Y (Sum.inr j)) -
          pathIntegral θ (Y (Sum.inr j)) * pathIntegral θ' (Y (Sum.inl j))) =
        ∑ k, ∑ l, (Q k l : ℂ) * pathIntegral θ (Z k) * pathIntegral θ' (Z l) := by
    intro θ θ' hθ hθ'
    rw [← negJ_form n (fun s => pathIntegral θ (Y s)) (fun s => pathIntegral θ' (Y s))]
    exact bilin_transfer X (-Matrix.J (Fin n) ℤ) Q hkey' _ _ _ _ (hy_of_z θ hθ) (hy_of_z θ' hθ')
  refine ⟨fun _ => Q₀, fun _ => Q₀, fun j => Y (Sum.inl j), fun j => Y (Sum.inr j),
    fun j t => ⟨(hYS _ t).1, (hYS _ t).2, (hYS _ t).1, (hYS _ t).2⟩, ?_, ?_, ?_, ?_⟩
  ·
    intro P₁ δ
    obtain ⟨κ, hκ⟩ := hG1 P₁ δ
    refine ⟨fun j => ∑ k, P k (Sum.inl j) * κ k,
      fun j => ∑ k, P k (Sum.inr j) * κ k, fun ξ hξ => ?_⟩
    rw [hκ ξ hξ, coeff_transfer P κ _ _ (hz_of_y ξ (hregT ξ hξ)), Fintype.sum_sum_type,
      ← Finset.sum_add_distrib]
  ·
    intro P₁ δ hδ
    obtain ⟨κ, w, hκ⟩ := hG2 P₁ δ hδ
    refine ⟨fun j => ∑ k, P k (Sum.inl j) * κ k,
      fun j => ∑ k, P k (Sum.inr j) * κ k, w, fun θ h1 h2 => ?_⟩
    rw [hκ θ h1 h2, coeff_transfer P κ _ _ (hz_of_y θ (hthirdT θ h2)), Fintype.sum_sum_type,
      ← Finset.sum_add_distrib]
  ·
    intro ξ hξ ξ' hξ'
    rw [hform ξ ξ' (hregT ξ hξ) (hregT ξ' hξ')]
    exact hRR ξ hξ ξ' hξ'
  ·
    intro E θ h1 h2 h3
    obtain ⟨κ, hκ⟩ := hR3 E θ h1 h2 h3
    have hθS : ∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential θ := by
      intro v hv
      haveI := hgen v
      have hE : E v = 0 := by
        by_contra hne
        exact hv (h3 v hne)
      refine ordDifferential_nonneg_of_evalAt_eq_zero v (isRational_of_isAlgClosed v) (h1 v) ?_
      rw [h2 v, hE, Int.cast_zero]
    refine ⟨fun j => ∑ k, P k (Sum.inl j) * κ k,
      fun j => ∑ k, P k (Sum.inr j) * κ k, fun i => ?_⟩
    have hbi : (b i : Ω[F⁄ℂ]) ∈ regularDifferentials ℂ F := (b i).2
    rw [hform _ θ (hregT _ hbi) (hthirdT θ hθS), hκ i,
      coeff_transfer P κ _ _ (hz_of_y _ (hregT _ hbi)), Fintype.sum_sum_type,
      ← Finset.sum_add_distrib]
