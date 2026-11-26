import ZInQKernel.Contrib.OneProof.C8DeRham.KatoBdRDualRank

/-! # The newform representation in Kato's cohomological normalization

The literature input is existential on one coefficient model; it does not
assert anything about a separately selected Lean representation. Its local
period rank, Hodge–Tate multiplicities and good-prime traces are on that
same model. The arithmetic normalization is obtained by a linear dual.
-/

noncomputable section

namespace C8Kato

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module
open HTNewAssembly
open HDec.G0Galois.C8Conrad.Manuscript (geomBdRSpace isDeRham_dual_of_geomBdR_rank)

/-- The finite-coefficient consequences of Kato, *p-adic Hodge theory and
values of zeta functions of modular forms*, Astérisque 295 (2004): §§6.1,
6.3 and 8.3 (pp. 160–162, 181–182) give the normalized newform's coefficient
field and rank-two cohomological representation. §9.2 and §9.4 (pp. 187–188)
give the de Rham rank and the two filtration degrees, 0 and k−1. The
Hodge–Tate dimensions are the corresponding graded dimensions by the
filtered de Rham comparison (cf. Kato (13.13.1), p. 233). Equation (14.10.3),
p. 240, gives the good-prime trace on inverse arithmetic Frobenius and
unramifiedness there, since its polynomial on inertia invariants has degree
two. The finite field is the image of the completion cut out by the two
embeddings. There is no restriction on the level at the local prime and
no semisimplicity clause in this existence statement.

Source: https://www.numdam.org/item/AST_2004__295__117_0.pdf -/
def NewformGeometricComparison : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) [NeZero N] (k : ℤ) (f : HeckeRing.GL2.Newform N k), 2 ≤ k →
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (_ : FiniteDimensional ℚ_[ℓ] E)
      (ρ : GQ →* GL (Fin 2) E), Continuous ρ ∧
      (∀ q : ℕ, q.Prime → ¬ q ∣ N * ℓ → ∀ v : ValuationSubring Qbar, LiesOver v q →
        ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : GQ) = 1) ∧
      (∀ q : ℕ, q.Prime → ¬ q ∣ N * ℓ →
        ∃ α : Qbar, ιC α = coeff (f.toCuspForm : CF N k) q ∧
          ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v q → IsArithFrob σ v q →
            (((ρ σ⁻¹ : Matrix (Fin 2) (Fin 2) E).trace : E) : PadicAlgCl ℓ) = ιL α) ∧
      PrintHasHTWeights ℓ E (ρ.comp (decomp ℓ)) {0, k - 1} ∧
      finrank ℚ_[ℓ] (geomBdRSpace ℓ E (ρ.comp (decomp ℓ))) = 2 * finrank ℚ_[ℓ] E

/-- Forget the de Rham enhancement and select the geometric disjunct of the
live input, without an eigenform coefficient algebraicity premise. -/
theorem modularHTCoeff_of_kato (h : NewformGeometricComparison) : ModularHTCoeff := by
  intro ℓ _ ιC ιL N _ k f hk
  obtain ⟨E, hE, ρ, hc, hu, ht, hHT, _⟩ := h ℓ ιC ιL N k f hk
  refine ⟨E, hE, ρ, hc, hu, Or.inr ⟨?_, hHT⟩⟩
  intro q hq hqN α hα v σ hv hσ
  obtain ⟨β, hβ, htrace⟩ := ht q hq hqN
  have hαβ : α = β := ιC.injective (hα.trans hβ.symm)
  rw [hαβ]
  exact htrace v σ hv hσ

set_option maxHeartbeats 1700000 in
/-- The same cohomological model gives a single arithmetic-normalized
attached representation carrying both local conclusions. No identification
with an arbitrary semisimple `ρ` is assumed. -/
theorem arithmetic_witness_of_kato (h : NewformGeometricComparison)
    (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) [NeZero N] (k : ℤ) (f : HeckeRing.GL2.Newform N k) (hk : 2 ≤ k) :
    ∃ ρ : GaloisRep ℓ 2, ρ.AttachedTo ιC ιL (f.toCuspForm : CF N k) ∧
      ρ.HasHTWeightsAtSelf ℓ {0, 1 - k} ∧ LocalIsDeRham ℓ 2 (ρ.restrictLocal ℓ) := by
  obtain ⟨E, hE, ρ, hc, hu, hfrob, hHT, hdR⟩ := h ℓ ιC ιL N k f hk
  letI : FiniteDimensional ℚ_[ℓ] E := hE
  let ρ₀ := toGR E ρ hc
  let r := EigenformHTPrinted.dualGR ρ₀
  refine ⟨r, ?_, ?_, ?_⟩
  · intro q hq hqN
    refine ⟨?_, ?_⟩
    · intro v hv σ hσ
      apply Units.ext
      change r.mat ((σ : v.decompositionSubgroup ℚ) : GQ) = 1
      rw [EigenformHTPrinted.dualGR_mat, toGR_mat]
      have hτ := hu q hq hqN v hv (σ⁻¹) (inv_mem hσ)
      change ρ (((σ : v.decompositionSubgroup ℚ) : GQ)⁻¹) = 1 at hτ
      rw [hτ, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
    · obtain ⟨α, hα, ht⟩ := hfrob q hq hqN
      refine ⟨α, hα, fun v σ hv hσ => ?_⟩
      change (r.mat σ).trace = ιL α
      rw [EigenformHTPrinted.dualGR_mat, Matrix.trace_transpose, trace_toGR]
      exact ht v σ hv hσ
  · have h₀ := kernel_of_print E ρ hc {0, k - 1} (by simp) hHT
    have h₁ := EigenformHTPrinted.htDual ℓ 2 ρ₀ {0, k - 1} (by simp) h₀
    simpa only [neg_pair] using h₁
  · refine ⟨E, hE, dualE (ρ.comp (decomp ℓ)), fun σ => ?_, isDeRham_dual_of_geomBdR_rank ℓ E _ hdR⟩
    apply Units.ext
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, dualE_val, Matrix.transpose_apply]
    change _ = r.mat (decomp ℓ σ) i j
    rw [EigenformHTPrinted.dualGR_mat, Matrix.transpose_apply, toGR_mat, Matrix.map_apply]
    change (algebraMap E (PadicAlgCl ℓ)) ((ρ (decomp ℓ σ⁻¹) : Matrix (Fin 2) (Fin 2) E) j i) = _
    rw [map_inv (decomp ℓ)]

end C8Kato
