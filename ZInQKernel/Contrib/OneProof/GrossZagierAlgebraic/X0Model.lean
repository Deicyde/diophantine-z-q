import ZInQKernel.Contrib.OneProof.GrossZagierAlgebraic
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_aeval_jqN_toAdjoin
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi

/-!
# gzopt-dict: `ℚ(X₀(N)) = Frac(ℚ[X, Y]/(Φ_N))` for the field of the algebraic Gross–Zagier leaf

The leaf `GZAlg.GrossZagierAlgOptAt` takes `ℚ(X₀(N))` to be `X0Field N = ℚ(jq, jq(q^N)) ⊂ ℚ((q))`. This file
proves that this field is the function field of the plane model `Φ_N(X, Y) = 0` of `X₀(N)`: for the classical
modular polynomial `Φ_N` (any `ModularCurve.ModularPolynomialData N`, the FLT project's `Φ_N ∈ ℤ[j][Y]`, monic of
degree `ψ(N)` with `Φ_N(jq, jq(q^N)) = 0`):

* `ker_evJ`: the kernel of `ℚ[X][Y] → ℚ((q))`, `X ↦ jq`, `Y ↦ jq(q^N)`, is `(Φ_N)`;
* `nonempty_ringEquiv_fractionRing`: `X0Field N ≃+* Frac(ℚ[X][Y]/(Φ_N))`.

Inputs: the FLT project's (vendored) `[ℚ(jq)(jq(q^N)) : ℚ(jq)] = ψ(N)` and `Φ_N(jq, Y)(jq(q^N)) = 0`, and the
transcendence of `jq` (order `−1`, `GZAlg.aeval_ne_zero_of_order_neg`).

No `sorry`, no `axiom`.
-/

noncomputable section

open Polynomial ModularCurve

namespace ZInQ.GZAlg

variable {N : ℕ} [NeZero N]

/-- Evaluation `ℚ[X][Y] → ℚ((q))` at `(jq, jq(q^N))`. -/
def evJ (N : ℕ) [NeZero N] : ℚ[X][X] →+* LaurentSeries ℚ :=
  eval₂RingHom (aeval (R := ℚ) jq).toRingHom (jqN N)

/-- `Φ_N` with rational coefficients. -/
def PhiQ (data : ModularPolynomialData N) : ℚ[X][X] :=
  data.Φ.map (mapRingHom (Int.castRingHom ℚ))

theorem jq_order_neg : jq.order < 0 :=
  lt_of_le_of_lt (HahnSeries.order_le_of_coeff_ne_zero (by rw [coeff_jq_neg_one]; norm_num))
    (by norm_num)

theorem phiQ_monic (data : ModularPolynomialData N) : (PhiQ data).Monic := data.monic.map _

theorem natDegree_phiQ (data : ModularPolynomialData N) :
    (PhiQ data).natDegree = dedekindPsi N := by
  rw [PhiQ, data.monic.natDegree_map, data.natDegree_eq]

theorem evJ_phiQ (data : ModularPolynomialData N) : evJ N (PhiQ data) = 0 := by
  have h := data.eval_eq_zero
  rw [evJ, PhiQ, coe_eval₂RingHom, eval₂_map]
  have he : ((aeval (R := ℚ) jq).toRingHom.comp (mapRingHom (Int.castRingHom ℚ))) = evalAtJ := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [evalAtJ]
    · simp [evalAtJ]
  rw [he]; exact h

/-- `ℚ[X] → ℚ(jq)`, `X ↦ jq`. -/
def jqHom : ℚ[X] →+* IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) :=
  (aeval (R := ℚ) jGen).toRingHom

theorem val_jqHom (p : ℚ[X]) :
    ((jqHom p : IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) : LaurentSeries ℚ) =
      aeval jq p := by
  have h1 := Polynomial.hom_eval₂ p (algebraMap ℚ _)
    ((IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))).val :
      _ →+* LaurentSeries ℚ) jGen
  rw [jqHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_def]
  refine h1.trans ?_
  rw [aeval_def]
  congr 1
  exact Subsingleton.elim _ _

theorem jqHom_injective : Function.Injective jqHom := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hp0
  apply aeval_ne_zero_of_order_neg jq_order_neg hp0
  rw [← val_jqHom, hp]; rfl

/-- **The kernel of `(X, Y) ↦ (jq, jq(q^N))` is `(Φ_N)`.** -/
theorem ker_evJ (data : ModularPolynomialData N) :
    RingHom.ker (evJ N) = Ideal.span {PhiQ data} := by
  apply le_antisymm
  · intro P hP
    rw [RingHom.mem_ker] at hP
    set F := IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))
    set R := P %ₘ PhiQ data
    have hdec := modByMonic_add_div P (PhiQ data)
    have hR : evJ N R = 0 := by
      have := congrArg (evJ N) hdec
      rw [map_add, map_mul, evJ_phiQ, zero_mul, add_zero, hP] at this
      exact this
    -- `R(jq, Y)` kills `jq(q^N)` over `ℚ(jq)`
    have hR' : aeval (jqN N) (R.map jqHom) = 0 := by
      rw [aeval_def, eval₂_map]
      have he : (algebraMap F (LaurentSeries ℚ)).comp jqHom = (aeval (R := ℚ) jq).toRingHom := by
        refine Polynomial.ringHom_ext (fun a => ?_) ?_ <;>
        · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
            RingHom.coe_coe, IntermediateField.algebraMap_apply]
          exact val_jqHom _
      rw [he]; exact hR
    have hint : IsIntegral F (jqN N) := ⟨data.toAdjoin, data.toAdjoin_monic, by
      have := aeval_jqN_toAdjoin data
      rwa [aeval_def] at this⟩
    have hfin := IntermediateField.adjoin.finrank hint
    rw [finrank_adjoin_jqN_eq_dedekindPsi] at hfin
    have hR0 : R.map jqHom = 0 := by
      by_contra hne
      have h1 := minpoly.degree_le_of_ne_zero F (jqN N) hne hR'
      have h2 : (R.map jqHom).degree < (PhiQ data).degree :=
        lt_of_le_of_lt (degree_map_le) (degree_modByMonic_lt _ (phiQ_monic data))
      rw [degree_eq_natDegree (minpoly.ne_zero hint), ← hfin,
        degree_eq_natDegree (phiQ_monic data).ne_zero, natDegree_phiQ] at *
      exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)
    have hR00 : R = 0 := (Polynomial.map_eq_zero_iff jqHom_injective).1 hR0
    have hR00' : P %ₘ PhiQ data = 0 := hR00
    rw [← hdec, hR00', zero_add]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact evJ_phiQ data

/-- Evaluation `ℚ[X][Y] → X0Field N` at `(jq, jq(q^N))`. -/
def evK (N : ℕ) [NeZero N] : ℚ[X][X] →+* X0Field N :=
  eval₂RingHom (aeval (R := ℚ) (⟨jq, jq_mem N⟩ : X0Field N)).toRingHom ⟨jqN N, jqN_mem N⟩

theorem val_evK (P : ℚ[X][X]) : ((evK N P : X0Field N) : LaurentSeries ℚ) = evJ N P := by
  have h1 := Polynomial.hom_eval₂ P (aeval (R := ℚ) (⟨jq, jq_mem N⟩ : X0Field N)).toRingHom
    ((X0Field N).val : X0Field N →+* LaurentSeries ℚ) ⟨jqN N, jqN_mem N⟩
  rw [evK, evJ, coe_eval₂RingHom, coe_eval₂RingHom]
  refine h1.trans ?_
  congr 1
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · exact RingHom.congr_fun (Subsingleton.elim
      ((((X0Field N).val : X0Field N →+* LaurentSeries ℚ).comp
        (aeval (R := ℚ) (⟨jq, jq_mem N⟩ : X0Field N)).toRingHom).comp C)
      (((aeval (R := ℚ) jq).toRingHom).comp C)) a
  · simp

theorem ker_evK (data : ModularPolynomialData N) :
    RingHom.ker (evK N) = Ideal.span {PhiQ data} := by
  rw [← ker_evJ data]
  ext P
  simp only [RingHom.mem_ker]
  rw [← val_evK]
  exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.val_injective h⟩

/-- **`X0Field N` is the function field `Frac(ℚ[X, Y]/(Φ_N))` of the plane model of `X₀(N)`.** -/
theorem nonempty_ringEquiv_fractionRing (data : ModularPolynomialData N) :
    Nonempty (X0Field N ≃+* FractionRing (ℚ[X][X] ⧸ Ideal.span {PhiQ data})) := by
  set Q := ℚ[X][X] ⧸ Ideal.span {PhiQ data}
  let ψ : Q →+* X0Field N :=
    (RingHom.kerLift (evK N)).comp (Ideal.quotEquivOfEq (ker_evK data).symm).toRingHom
  have hψ : Function.Injective ψ :=
    (RingHom.kerLift_injective (evK N)).comp (Ideal.quotEquivOfEq (ker_evK data).symm).injective
  have hψmk : ∀ p, ψ (Ideal.Quotient.mk _ p) = evK N p := fun p => rfl
  let _ : Algebra Q (X0Field N) := ψ.toAlgebra
  have : FaithfulSMul Q (X0Field N) := (faithfulSMul_iff_algebraMap_injective Q _).2 hψ
  have hT : ∀ c : ℚ, algebraMap ℚ (LaurentSeries ℚ) c ∈
      Subfield.closure (Set.range (evJ N)) := fun c =>
    Subfield.subset_closure ⟨C (C c), by
      rw [evJ, coe_eval₂RingHom, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]⟩
  have hle : X0Field N ≤ (Subfield.closure (Set.range (evJ N))).toIntermediateField hT := by
    rw [X0Field, modularFunctionField, IntermediateField.adjoin_le_iff]
    rintro w (rfl | rfl)
    · exact Subfield.subset_closure ⟨C X, by simp [evJ]⟩
    · exact Subfield.subset_closure ⟨X, by simp [evJ, jqN]⟩
  have : IsFractionRing Q (X0Field N) := IsFractionRing.of_field Q (X0Field N) fun z => by
    have hz : (z : LaurentSeries ℚ) ∈ Subfield.closure (Set.range (evJ N)) := hle z.2
    obtain ⟨x, hx, y, hy, hxy⟩ := Subfield.mem_closure_iff.1 hz
    rw [show Set.range (evJ N) = ((evJ N).range : Set (LaurentSeries ℚ)) from
      (RingHom.coe_range _).symm, Subring.closure_eq] at hx hy
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨r, rfl⟩ := hy
    refine ⟨Ideal.Quotient.mk _ p, Ideal.Quotient.mk _ r, Subtype.val_injective ?_⟩
    change (z : LaurentSeries ℚ) = (((ψ (Ideal.Quotient.mk _ p)) / (ψ (Ideal.Quotient.mk _ r)) :
      X0Field N) : LaurentSeries ℚ)
    rw [hψmk, hψmk, ← hxy]
    rw [show (((evK N p / evK N r : X0Field N)) : LaurentSeries ℚ) =
      ((X0Field N).val : X0Field N →+* LaurentSeries ℚ) (evK N p / evK N r) from rfl, map_div₀]
    rw [show ((X0Field N).val : X0Field N →+* LaurentSeries ℚ) (evK N p) = evJ N p from val_evK p,
      show ((X0Field N).val : X0Field N →+* LaurentSeries ℚ) (evK N r) = evJ N r from val_evK r]
  exact ⟨(IsFractionRing.ringEquivOfRingEquiv (A := Q) (B := Q) (K := FractionRing Q) (L := X0Field N) (RingEquiv.refl _)).symm⟩

end ZInQ.GZAlg
