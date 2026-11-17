import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.TorsionQuadraticGeneratorSpan
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelDiamondFromProducts
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinLowerTraceClosure
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelDivisionSeriesMembership
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionCorrelationSigned

/-!
# Repeated-prime trace of degree-two principal products

Let `p` be prime, `ℓ ≥ 3` and `p ∣ ℓ`. For the actual normalized trace from `Γ(pℓ)` to `Γ(ℓ)`
(the true `ModularForm.trace` divided by the relative index), the trace of every admissible
degree-two product `λ_P λ_Q` of principal weight-one torsion forms at level `pℓ` lies in the span of
admissible degree-two products at level `ℓ` (`trace_product_mem'`).

* Rank zero (both labels divisible by `p`): the product is a restricted lower product.
* Rank one (`P` nonzero modulo `p`, `Q ≡ σ P`): actual `Γ(ℓ)` moves reach the whole paired fibre
  `(P + ℓT, Q + σℓT)`, so the trace is `p⁻²` times the trace of the fibre sum. The fibre sum is the
  signed correlation at slope `-σ`; its rows have both row combinations divisible by `p`, so they
  are restricted lower products, and the series correction descends from the canonical level to
  `pℓ` by invariance, then traces into the lower series span, which lies in the product span.
* Rank two (`P, Q` independent modulo `p`): one-parameter exactly trace-zero moves fix `P` and move
  `Q` to `Q + γℓP`. Averaging over `γ`, the Fourier duality of the second factor and the finite
  geometric sum keep only labels `W` with `det(P, W) ≡ 0 (mod p)`, i.e. dependent pairs, handled
  by the first two cases.

No trace preservation, spanning of the whole modular-form space, basis or rank statement, or
correlation-membership premise is used.
-/

noncomputable section
set_option autoImplicit false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.RepeatedPrimeProductTrace

open EisensteinWeightTwo DivisionEisensteinLevelMaps DivisionEisensteinLowerClosure
open AllLevelForms AllLevelPrincipal AllLevelProducts
open ThetaFiveTorsion (act act_mul act_one)

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-! ### Series generators lie in the product span -/

theorem series_generator_mem_productSpan (ell : ℕ) (hl : 3 ≤ ell) (a : Fin 2 → ℤ) :
    divisionEisensteinMF ell (by omega) a ∈ TorsionQuadraticGenerators.productSpan ell (by omega) := by
  have : NeZero ell := ⟨by omega⟩
  have ha : a = ![a 0, a 1] := by ext i; fin_cases i <;> rfl
  rw [ha, ← DivisionSeriesMembership.xForm_eq_divisionEisensteinMF ell (by omega) (a 0) (a 1)]
  have he : WeierstrassForms.xForm ell (by omega) (a 0) (a 1) =
      TorsionQuadraticGenerators.xForm ell hl (a 0) (a 1) :=
    DFunLike.ext _ _ fun τ => by
      rw [WeierstrassForms.xForm_apply, TorsionQuadraticGenerators.xForm_apply]
  rw [he]
  exact TorsionQuadraticGenerators.xForm_mem_productSpan ell hl _ _

theorem seriesSpan_le_productSpan (ell : ℕ) (hl : 3 ≤ ell) :
    seriesSpan ell (by omega) ≤ TorsionQuadraticGenerators.productSpan ell (by omega) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact series_generator_mem_productSpan ell hl a

theorem trace_series_mem_productSpan {ell M : ℕ} (hl : 3 ≤ ell) (hM : 0 < M) (hlM : ell ∣ M)
    {f : _root_.ModularForm (ΓP M) 2} (hf : f ∈ seriesSpan M hM) :
    normalizedTrace ell M hM f ∈ TorsionQuadraticGenerators.productSpan ell (by omega) :=
  seriesSpan_le_productSpan ell hl (trace_seriesSpan_all (by omega) hM hlM hf)

/-! ### Rank zero: both labels divisible by the prime -/

theorem productForm_scaled_eq_restriction (p ell : ℕ) (hp : 0 < p) (hl : 0 < ell)
    (w : Fin 2 → ℤ × ℤ) (hw : ∀ i, Good ell (w i))
    (hw' : ∀ i, Good (p * ell) ((p : ℤ) * (w i).1, (p : ℤ) * (w i).2)) :
    (productForm (p * ell) (Nat.mul_pos hp hl) 2
        (fun i => ((p : ℤ) * (w i).1, (p : ℤ) * (w i).2)) hw' : _root_.ModularForm (ΓP (p * ell)) 2) =
      restriction ell (p * ell) (dvd_mul_left ell p) (productForm ell hl 2 w hw) := by
  apply _root_.ModularForm.ext
  intro τ
  rw [restriction_apply, productForm_apply, productForm_apply]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : ¬ (((p * ell : ℕ) : ℤ) ∣ (p : ℤ) * (w i).1 ∧ ((p * ell : ℕ) : ℤ) ∣ (p : ℤ) * (w i).2) :=
    hw' i
  have h2 : ¬ ((ell : ℤ) ∣ (w i).1 ∧ (ell : ℤ) ∣ (w i).2) := hw i
  rw [← TorsionDistributionTwo.reg_of_good h1, ← TorsionDistributionTwo.reg_of_good h2]
  exact TorsionCorrelation.reg_scale p ell hp hl _ _ τ

/-- **Rank zero.** -/
theorem trace_rank_zero_mem (p ell : ℕ) (hp : 0 < p) (hl : 3 ≤ ell)
    (v : Fin 2 → ℤ × ℤ) (hv : ∀ i, Good (p * ell) (v i))
    (hdiv : ∀ i, (p : ℤ) ∣ (v i).1 ∧ (p : ℤ) ∣ (v i).2) :
    normalizedTrace ell (p * ell) (Nat.mul_pos hp (by omega))
        (productForm (p * ell) (Nat.mul_pos hp (by omega)) 2 v hv) ∈
      TorsionQuadraticGenerators.productSpan ell (by omega) := by
  have hl0 : 0 < ell := by omega
  have : NeZero (p * ell) := ⟨(Nat.mul_pos hp hl0).ne'⟩
  set w : Fin 2 → ℤ × ℤ := fun i => ((v i).1 / p, (v i).2 / p) with hwdef
  have hvw : ∀ i, v i = ((p : ℤ) * (w i).1, (p : ℤ) * (w i).2) := fun i =>
    Prod.ext (Int.mul_ediv_cancel' (hdiv i).1).symm (Int.mul_ediv_cancel' (hdiv i).2).symm
  have hw' : ∀ i, Good (p * ell) ((p : ℤ) * (w i).1, (p : ℤ) * (w i).2) := fun i => by
    rw [← hvw i]; exact hv i
  have hw : ∀ i, Good ell (w i) := fun i h => hw' i (by
    push_cast
    exact ⟨mul_dvd_mul_left (p : ℤ) h.1, mul_dvd_mul_left (p : ℤ) h.2⟩)
  have heq : productForm (p * ell) (Nat.mul_pos hp hl0) 2 v hv =
      productForm (p * ell) (Nat.mul_pos hp hl0) 2
        (fun i => ((p : ℤ) * (w i).1, (p : ℤ) * (w i).2)) hw' :=
    AllLevelDiamondFromProducts.productForm_eq_of_congr 2 _ _ hv hw' fun i => by
      rw [← hvw i]; exact ⟨by simp, by simp⟩
  rw [heq, productForm_scaled_eq_restriction p ell hp hl0 w hw hw', normalizedTrace_restriction]
  exact Submodule.subset_span ⟨w, hw, rfl⟩

/-! ### Trace constancy along `Γ(ℓ)` moves of both labels -/

theorem quotientFunc_product_right_shift (N M : ℕ) (hM : 0 < M) (v : Fin 2 → ℤ × ℤ)
    (hv : ∀ i, Good M (v i)) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma N)
    (q : (ΓP N) ⧸ (ΓP M).subgroupOf (ΓP N)) :
    let g : (ΓP N) := ⟨mapGL ℝ γ, Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩⟩
    let _ := mapped_principal_subgroup_normal N M
    SlashInvariantForm.quotientFunc
        (productForm M hM 2 (fun i => act (v i) γ) (good_act_tuple hv γ) :
          _root_.ModularForm (ΓP M) 2) q =
      SlashInvariantForm.quotientFunc (productForm M hM 2 v hv : _root_.ModularForm (ΓP M) 2)
        (MulOpposite.op g⁻¹ • q) := by
  let g : (ΓP N) := ⟨mapGL ℝ γ, Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩⟩
  let _ := mapped_principal_subgroup_normal N M
  change SlashInvariantForm.quotientFunc
      (productForm M hM 2 (fun i => act (v i) γ) (good_act_tuple hv γ) :
        _root_.ModularForm (ΓP M) 2) q =
    SlashInvariantForm.quotientFunc (productForm M hM 2 v hv : _root_.ModularForm (ΓP M) 2)
      (MulOpposite.op g⁻¹ • q)
  have hseries : ⇑(productForm M hM 2 (fun i => act (v i) γ) (good_act_tuple hv γ) :
      _root_.ModularForm (ΓP M) 2) =
      (⇑(productForm M hM 2 v hv : _root_.ModularForm (ΓP M) 2) : ℍ → ℂ) ∣[((2 : ℕ) : ℤ)]
        (mapGL ℝ γ) := by
    have h := productForm_slash hM 2 v hv γ
    rw [ModularForm.SL_slash] at h
    exact h.symm
  induction q using QuotientGroup.induction_on' with
  | H r =>
    rw [MulAction.Quotient.smul_coe, SlashInvariantForm.quotientFunc_mk,
      SlashInvariantForm.quotientFunc_mk, hseries, ← SlashAction.slash_mul]
    simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Subgroup.coe_mul,
      Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv, g]

/-- The actual normalized trace of a product is constant on actual `Γ(N)` label moves. -/
theorem normalizedTrace_product_SL (N M : ℕ) (hM : 0 < M) (v : Fin 2 → ℤ × ℤ)
    (hv : ∀ i, Good M (v i)) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma N) :
    normalizedTrace N M hM (productForm M hM 2 (fun i => act (v i) γ) (good_act_tuple hv γ)) =
      normalizedTrace N M hM (productForm M hM 2 v hv) := by
  classical
  let : NeZero M := ⟨hM.ne'⟩
  let _ := mapped_principal_subgroup_normal N M
  let Q := (ΓP N) ⧸ (ΓP M).subgroupOf (ΓP N)
  let : Fintype Q := Fintype.ofFinite Q
  let g : (ΓP N) := ⟨mapGL ℝ γ, Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩⟩
  rw [normalizedTrace_apply, normalizedTrace_apply]
  apply congrArg (fun f : _root_.ModularForm (ΓP N) 2 => (traceIndex N M : ℂ)⁻¹ • f)
  apply DFunLike.coe_injective
  rw [_root_.ModularForm.coe_trace, _root_.ModularForm.coe_trace]
  have he : ∀ q : Q,
      SlashInvariantForm.quotientFunc
          (productForm M hM 2 (fun i => act (v i) γ) (good_act_tuple hv γ) :
            _root_.ModularForm (ΓP M) 2) q =
        SlashInvariantForm.quotientFunc (productForm M hM 2 v hv : _root_.ModularForm (ΓP M) 2)
          (MulOpposite.op g⁻¹ • q) := fun q =>
    quotientFunc_product_right_shift N M hM v hv γ hγ q
  simp_rw [he]
  exact Equiv.sum_comp (MulAction.toPerm (MulOpposite.op g⁻¹))
    (SlashInvariantForm.quotientFunc (productForm M hM 2 v hv : _root_.ModularForm (ΓP M) 2))

/-! ### Rank one: the paired fibre -/

theorem good_of_congr {M : ℕ} {v w : ℤ × ℤ} (hv : Good M v) (h : CongrN M v w) : Good M w := by
  rintro ⟨h1, h2⟩
  exact hv ⟨by simpa using dvd_add h.1 h1, by simpa using dvd_add h.2 h2⟩

/-- Paired fibre moves: one actual `Γ(ℓ)` element moves `P` to `P + ℓ(r,t)` and simultaneously
`Q ≡ σ P (mod p)` to `Q + σ ℓ (r,t)`, modulo `pℓ`. -/
theorem exists_rank_one_move (p ell : ℕ) [Fact p.Prime] (hpl : p ∣ ell) (a b c d σ : ℤ)
    (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0)
    (hc : (p : ℤ) ∣ c - σ * a) (hd : (p : ℤ) ∣ d - σ * b) (r t : ℤ) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma ell ∧
      CongrN (p * ell) (act (a, b) γ) (a + ell * r, b + ell * t) ∧
      CongrN (p * ell) (act (c, d) γ) (c + ell * (σ * r), d + ell * (σ * t)) := by
  obtain ⟨x, y, z, hr, hs⟩ := exists_trace_zero_coefficients p a b r t hab
  obtain ⟨γ, hγ, he⟩ := exists_Gamma_lift_trace_zero p ell hpl x y z
  have hd' : ∀ i j, ((p * ell : ℕ) : ℤ) ∣
      ((!![1 + (ell : ℤ) * x, (ell : ℤ) * y; (ell : ℤ) * z, 1 - (ell : ℤ) * x] :
        Matrix (Fin 2) (Fin 2) ℤ) i j) - γ i j := fun i j =>
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (he i j)
  obtain ⟨m00, e00⟩ := hd' 0 0
  obtain ⟨m01, e01⟩ := hd' 0 1
  obtain ⟨m10, e10⟩ := hd' 1 0
  obtain ⟨m11, e11⟩ := hd' 1 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Nat.cast_mul] at e00 e01 e10 e11
  obtain ⟨k1, hk1⟩ := hr
  obtain ⟨k2, hk2⟩ := hs
  obtain ⟨u, hu⟩ := hc
  obtain ⟨w, hw⟩ := hd
  refine ⟨γ, hγ, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · refine ⟨k1 - a * m00 - b * m10, ?_⟩
    simp only [act]; push_cast
    linear_combination (-a) * e00 + (-b) * e10 + (ell : ℤ) * hk1
  · refine ⟨k2 - a * m01 - b * m11, ?_⟩
    simp only [act]; push_cast
    linear_combination (-a) * e01 + (-b) * e11 + (ell : ℤ) * hk2
  · refine ⟨u * x + w * z + σ * k1 - c * m00 - d * m10, ?_⟩
    simp only [act]; push_cast
    linear_combination (-c) * e00 + (-d) * e10 + (ell : ℤ) * x * hu + (ell : ℤ) * z * hw +
      (ell : ℤ) * σ * hk1
  · refine ⟨u * y - w * x + σ * k2 - c * m01 - d * m11, ?_⟩
    simp only [act]; push_cast
    linear_combination (-c) * e01 + (-d) * e11 + (ell : ℤ) * y * hu - (ell : ℤ) * x * hw +
      (ell : ℤ) * σ * hk2

/-- The shifted pair of labels in the paired fibre. -/
def fibreLabels (ell : ℕ) (a b c d σ r t : ℤ) : Fin 2 → ℤ × ℤ :=
  ![(a + ell * r, b + ell * t), (c + ell * (σ * r), d + ell * (σ * t))]

theorem fibre_good (p ell : ℕ) [Fact p.Prime] (hpl : p ∣ ell) (a b c d σ : ℤ)
    (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0)
    (hc : (p : ℤ) ∣ c - σ * a) (hd : (p : ℤ) ∣ d - σ * b)
    (hv : ∀ i, Good (p * ell) (![(a, b), (c, d)] i)) (r t : ℤ) :
    ∀ i, Good (p * ell) (fibreLabels ell a b c d σ r t i) := by
  obtain ⟨γ, _, h1, h2⟩ := exists_rank_one_move p ell hpl a b c d σ hab hc hd r t
  intro i
  fin_cases i
  · exact good_of_congr (good_act (hv 0) γ) h1
  · exact good_of_congr (good_act (hv 1) γ) h2

/-- Every member of the paired fibre has the same actual trace as the original product. -/
theorem normalizedTrace_fibre_point (p ell : ℕ) [Fact p.Prime] (hl : 0 < ell) (hpl : p ∣ ell)
    (a b c d σ : ℤ) (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0)
    (hc : (p : ℤ) ∣ c - σ * a) (hd : (p : ℤ) ∣ d - σ * b)
    (hv : ∀ i, Good (p * ell) (![(a, b), (c, d)] i)) (r t : ℤ)
    (hf : ∀ i, Good (p * ell) (fibreLabels ell a b c d σ r t i)) :
    normalizedTrace ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl)
        (productForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl) 2
          (fibreLabels ell a b c d σ r t) hf) =
      normalizedTrace ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl)
        (productForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl) 2 ![(a, b), (c, d)] hv) := by
  have hM := Nat.mul_pos (Fact.out : p.Prime).pos hl
  have : NeZero (p * ell) := ⟨hM.ne'⟩
  obtain ⟨γ, hγ, h1, h2⟩ := exists_rank_one_move p ell hpl a b c d σ hab hc hd r t
  have heq : productForm (p * ell) hM 2 (fibreLabels ell a b c d σ r t) hf =
      productForm (p * ell) hM 2 (fun i => act (![(a, b), (c, d)] i) γ) (good_act_tuple hv γ) := by
    refine AllLevelDiamondFromProducts.productForm_eq_of_congr 2 _ _ hf _ fun i => ?_
    fin_cases i
    · exact ⟨dvd_sub_comm.mp h1.1, dvd_sub_comm.mp h1.2⟩
    · exact ⟨dvd_sub_comm.mp h2.1, dvd_sub_comm.mp h2.2⟩
  rw [heq]
  exact normalizedTrace_product_SL ell (p * ell) hM _ hv γ hγ

/-- **Rank-one normalization**: the actual trace equals `p⁻²` times the trace of the complete
paired fibre sum, with the count `p²` coming from the explicit index set. -/
theorem normalizedTrace_rank_one_average (p ell : ℕ) [Fact p.Prime] (hl : 0 < ell)
    (hpl : p ∣ ell) (a b c d σ : ℤ) (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0)
    (hc : (p : ℤ) ∣ c - σ * a) (hd : (p : ℤ) ∣ d - σ * b)
    (hv : ∀ i, Good (p * ell) (![(a, b), (c, d)] i)) :
    normalizedTrace ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl)
        (productForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl) 2 ![(a, b), (c, d)] hv) =
      ((p : ℂ) ^ 2)⁻¹ • normalizedTrace ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl)
        (∑ r : Fin p, ∑ t : Fin p,
          (productForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl) 2
            (fibreLabels ell a b c d σ (r : ℕ) (t : ℕ))
            (fibre_good p ell hpl a b c d σ hab hc hd hv (r : ℕ) (t : ℕ)) :
            _root_.ModularForm (ΓP (p * ell)) 2)) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [map_sum]
  simp_rw [map_sum]
  simp_rw [normalizedTrace_fibre_point p ell hl hpl a b c d σ hab hc hd hv]
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_smul,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [show ((p : ℂ) ^ 2)⁻¹ * ((p * p : ℕ) : ℂ) = 1 by push_cast; field_simp, one_smul]


/-! ### Rank one: membership of the fibre sum -/

open TorsionCorrelation TorsionCorrelationRows TorsionCorrelationSigned TorsionDistributionTwo

open Classical in
/-- A lower-level degree-two product with the zero convention on bad labels. -/
def lowerProd (ell : ℕ) (hl : 0 < ell) (U V : ℤ × ℤ) : _root_.ModularForm (ΓP ell) 2 :=
  if h : Good ell U ∧ Good ell V then
    productForm ell hl 2 ![U, V] (by intro i; fin_cases i; exacts [h.1, h.2])
  else 0

theorem lowerProd_apply (ell : ℕ) (hl : 0 < ell) (U V : ℤ × ℤ) (τ : ℍ) :
    lowerProd ell hl U V τ = reg ell U.1 U.2 τ * reg ell V.1 V.2 τ := by
  unfold lowerProd
  split_ifs with h
  · rw [productForm_apply, Fin.prod_univ_two]
    have h1 : ¬ ((ell : ℤ) ∣ U.1 ∧ (ell : ℤ) ∣ U.2) := h.1
    have h2 : ¬ ((ell : ℤ) ∣ V.1 ∧ (ell : ℤ) ∣ V.2) := h.2
    rw [reg_of_good h1, reg_of_good h2]
    rfl
  · change (0 : ℂ) = _
    by_cases hU : Good ell U
    · have hV : (ell : ℤ) ∣ V.1 ∧ (ell : ℤ) ∣ V.2 := not_not.mp fun hV => h ⟨hU, hV⟩
      rw [reg_of_bad hV, mul_zero]
    · rw [reg_of_bad (not_not.mp hU), zero_mul]

theorem lowerProd_mem (ell : ℕ) (hl : 0 < ell) (U V : ℤ × ℤ) :
    lowerProd ell hl U V ∈ TorsionQuadraticGenerators.productSpan ell hl := by
  unfold lowerProd
  split_ifs with h
  · exact Submodule.subset_span ⟨_, _, rfl⟩
  · exact Submodule.zero_mem _

theorem label_zsmul (M : ℕ) (σ a b : ℤ) : σ • label M a b = label M (σ * a) (σ * b) := by
  apply Prod.ext <;> simp [label]

/-- Divided row coordinates. -/
def rowDiv (p : ℕ) (a b c d x y : ℤ) : ℤ × ℤ := ((x * a + y * c) / p, (x * b + y * d) / p)

theorem rowDiv_spec (p : ℕ) (a b c d σ x y : ℤ)
    (hc : (p : ℤ) ∣ c - σ * a) (hd : (p : ℤ) ∣ d - σ * b) (hxy : (p : ℤ) ∣ x + σ * y) :
    x * a + y * c = (p : ℤ) * (rowDiv p a b c d x y).1 ∧
      x * b + y * d = (p : ℤ) * (rowDiv p a b c d x y).2 := by
  have h1 : (p : ℤ) ∣ x * a + y * c := by
    have : x * a + y * c = (x + σ * y) * a + y * (c - σ * a) := by ring
    rw [this]; exact dvd_add (dvd_mul_of_dvd_left hxy a) (dvd_mul_of_dvd_right hc y)
  have h2 : (p : ℤ) ∣ x * b + y * d := by
    have : x * b + y * d = (x + σ * y) * b + y * (d - σ * b) := by ring
    rw [this]; exact dvd_add (dvd_mul_of_dvd_left hxy b) (dvd_mul_of_dvd_right hd y)
  exact ⟨(Int.mul_ediv_cancel' h1).symm, (Int.mul_ediv_cancel' h2).symm⟩

/-- A valid row value at level `pℓ` is a lower product value at level `ℓ`. -/
theorem rowValue_lower (p ell : ℕ) (hp : 0 < p) (hl : 0 < ell) (a b c d σ : ℤ)
    (hc : (p : ℤ) ∣ c - σ * a) (hd : (p : ℤ) ∣ d - σ * b) (R : Rows)
    (hR : ValidRowsInt p (-σ) R) (τ : ℍ) :
    rowValue (p * ell) τ (label (p * ell) a b) (label (p * ell) c d) R =
      lowerProd ell hl (rowDiv p a b c d R.a R.b) (rowDiv p a b c d R.c R.d) τ := by
  have hab : (p : ℤ) ∣ R.a + σ * R.b := by simpa using hR.2.1
  have hcd : (p : ℤ) ∣ R.c + σ * R.d := by simpa using hR.2.2
  obtain ⟨e1, e2⟩ := rowDiv_spec p a b c d σ R.a R.b hc hd hab
  obtain ⟨e3, e4⟩ := rowDiv_spec p a b c d σ R.c R.d hc hd hcd
  have hM : 0 < p * ell := Nat.mul_pos hp hl
  unfold rowValue
  rw [label_zsmul, label_zsmul, label_zsmul, label_zsmul, label_add, label_add,
    h_label hM, h_label hM, lowerProd_apply]
  rw [show R.a * a + R.b * c = (p : ℤ) * (rowDiv p a b c d R.a R.b).1 from e1,
    show R.a * b + R.b * d = (p : ℤ) * (rowDiv p a b c d R.a R.b).2 from e2,
    show R.c * a + R.d * c = (p : ℤ) * (rowDiv p a b c d R.c R.d).1 from e3,
    show R.c * b + R.d * d = (p : ℤ) * (rowDiv p a b c d R.c R.d).2 from e4,
    reg_scale p ell hp hl, reg_scale p ell hp hl]

/-- The lower combination realizing a weighted row list. -/
def rowsForm (p ell : ℕ) (hl : 0 < ell) (a b c d : ℤ) (L : List WeightedRow) :
    _root_.ModularForm (ΓP ell) 2 :=
  (L.map fun T => T.1 • lowerProd ell hl (rowDiv p a b c d T.2.a T.2.b)
    (rowDiv p a b c d T.2.c T.2.d)).sum

theorem rowsForm_mem (p ell : ℕ) (hl : 0 < ell) (a b c d : ℤ) (L : List WeightedRow) :
    rowsForm p ell hl a b c d L ∈ TorsionQuadraticGenerators.productSpan ell hl := by
  unfold rowsForm
  induction L with
  | nil => exact Submodule.zero_mem _
  | cons T L ih =>
    rw [List.map_cons, List.sum_cons]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (lowerProd_mem ell hl _ _)) ih

theorem rowsForm_apply (p ell : ℕ) (hp : 0 < p) (hl : 0 < ell) (a b c d σ : ℤ)
    (hc : (p : ℤ) ∣ c - σ * a) (hd : (p : ℤ) ∣ d - σ * b) (τ : ℍ) :
    ∀ L : List WeightedRow, (∀ T ∈ L, ValidRowsInt p (-σ) T.2) →
      rowsForm p ell hl a b c d L τ =
        rowSum (p * ell) τ (label (p * ell) a b) (label (p * ell) c d) L
  | [], _ => by
    simp only [rowsForm, rowSum, List.map_nil, List.sum_nil]
    rfl
  | T :: L, hL => by
    have ih := rowsForm_apply p ell hp hl a b c d σ hc hd τ L fun U hU => hL U (by simp [hU])
    unfold rowsForm at ih ⊢
    unfold rowSum at ih ⊢
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ← ih,
      rowValue_lower p ell hp hl a b c d σ hc hd T.2 (hL T (by simp)) τ]
    rfl

/-- The fibre-sum form at level `pℓ`. -/
def fibreSum (p ell : ℕ) [Fact p.Prime] (hl : 0 < ell) (hpl : p ∣ ell) (a b c d σ : ℤ)
    (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0)
    (hc : (p : ℤ) ∣ c - σ * a) (hd : (p : ℤ) ∣ d - σ * b)
    (hv : ∀ i, Good (p * ell) (![(a, b), (c, d)] i)) : _root_.ModularForm (ΓP (p * ell)) 2 :=
  ∑ r : Fin p, ∑ t : Fin p,
    (productForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl) 2
      (fibreLabels ell a b c d σ (r : ℕ) (t : ℕ))
      (fibre_good p ell hpl a b c d σ hab hc hd hv (r : ℕ) (t : ℕ)) :
      _root_.ModularForm (ΓP (p * ell)) 2)

/-- The fibre sum evaluates to the actual signed correlation at slope `-σ`. -/
theorem fibreSum_apply (p ell : ℕ) [Fact p.Prime] (hl : 0 < ell) (hpl : p ∣ ell)
    (a b c d σ : ℤ) (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0)
    (hc : (p : ℤ) ∣ c - σ * a) (hd : (p : ℤ) ∣ d - σ * b)
    (hv : ∀ i, Good (p * ell) (![(a, b), (c, d)] i)) (τ : ℍ) :
    fibreSum p ell hl hpl a b c d σ hab hc hd hv τ =
      CInt (p * ell) τ p (-σ) (label (p * ell) a b) (label (p * ell) c d) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hM : 0 < p * ell := Nat.mul_pos hp hl
  have hq : p * ell / p = ell := Nat.mul_div_cancel_left ell hp
  unfold fibreSum CInt
  simp only [sum_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => ?_
  rw [productForm_apply, Fin.prod_univ_two]
  have hg := fibre_good p ell hpl a b c d σ hab hc hd hv (r : ℕ) (t : ℕ)
  have g0 : ¬ (((p * ell : ℕ) : ℤ) ∣ (fibreLabels ell a b c d σ (r : ℕ) (t : ℕ) 0).1 ∧
      ((p * ell : ℕ) : ℤ) ∣ (fibreLabels ell a b c d σ (r : ℕ) (t : ℕ) 0).2) := hg 0
  have g1 : ¬ (((p * ell : ℕ) : ℤ) ∣ (fibreLabels ell a b c d σ (r : ℕ) (t : ℕ) 1).1 ∧
      ((p * ell : ℕ) : ℤ) ∣ (fibreLabels ell a b c d σ (r : ℕ) (t : ℕ) 1).2) := hg 1
  rw [← reg_of_good g0, ← reg_of_good g1, ← h_label hM, ← h_label hM]
  unfold divisionPoint
  rw [hq, label_zsmul, label_add, sub_eq_add_neg, label_neg, label_add]
  congr 2
  simp [fibreLabels]
  ring_nf

theorem divisionSpan_le_seriesSpan (K : ℕ) (hK : 0 < K) :
    DivisionSeriesMembership.divisionSpan K hK ≤ seriesSpan K hK := by
  apply Submodule.span_le.mpr
  rintro _ ⟨q, rfl⟩
  exact generator_mem_seriesSpan K hK _

/-- **Rank one, fibre sum**: the trace of the paired fibre sum lies in the lower product span. -/
theorem trace_fibreSum_mem (p ell : ℕ) [Fact p.Prime] (hl : 3 ≤ ell) (hpl : p ∣ ell)
    (a b c d σ : ℤ) (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0)
    (hc : (p : ℤ) ∣ c - σ * a) (hd : (p : ℤ) ∣ d - σ * b)
    (hv : ∀ i, Good (p * ell) (![(a, b), (c, d)] i)) :
    normalizedTrace ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
        (fibreSum p ell (by omega) hpl a b c d σ hab hc hd hv) ∈
      TorsionQuadraticGenerators.productSpan ell (by omega) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hl0 : 0 < ell := by omega
  have hM : 0 < p * ell := Nat.mul_pos hp hl0
  obtain ⟨rows, E, hE, hval, hrows, _⟩ :=
    signed_correlation_with_modular_correction p hp (p * ell) hM (dvd_mul_right p ell) (-σ)
      (label (p * ell) a b) (label (p * ell) c d)
  have hK : 0 < TorsionCorrelationModular.canonicalLevel p (p * ell) :=
    TorsionCorrelationModular.canonicalLevel_pos p hM
  have hMK : p * ell ∣ TorsionCorrelationModular.canonicalLevel p (p * ell) := dvd_mul_left _ _
  set D := fibreSum p ell hl0 hpl a b c d σ hab hc hd hv
  set G := rowsForm p ell hl0 a b c d rows
  set X : _root_.ModularForm (ΓP (p * ell)) 2 := D - restriction ell (p * ell) (dvd_mul_left ell p) G
  have hXE : restriction (p * ell) (TorsionCorrelationModular.canonicalLevel p (p * ell)) hMK X = E := by
    apply _root_.ModularForm.ext
    intro τ
    rw [restriction_apply]
    change D τ - restriction ell (p * ell) (dvd_mul_left ell p) G τ = E τ
    rw [restriction_apply, fibreSum_apply, hval τ,
      rowsForm_apply p ell hp hl0 a b c d σ hc hd τ rows hrows]
    ring
  have hEs : restriction (p * ell) (TorsionCorrelationModular.canonicalLevel p (p * ell)) hMK X ∈
      seriesSpan (TorsionCorrelationModular.canonicalLevel p (p * ell)) hK := by
    rw [hXE]; exact divisionSpan_le_seriesSpan _ hK hE
  have hInv : ∀ γ ∈ (ΓP (p * ell)),
      ⇑(restriction (p * ell) (TorsionCorrelationModular.canonicalLevel p (p * ell)) hMK X) ∣[(2 : ℤ)] γ = ⇑(restriction (p * ell) (TorsionCorrelationModular.canonicalLevel p (p * ell)) hMK X) :=
    fun γ hγ => X.slash_action_eq' γ hγ
  obtain ⟨g, hg, hge⟩ :=
    invariant_series_descent_all (TorsionCorrelationModular.canonicalLevel p (p * ell)) (p * ell) hM hK hMK (restriction (p * ell) (TorsionCorrelationModular.canonicalLevel p (p * ell)) hMK X) hEs hInv
  have hgX : g = X := restriction_injective (p * ell) _ hMK hge
  have hD : D = restriction ell (p * ell) (dvd_mul_left ell p) G + g := by
    rw [hgX]; exact (add_sub_cancel _ _).symm
  rw [hD, map_add, normalizedTrace_restriction]
  exact Submodule.add_mem _ (rowsForm_mem p ell hl0 a b c d rows)
    (trace_series_mem_productSpan hl hM (dvd_mul_left ell p) hg)

/-- **Rank one**: an upper product whose first label is nonzero modulo `p` and whose second label
is congruent modulo `p` to a multiple of it has actual trace in the lower product span. -/
theorem trace_rank_one_mem (p ell : ℕ) [Fact p.Prime] (hl : 3 ≤ ell) (hpl : p ∣ ell)
    (a b c d σ : ℤ) (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0)
    (hc : (p : ℤ) ∣ c - σ * a) (hd : (p : ℤ) ∣ d - σ * b)
    (hv : ∀ i, Good (p * ell) (![(a, b), (c, d)] i)) :
    normalizedTrace ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
        (productForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) 2
          ![(a, b), (c, d)] hv) ∈
      TorsionQuadraticGenerators.productSpan ell (by omega) := by
  rw [normalizedTrace_rank_one_average p ell (by omega) hpl a b c d σ hab hc hd hv]
  exact Submodule.smul_mem _ _ (trace_fibreSum_mem p ell hl hpl a b c d σ hab hc hd hv)

/-! ### All dependent pairs (rank at most one modulo `p`) -/

theorem exists_slope (p : ℕ) [Fact p.Prime] (a b c d : ℤ)
    (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0) (hdet : (p : ℤ) ∣ a * d - b * c) :
    ∃ σ : ℤ, (p : ℤ) ∣ c - σ * a ∧ (p : ℤ) ∣ d - σ * b := by
  have hdet' : (a : ZMod p) * d - b * c = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdet
    push_cast at h
    exact h
  rcases hab with ha | hb
  · refine ⟨(((c : ZMod p) * (a : ZMod p)⁻¹).val : ℤ), ?_, ?_⟩
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
      rw [mul_assoc, inv_mul_cancel₀ ha, mul_one, sub_self]
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
      apply mul_left_cancel₀ ha
      rw [mul_zero]
      calc (a : ZMod p) * ((d : ZMod p) - c * (a : ZMod p)⁻¹ * b) =
          a * d - c * b * (a * (a : ZMod p)⁻¹) := by ring
        _ = 0 := by rw [mul_inv_cancel₀ ha, mul_one]; linear_combination hdet'
  · refine ⟨(((d : ZMod p) * (b : ZMod p)⁻¹).val : ℤ), ?_, ?_⟩
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
      apply mul_left_cancel₀ hb
      rw [mul_zero]
      calc (b : ZMod p) * ((c : ZMod p) - d * (b : ZMod p)⁻¹ * a) =
          b * c - d * a * (b * (b : ZMod p)⁻¹) := by ring
        _ = 0 := by rw [mul_inv_cancel₀ hb, mul_one]; linear_combination -hdet'
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
      rw [mul_assoc, inv_mul_cancel₀ hb, mul_one, sub_self]

theorem productForm_swap (M : ℕ) (hM : 0 < M) (P Q : ℤ × ℤ)
    (hv : ∀ i, Good M (![P, Q] i)) (hw : ∀ i, Good M (![Q, P] i)) :
    productForm M hM 2 ![P, Q] hv = productForm M hM 2 ![Q, P] hw := by
  apply _root_.ModularForm.ext
  intro τ
  rw [productForm_apply, productForm_apply, Fin.prod_univ_two, Fin.prod_univ_two]
  exact mul_comm _ _

/-- **Every dependent pair**: if the two upper labels are linearly dependent modulo `p`
(determinant divisible by `p`), the actual trace lies in the lower product span. This covers
rank zero and rank one; only pairs independent modulo `p` remain. -/
theorem trace_dependent_mem (p ell : ℕ) [Fact p.Prime] (hl : 3 ≤ ell) (hpl : p ∣ ell)
    (a b c d : ℤ) (hdet : (p : ℤ) ∣ a * d - b * c)
    (hv : ∀ i, Good (p * ell) (![(a, b), (c, d)] i)) :
    normalizedTrace ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
        (productForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) 2
          ![(a, b), (c, d)] hv) ∈
      TorsionQuadraticGenerators.productSpan ell (by omega) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  by_cases hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0
  · obtain ⟨σ, hc, hd⟩ := exists_slope p a b c d hab hdet
    exact trace_rank_one_mem p ell hl hpl a b c d σ hab hc hd hv
  · push Not at hab
    have ha : (p : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp hab.1
    have hb : (p : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp hab.2
    by_cases hcd : (c : ZMod p) ≠ 0 ∨ (d : ZMod p) ≠ 0
    · have hw : ∀ i, Good (p * ell) (![(c, d), (a, b)] i) := by
        intro i; fin_cases i
        · exact hv 1
        · exact hv 0
      rw [productForm_swap (p * ell) _ (a, b) (c, d) hv hw]
      exact trace_rank_one_mem p ell hl hpl c d a b 0 hcd (by simpa using ha) (by simpa using hb) hw
    · push Not at hcd
      have hc : (p : ℤ) ∣ c := (ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp hcd.1
      have hd : (p : ℤ) ∣ d := (ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp hcd.2
      refine trace_rank_zero_mem p ell hp hl _ hv fun i => ?_
      fin_cases i
      · exact ⟨ha, hb⟩
      · exact ⟨hc, hd⟩

/-! ### Rank two: pairs independent modulo `p` -/

/-- One-parameter moves for an independent pair: an actual `Γ(ℓ)` element fixes `P` and moves
`Q` to `Q + γ ℓ P`, modulo `pℓ`. The coefficient matrix is exactly trace-zero. -/
theorem exists_rank_two_move (p ell : ℕ) [Fact p.Prime] (hpl : p ∣ ell) (a b c d : ℤ)
    (hΔ : ((a * d - b * c : ℤ) : ZMod p) ≠ 0) (γ : ℤ) :
    ∃ g : SL(2, ℤ), g ∈ Gamma ell ∧
      CongrN (p * ell) (act (a, b) g) (a, b) ∧
      CongrN (p * ell) (act (c, d) g) (c + ell * (γ * a), d + ell * (γ * b)) := by
  obtain ⟨e, hk⟩ : ∃ e : ℤ, (p : ℤ) ∣ e * (a * d - b * c) - 1 := by
    refine ⟨Nat.cast (R := ℤ) (((a * d - b * c : ℤ) : ZMod p)⁻¹).val, ?_⟩
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val,
      inv_mul_cancel₀ hΔ, Int.cast_one, sub_self]
  obtain ⟨k, hk⟩ := hk
  obtain ⟨g, hg, hge⟩ := exists_Gamma_lift_trace_zero p ell hpl (-(γ * e * a * b))
    (-(γ * e * b ^ 2)) (γ * e * a ^ 2)
  have hd' : ∀ i j, ((p * ell : ℕ) : ℤ) ∣
      ((!![1 + (ell : ℤ) * (-(γ * e * a * b)), (ell : ℤ) * (-(γ * e * b ^ 2));
          (ell : ℤ) * (γ * e * a ^ 2), 1 - (ell : ℤ) * (-(γ * e * a * b))] :
        Matrix (Fin 2) (Fin 2) ℤ) i j) - g i j := fun i j =>
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (hge i j)
  obtain ⟨m00, e00⟩ := hd' 0 0
  obtain ⟨m01, e01⟩ := hd' 0 1
  obtain ⟨m10, e10⟩ := hd' 1 0
  obtain ⟨m11, e11⟩ := hd' 1 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Nat.cast_mul] at e00 e01 e10 e11
  refine ⟨g, hg, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · refine ⟨-(a * m00 + b * m10), ?_⟩
    simp only [act]; push_cast
    linear_combination (-a) * e00 + (-b) * e10
  · refine ⟨-(a * m01 + b * m11), ?_⟩
    simp only [act]; push_cast
    linear_combination (-a) * e01 + (-b) * e11
  · refine ⟨γ * a * k - c * m00 - d * m10, ?_⟩
    simp only [act]; push_cast
    linear_combination (-c) * e00 + (-d) * e10 + (ell : ℤ) * γ * a * hk
  · refine ⟨γ * b * k - c * m01 - d * m11, ?_⟩
    simp only [act]; push_cast
    linear_combination (-c) * e01 + (-d) * e11 + (ell : ℤ) * γ * b * hk

/-- The moved pair of labels. -/
def lineLabels (ell : ℕ) (a b c d γ : ℤ) : Fin 2 → ℤ × ℤ :=
  ![(a, b), (c + ell * (γ * a), d + ell * (γ * b))]

theorem line_good (p ell : ℕ) [Fact p.Prime] (hpl : p ∣ ell) (a b c d : ℤ)
    (hΔ : ((a * d - b * c : ℤ) : ZMod p) ≠ 0)
    (hv : ∀ i, Good (p * ell) (![(a, b), (c, d)] i)) (γ : ℤ) :
    ∀ i, Good (p * ell) (lineLabels ell a b c d γ i) := by
  obtain ⟨g, _, h1, h2⟩ := exists_rank_two_move p ell hpl a b c d hΔ γ
  intro i
  fin_cases i
  · exact good_of_congr (good_act (hv 0) g) h1
  · exact good_of_congr (good_act (hv 1) g) h2

theorem normalizedTrace_line_point (p ell : ℕ) [Fact p.Prime] (hl : 0 < ell) (hpl : p ∣ ell)
    (a b c d : ℤ) (hΔ : ((a * d - b * c : ℤ) : ZMod p) ≠ 0)
    (hv : ∀ i, Good (p * ell) (![(a, b), (c, d)] i)) (γ : ℤ)
    (hf : ∀ i, Good (p * ell) (lineLabels ell a b c d γ i)) :
    normalizedTrace ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl)
        (productForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl) 2
          (lineLabels ell a b c d γ) hf) =
      normalizedTrace ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl)
        (productForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl) 2 ![(a, b), (c, d)] hv) := by
  have hM := Nat.mul_pos (Fact.out : p.Prime).pos hl
  have : NeZero (p * ell) := ⟨hM.ne'⟩
  obtain ⟨g, hg, h1, h2⟩ := exists_rank_two_move p ell hpl a b c d hΔ γ
  have heq : productForm (p * ell) hM 2 (lineLabels ell a b c d γ) hf =
      productForm (p * ell) hM 2 (fun i => act (![(a, b), (c, d)] i) g) (good_act_tuple hv g) := by
    refine AllLevelDiamondFromProducts.productForm_eq_of_congr 2 _ _ hf _ fun i => ?_
    fin_cases i
    · exact ⟨dvd_sub_comm.mp h1.1, dvd_sub_comm.mp h1.2⟩
    · exact ⟨dvd_sub_comm.mp h2.1, dvd_sub_comm.mp h2.2⟩
  rw [heq]
  exact normalizedTrace_product_SL ell (p * ell) hM _ hv g hg

/-- The line sum at level `pℓ`. -/
def lineSum (p ell : ℕ) [Fact p.Prime] (hl : 0 < ell) (hpl : p ∣ ell) (a b c d : ℤ)
    (hΔ : ((a * d - b * c : ℤ) : ZMod p) ≠ 0)
    (hv : ∀ i, Good (p * ell) (![(a, b), (c, d)] i)) : _root_.ModularForm (ΓP (p * ell)) 2 :=
  ∑ γ : Fin p, (productForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl) 2
    (lineLabels ell a b c d (γ : ℕ)) (line_good p ell hpl a b c d hΔ hv (γ : ℕ)) :
    _root_.ModularForm (ΓP (p * ell)) 2)

theorem normalizedTrace_rank_two_average (p ell : ℕ) [Fact p.Prime] (hl : 0 < ell)
    (hpl : p ∣ ell) (a b c d : ℤ) (hΔ : ((a * d - b * c : ℤ) : ZMod p) ≠ 0)
    (hv : ∀ i, Good (p * ell) (![(a, b), (c, d)] i)) :
    normalizedTrace ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl)
        (productForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl) 2 ![(a, b), (c, d)] hv) =
      ((p : ℂ))⁻¹ • normalizedTrace ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl)
        (lineSum p ell hl hpl a b c d hΔ hv) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  unfold lineSum
  rw [map_sum]
  simp_rw [normalizedTrace_line_point p ell hl hpl a b c d hΔ hv]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hp0, one_smul]

/-- The alternating pairing with `ℓ P` at level `pℓ` is a `p`-th root of unity. -/
theorem character_line (p ell : ℕ) [NeZero p] [NeZero ell] [NeZero (p * ell)] (a b a' b' : ℤ) :
    TorsionFourierComparison.character (p * ell) a' b' (ell * a) (ell * b) =
      Torsion.w p (b' * a - a' * b) := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hl : (ell : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne ell)
  rw [AllLevelTorsionCoefficients.w_eq_exp]
  unfold TorsionFourierComparison.character
  congr 1
  push_cast
  field_simp

theorem character_line_shift (p ell : ℕ) [NeZero (p * ell)] (a b c d a' b' : ℤ) (γ : ℕ) :
    TorsionFourierComparison.character (p * ell) a' b' (c + ell * ((γ : ℤ) * a))
        (d + ell * ((γ : ℤ) * b)) =
      TorsionFourierComparison.character (p * ell) a' b' c d *
        TorsionFourierComparison.character (p * ell) a' b' (ell * a) (ell * b) ^ γ := by
  unfold TorsionFourierComparison.character
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The line sum is a combination of products of pairs dependent modulo `p`. -/
theorem lineSum_eq (p ell : ℕ) [Fact p.Prime] (hl : 0 < ell) (hpl : p ∣ ell) (a b c d : ℤ)
    (hΔ : ((a * d - b * c : ℤ) : ZMod p) ≠ 0)
    (hv : ∀ i, Good (p * ell) (![(a, b), (c, d)] i)) :
    lineSum p ell hl hpl a b c d hΔ hv =
      ∑ a' : Fin (p * ell), ∑ b' : Fin (p * ell),
        (if (p : ℤ) ∣ ((b' : ℕ) : ℤ) * a - ((a' : ℕ) : ℤ) * b then
          (-((p : ℂ) / ((p * ell : ℕ) : ℂ)) *
            TorsionFourierComparison.character (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ) c d) •
            lowerProd (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos hl) (a, b)
              (((a' : ℕ) : ℤ), ((b' : ℕ) : ℤ))
        else 0) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hM : 0 < p * ell := Nat.mul_pos hp hl
  have : NeZero p := ⟨hp.ne'⟩
  have : NeZero ell := ⟨hl.ne'⟩
  have : NeZero (p * ell) := ⟨hM.ne'⟩
  apply _root_.ModularForm.ext
  intro τ
  unfold lineSum
  simp only [sum_apply]
  have hP : ¬ (((p * ell : ℕ) : ℤ) ∣ a ∧ ((p * ell : ℕ) : ℤ) ∣ b) := hv 0
  have hterm : ∀ γ : Fin p, productForm (p * ell) hM 2 (lineLabels ell a b c d (γ : ℕ))
      (line_good p ell hpl a b c d hΔ hv (γ : ℕ)) τ =
      reg (p * ell) a b τ * (-(1 / ((p * ell : ℕ) : ℂ)) * ∑ a' : Fin (p * ell), ∑ b' : Fin (p * ell),
        reg (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ) τ *
          (TorsionFourierComparison.character (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ) c d *
            Torsion.w p (((b' : ℕ) : ℤ) * a - ((a' : ℕ) : ℤ) * b) ^ (γ : ℕ))) := by
    intro γ
    have hg := line_good p ell hpl a b c d hΔ hv (γ : ℕ)
    have g0 : ¬ (((p * ell : ℕ) : ℤ) ∣ (lineLabels ell a b c d (γ : ℕ) 0).1 ∧
        ((p * ell : ℕ) : ℤ) ∣ (lineLabels ell a b c d (γ : ℕ) 0).2) := hg 0
    have g1 : ¬ (((p * ell : ℕ) : ℤ) ∣ (lineLabels ell a b c d (γ : ℕ) 1).1 ∧
        ((p * ell : ℕ) : ℤ) ∣ (lineLabels ell a b c d (γ : ℕ) 1).2) := hg 1
    rw [productForm_apply, Fin.prod_univ_two, ← reg_of_good g0, ← reg_of_good g1]
    refine congrArg₂ (· * ·) rfl ?_
    rw [TorsionFourierComparison.torsion_fourier_duality (p * ell) τ]
    congr 1
    refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => ?_
    congr 1
    change TorsionFourierComparison.character (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ)
      (c + ell * (((γ : ℕ) : ℤ) * a)) (d + ell * (((γ : ℕ) : ℤ) * b)) = _
    rw [character_line_shift, character_line]
  simp_rw [hterm]
  have hgeom : ∀ a' b' : Fin (p * ell), (∑ γ : Fin p,
      Torsion.w p (((b' : ℕ) : ℤ) * a - ((a' : ℕ) : ℤ) * b) ^ (γ : ℕ)) =
      if (p : ℤ) ∣ ((b' : ℕ) : ℤ) * a - ((a' : ℕ) : ℤ) * b then (p : ℂ) else 0 := by
    intro a' b'
    rw [TorsionFourierComparison.finite_geometric p _ (TorsionFourierComparison.w_pow_level p _)]
    simp only [AllLevelTorsionCoefficients.w_eq_one_iff p]
  calc ∑ γ : Fin p, reg (p * ell) a b τ * (-(1 / ((p * ell : ℕ) : ℂ)) *
        ∑ a' : Fin (p * ell), ∑ b' : Fin (p * ell),
          reg (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ) τ *
            (TorsionFourierComparison.character (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ) c d *
              Torsion.w p (((b' : ℕ) : ℤ) * a - ((a' : ℕ) : ℤ) * b) ^ (γ : ℕ)))
      = ∑ a' : Fin (p * ell), ∑ b' : Fin (p * ell), ∑ γ : Fin p,
          reg (p * ell) a b τ * (-(1 / ((p * ell : ℕ) : ℂ)) *
            (reg (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ) τ *
              (TorsionFourierComparison.character (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ) c d *
                Torsion.w p (((b' : ℕ) : ℤ) * a - ((a' : ℕ) : ℤ) * b) ^ (γ : ℕ)))) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.sum_comm]
    _ = _ := by
        refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => ?_
        rw [show (∑ γ : Fin p, reg (p * ell) a b τ * (-(1 / ((p * ell : ℕ) : ℂ)) *
            (reg (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ) τ *
              (TorsionFourierComparison.character (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ) c d *
                Torsion.w p (((b' : ℕ) : ℤ) * a - ((a' : ℕ) : ℤ) * b) ^ (γ : ℕ))))) =
            reg (p * ell) a b τ * (-(1 / ((p * ell : ℕ) : ℂ)) *
              (reg (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ) τ *
                (TorsionFourierComparison.character (p * ell) ((a' : ℕ) : ℤ) ((b' : ℕ) : ℤ) c d *
                  ∑ γ : Fin p, Torsion.w p (((b' : ℕ) : ℤ) * a - ((a' : ℕ) : ℤ) * b) ^ (γ : ℕ))))
            by simp_rw [Finset.mul_sum], hgeom]
        split_ifs with hdiv
        · rw [smul_apply, smul_eq_mul, lowerProd_apply]
          ring
        · simp only [mul_zero]
          rfl

/-- **Rank two**: an upper product whose labels are independent modulo `p` has actual trace in
the lower product span. -/
theorem trace_rank_two_mem (p ell : ℕ) [Fact p.Prime] (hl : 3 ≤ ell) (hpl : p ∣ ell)
    (a b c d : ℤ) (hΔ : ((a * d - b * c : ℤ) : ZMod p) ≠ 0)
    (hv : ∀ i, Good (p * ell) (![(a, b), (c, d)] i)) :
    normalizedTrace ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
        (productForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) 2
          ![(a, b), (c, d)] hv) ∈
      TorsionQuadraticGenerators.productSpan ell (by omega) := by
  have hl0 : 0 < ell := by omega
  rw [normalizedTrace_rank_two_average p ell hl0 hpl a b c d hΔ hv, lineSum_eq, map_sum]
  apply Submodule.smul_mem
  refine Submodule.sum_mem _ fun a' _ => ?_
  rw [map_sum]
  refine Submodule.sum_mem _ fun b' _ => ?_
  split_ifs with hdiv
  · rw [map_smul]
    apply Submodule.smul_mem
    unfold lowerProd
    split_ifs with hg
    · have hdet : (p : ℤ) ∣ a * ((b' : ℕ) : ℤ) - b * ((a' : ℕ) : ℤ) := by
        have : a * ((b' : ℕ) : ℤ) - b * ((a' : ℕ) : ℤ) =
            ((b' : ℕ) : ℤ) * a - ((a' : ℕ) : ℤ) * b := by ring
        rw [this]; exact hdiv
      exact trace_dependent_mem p ell hl hpl a b _ _ hdet _
    · rw [map_zero]; exact Submodule.zero_mem _
  · rw [map_zero]; exact Submodule.zero_mem _

/-- **Repeated-prime product trace closure**: for `p` prime, `ℓ ≥ 3`, `p ∣ ℓ`, the actual
normalized trace from `Γ(pℓ)` to `Γ(ℓ)` of every admissible degree-two principal product lies in
the degree-two product span at level `ℓ`. -/
theorem trace_product_mem (p ell : ℕ) [Fact p.Prime] (hl : 3 ≤ ell) (hpl : p ∣ ell)
    (a b c d : ℤ) (hv : ∀ i, Good (p * ell) (![(a, b), (c, d)] i)) :
    normalizedTrace ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
        (productForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) 2
          ![(a, b), (c, d)] hv) ∈
      TorsionQuadraticGenerators.productSpan ell (by omega) := by
  by_cases hΔ : ((a * d - b * c : ℤ) : ZMod p) = 0
  · exact trace_dependent_mem p ell hl hpl a b c d
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hΔ) hv
  · exact trace_rank_two_mem p ell hl hpl a b c d hΔ hv

/-- The same closure for an arbitrary admissible pair of labels. -/
theorem trace_product_mem' (p ell : ℕ) [Fact p.Prime] (hl : 3 ≤ ell) (hpl : p ∣ ell)
    (v : Fin 2 → ℤ × ℤ) (hv : ∀ i, Good (p * ell) (v i)) :
    normalizedTrace ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
        (productForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) 2 v hv) ∈
      TorsionQuadraticGenerators.productSpan ell (by omega) := by
  have hvv : v = ![((v 0).1, (v 0).2), ((v 1).1, (v 1).2)] := by
    ext i <;> fin_cases i <;> rfl
  have hw : ∀ i, Good (p * ell) (![((v 0).1, (v 0).2), ((v 1).1, (v 1).2)] i) := by
    rw [← hvv]; exact hv
  have : NeZero (p * ell) := ⟨(Nat.mul_pos (Fact.out : p.Prime).pos (by omega)).ne'⟩
  have heq := AllLevelDiamondFromProducts.productForm_eq_of_congr (N := p * ell) 2 v _ hv hw
    fun i => by rw [← hvv]; exact ⟨by simp, by simp⟩
  rw [heq]
  exact trace_product_mem p ell hl hpl _ _ _ _ hw

end ZInQ.Contrib.HeckePrimeRationality.RepeatedPrimeProductTrace
