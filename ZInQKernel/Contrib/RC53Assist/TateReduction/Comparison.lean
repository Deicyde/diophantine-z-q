import ZInQKernel.Contrib.CloudB3RC53.ModularWeil.FrobeniusTrace
import ZInQKernel.Contrib.CloudB3RC53.ModularWeil.ReductionInjective
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapEquiv

/-!
# Theorem 5.3, ModularWeil: the reduction comparison of Tate modules (R)

`ModularWeil/FrobeniusTrace.lean` reduces the Frobenius trace dictionary at good reduction,
`GoodReductionFrobeniusTraceDictionaryQ`, to two classical inputs: the reduction comparison of
Tate modules (R) `TateReductionComparison` and the determinant-degree compatibility (D)
`DetEqDegree` (`goodReductionFrobeniusTraceDictionaryQ_of_RD`). This file proves (R) exactly as
stated there, with no further input (`tateReductionComparison`). Hence the dictionary follows from
(D) alone (`goodReductionFrobeniusTraceDictionaryQ_of_detEqDegree`).

## The argument

The classical source is Silverman, *The Arithmetic of Elliptic Curves*, VII.1–VII.3 (minimal
models, reduction, injectivity of reduction on prime-to-`p` torsion) and VII.7 (Galois
compatibility of reduction, as in the proof of VII.7.1). Let `E/ℚ` have good reduction at `p`, let
`ℓ ≠ p`, let `w` be a valuation of `\bar ℚ_p` whose restriction to `ℚ_p` is equivalent to the
`p`-adic valuation, with valuation ring `A` and residue field `k_A`, and let `σ` be an arithmetic
Frobenius: `w(σ x − x^p) < 1` whenever `w x ≤ 1`.

1. *Integral model.* `A` lies over `ℤ_p` (`algebraMap_mem_valuationSubring_iff`), so the minimal
   model of `E` over `ℤ_p` (Mathlib's `WeierstrassCurve.minimal`, obtained from `E` by the change of
   variables `minimalChange` over `ℚ_p`) gives an integral model `integralModelA` over `A`. Its
   generic fibre is the minimal model over `\bar ℚ_p` (`integralModelA_map_subtype`), its special
   fibre is `reducedCurveModP E p` base changed to `k_A` (`integralModelA_map_residue`), and it has
   good reduction (`integralModelA_Δ_ne_zero`).
2. *Residue field.* `k_A` is algebraically closed (`isAlgClosed_residueField`: a monic polynomial
   over `k_A` lifts to a monic polynomial over `A`, whose roots in `\bar ℚ_p` are integral over
   `A`, hence lie in `A`) and algebraic over `𝔽_p` (`exists_residue_polynomial`: a polynomial over
   `ℚ_p` vanishing at a lift, divided by its coefficient of largest valuation, has integral
   coefficients, one of them `1`, and reduces to a nonzero polynomial vanishing at the residue).
   So `k_A` is an algebraic closure of `𝔽_p` (`isAlgClosure_residueField`) and `k_A ≅ \bar 𝔽_p`
   (`residueEquiv`).
3. *Reduction of points.* `reductionPointHom` is the composite of the change of variables to the
   minimal model (`WeierstrassCurve.pointEquivVariableChange`), the reduction homomorphism
   `reduceHom` of the integral model, and the transport of points along `k_A ≅ \bar 𝔽_p`. It is a
   bijection on `N`-torsion for every `N` prime to `p` (`reductionPointHom_bijOn`, from
   `reduceHom_bijOn_torsion` of `ModularWeil/ReductionInjective.lean`), hence induces a
   `ℤ_ℓ`-linear isomorphism of Tate modules (`tateLinearEquivOfBijOn`, `map_bijective_of_bijOn`).
4. *Frobenius.* The congruence for `σ` forces `σ` into the decomposition group of `A`
   (`mem_decompositionSubgroup_of_frobenius`) and makes it act on `k_A` as `z ↦ z^p`
   (`smul_residue_eq_pow`). The change of variables is defined over `ℚ_p`, so it commutes with `σ`;
   integral points reduce coordinatewise and non-integral points to infinity; and `k_A ≅ \bar 𝔽_p`
   commutes with `p`-th powers. So reduction carries `σ` to the `p`-power Frobenius
   `FiniteField.frobeniusAlgHom` (`reductionPointHom_frobenius`), and on Tate modules
   `e ∘ ρ(σ) = frobTate ∘ e`.

Only the hypotheses of `TateReductionComparison` are used. In particular neither the uniqueness
of the extension of the `p`-adic valuation to `\bar ℚ_p` nor the spectral norm is needed: that `σ`
preserves the valuation ring of `w` follows from the Frobenius congruence itself, and the residue
field of any such `w` is an algebraic closure of `𝔽_p`.

## Classification

Definitions and PROVED; no prints. Infrastructure: Mathlib (minimal Weierstrass models, residue
fields, algebraic closures, decomposition groups), the vendored TauCeti library (Tate modules and
their Galois representation, points under a change of variables, transport of points along an
algebra equivalence), and the vendored reduction library used in
`ModularWeil/ReductionInjective.lean` (`reduceHom`, `reducePoint`, `reduceHom_bijOn_torsion`; see
that file for its provenance).
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.TateReduction

open IsLocalRing Polynomial

section TateMap

open TauCeti

variable {ℓ : ℕ} {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- **A bijection on `ℓⁿ`-torsion is a bijective level map** (PROVED; step 3 of the module
documentation). -/
theorem levelMap_bijective_of_bijOn (f : A →+ B) (n : ℕ)
    (hf : Set.BijOn f {a : A | (ℓ ^ n) • a = 0} {b : B | (ℓ ^ n) • b = 0}) :
    Function.Bijective (TateModule.levelMap (p := ℓ) f n) := by
  refine ⟨fun x y hxy => Subtype.ext ?_, fun y => ?_⟩
  · refine hf.injOn (AddSubgroup.torsionBy.nsmul_iff.mp x.2)
      (AddSubgroup.torsionBy.nsmul_iff.mp y.2) ?_
    have h := congrArg Subtype.val hxy
    rwa [TateModule.levelMap_apply, TateModule.levelMap_apply] at h
  · obtain ⟨a, ha, hfa⟩ := hf.surjOn (AddSubgroup.torsionBy.nsmul_iff.mp y.2)
    exact ⟨⟨a, AddSubgroup.torsionBy.nsmul_iff.mpr ha⟩, Subtype.ext hfa⟩

/-- **Bijective level maps give a bijective map of Tate modules** (PROVED). Injectivity is checked
level by level. For surjectivity, a compatible family `(yₙ)` is lifted to the family of unique
preimages `(xₙ)`, which is compatible because `ℓ xₙ₊₁` and `xₙ` have the same image `yₙ` in the
`n`-th level, where the level map is injective. -/
theorem map_bijective_of_levelMap_bijective (f : A →+ B)
    (hf : ∀ n, Function.Bijective (TateModule.levelMap (p := ℓ) f n)) :
    Function.Bijective (TateModule.map (p := ℓ) f) := by
  refine ⟨fun x y hxy => TateModule.ext fun n => (hf n).1 ?_, fun y => ?_⟩
  · rw [← TateModule.proj_map, ← TateModule.proj_map, hxy]
  · choose g hg using fun n => (hf n).2 (TateModule.proj n y)
    refine ⟨TateModule.mk g fun n => (hf n).1 ?_, TateModule.ext fun n => ?_⟩
    · rw [hg n, ← TateModule.proj_succ y n, ← hg (n + 1)]
      apply Subtype.ext
      simp only [TateModule.levelMap_apply, tateModuleTransition_apply, map_nsmul]
    · rw [TateModule.proj_map, TateModule.proj_mk, hg n]

/-- **A bijection on every `ℓⁿ`-torsion subgroup gives a bijective map of Tate modules**
(PROVED; step 3). -/
theorem map_bijective_of_bijOn (f : A →+ B)
    (hf : ∀ n, Set.BijOn f {a : A | (ℓ ^ n) • a = 0} {b : B | (ℓ ^ n) • b = 0}) :
    Function.Bijective (TateModule.map (p := ℓ) f) :=
  map_bijective_of_levelMap_bijective f fun n => levelMap_bijective_of_bijOn f n (hf n)

/-- **A bijective additive map is a bijection on `N`-torsion** (PROVED; step 3). -/
theorem bijOn_torsion_of_bijective (f : A →+ B) (hf : Function.Bijective f) (N : ℕ) :
    Set.BijOn f {a : A | N • a = 0} {b : B | N • b = 0} := by
  refine ⟨fun a ha => ?_, hf.1.injOn, fun b hb => ?_⟩
  · change N • f a = 0
    rw [← map_nsmul, show N • a = 0 from ha, map_zero]
  · obtain ⟨a, rfl⟩ := hf.2 b
    refine ⟨a, hf.1 ?_, rfl⟩
    rw [map_nsmul, map_zero]
    exact hb

/-- **The `ℤ_ℓ`-linear isomorphism of Tate modules** induced by an additive map that is a bijection
on every `ℓⁿ`-torsion subgroup (definition; step 3, Silverman III.7 for Tate modules). -/
def tateLinearEquivOfBijOn [Fact ℓ.Prime] (f : A →+ B)
    (hf : ∀ n, Set.BijOn f {a : A | (ℓ ^ n) • a = 0} {b : B | (ℓ ^ n) • b = 0}) :
    TateModule ℓ A ≃ₗ[ℤ_[ℓ]] TateModule ℓ B :=
  LinearEquiv.ofBijective (TateModule.mapLinearMap f) (map_bijective_of_bijOn f hf)

/-- The isomorphism `tateLinearEquivOfBijOn` is the induced map of Tate modules (PROVED, by
definition). -/
theorem tateLinearEquivOfBijOn_apply [Fact ℓ.Prime] (f : A →+ B)
    (hf : ∀ n, Set.BijOn f {a : A | (ℓ ^ n) • a = 0} {b : B | (ℓ ^ n) • b = 0})
    (x : TateModule ℓ A) :
    tateLinearEquivOfBijOn f hf x = TateModule.map f x :=
  rfl

end TateMap

section ResidueField

/-- **The residue field of a valuation subring of an algebraically closed field is algebraically
closed** (PROVED; step 2). A monic polynomial over the residue field lifts to a monic polynomial
over the valuation ring; a root in the algebraically closed field is integral over the valuation
ring, hence lies in it, and its residue is a root of the given polynomial. -/
theorem isAlgClosed_residueField {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) :
    IsAlgClosed (ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ fun f hfm hfi => ?_
  obtain ⟨g, hgf, hgdeg, hgm⟩ := lifts_and_natDegree_eq_and_monic
    ((mem_lifts f).mpr (map_surjective (residue A) residue_surjective f)) hfm
  have hdeg : (g.map (algebraMap A L)).degree ≠ 0 := by
    rw [degree_eq_natDegree (hgm.map _).ne_zero, hgm.natDegree_map, hgdeg]
    exact_mod_cast hfi.natDegree_pos.ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hdeg
  have hint : IsIntegral A α := ⟨g, hgm, by rwa [IsRoot, eval_map] at hα⟩
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨residue A a, ?_⟩
  have h0 : algebraMap A L (g.eval a) = 0 := by
    rw [← eval₂_at_apply]
    rwa [IsRoot, eval_map] at hα
  have h1 : g.eval a = 0 := (IsFractionRing.injective A L) (by rw [h0, map_zero])
  rw [← hgf, eval_map, eval₂_at_apply, h1, map_zero]

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {O : ValuationSubring K}
  {A : ValuationSubring L} (hOA : ∀ a : K, algebraMap K L a ∈ A ↔ a ∈ O)

include hOA in
/-- **Nonunits correspond** for a valuation subring `A` of `L` lying over a valuation subring `O`
of `K` (PROVED; step 2): `x ∈ O` is a nonunit of `O` iff its image is a nonunit of `A`. -/
theorem algebraMap_mem_nonunits_iff (x : K) : algebraMap K L x ∈ A.nonunits ↔ x ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ← map_inv₀,
    hOA, map_eq_zero]

/-- **The inclusion of valuation rings** `O → A` for a valuation subring `A` lying over `O`
(definition; step 1). -/
def integerHom : O →+* A :=
  ((algebraMap K L).comp O.subtype).codRestrict A fun r => (hOA r).mpr r.2

/-- The inclusion of valuation rings is the field embedding on elements (PROVED, by
definition). -/
theorem coe_integerHom (r : O) : (integerHom hOA r : L) = algebraMap K L r :=
  rfl

/-- **The inclusion of valuation rings is local** (PROVED; step 2), by
`algebraMap_mem_nonunits_iff`. -/
theorem isLocalHom_integerHom : IsLocalHom (integerHom hOA) := by
  refine ((local_hom_TFAE (integerHom hOA)).out 4 1).mp fun r hr => ?_
  rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff, coe_integerHom,
    algebraMap_mem_nonunits_iff hOA]
  exact ValuationSubring.coe_mem_nonunits_iff.mpr hr

/-- **The induced map of residue fields** `k_O → k_A` (definition; step 2). -/
def residueHom : ResidueField O →+* ResidueField A :=
  haveI := isLocalHom_integerHom hOA
  ResidueField.map (integerHom hOA)

/-- The induced map of residue fields on residues (PROVED). -/
theorem residueHom_residue (r : O) :
    residueHom hOA (residue O r) = residue A (integerHom hOA r) := by
  have := isLocalHom_integerHom hOA
  exact ResidueField.map_residue _ r

/-- The induced map of residue fields after reduction is reduction after inclusion (PROVED). -/
theorem residueHom_comp_residue :
    (residueHom hOA).comp (residue O) = (residue A).comp (integerHom hOA) :=
  RingHom.ext fun r => residueHom_residue hOA r

include hOA in
/-- **Residues over an algebraic extension are algebraic** (PROVED; step 2): if `L` is algebraic
over `K`, every residue of `A` is a root of a nonzero polynomial over the residue field of `O`. A
polynomial over `K` vanishing at a lift is divided by its coefficient of largest valuation; the
quotient has coefficients in `O`, one of them equal to `1`, so its reduction is nonzero, and the
reduction vanishes at the residue. -/
theorem exists_residue_polynomial [Algebra.IsAlgebraic K L] (x : A) :
    ∃ q : Polynomial (ResidueField O), q ≠ 0 ∧
      q.eval₂ (residueHom hOA) (residue A x) = 0 := by
  obtain ⟨f, hf0, hfx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := K) (x : L)
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image f.support (fun i => O.valuation (f.coeff i))
    (support_nonempty.mpr hf0)
  have hc : f.coeff i₀ ≠ 0 := mem_support_iff.mp hi₀
  have hcoeff : ∀ i, (f.coeff i₀)⁻¹ * f.coeff i ∈ O := by
    intro i
    rw [← O.valuation_le_one_iff]
    by_cases hi : f.coeff i = 0
    · rw [hi, mul_zero, map_zero]
      exact zero_le
    · rw [map_mul, map_inv₀]
      exact inv_mul_le_one_of_le₀ (hmax i (mem_support_iff.mpr hi)) zero_le
  obtain ⟨g, hg⟩ : ∃ g : Polynomial O, g.map (algebraMap O K) = C (f.coeff i₀)⁻¹ * f := by
    rw [← mem_lifts, lifts_iff_coeff_lifts]
    intro n
    rw [coeff_C_mul]
    exact ⟨⟨_, hcoeff n⟩, rfl⟩
  have hg1 : g.coeff i₀ = 1 := by
    apply Subtype.ext
    have h := congrArg (fun q => q.coeff i₀) hg
    simp only [coeff_map, coeff_C_mul, inv_mul_cancel₀ hc] at h
    exact h
  refine ⟨g.map (residue O), fun h => ?_, ?_⟩
  · have h' := congrArg (fun q => q.coeff i₀) h
    simp only [coeff_map, hg1, map_one, coeff_zero] at h'
    exact one_ne_zero h'
  · have hev : g.eval₂ (integerHom hOA) x = 0 := by
      apply Subtype.ext
      have h1 := hom_eval₂ g (integerHom hOA) A.subtype x
      have h2 : A.subtype.comp (integerHom hOA) = (algebraMap K L).comp (algebraMap O K) :=
        RingHom.ext fun r => rfl
      rw [h2, ← eval₂_map, hg] at h1
      change A.subtype (g.eval₂ (integerHom hOA) x) = 0
      rw [h1]
      simpa [eval₂_mul, aeval_def] using Or.inr hfx
    rw [eval₂_map, residueHom_comp_residue, ← hom_eval₂, hev, map_zero]

end ResidueField

section Frobenius

open scoped Pointwise

variable {K L Γ : Type*} [Field K] [Field L] [Algebra K L] [LinearOrderedCommGroupWithZero Γ]

/-- **The maximal ideal of the valuation ring of `w`** is `{w < 1}` (PROVED; step 4). -/
theorem mem_maximalIdeal_valuationSubring_iff (w : Valuation L Γ) (a : w.valuationSubring) :
    a ∈ maximalIdeal w.valuationSubring ↔ w a < 1 := by
  rw [← ValuationSubring.coe_mem_nonunits_iff, ValuationSubring.mem_nonunits_iff]
  exact (Valuation.isEquiv_valuation_valuationSubring w).lt_one_iff_lt_one.symm

/-- **A Frobenius congruence forces the decomposition group** (PROVED; step 4): if
`w(σ x − x^q) < 1` for every `x` with `w x ≤ 1`, and `q ≥ 1`, then `σ` preserves the valuation
ring of `w`. Integral elements stay integral, and so do elements of the maximal ideal; applying the
latter to `x⁻¹` shows that non-integral elements stay non-integral. -/
theorem mem_decompositionSubgroup_of_frobenius (w : Valuation L Γ) (σ : L ≃ₐ[K] L) {q : ℕ}
    (hq : q ≠ 0) (hσ : ∀ x, w x ≤ 1 → w (σ x - x ^ q) < 1) :
    σ ∈ w.valuationSubring.decompositionSubgroup K := by
  have h1 : ∀ x, w x ≤ 1 → w (σ x) ≤ 1 := fun x hx => by
    rw [show σ x = (σ x - x ^ q) + x ^ q by ring]
    exact w.map_add_le (hσ x hx).le (by rw [map_pow]; exact pow_le_one' hx q)
  have h2 : ∀ x, w x < 1 → w (σ x) < 1 := fun x hx => by
    rw [show σ x = (σ x - x ^ q) + x ^ q by ring]
    exact w.map_add_lt (hσ x hx.le) (by rw [map_pow]; exact pow_lt_one₀ zero_le hx hq)
  have h3 : ∀ x, 1 < w x → 1 < w (σ x) := fun x hx => by
    have hx0 : x ≠ 0 := fun h => by rw [h, map_zero] at hx; exact not_lt.mpr zero_le hx
    have hσx0 : σ x ≠ 0 := (map_ne_zero σ).mpr hx0
    rw [w.one_lt_val_iff hσx0, ← map_inv₀]
    exact h2 _ ((w.one_lt_val_iff hx0).mp hx)
  rw [MulAction.mem_stabilizer_iff]
  ext z
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, Valuation.mem_valuationSubring_iff,
    Valuation.mem_valuationSubring_iff, AlgEquiv.smul_def, AlgEquiv.aut_inv]
  constructor
  · intro hz
    have h := h1 _ hz
    rwa [AlgEquiv.apply_symm_apply] at h
  · intro hz
    by_contra hn
    have h := h3 _ (not_le.mp hn)
    rw [AlgEquiv.apply_symm_apply] at h
    exact not_lt.mpr hz h

/-- **A Frobenius congruence acts as the `q`-power map on the residue field** (PROVED; step 4):
the induced automorphism `σ̄` of the residue field is `z ↦ z^q`. -/
theorem smul_residue_eq_pow (w : Valuation L Γ) (σ : L ≃ₐ[K] L) {q : ℕ}
    (hσ : ∀ x, w x ≤ 1 → w (σ x - x ^ q) < 1)
    (hdec : σ ∈ w.valuationSubring.decompositionSubgroup K) (z : ResidueField w.valuationSubring) :
    (⟨σ, hdec⟩ : w.valuationSubring.decompositionSubgroup K) • z = z ^ q := by
  obtain ⟨a, rfl⟩ := residue_surjective z
  change residue _ ((⟨σ, hdec⟩ : w.valuationSubring.decompositionSubgroup K) • a) = _
  rw [← map_pow]
  refine Ideal.Quotient.eq.mpr ((mem_maximalIdeal_valuationSubring_iff w _).mpr ?_)
  exact hσ a a.2

end Frobenius

section Comparison

open IsDedekindDomain NewformPeriodsDictionary WeierstrassCurve
open scoped WithZero Classical

variable (E : WeierstrassCurve ℚ) (p : ℕ) (hp : p.Prime) {Γ : Type}
  [LinearOrderedCommGroupWithZero Γ]
  (w : Valuation (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) Γ)
  (hw : (w.comap (algebraMap ((primeIdealQ p hp).adicCompletion ℚ)
    (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)))).IsEquiv
    (Valued.v : Valuation ((primeIdealQ p hp).adicCompletion ℚ) ℤᵐ⁰))

include hw in
/-- **The valuation ring of `w` lies over `ℤ_p`** (PROVED; step 1): this is the hypothesis that
`w` restricted to `ℚ_p` is equivalent to the `p`-adic valuation. -/
theorem algebraMap_mem_valuationSubring_iff (a : (primeIdealQ p hp).adicCompletion ℚ) :
    algebraMap _ (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) a ∈
        w.valuationSubring ↔ a ∈ (primeIdealQ p hp).adicCompletionIntegers ℚ :=
  hw.le_one_iff_le_one

/-- **The prime field inside the residue field of `w`** (definition; step 2): `𝔽_p ≅ k_{ℤ_p}`
followed by the induced map of residue fields. -/
def primeFieldHom [Fact p.Prime] : ZMod p →+* ResidueField w.valuationSubring :=
  (residueHom (algebraMap_mem_valuationSubring_iff p hp w hw)).comp
    (residueFieldEquivZModQ p hp).symm.toRingHom

/-- Any `𝔽_p`-algebra structure on the residue field of `w` is compatible with the residue map
of `ℤ_p` (PROVED; ring homomorphisms out of `𝔽_p` are unique). -/
theorem algebraMap_zmod_comp_residueFieldEquiv [Fact p.Prime]
    [Algebra (ZMod p) (ResidueField w.valuationSubring)] :
    (algebraMap (ZMod p) (ResidueField w.valuationSubring)).comp
        (residueFieldEquivZModQ p hp).toRingHom =
      residueHom (algebraMap_mem_valuationSubring_iff p hp w hw) := by
  rw [RingHom.ext_zmod (algebraMap (ZMod p) _) (primeFieldHom p hp w hw)]
  ext x
  simp [primeFieldHom]

include hw in
/-- **The residue field of `w` is an algebraic closure of `𝔽_p`** (PROVED; step 2), by
`isAlgClosed_residueField` and `exists_residue_polynomial`. -/
theorem isAlgClosure_residueField [Fact p.Prime]
    [Algebra (ZMod p) (ResidueField w.valuationSubring)] :
    IsAlgClosure (ZMod p) (ResidueField w.valuationSubring) := by
  refine IsAlgClosure.mk (isAlgClosed_residueField _) ⟨fun z => ?_⟩
  obtain ⟨x, rfl⟩ := residue_surjective z
  obtain ⟨q, hq0, hq⟩ := exists_residue_polynomial (algebraMap_mem_valuationSubring_iff p hp w hw) x
  refine ⟨q.map (residueFieldEquivZModQ p hp).toRingHom,
    (Polynomial.map_ne_zero_iff (residueFieldEquivZModQ p hp).injective).mpr hq0, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map,
    algebraMap_zmod_comp_residueFieldEquiv p hp w hw]
  exact hq

/-- **An identification of the residue field of `w` with `\bar 𝔽_p`** (definition; step 2): the
uniqueness of algebraic closures. -/
def residueEquiv [Fact p.Prime] [Algebra (ZMod p) (ResidueField w.valuationSubring)] :
    ResidueField w.valuationSubring ≃ₐ[ZMod p] AlgebraicClosure (ZMod p) :=
  haveI := isAlgClosure_residueField p hp w hw
  IsAlgClosure.equiv (ZMod p) _ _

/-- **The change of variables from `E` over `ℚ_p` to its minimal model** (definition; step 1,
Silverman VII.1): the one chosen by Mathlib's `WeierstrassCurve.minimal`, so that
`minimalChange E p hp • E = (E/ℚ_p).minimal ℤ_p` by definition. -/
def minimalChange : VariableChange ((primeIdealQ p hp).adicCompletion ℚ) :=
  ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).exists_isMinimal
    ((primeIdealQ p hp).adicCompletionIntegers ℚ)).choose

/-- **The integral model of `E` over the valuation ring of `w`** (definition; step 1): the
minimal model over `ℤ_p`, with coefficients moved along `ℤ_p → A`. -/
def integralModelA : WeierstrassCurve w.valuationSubring :=
  (integralModel ((primeIdealQ p hp).adicCompletionIntegers ℚ)
    ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).minimal
      ((primeIdealQ p hp).adicCompletionIntegers ℚ))).map
    (integerHom (algebraMap_mem_valuationSubring_iff p hp w hw))

/-- **The generic fibre of the integral model** is the minimal model of `E` over `\bar ℚ_p`
(PROVED; step 1). -/
theorem integralModelA_map_subtype :
    (integralModelA E p hp w hw).map w.valuationSubring.subtype =
      (minimalChange E p hp • E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).baseChange
        (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) := by
  rw [integralModelA, WeierstrassCurve.map_map]
  have h : w.valuationSubring.subtype.comp
      (integerHom (algebraMap_mem_valuationSubring_iff p hp w hw)) =
      (algebraMap ((primeIdealQ p hp).adicCompletion ℚ)
        (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))).comp
        (algebraMap ((primeIdealQ p hp).adicCompletionIntegers ℚ)
          ((primeIdealQ p hp).adicCompletion ℚ)) :=
    RingHom.ext fun r => rfl
  rw [h, ← WeierstrassCurve.map_map]
  change ((integralModel _ _).baseChange _).baseChange _ = _
  rw [baseChange_integralModel_eq]
  rfl

/-- **The special fibre of the integral model** is `reducedCurveModP E p`, base changed to the
residue field of `w` (PROVED; step 1): both are the minimal model over `ℤ_p` with coefficients
reduced to `k_A`, through the residue maps `ℤ_p → k_{ℤ_p} → k_A`. -/
theorem integralModelA_map_residue [Fact p.Prime]
    [Algebra (ZMod p) (ResidueField w.valuationSubring)] :
    (integralModelA E p hp w hw).map (residue w.valuationSubring) =
      (reducedCurveModP E p hp).baseChange (ResidueField w.valuationSubring) := by
  rw [integralModelA, WeierstrassCurve.map_map, ← residueHom_comp_residue,
    ← algebraMap_zmod_comp_residueFieldEquiv p hp w hw]
  rfl

/-- **The integral model has good reduction** (PROVED; step 1): its special fibre is the
elliptic curve `reducedCurveModP E p` over `k_A`. -/
theorem integralModelA_Δ_ne_zero [Fact p.Prime]
    [Algebra (ZMod p) (ResidueField w.valuationSubring)]
    (hgood : GoodReductionAt E (primeIdealQ p hp)) :
    ((integralModelA E p hp w hw).map (residue w.valuationSubring)).Δ ≠ 0 := by
  rw [integralModelA_map_residue]
  have := reducedCurveModP_isElliptic E p hp hgood
  exact ((reducedCurveModP E p hp).baseChange _).isUnit_Δ.ne_zero

/-- **Reduction of points** (definition; step 3, Silverman VII.2): from `E(\bar ℚ_p)` to the
points of `reducedCurveModP E p` over `\bar 𝔽_p`, through the minimal model, its integral model
over the valuation ring of `w`, reduction, and the identification of the residue field of `w` with
`\bar 𝔽_p`. -/
def reductionPointHom [Fact p.Prime] [Algebra (ZMod p) (ResidueField w.valuationSubring)]
    (hgood : GoodReductionAt E (primeIdealQ p hp)) :
    ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).baseChange
        (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))).toAffine.Point →+
      ((reducedCurveModP E p hp).baseChange (AlgebraicClosure (ZMod p))).toAffine.Point :=
  haveI := reducedCurveModP_isElliptic E p hp hgood
  (Affine.Point.mapEquiv (reducedCurveModP E p hp) (residueEquiv p hp w hw)).toAddMonoidHom.comp
    ((AddEquiv.cast (M := fun V : WeierstrassCurve (ResidueField w.valuationSubring) =>
        V.toAffine.Point) (integralModelA_map_residue E p hp w hw)).toAddMonoidHom.comp
      ((reduceHom (integralModelA_Δ_ne_zero E p hp w hw hgood)).comp
        ((AddEquiv.cast (M := fun V : WeierstrassCurve
            (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) => V.toAffine.Point)
            (integralModelA_map_subtype E p hp w hw).symm).toAddMonoidHom.comp
          ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).pointEquivVariableChange
            (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))
            (minimalChange E p hp)).symm.toAddMonoidHom)))

/-- **Reduction is a bijection on prime-to-`p` torsion** (PROVED; step 3, Silverman VII.3.1):
every step is a group isomorphism except reduction itself, which is a bijection on `N`-torsion for
`N` prime to `p` (`reduceHom_bijOn_torsion`). -/
theorem reductionPointHom_bijOn [Fact p.Prime] [Algebra (ZMod p) (ResidueField w.valuationSubring)]
    (hgood : GoodReductionAt E (primeIdealQ p hp)) {N : ℕ}
    (hN : (N : ResidueField w.valuationSubring) ≠ 0) :
    Set.BijOn (reductionPointHom E p hp w hw hgood) {P | N • P = 0} {Q | N • Q = 0} := by
  rw [reductionPointHom]
  simp only [AddMonoidHom.coe_comp]
  exact (bijOn_torsion_of_bijective _ (AddEquiv.bijective _) N).comp
    ((bijOn_torsion_of_bijective _ (AddEquiv.bijective _) N).comp
      ((CloudB3RC53.ModularWeil.reduceHom_bijOn_torsion _ hN).comp
        ((bijOn_torsion_of_bijective _ (AddEquiv.bijective _) N).comp
          (bijOn_torsion_of_bijective _ (AddEquiv.bijective _) N))))

/-- The reduction homomorphism applies the reduction map (PROVED, by definition). -/
theorem reduceHom_apply {F : Type*} [Field F] [DecidableEq F] {B : ValuationSubring F}
    [DecidableEq (ResidueField B)] {V : WeierstrassCurve B} (hΔ : (V.map (residue B)).Δ ≠ 0)
    (P : (V.map B.subtype).toAffine.Point) : reduceHom hΔ P = reducePoint hΔ P :=
  rfl

/-- **Reduction of a non-integral point** (PROVED; step 4): a point of the minimal model whose
abscissa is not `w`-integral reduces to the point at infinity. -/
theorem reductionPointHom_some_of_notMem [Fact p.Prime]
    [Algebra (ZMod p) (ResidueField w.valuationSubring)]
    (hgood : GoodReductionAt E (primeIdealQ p hp))
    {x y : AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)}
    (h : ((minimalChange E p hp • E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).baseChange
      (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))).toAffine.Nonsingular x y)
    (hx : x ∉ w.valuationSubring) :
    reductionPointHom E p hp w hw hgood
        ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).pointEquivVariableChange
          (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) (minimalChange E p hp)
          (.some x y h)) = 0 := by
  simp only [reductionPointHom, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.symm_apply_apply, Affine.Point.mapEquiv_apply]
  rw [AddEquiv.cast_apply (integralModelA_map_subtype E p hp w hw).symm,
    Affine.Point.cast_some (integralModelA_map_subtype E p hp w hw).symm,
    reduceHom_apply, reducePoint_some_of_notMem _ _ hx, map_zero, map_zero]

/-- **Reduction carries an arithmetic Frobenius to the `p`-power Frobenius** (PROVED; step 4,
Silverman VII.7). An arithmetic Frobenius `σ` lies in the decomposition group of the valuation
ring of `w` and acts on its residue field as `z ↦ z^p` (`mem_decompositionSubgroup_of_frobenius`,
`smul_residue_eq_pow`); the change of variables to the minimal model is defined over `ℚ_p`, so it
commutes with `σ`; integral points reduce coordinatewise and non-integral points to infinity,
before and after `σ`; and the identification of the residue field with `\bar 𝔽_p` commutes with
`p`-th powers. -/
theorem reductionPointHom_frobenius [Fact p.Prime]
    [Algebra (ZMod p) (ResidueField w.valuationSubring)]
    (hgood : GoodReductionAt E (primeIdealQ p hp))
    (σ : AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ) ≃ₐ[
      (primeIdealQ p hp).adicCompletion ℚ] AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))
    (hσ : IsArithmeticFrobeniusOnClosureQ (primeIdealQ p hp) Γ w σ)
    (P : ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).baseChange
      (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))).toAffine.Point) :
    reductionPointHom E p hp w hw hgood
        (Affine.Point.map (W' := E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)) σ.toAlgHom P) =
      Affine.Point.map (W' := reducedCurveModP E p hp)
        (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)))
        (reductionPointHom E p hp w hw hgood P) := by
  have hσ' : ∀ x, w x ≤ 1 → w (σ x - x ^ p) < 1 := by
    intro x hx
    have h := hσ x hx
    rwa [primeIdealQ_absNorm] at h
  have hdec := mem_decompositionSubgroup_of_frobenius w σ hp.ne_zero hσ'
  have hfrob := smul_residue_eq_pow w σ hσ' hdec
  obtain ⟨Q, rfl⟩ := ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).pointEquivVariableChange
    (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) (minimalChange E p hp)).surjective P
  rw [map_pointEquivVariableChange]
  rcases Q with _ | ⟨x, y, h⟩
  · simp only [← Affine.Point.zero_def, map_zero]
  · have h₁ := (Affine.baseChange_nonsingular
      (minimalChange E p hp • E.baseChange ((primeIdealQ p hp).adicCompletion ℚ))
      (f := σ.toAlgHom) σ.injective x y).mpr h
    rw [Affine.Point.map_some]
    by_cases hx : x ∈ w.valuationSubring
    · have hσx : σ.toAlgHom x ∈ w.valuationSubring :=
        ValuationSubring.smul_mem_of_mem_decompositionSubgroup _ hdec hx
      have h₂ : ((integralModelA E p hp w hw).map w.valuationSubring.subtype).toAffine.Nonsingular
          x y := by
        rw [integralModelA_map_subtype]
        exact h
      have h₃ : ((integralModelA E p hp w hw).map w.valuationSubring.subtype).toAffine.Nonsingular
          (σ.toAlgHom x) (σ.toAlgHom y) := by
        rw [integralModelA_map_subtype]
        exact h₁
      have hy : y ∈ w.valuationSubring := Affine.Y_mem_of_X_mem _ h₂.1 hx
      have hσy : σ.toAlgHom y ∈ w.valuationSubring := Affine.Y_mem_of_X_mem _ h₃.1 hσx
      have hx' : residue w.valuationSubring ⟨σ.toAlgHom x, hσx⟩ =
          residue w.valuationSubring ⟨x, hx⟩ ^ p := hfrob (residue w.valuationSubring ⟨x, hx⟩)
      have hy' : residue w.valuationSubring ⟨σ.toAlgHom y, hσy⟩ =
          residue w.valuationSubring ⟨y, hy⟩ ^ p := hfrob (residue w.valuationSubring ⟨y, hy⟩)
      simp only [reductionPointHom, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
        AddEquiv.symm_apply_apply, Affine.Point.mapEquiv_apply]
      rw [AddEquiv.cast_apply (integralModelA_map_subtype E p hp w hw).symm,
        Affine.Point.cast_some (integralModelA_map_subtype E p hp w hw).symm,
        AddEquiv.cast_apply (integralModelA_map_subtype E p hp w hw).symm,
        Affine.Point.cast_some (integralModelA_map_subtype E p hp w hw).symm,
        reduceHom_apply, reduceHom_apply, reducePoint_some_of_mem _ _ hx,
        reducePoint_some_of_mem _ _ hσx,
        AddEquiv.cast_apply (integralModelA_map_residue E p hp w hw),
        Affine.Point.cast_some (integralModelA_map_residue E p hp w hw),
        AddEquiv.cast_apply (integralModelA_map_residue E p hp w hw),
        Affine.Point.cast_some (integralModelA_map_residue E p hp w hw),
        Affine.Point.map_some, Affine.Point.map_some, Affine.Point.map_some]
      simp only [FiniteField.frobeniusAlgHom_apply, ZMod.card, hx', hy', map_pow]
    · have hσx : σ.toAlgHom x ∉ w.valuationSubring := fun hmem => hx (by
        simpa using ValuationSubring.smul_mem_of_mem_decompositionSubgroup _ (inv_mem hdec) hmem)
      rw [reductionPointHom_some_of_notMem E p hp w hw hgood h hx,
        reductionPointHom_some_of_notMem E p hp w hw hgood h₁ hσx, map_zero]

end Comparison

/-! ### The reduction comparison -/

section Main

open IsDedekindDomain NewformPeriodsDictionary WeierstrassCurve
open scoped Classical

/-- **(R) The reduction comparison of Tate modules** (PROVED; Silverman VII.3.1 and VII.7.1):
`TateReductionComparison` of `ModularWeil/FrobeniusTrace.lean`, exactly as stated. For `E/ℚ` with
good reduction at `p`, `ℓ ≠ p`, a valuation `w` of `\bar ℚ_p` extending the `p`-adic valuation and
an arithmetic Frobenius `σ`, the reduction of points through the minimal model
(`reductionPointHom`) is a bijection on `ℓⁿ`-torsion for every `n` (`reductionPointHom_bijOn`),
hence induces an isomorphism of Tate modules (`tateLinearEquivOfBijOn`), and it carries `σ` to the
`p`-power Frobenius (`reductionPointHom_frobenius`). -/
theorem tateReductionComparison : CloudB3RC53.ModularWeil.TateReductionComparison := by
  intro E _ p hp hgood ℓ _ hℓ Γ _ w hw σ hσ
  have : Fact p.Prime := ⟨hp⟩
  let _ : Algebra (ZMod p) (ResidueField w.valuationSubring) := (primeFieldHom p hp w hw).toAlgebra
  have hN : ∀ n : ℕ, ((ℓ ^ n : ℕ) : ResidueField w.valuationSubring) ≠ 0 := by
    intro n h
    have := charP_of_injective_algebraMap
      (algebraMap (ZMod p) (ResidueField w.valuationSubring)).injective p
    rw [CharP.cast_eq_zero_iff _ p] at h
    exact hℓ ((Nat.prime_dvd_prime_iff_eq hp (Fact.out : ℓ.Prime)).mp (hp.dvd_of_dvd_pow h)).symm
  refine ⟨tateLinearEquivOfBijOn (reductionPointHom E p hp w hw hgood)
    (fun n => reductionPointHom_bijOn E p hp w hw hgood (hN n)), fun x => ?_⟩
  have key : (reductionPointHom E p hp w hw hgood).comp
      (Affine.Point.map (W' := E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)) σ.toAlgHom) =
      (Affine.Point.map (W' := reducedCurveModP E p hp)
        (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)))).comp
        (reductionPointHom E p hp w hw hgood) :=
    AddMonoidHom.ext fun P => reductionPointHom_frobenius E p hp w hw hgood σ hσ P
  rw [tateLinearEquivOfBijOn_apply, tateLinearEquivOfBijOn_apply,
    WeierstrassCurve.tateModuleGaloisRepresentation_apply]
  change TauCeti.TateModule.map _ (TauCeti.TateModule.map _ x) =
    TauCeti.TateModule.map _ (TauCeti.TateModule.map _ x)
  rw [← AddMonoidHom.comp_apply (TauCeti.TateModule.map _), ← TauCeti.TateModule.map_comp, key,
    TauCeti.TateModule.map_comp, AddMonoidHom.comp_apply]

/-- **The Frobenius trace dictionary from (D) alone** (PROVED from `DetEqDegree`): by
`goodReductionFrobeniusTraceDictionaryQ_of_RD` and `tateReductionComparison`. -/
theorem goodReductionFrobeniusTraceDictionaryQ_of_detEqDegree
    (hD : CloudB3RC53.ModularWeil.DetEqDegree) : GoodReductionFrobeniusTraceDictionaryQ :=
  CloudB3RC53.ModularWeil.goodReductionFrobeniusTraceDictionaryQ_of_RD tateReductionComparison hD

/-- **The Frobenius trace dictionary from (FD) alone** (PROVED from `FrobeniusTateDetForm`): by
`goodReductionFrobeniusTraceDictionaryQ_of` and `tateReductionComparison`. -/
theorem goodReductionFrobeniusTraceDictionaryQ_of_tateDetForm
    (hFD : CloudB3RC53.ModularWeil.FrobeniusTateDetForm) :
    GoodReductionFrobeniusTraceDictionaryQ :=
  CloudB3RC53.ModularWeil.goodReductionFrobeniusTraceDictionaryQ_of tateReductionComparison hFD

/-- **The Frobenius trace dictionary from (FD) at `m = 1` alone** (PROVED from
`FrobeniusTateDetFormOne`): by `goodReductionFrobeniusTraceDictionaryQ_of_one` and
`tateReductionComparison`. -/
theorem goodReductionFrobeniusTraceDictionaryQ_of_tateDetFormOne
    (hFD : CloudB3RC53.ModularWeil.FrobeniusTateDetFormOne) :
    GoodReductionFrobeniusTraceDictionaryQ :=
  CloudB3RC53.ModularWeil.goodReductionFrobeniusTraceDictionaryQ_of_one tateReductionComparison
    hFD

end Main

end ZInQ.Contrib.RC53Assist.TateReduction
