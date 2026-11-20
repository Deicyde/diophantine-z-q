import ZInQKernel.Contrib.CMSerreTateSupport.FrobLift.ResidueFiniteV002
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.Frobenius
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.Integral

/-!
# The arithmetic Frobenius lift in the decomposition group of a valuation of `K̄`

`K` a number field, `O ⊆ K` a discrete valuation subring, `Ω` an algebraic closure of `K`, `w` a
valuation subring of `Ω` with `w ∩ K = O`, and `q = #(O / 𝔪_O)` (finite, `q ≥ 2`).

* `Gal(Ω/K)` (Krull topology, profinite) acts continuously on the integral closure `B` of `O` in
  `Ω` (discrete topology), with invariants `O`; `Q = 𝔪_w ∩ B` is a prime of `B` over `𝔪_O`;
  the stabilizer of `Q` surjects onto `Aut((B/Q)/(O/𝔪_O))` (profinite stabilization).
* Lifting `t ↦ t^q` gives `σ` with `σ b ≡ b^q (mod Q)` on `B`.
* Every `x ∈ w` is `a / s` with `a, s ∈ B`, `s` a `w`-unit; hence `σ (w) = w` and
  `σ x ≡ x^q (mod 𝔪_w)` for every `x ∈ w`.
-/

noncomputable section

namespace FrobLift

open scoped Pointwise

attribute [local instance] Ideal.Quotient.field

section Action

variable (K : Type) [Field K] (O : ValuationSubring K) (Ω : Type) [Field Ω] [Algebra K Ω]

theorem gal_map_mem (g : Ω ≃ₐ[K] Ω) {b : Ω} (hb : b ∈ integralClosure O Ω) :
    g b ∈ integralClosure O Ω := by
  rw [mem_integralClosure_iff] at hb ⊢
  exact hb.map ((g : Ω →ₐ[K] Ω).restrictScalars O)

/-- `Gal(Ω/K)` acting on the integral closure of `O`. -/
instance galAction : MulSemiringAction (Ω ≃ₐ[K] Ω) (integralClosure O Ω) where
  smul g b := ⟨g b, gal_map_mem K O Ω g b.2⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl
  smul_zero g := Subtype.ext (map_zero g)
  smul_add g _ _ := Subtype.ext (map_add g _ _)
  smul_one g := Subtype.ext (map_one g)
  smul_mul g _ _ := Subtype.ext (map_mul g _ _)

theorem coe_gal_smul (g : Ω ≃ₐ[K] Ω) (b : integralClosure O Ω) :
    ((g • b : integralClosure O Ω) : Ω) = g b := rfl

instance galSMulComm : SMulCommClass (Ω ≃ₐ[K] Ω) O (integralClosure O Ω) where
  smul_comm g a b := by
    apply Subtype.ext
    show g (a • (b : Ω)) = a • g b
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply O K Ω,
      AlgEquiv.commutes]

theorem isInvariant [IsGalois K Ω] [IsIntegrallyClosed O] :
    Algebra.IsInvariant O (integralClosure O Ω) (Ω ≃ₐ[K] Ω) := by
  constructor
  intro b hb
  have hfix : ∀ g : Ω ≃ₐ[K] Ω, g b = b := fun g => congrArg Subtype.val (hb g)
  obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (b : Ω)).mpr hfix
  have hint : IsIntegral O (b : Ω) := (mem_integralClosure_iff O Ω).mp b.2
  rw [← hk] at hint
  have hint' : IsIntegral O k :=
    (isIntegral_algHom_iff ((Algebra.ofId K Ω).restrictScalars O)
      (algebraMap K Ω).injective).mp hint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
  refine ⟨y, Subtype.ext ?_⟩
  show algebraMap O Ω y = b
  rw [IsScalarTower.algebraMap_apply O K Ω, hy, hk]

theorem continuousSMul [Algebra.IsAlgebraic K Ω] :
    @ContinuousSMul (Ω ≃ₐ[K] Ω) (integralClosure O Ω) _ _ ⊥ := by
  letI : TopologicalSpace (integralClosure O Ω) := ⊥
  haveI : DiscreteTopology (integralClosure O Ω) := ⟨rfl⟩
  constructor
  rw [continuous_prod_of_discrete_right]
  intro b
  rw [continuous_discrete_rng]
  intro c
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  let E := IntermediateField.adjoin K {(b : Ω)}
  haveI : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := K) (b : Ω))
  refine ⟨g • (E.fixingSubgroup : Set (Ω ≃ₐ[K] Ω)), ?_, E.fixingSubgroup_isOpen.leftCoset g,
    ⟨1, E.fixingSubgroup.one_mem, mul_one g⟩⟩
  rintro _ ⟨h, hh, rfl⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hg ⊢
  rw [← hg]
  apply Subtype.ext
  show (g * h) (b : Ω) = g b
  rw [AlgEquiv.mul_apply, (IntermediateField.mem_fixingSubgroup_iff _ _).mp hh _
    (IntermediateField.mem_adjoin_simple_self K _)]

end Action

section Lift

variable {K : Type} [Field K] [NumberField K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {w : ValuationSubring Ω}

omit [NumberField K] [IsDiscreteValuationRing O] [IsAlgClosure K Ω] in
theorem mem_iff_of_comap (hw : w.comap (algebraMap K Ω) = O) (k : K) :
    algebraMap K Ω k ∈ w ↔ k ∈ O := by
  rw [← hw]
  rfl

omit [NumberField K] [IsDiscreteValuationRing O] [IsAlgClosure K Ω] in
theorem val_lt_one_iff_of_comap (hw : w.comap (algebraMap K Ω) = O) (k : K) :
    w.valuation (algebraMap K Ω k) < 1 ↔ O.valuation k < 1 := by
  by_cases hk : k = 0
  · simp [hk]
  have hk' : algebraMap K Ω k ≠ 0 := (map_ne_zero _).mpr hk
  have h1 : 0 < w.valuation (algebraMap K Ω k) :=
    zero_lt_iff.mpr ((Valuation.ne_zero_iff _).2 hk')
  have h2 : 0 < O.valuation k := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).2 hk)
  rw [← not_le, ← inv_le_one₀ h1, ← map_inv₀, ← map_inv₀, ValuationSubring.valuation_le_one_iff,
    mem_iff_of_comap hw, ← not_le, ← inv_le_one₀ h2, ← map_inv₀,
    ValuationSubring.valuation_le_one_iff]

omit [NumberField K] [IsDiscreteValuationRing O] [IsAlgClosure K Ω] in
theorem intClosure_mem (hw : w.comap (algebraMap K Ω) = O) (b : integralClosure O Ω) :
    (b : Ω) ∈ w := by
  have hint : IsIntegral O (b : Ω) := (mem_integralClosure_iff O Ω).mp b.2
  let φ : O →+* w :=
    { toFun := fun a => ⟨algebraMap O Ω a, by
        rw [IsScalarTower.algebraMap_apply O K Ω, mem_iff_of_comap hw]; exact a.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
  have hw' : IsIntegral w (b : Ω) :=
    IsIntegral.map_of_comp_eq (S := Ω) (U := Ω) φ (RingHom.id Ω) (by ext; rfl) hint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hw'
  rw [← hy]
  exact y.2

/-- The prime `𝔪_w ∩ B` of the integral closure `B` of `O`. -/
def primeQ (hw : w.comap (algebraMap K Ω) = O) : Ideal (integralClosure O Ω) :=
  (IsLocalRing.maximalIdeal w).comap
    ((algebraMap (integralClosure O Ω) Ω).codRestrict w (intClosure_mem hw))

omit [NumberField K] [IsDiscreteValuationRing O] [IsAlgClosure K Ω] in
theorem mem_primeQ (hw : w.comap (algebraMap K Ω) = O) (b : integralClosure O Ω) :
    b ∈ primeQ hw ↔ w.valuation (b : Ω) < 1 := by
  rw [primeQ, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

instance primeQ_isPrime (hw : w.comap (algebraMap K Ω) = O) : (primeQ hw).IsPrime := by
  rw [primeQ]
  infer_instance

omit [NumberField K] [IsDiscreteValuationRing O] [IsAlgClosure K Ω] in
theorem primeQ_liesOver (hw : w.comap (algebraMap K Ω) = O) :
    (primeQ hw).LiesOver (IsLocalRing.maximalIdeal O) := by
  constructor
  ext a
  rw [Ideal.under, Ideal.mem_comap, mem_primeQ, ValuationSubring.valuation_lt_one_iff]
  show O.valuation a < 1 ↔ w.valuation (algebraMap O Ω a) < 1
  rw [IsScalarTower.algebraMap_apply O K Ω, val_lt_one_iff_of_comap hw]
  rfl

/-- **Unit denominators in `B`**: every `x ∈ w` is `a / s` with `a, s ∈ B`, `s` a `w`-unit. -/
theorem exists_unit_denom_intClosure (hw : w.comap (algebraMap K Ω) = O) {x : Ω} (hx : x ∈ w) :
    ∃ s a : integralClosure O Ω, w.valuation (s : Ω) = 1 ∧ (s : Ω) * x = a := by
  classical
  set f := minpoly K x with hf
  have hxint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hmon : f.Monic := minpoly.monic hxint
  -- a coefficient of largest `O`-valuation
  obtain ⟨i₀, -, hi₀⟩ := (Finset.range (f.natDegree + 1)).exists_max_image
    (fun i => O.valuation (f.coeff i)) ⟨f.natDegree, Finset.self_mem_range_succ _⟩
  set c := f.coeff i₀ with hc
  have hlead : O.valuation (f.coeff f.natDegree) ≤ O.valuation c :=
    hi₀ _ (Finset.self_mem_range_succ _)
  rw [hmon.coeff_natDegree, map_one] at hlead
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hlead
    exact not_le.mpr zero_lt_one hlead
  have hcpos : 0 < O.valuation c := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).2 hc0)
  have hcoeffO : ∀ i, c⁻¹ * f.coeff i ∈ O := by
    intro i
    rw [← ValuationSubring.valuation_le_one_iff, map_mul, map_inv₀]
    by_cases hi : i ≤ f.natDegree
    · rw [inv_mul_le_iff₀ hcpos, mul_one]
      exact hi₀ i (Finset.mem_range.mpr (by omega))
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero, mul_zero]
      exact zero_le_one
  set P : Polynomial Ω := (Polynomial.C c⁻¹ * f).map (algebraMap K Ω) with hP
  have hlift : P ∈ Polynomial.lifts (algebraMap (integralClosure O Ω) Ω) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    refine ⟨algebraMap O (integralClosure O Ω) ⟨_, hcoeffO i⟩, ?_⟩
    rw [hP, Polynomial.coeff_map, Polynomial.coeff_C_mul,
      ← IsScalarTower.algebraMap_apply O (integralClosure O Ω) Ω,
      IsScalarTower.algebraMap_apply O K Ω]
    rfl
  obtain ⟨g, hg⟩ := Polynomial.mem_lifts _ |>.mp hlift
  have hgx : Polynomial.aeval x g = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hg, hP, Polynomial.eval_map,
      ← Polynomial.aeval_def, map_mul, Polynomial.aeval_C, minpoly.aeval, mul_zero]
  have hgc : ∀ i, algebraMap (integralClosure O Ω) Ω (g.coeff i) =
      algebraMap K Ω (c⁻¹ * f.coeff i) := by
    intro i
    rw [← Polynomial.coeff_map, hg, hP, Polynomial.coeff_map, Polynomial.coeff_C_mul]
  have hB : ∀ z : Ω, IsIntegral (integralClosure O Ω) z →
      z ∈ (algebraMap (integralClosure O Ω) Ω).range := by
    intro z hz
    have hz' : IsIntegral O z := isIntegral_trans _ hz
    exact ⟨⟨z, (mem_integralClosure_iff O Ω).mpr hz'⟩, rfl⟩
  have hunit : ∃ i, w.valuation (algebraMap (integralClosure O Ω) Ω (g.coeff i)) = 1 :=
    ⟨i₀, by rw [hgc, ← hc, inv_mul_cancel₀ hc0, map_one, map_one]⟩
  exact exists_unit_denominator w hB (intClosure_mem hw) g hx hgx hunit

/-- The arithmetic Frobenius lift exists on the integral closure: a `σ ∈ Gal(Ω/K)` with
`σ b ≡ b^q (mod 𝔪_w ∩ B)` for every `b ∈ B`. -/
theorem exists_frob_intClosure (hw : w.comap (algebraMap K Ω) = O) :
    ∃ σ : Ω ≃ₐ[K] Ω, σ ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) (primeQ hw) ∧
      ∀ b : integralClosure O Ω,
        w.valuation (σ b - (b : Ω) ^ Nat.card (IsLocalRing.ResidueField O)) < 1 := by
  set B := integralClosure O Ω
  set G := Ω ≃ₐ[K] Ω
  set P := IsLocalRing.maximalIdeal O
  set Q := primeQ hw
  haveI : Q.LiesOver P := primeQ_liesOver hw
  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  haveI : ContinuousSMul G B := continuousSMul K O Ω
  haveI : Algebra.IsInvariant O B G := isInvariant K O Ω
  haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap O B)
    (fun x => Algebra.IsIntegral.isIntegral x) Q
    (by rw [← Ideal.under_def, ← Ideal.over_def Q P]; infer_instance)
  haveI hfin : Finite (O ⧸ P) := finite_residueField O
  cases nonempty_fintype (O ⧸ P)
  obtain ⟨p, hc⟩ := CharP.exists (O ⧸ P)
  obtain ⟨k, hp, hk⟩ := FiniteField.card (O ⧸ P) p
  haveI := CharP.of_ringHom_of_ne_zero (algebraMap (O ⧸ P) (B ⧸ Q)) p hp.ne_zero
  haveI : ExpChar (B ⧸ Q) p := .prime hp
  haveI : Algebra.IsIntegral (O ⧸ P) (B ⧸ Q) := inferInstance
  haveI : PerfectField (B ⧸ Q) := Algebra.IsAlgebraic.perfectField (O ⧸ P)
  haveI : PerfectRing (B ⧸ Q) p := PerfectField.toPerfectRing (K := B ⧸ Q) p
  let l : (B ⧸ Q) ≃ₐ[O ⧸ P] B ⧸ Q :=
    { __ := iterateFrobeniusEquiv (B ⧸ Q) p k,
      commutes' r := by
        dsimp [iterateFrobenius_def]
        rw [← map_pow, ← hk, FiniteField.pow_card] }
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := G) P Q l
  refine ⟨σ.1, σ.2, fun b => ?_⟩
  have hq : Nat.card (IsLocalRing.ResidueField O) = p ^ (k : ℕ) := by
    rw [← hk]
    exact Nat.card_eq_fintype_card (α := O ⧸ P)
  have h1 := congrArg (fun e => e (Ideal.Quotient.mk Q b)) hσ
  simp only [Ideal.Quotient.stabilizerHom_apply] at h1
  have h2 : Ideal.Quotient.mk Q (σ • b) = Ideal.Quotient.mk Q (b ^ (p ^ (k : ℕ))) := by
    rw [h1, map_pow]
    rfl
  rw [Ideal.Quotient.eq, mem_primeQ] at h2
  rw [hq]
  exact h2

omit [NumberField K] [IsDiscreteValuationRing O] [IsAlgClosure K Ω] in
theorem stab_maps_mem (hw : w.comap (algebraMap K Ω) = O)
    (hden : ∀ x ∈ w, ∃ s a : integralClosure O Ω, w.valuation (s : Ω) = 1 ∧ (s : Ω) * x = a)
    {g : Ω ≃ₐ[K] Ω} (hg : g ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) (primeQ hw)) {x : Ω} (hx : x ∈ w) :
    g x ∈ w := by
  obtain ⟨s, a, hs, ha⟩ := hden x hx
  have hgQ : g • primeQ hw = primeQ hw := hg
  have hsQ : g • s ∉ primeQ hw := by
    intro h
    have h' := Ideal.smul_mem_pointwise_smul g⁻¹ _ _ h
    rw [inv_smul_smul, ← hgQ, inv_smul_smul] at h'
    rw [mem_primeQ, hs] at h'
    exact lt_irrefl _ h'
  have hgs : w.valuation (g s) = 1 := by
    rw [mem_primeQ, not_lt] at hsQ
    exact le_antisymm ((ValuationSubring.valuation_le_one_iff w _).2 (intClosure_mem hw (g • s)))
      hsQ
  have hgs0 : g s ≠ 0 := by
    intro h
    rw [h, map_zero] at hgs
    exact zero_ne_one hgs
  have hmul : g s * g x = g a := by rw [← map_mul, ha]
  have hga : w.valuation (g a) ≤ 1 :=
    (ValuationSubring.valuation_le_one_iff w _).2 (intClosure_mem hw (g • a))
  rw [← ValuationSubring.valuation_le_one_iff]
  rw [← hmul, map_mul, hgs, one_mul] at hga
  exact hga

/-- **The arithmetic Frobenius lift in the decomposition group of `w`.** -/
theorem exists_frobenius_lift (hw : w.comap (algebraMap K Ω) = O) :
    ∃ σ : Ω ≃ₐ[K] Ω, σ ∈ w.decompositionSubgroup K ∧
      ∀ x ∈ w, w.valuation (σ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1 := by
  obtain ⟨σ, hσQ, hσB⟩ := exists_frob_intClosure hw
  set q := Nat.card (IsLocalRing.ResidueField O)
  have hden := fun x (hx : x ∈ w) => exists_unit_denom_intClosure hw hx
  have hσinv : σ⁻¹ ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) (primeQ hw) := inv_mem hσQ
  refine ⟨σ, ?_, fun x hx => ?_⟩
  · show σ • w = w
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    constructor
    · intro hy
      have := stab_maps_mem hw hden hσQ hy
      rwa [AlgEquiv.smul_def, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at this
    · intro hy
      exact stab_maps_mem hw hden hσinv hy
  · obtain ⟨s, a, hs, ha⟩ := hden x hx
    have hsv : w.valuation ((s : Ω) ^ q) = 1 := by rw [map_pow, hs, one_pow]
    have hσs : w.valuation (σ s) = 1 := by
      have e : σ s = (s : Ω) ^ q + (σ s - (s : Ω) ^ q) := by ring
      rw [e, Valuation.map_add_eq_of_lt_left _ (by rw [hsv]; exact hσB s), hsv]
    have hav : w.valuation ((a : Ω) ^ q) ≤ 1 := by
      rw [map_pow]
      exact pow_le_one₀ zero_le ((ValuationSubring.valuation_le_one_iff w _).2 (intClosure_mem hw a))
    have h1 : σ s * σ x = σ a := by rw [← map_mul, ha]
    have hpow : (s : Ω) ^ q * x ^ q = (a : Ω) ^ q := by rw [← mul_pow, ha]
    have key : (σ x - x ^ q) * (σ s * (s : Ω) ^ q) =
        (σ a - (a : Ω) ^ q) * (s : Ω) ^ q - (a : Ω) ^ q * (σ s - (s : Ω) ^ q) := by
      linear_combination (s : Ω) ^ q * h1 - σ s * hpow
    have hN : w.valuation ((σ a - (a : Ω) ^ q) * (s : Ω) ^ q -
        (a : Ω) ^ q * (σ s - (s : Ω) ^ q)) < 1 := by
      apply Valuation.map_sub_lt
      · rw [map_mul, hsv, mul_one]
        exact hσB a
      · rw [map_mul]
        calc w.valuation ((a : Ω) ^ q) * w.valuation (σ s - (s : Ω) ^ q)
            ≤ 1 * w.valuation (σ s - (s : Ω) ^ q) := by gcongr
          _ < 1 := by rw [one_mul]; exact hσB s
    have hval := congrArg w.valuation key
    rw [map_mul, map_mul, hσs, hsv, one_mul, mul_one] at hval
    rw [hval]
    exact hN

end Lift

end FrobLift
