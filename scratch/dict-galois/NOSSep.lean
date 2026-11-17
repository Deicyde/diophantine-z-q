import ZInQKernel.Contrib.OneProof.UnipotentForward
import ZInQKernel.Contrib.OneProof.MulEtale

/-!
# dict-galois (3): `r7a` (Néron–Ogg–Shafarevich over `K̄`) from Serre–Tate Thm 1 over a separable closure

The chain's field `r7a : PkgI2.NeronOggShafarevich.{0}` (`ZInQKernel/HDecomp/Objects.lean`) states Serre–Tate's
criterion with the inertia group of a valuation ring of `K̄ = AlgebraicClosure K` acting on `A(K̄)[m]`. Serre and
Tate work over a separable closure `K_s`. The new leaf `NeronOggShafarevichSep` is the criterion over any
separable closure (`IsSepClosure K Ks`), with the inertia group of a valuation ring of `Ks` acting on `A(Ks)[m]`.
The `K̄` form follows for `Ks = K^s ⊆ K̄`: for `m` invertible in `O`, `[m]` is étale (the proved
`AvSplit.T4.MulEtaleAbelianScheme`, fork PR #19), so `A(K̄)[m] = A(K^s)[m]`; inertia of `K̄` restricts onto
inertia of `K^s` (unipotent-b's `inertiaRestrict'` in one direction, the pure inseparability of `K̄/K^s` here in
the other).
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction InertiaTrivialOn torsion galAct)
open scoped Pointwise

namespace NOSSepDict

/-- **LEAF (Serre–Tate 1968, Thm 1, the criterion of Néron–Ogg–Shafarevich, over a separable closure; numbering
from memory, UNVERIFIED).** Serre, Tate, *Good reduction of abelian varieties*, Ann. of Math. 88 (1968), 492-517,
§1, Theorem 1: `K` a field with a discrete valuation, `O` its valuation ring, `K_s` a separable closure of `K`,
`w` a valuation ring of `K_s` over `O` (the print's extension `\bar v`), `I` its inertia group in
`Gal(K_s/K)`, `A/K` an abelian variety. Then (a) `A` has good reduction ⟺ (b) for every `m ≥ 1` prime to the
residue characteristic, `I` acts trivially on `A(K_s)[m]` ⟺ (c) the same for infinitely many such `m`. Lean form:
as the chain's `PkgI2.NeronOggShafarevich` (good reduction = an abelian scheme over `O` with generic fibre `A`;
"`m` prime to the residue characteristic" = `IsUnit (m : O)`), with `AlgebraicClosure K` replaced by any `Ks`
with `IsSepClosure K Ks`. The print's (d) (`T_ℓ` unramified for one `ℓ`) is not stated. -/
def NeronOggShafarevichSep : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ks : Type) [Field Ks] [Algebra K Ks] [IsSepClosure K Ks]
    (w : ValuationSubring Ks), w.comap (algebraMap K Ks) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      (HasGoodReduction A O ↔
        ∀ m : ℕ, 0 < m → IsUnit (m : O) → InertiaTrivialOn A w m) ∧
      (HasGoodReduction A O ↔
        {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m}.Infinite)

section Extend

variable (K : Type) [Field K]

local notation "Ω" => AlgebraicClosure K
local notation "E" => separableClosure K (AlgebraicClosure K)

/-- Every element of `K̄` has a `q^n`-th power in `K^s` (`q` the exponential characteristic). -/
theorem exists_pow_mem_sep (q : ℕ) [ExpChar K q] (y : Ω) : ∃ n : ℕ, ∃ z : E, y ^ q ^ n = (z : Ω) := by
  haveI : ExpChar E q := expChar_of_injective_algebraMap (algebraMap K E).injective q
  have hpi : IsPurelyInseparable E Ω := separableClosure.isPurelyInseparable K Ω
  obtain ⟨n, z, hz⟩ := (isPurelyInseparable_iff_pow_mem E q).mp hpi y
  exact ⟨n, z, hz.symm⟩

/-- For a valuation ring `w` and `k ≠ 0`, `y^k ∈ w → y ∈ w`. -/
theorem mem_of_pow_mem_vs {L : Type} [Field L] (w : ValuationSubring L) {y : L} {k : ℕ} (hk : k ≠ 0)
    (h : y ^ k ∈ w) : y ∈ w := by
  rw [← w.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff_of_nonneg zero_le' hk).mp h

/-- If `ψ ∈ Aut(K̄/K)` restricts to `τ ∈ Aut(K^s/K)` and `τ` maps `w ∩ K^s` into itself, then `ψ` maps `w` into
itself (pure inseparability of `K̄/K^s`). -/
theorem map_mem_of_restrict (w : ValuationSubring Ω) (ψ : Ω ≃ₐ[K] Ω) (τ : E ≃ₐ[K] E)
    (hres : ∀ x : E, ψ (x : Ω) = ((τ x : E) : Ω))
    (hτ : ∀ z : E, (z : Ω) ∈ w → ((τ z : E) : Ω) ∈ w) {y : Ω} (hy : y ∈ w) : ψ y ∈ w := by
  obtain ⟨q, hq⟩ := ExpChar.exists K
  obtain ⟨n, z, hz⟩ := exists_pow_mem_sep K q y
  have hqn : q ^ n ≠ 0 := pow_ne_zero _ (expChar_pos K q).ne'
  refine mem_of_pow_mem_vs w hqn ?_
  rw [← map_pow, hz, hres]
  exact hτ z (hz ▸ w.pow_mem hy _)

/-- A non-unit of `w ∩ K^s` is a non-unit of `w`. -/
theorem mem_maximalIdeal_of_comap (w : ValuationSubring Ω) (c : w.comap (algebraMap E Ω))
    (hc : c ∈ IsLocalRing.maximalIdeal (w.comap (algebraMap E Ω))) :
    (⟨((c : E) : Ω), c.2⟩ : w) ∈ IsLocalRing.maximalIdeal w := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hc ⊢
  intro hu
  apply hc
  by_cases h0 : (c : E) = 0
  · exfalso
    have : (⟨((c : E) : Ω), c.2⟩ : w) = 0 := Subtype.ext (by simp [h0])
    rw [this] at hu
    exact not_isUnit_zero hu
  have hinv : ((c : E)⁻¹ : E) ∈ w.comap (algebraMap E Ω) := by
    obtain ⟨u, hu'⟩ := hu
    have h1 : ((u⁻¹ : wˣ) : w) * (⟨((c : E) : Ω), c.2⟩ : w) = 1 := by rw [← hu']; exact u.inv_mul
    have h2 : (((u⁻¹ : wˣ) : w) : Ω) = (((c : E)⁻¹ : E) : Ω) := by
      have h3 := congrArg (fun t : w => (t : Ω)) h1
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h3
      rw [IntermediateField.coe_inv]
      exact eq_inv_of_mul_eq_one_left h3
    show (algebraMap E Ω ((c : E)⁻¹)) ∈ w
    change (((c : E)⁻¹ : E) : Ω) ∈ w
    rw [← h2]
    exact (((u⁻¹ : wˣ) : w)).2
  refine isUnit_iff_exists_inv.mpr ⟨⟨(c : E)⁻¹, hinv⟩, ?_⟩
  apply Subtype.ext
  change (c : E) * (c : E)⁻¹ = 1
  exact mul_inv_cancel₀ h0

/-- **Inertia extends from `K^s` to `K̄`**: an extension `σ ∈ Aut(K̄/K)` of an element `τ` of the inertia group
of `w ∩ K^s` lies in the inertia group of `w`. -/
theorem isInertia_extend (w : ValuationSubring Ω) (τ : E ≃ₐ[K] E)
    (hτ : IsInertia (w.comap (algebraMap E Ω)) τ) (σ : Ω ≃ₐ[K] Ω)
    (hres : ∀ x : E, σ (x : Ω) = ((τ x : E) : Ω)) : IsInertia w σ := by
  obtain ⟨hd, hi⟩ := hτ
  set w' := w.comap (algebraMap E Ω)
  have hs : τ • w' = w' := hd
  -- `τ` and `τ⁻¹` preserve `w'`
  have hτw : ∀ z : E, (z : Ω) ∈ w → ((τ z : E) : Ω) ∈ w := by
    intro z hz
    have hz' : z ∈ w' := hz
    have : τ z ∈ τ • w' := by
      rw [← SetLike.mem_coe, ValuationSubring.coe_pointwise_smul]
      exact Set.smul_mem_smul_set hz'
    rw [hs] at this
    exact this
  have hτw' : ∀ z : E, (z : Ω) ∈ w → ((τ.symm z : E) : Ω) ∈ w := by
    intro z hz
    have hz' : z ∈ τ • w' := by rw [hs]; exact hz
    rw [← SetLike.mem_coe, ValuationSubring.coe_pointwise_smul] at hz'
    obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hz'
    rw [AlgEquiv.smul_def, AlgEquiv.symm_apply_apply]
    exact hu
  have hres' : ∀ x : E, σ.symm (x : Ω) = ((τ.symm x : E) : Ω) := by
    intro x
    apply σ.injective
    rw [AlgEquiv.apply_symm_apply, hres, AlgEquiv.apply_symm_apply]
  have hmap : ∀ y ∈ w, σ y ∈ w := fun y hy => map_mem_of_restrict K w σ τ hres hτw hy
  have hmap' : ∀ y ∈ w, σ.symm y ∈ w := fun y hy => map_mem_of_restrict K w σ.symm τ.symm hres' hτw' hy
  have hd' : σ ∈ w.decompositionSubgroup K := by
    show σ • w = w
    ext y
    simp only [← SetLike.mem_coe, ValuationSubring.coe_pointwise_smul, Set.mem_smul_set, AlgEquiv.smul_def]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hmap z hz
    · intro hy
      exact ⟨σ.symm y, hmap' y hy, σ.apply_symm_apply y⟩
  refine ⟨hd', ?_⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hi ⊢
  refine RingEquiv.ext fun r => ?_
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  change (⟨σ, hd'⟩ : w.decompositionSubgroup K) • IsLocalRing.residue w a = IsLocalRing.residue w a
  rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  -- `(σ a - a)^{q^n} = τ z - z` with `z = a^{q^n} ∈ w'`
  obtain ⟨q, hq⟩ := ExpChar.exists K
  haveI : ExpChar Ω q := expChar_of_injective_algebraMap (algebraMap K Ω).injective q
  obtain ⟨n, z, hz⟩ := exists_pow_mem_sep K q (a : Ω)
  have hzw : z ∈ w' := by
    show (z : Ω) ∈ w
    rw [← hz]; exact w.pow_mem a.2 _
  let zw : w' := ⟨z, hzw⟩
  have hz1 := RingEquiv.congr_fun hi (IsLocalRing.residue w' zw)
  change (⟨τ, hd⟩ : w'.decompositionSubgroup K) • IsLocalRing.residue w' zw =
    IsLocalRing.residue w' zw at hz1
  rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff] at hz1
  have hm := mem_maximalIdeal_of_comap K w _ hz1
  have hqn : q ^ n ≠ 0 := pow_ne_zero _ (expChar_pos K q).ne'
  refine (IsLocalRing.maximalIdeal.isMaximal w).isPrime.mem_of_pow_mem (q ^ n) ?_
  convert hm using 1
  apply Subtype.ext
  change (σ (a : Ω) - (a : Ω)) ^ q ^ n = ((τ z : E) : Ω) - (z : Ω)
  rw [sub_pow_expChar_pow, ← map_pow, hz, hres]

end Extend

section Transfer

open ZInQ.Contrib.AbVarBC

variable {K : Type} [Field K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]

local notation "Ω" => AlgebraicClosure K
local notation "E" => separableClosure K (AlgebraicClosure K)

/-- **`InertiaTrivialOn` over `K̄` and over `K^s` agree** for `m` invertible in `K`. -/
theorem inertiaTrivialOn_sep_iff (w : ValuationSubring Ω) (m : ℕ) (hm : (m : K) ≠ 0) :
    InertiaTrivialOn A w m ↔ InertiaTrivialOn A (w.comap (algebraMap E Ω)) m := by
  let B := ObjBridge.ofGrp A
  let κ : E →ₐ[K] Ω := IsScalarTower.toAlgHom K E Ω
  constructor
  · intro h τ hτ x hx
    haveI : Normal K Ω := IsAlgClosure.normal K Ω
    let σ : Ω ≃ₐ[K] Ω := τ.liftNormal Ω
    have hres : ∀ y : E, σ (y : Ω) = ((τ y : E) : Ω) := fun y => AlgEquiv.liftNormal_commutes τ Ω y
    have hσ := NOSSepDict.isInertia_extend K w τ hτ σ hres
    let x' : B.Pt E := x
    have hx' : x' ^ m = 1 := hx
    have hfix : B.galAct σ (extPt B κ x') = extPt B κ x' := by
      refine h σ hσ (extPt B κ x') ?_
      show (extPt B κ x') ^ m = 1
      rw [← map_pow, hx', map_one]
    show B.galAct τ x' = x'
    apply extPt_injective B κ
    rw [extPt_galAct B κ τ σ (fun y => (hres y).symm) x', hfix]
  · intro h σ hσ x hx
    obtain ⟨y, hy⟩ := UnipotentForward.torsion_from_sepClosure ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof Ω B m hm x hx
    obtain ⟨σs, hσs, hres⟩ := UnipotentForward.inertiaRestrict' K Ω w σ hσ
    have hym : y ^ m = 1 := by
      apply extPt_injective B κ
      rw [map_pow, map_one]
      change extPt B _ y ^ m = 1
      rw [hy]
      exact hx
    have h1 : B.galAct σs y = y := h σs hσs y hym
    rw [← hy]
    change B.galAct σ (extPt B κ y) = extPt B κ y
    rw [← extPt_galAct B κ σs σ (fun x => hres x), h1]

/-- **The chain's field `r7a` from the new leaf** (with the proved `MulEtaleAbelianScheme`). -/
theorem neronOggShafarevich_of_sep (h : NeronOggShafarevichSep) : PkgI2.NeronOggShafarevich.{0} := by
  intro K _ O _ w hw A _
  have hw' : (w.comap (algebraMap (separableClosure K (AlgebraicClosure K)) (AlgebraicClosure K))).comap
      (algebraMap K (separableClosure K (AlgebraicClosure K))) = O := by
    rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq]
    exact hw
  have key : ∀ m : ℕ, IsUnit (m : O) → (InertiaTrivialOn A w m ↔
      InertiaTrivialOn A (w.comap (algebraMap (separableClosure K (AlgebraicClosure K)) (AlgebraicClosure K))) m) := by
    intro m hu
    refine inertiaTrivialOn_sep_iff A w m ?_
    intro h0
    apply hu.ne_zero
    apply Subtype.ext
    simpa using h0
  obtain ⟨h1, h2⟩ := h K O (separableClosure K (AlgebraicClosure K)) _ hw' A
  refine ⟨h1.trans ?_, h2.trans ?_⟩
  · exact forall_congr' fun m => imp_congr_right fun _ => forall_congr' fun hu => (key m hu).symm
  · have hset : {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A
        (w.comap (algebraMap (separableClosure K (AlgebraicClosure K)) (AlgebraicClosure K))) m} =
        {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m} := by
      ext m
      simp only [Set.mem_setOf_eq]
      exact and_congr_right fun _ => and_congr_right fun hu => (key m hu).symm
    rw [hset]

end Transfer

end NOSSepDict
