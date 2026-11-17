import ZInQKernel.Contrib.OneProof.UnipotentForward
import ZInQKernel.Contrib.OneProof.MulEtale

/-!
# nos-proof: `r7a` (Néron–Ogg–Shafarevich, Serre–Tate 1968 Thm 1) with the direction (a) ⇒ (b) proved

The chain's field `r7a : PkgI2.NeronOggShafarevich.{0}` (`ZInQKernel/HDecomp/Objects.lean`) states
(a) ⟺ (b) and (a) ⟺ (c) of Serre–Tate's Theorem 1 over `K̄ = AlgebraicClosure K`. This file proves

* (a) ⇒ (b) (`inertiaTrivialOn_of_goodReduction`): good reduction makes inertia act trivially on
  `A(K̄)[m]` for every `m ≥ 1` invertible in `O`. Proof: reduction `A(K̄)[m] → 𝒜(κ(w))[m]` is bijective
  (the proved row `PkgI2.ReductionTorsionBijective`, `AvSplit.T4.reductionTorsionBijective_of_mulEtale` with
  fork PR #19's `mulEtaleAbelianScheme_proof`); an inertia element `σ` maps the lift `x̃ : Spec w → 𝒜` of `x`
  to the lift `Spec(σ|_w) ≫ x̃` of `σ x`, whose reduction is that of `x` because `σ` acts trivially on `κ(w)`;
  injectivity of reduction gives `σ x = x`.
* (b) ⇒ (c): infinitely many `m ≥ 1` are invertible in the local ring `O` (`m = k·p + 1` with `p` the
  residue characteristic, or every `m` in residue characteristic `0`).
* (c) ⇒ (a) from the new leaf `NOSConverseSep` (Serre–Tate Thm 1, (c) ⇒ (a), over a separable closure, as
  printed), via `K^s = separableClosure K K̄`: inertia of `w ∩ K^s` extends to inertia of `w`
  (dict-galois's `isInertia_extend`, copied) and `A(K^s) ↪ A(K̄)` is Galois-equivariant.
* §5: (a) ⇒ (b) over any field `Ω ⊇ K` (`inertiaTrivialOn_of_goodReduction_any`), av-split's injectivity of
  reduction copied with `K̄` replaced by `Ω`; it proves dict-galois's `NeronOggShafarevichSep` from
  `NOSConverseSep` as well (scratch/nos-proof/SepCompat.lean), should that fold land first.
-/

set_option linter.style.longLine false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI2 (IsAbelianVariety IsAbelianScheme IsInertia HasGoodReduction InertiaTrivialOn torsion galAct
  galHom Pts toW IsReductionOf)
open scoped Pointwise

namespace NOSProof

/-! ## 1. (a) ⇒ (b): good reduction makes inertia trivial on prime-to-`p` torsion -/

section Forward

variable {K : Type} [Field K]

/-- The restriction `σ|_w : w → w` of an element of the decomposition group of `w`. -/
def resW (w : ValuationSubring (AlgebraicClosure K)) (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hd : σ ∈ w.decompositionSubgroup K) : w →+* w :=
  MulSemiringAction.toRingHom (w.decompositionSubgroup K) w ⟨σ, hd⟩

theorem resW_coe (w : ValuationSubring (AlgebraicClosure K))
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (hd : σ ∈ w.decompositionSubgroup K) (a : w) :
    ((resW w σ hd a : w) : AlgebraicClosure K) = σ a := rfl

/-- `σ|_w` fixes the image of `O`. -/
theorem resW_comp_toW (O : ValuationSubring K) (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (hd : σ ∈ w.decompositionSubgroup K) :
    (resW w σ hd).comp (toW O w hw) = toW O w hw := by
  ext a
  change σ (algebraMap K (AlgebraicClosure K) (a : K)) = algebraMap K (AlgebraicClosure K) (a : K)
  exact σ.commutes _

/-- An inertia element acts trivially on `κ(w)`: `residue ∘ σ|_w = residue`. -/
theorem residue_comp_resW (w : ValuationSubring (AlgebraicClosure K))
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (hd : σ ∈ w.decompositionSubgroup K)
    (hi : (⟨σ, hd⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K) :
    (IsLocalRing.residue w).comp (resW w σ hd) = IsLocalRing.residue w := by
  ext a
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hi
  have h1 := RingEquiv.congr_fun hi (IsLocalRing.residue w a)
  change (⟨σ, hd⟩ : w.decompositionSubgroup K) • IsLocalRing.residue w a = IsLocalRing.residue w a at h1
  rw [← IsLocalRing.ResidueField.residue_smul] at h1
  exact h1

/-- **(a) ⇒ (b) of Serre–Tate's Theorem 1 (proved).** If `A` has good reduction at `O`, every element of
the inertia group of `w` fixes `A(K̄)[m]` for every `m ≥ 1` invertible in `O`. -/
theorem inertiaTrivialOn_of_goodReduction (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)) (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (hA : HasGoodReduction A O)
    (m : ℕ) (hm : 0 < m) (hmO : IsUnit (m : O)) : InertiaTrivialOn A w m := by
  obtain ⟨𝒜, h𝒜, ⟨e⟩⟩ := hA
  have hR := AvSplit.T4.reductionTorsionBijective_of_mulEtale
    ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof K O w hw A 𝒜 e m hm hmO
  intro σ hσ x hx
  obtain ⟨y, ⟨hy, x', hx1, hx2⟩, -⟩ := hR.1 x hx
  obtain ⟨hd, hi⟩ := hσ
  let s := resW w σ hd
  have hs1 : (CommRingCat.ofHom (toW O w hw) ≫ CommRingCat.ofHom s) =
      CommRingCat.ofHom (toW O w hw) := by
    rw [← CommRingCat.ofHom_comp, resW_comp_toW]
  have hs2 : (CommRingCat.ofHom s ≫ CommRingCat.ofHom (IsLocalRing.residue w)) =
      CommRingCat.ofHom (IsLocalRing.residue w) := by
    rw [← CommRingCat.ofHom_comp, residue_comp_resW w σ hd hi]
  let x'' : Over.mk (Spec.map (CommRingCat.ofHom (toW O w hw))) ⟶ 𝒜.X :=
    Over.homMk (Spec.map (CommRingCat.ofHom s) ≫ x'.left) (by
      have hx'w := Over.w x'
      simp only [Over.mk_hom] at hx'w ⊢
      rw [Category.assoc, hx'w, ← Spec.map_comp, hs1])
  have hσx : galAct A σ x ∈ torsion A (AlgebraicClosure K) m := by
    show galAct A σ x ^ m = 1
    rw [← PkgI2.galAct_pow]
    have hx' : x ^ m = 1 := hx
    rw [hx']
    exact PkgI2.galAct_one _ _
  have hred : IsReductionOf 𝒜 e w hw (galAct A σ x) y := by
    refine ⟨x'', ?_, ?_⟩
    · have h1 : (galAct A σ x ≫ (e.inv.hom.hom : A.X ⟶
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).obj 𝒜.X)).left =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫
            (x ≫ (e.inv.hom.hom : A.X ⟶
              (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).obj 𝒜.X)).left := by
        simp only [galAct, galHom, Category.assoc, Over.comp_left]
        rfl
      rw [h1]
      refine (Category.assoc _ _ _).trans ((congrArg (fun t =>
        Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫ t) hx1).trans ?_)
      show Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫
          Spec.map (CommRingCat.ofHom w.subtype) ≫ x'.left =
        Spec.map (CommRingCat.ofHom w.subtype) ≫ Spec.map (CommRingCat.ofHom s) ≫ x'.left
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      congr 2
    · show y.left = Spec.map (CommRingCat.ofHom (IsLocalRing.residue w)) ≫
          Spec.map (CommRingCat.ofHom s) ≫ x'.left
      rw [hx2, ← Category.assoc, ← Spec.map_comp, hs2]
  obtain ⟨x0, -, huniq⟩ := hR.2 y hy
  exact (huniq _ ⟨hσx, hred⟩).trans (huniq _ ⟨hx, ⟨x', hx1, hx2⟩⟩).symm

end Forward

/-! ## 2. (b) ⇒ (c): infinitely many integers are invertible in `O` -/

section Units

variable {K : Type} [Field K]

/-- Infinitely many `m ≥ 1` are units of the local ring `O`: `m = (N+1)p + 1` with `p` the residue
characteristic, or every `m ≥ 1` if the residue field has characteristic `0`. -/
theorem infinite_natCast_isUnit (O : ValuationSubring K) [IsDiscreteValuationRing O] :
    {m : ℕ | 0 < m ∧ IsUnit (m : O)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  by_cases hp : ringChar (IsLocalRing.ResidueField O) = 0
  · haveI : CharP (IsLocalRing.ResidueField O) 0 := hp ▸ ringChar.charP _
    haveI : CharZero (IsLocalRing.ResidueField O) := CharP.charP_to_charZero _
    refine ⟨N + 1, ⟨Nat.succ_pos N, ?_⟩, Nat.lt_succ_self N⟩
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero N)
  · refine ⟨(N + 1) * ringChar (IsLocalRing.ResidueField O) + 1, ⟨Nat.succ_pos _, ?_⟩, ?_⟩
    · rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast]
      push_cast
      rw [ringChar.Nat.cast_ringChar, mul_zero, zero_add]
      exact one_ne_zero
    · have : 1 ≤ ringChar (IsLocalRing.ResidueField O) := Nat.one_le_iff_ne_zero.mpr hp
      nlinarith

end Units

/-! ## 3. Inertia of `K^s` extends to inertia of `K̄` (dict-galois's lemmas, copied verbatim) -/

section Extend

variable (K : Type) [Field K]


/-- Every element of `K̄` has a `q^n`-th power in `K^s` (`q` the exponential characteristic). -/
theorem exists_pow_mem_sep (q : ℕ) [ExpChar K q] (y : (AlgebraicClosure K)) : ∃ n : ℕ, ∃ z : (separableClosure K (AlgebraicClosure K)), y ^ q ^ n = (z : (AlgebraicClosure K)) := by
  haveI : ExpChar (separableClosure K (AlgebraicClosure K)) q := expChar_of_injective_algebraMap (algebraMap K (separableClosure K (AlgebraicClosure K))).injective q
  have hpi : IsPurelyInseparable (separableClosure K (AlgebraicClosure K)) (AlgebraicClosure K) := separableClosure.isPurelyInseparable K (AlgebraicClosure K)
  obtain ⟨n, z, hz⟩ := (isPurelyInseparable_iff_pow_mem (separableClosure K (AlgebraicClosure K)) q).mp hpi y
  exact ⟨n, z, hz.symm⟩

/-- For a valuation ring `w` and `k ≠ 0`, `y^k ∈ w → y ∈ w`. -/
theorem mem_of_pow_mem_vs {L : Type} [Field L] (w : ValuationSubring L) {y : L} {k : ℕ} (hk : k ≠ 0)
    (h : y ^ k ∈ w) : y ∈ w := by
  rw [← w.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff_of_nonneg zero_le hk).mp h

/-- If `ψ ∈ Aut(K̄/K)` restricts to `τ ∈ Aut(K^s/K)` and `τ` maps `w ∩ K^s` into itself, then `ψ` maps `w` into
itself (pure inseparability of `K̄/K^s`). -/
theorem map_mem_of_restrict (w : ValuationSubring (AlgebraicClosure K)) (ψ : (AlgebraicClosure K) ≃ₐ[K] (AlgebraicClosure K)) (τ : (separableClosure K (AlgebraicClosure K)) ≃ₐ[K] (separableClosure K (AlgebraicClosure K)))
    (hres : ∀ x : (separableClosure K (AlgebraicClosure K)), ψ (x : (AlgebraicClosure K)) = ((τ x : (separableClosure K (AlgebraicClosure K))) : (AlgebraicClosure K)))
    (hτ : ∀ z : (separableClosure K (AlgebraicClosure K)), (z : (AlgebraicClosure K)) ∈ w → ((τ z : (separableClosure K (AlgebraicClosure K))) : (AlgebraicClosure K)) ∈ w) {y : (AlgebraicClosure K)} (hy : y ∈ w) : ψ y ∈ w := by
  obtain ⟨q, hq⟩ := ExpChar.exists K
  obtain ⟨n, z, hz⟩ := exists_pow_mem_sep K q y
  have hqn : q ^ n ≠ 0 := pow_ne_zero _ (expChar_pos K q).ne'
  refine mem_of_pow_mem_vs w hqn ?_
  rw [← map_pow, hz, hres]
  exact hτ z (hz ▸ w.pow_mem hy _)

/-- A non-unit of `w ∩ K^s` is a non-unit of `w`. -/
theorem mem_maximalIdeal_of_comap (w : ValuationSubring (AlgebraicClosure K)) (c : w.comap (algebraMap (separableClosure K (AlgebraicClosure K)) (AlgebraicClosure K)))
    (hc : c ∈ IsLocalRing.maximalIdeal (w.comap (algebraMap (separableClosure K (AlgebraicClosure K)) (AlgebraicClosure K)))) :
    (⟨((c : (separableClosure K (AlgebraicClosure K))) : (AlgebraicClosure K)), c.2⟩ : w) ∈ IsLocalRing.maximalIdeal w := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hc ⊢
  intro hu
  apply hc
  by_cases h0 : (c : (separableClosure K (AlgebraicClosure K))) = 0
  · exfalso
    have : (⟨((c : (separableClosure K (AlgebraicClosure K))) : (AlgebraicClosure K)), c.2⟩ : w) = 0 := Subtype.ext (by simp [h0])
    rw [this] at hu
    exact not_isUnit_zero hu
  have hinv : ((c : (separableClosure K (AlgebraicClosure K)))⁻¹ : (separableClosure K (AlgebraicClosure K))) ∈ w.comap (algebraMap (separableClosure K (AlgebraicClosure K)) (AlgebraicClosure K)) := by
    obtain ⟨u, hu'⟩ := hu
    have h1 : ((u⁻¹ : wˣ) : w) * (⟨((c : (separableClosure K (AlgebraicClosure K))) : (AlgebraicClosure K)), c.2⟩ : w) = 1 := by rw [← hu']; exact u.inv_mul
    have h2 : (((u⁻¹ : wˣ) : w) : (AlgebraicClosure K)) = (((c : (separableClosure K (AlgebraicClosure K)))⁻¹ : (separableClosure K (AlgebraicClosure K))) : (AlgebraicClosure K)) := by
      have h3 := congrArg (fun t : w => (t : (AlgebraicClosure K))) h1
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h3
      rw [IntermediateField.coe_inv]
      exact eq_inv_of_mul_eq_one_left h3
    show (algebraMap (separableClosure K (AlgebraicClosure K)) (AlgebraicClosure K) ((c : (separableClosure K (AlgebraicClosure K)))⁻¹)) ∈ w
    change (((c : (separableClosure K (AlgebraicClosure K)))⁻¹ : (separableClosure K (AlgebraicClosure K))) : (AlgebraicClosure K)) ∈ w
    rw [← h2]
    exact (((u⁻¹ : wˣ) : w)).2
  refine isUnit_iff_exists_inv.mpr ⟨⟨(c : (separableClosure K (AlgebraicClosure K)))⁻¹, hinv⟩, ?_⟩
  apply Subtype.ext
  change (c : (separableClosure K (AlgebraicClosure K))) * (c : (separableClosure K (AlgebraicClosure K)))⁻¹ = 1
  exact mul_inv_cancel₀ h0

/-- **Inertia extends from `K^s` to `K̄`**: an extension `σ ∈ Aut(K̄/K)` of an element `τ` of the inertia group
of `w ∩ K^s` lies in the inertia group of `w`. -/
theorem isInertia_extend (w : ValuationSubring (AlgebraicClosure K)) (τ : (separableClosure K (AlgebraicClosure K)) ≃ₐ[K] (separableClosure K (AlgebraicClosure K)))
    (hτ : IsInertia (w.comap (algebraMap (separableClosure K (AlgebraicClosure K)) (AlgebraicClosure K))) τ) (σ : (AlgebraicClosure K) ≃ₐ[K] (AlgebraicClosure K))
    (hres : ∀ x : (separableClosure K (AlgebraicClosure K)), σ (x : (AlgebraicClosure K)) = ((τ x : (separableClosure K (AlgebraicClosure K))) : (AlgebraicClosure K))) : IsInertia w σ := by
  obtain ⟨hd, hi⟩ := hτ
  set w' := w.comap (algebraMap (separableClosure K (AlgebraicClosure K)) (AlgebraicClosure K))
  have hs : τ • w' = w' := hd
  -- `τ` and `τ⁻¹` preserve `w'`
  have hτw : ∀ z : (separableClosure K (AlgebraicClosure K)), (z : (AlgebraicClosure K)) ∈ w → ((τ z : (separableClosure K (AlgebraicClosure K))) : (AlgebraicClosure K)) ∈ w := by
    intro z hz
    have hz' : z ∈ w' := hz
    have : τ z ∈ τ • w' := by
      rw [← SetLike.mem_coe, ValuationSubring.coe_pointwise_smul]
      exact Set.smul_mem_smul_set hz'
    rw [hs] at this
    exact this
  have hτw' : ∀ z : (separableClosure K (AlgebraicClosure K)), (z : (AlgebraicClosure K)) ∈ w → ((τ.symm z : (separableClosure K (AlgebraicClosure K))) : (AlgebraicClosure K)) ∈ w := by
    intro z hz
    have hz' : z ∈ τ • w' := by rw [hs]; exact hz
    rw [← SetLike.mem_coe, ValuationSubring.coe_pointwise_smul] at hz'
    obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hz'
    rw [AlgEquiv.smul_def, AlgEquiv.symm_apply_apply]
    exact hu
  have hres' : ∀ x : (separableClosure K (AlgebraicClosure K)), σ.symm (x : (AlgebraicClosure K)) = ((τ.symm x : (separableClosure K (AlgebraicClosure K))) : (AlgebraicClosure K)) := by
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
  haveI : ExpChar (AlgebraicClosure K) q := expChar_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective q
  obtain ⟨n, z, hz⟩ := exists_pow_mem_sep K q (a : (AlgebraicClosure K))
  have hzw : z ∈ w' := by
    show (z : (AlgebraicClosure K)) ∈ w
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
  change (σ (a : (AlgebraicClosure K)) - (a : (AlgebraicClosure K))) ^ q ^ n = ((τ z : (separableClosure K (AlgebraicClosure K))) : (AlgebraicClosure K)) - (z : (AlgebraicClosure K))
  rw [sub_pow_expChar_pow, ← map_pow, hz, hres]

end Extend

/-! ## 4. The new leaf and the field -/

section Transfer

open ZInQ.Contrib.AbVarBC

variable {K : Type} [Field K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]

/-- Triviality of inertia on `A(K̄)[m]` gives triviality on `A(K^s)[m]` for `K^s = separableClosure K K̄`
(the first half of dict-galois's `inertiaTrivialOn_sep_iff`, copied; no hypothesis on `m`). -/
theorem inertiaTrivialOn_sep_of (w : ValuationSubring (AlgebraicClosure K)) (m : ℕ)
    (h : InertiaTrivialOn A w m) :
    InertiaTrivialOn A (w.comap (algebraMap (separableClosure K (AlgebraicClosure K)) (AlgebraicClosure K))) m := by
  let B := ObjBridge.ofGrp A
  let κ : (separableClosure K (AlgebraicClosure K)) →ₐ[K] (AlgebraicClosure K) :=
    IsScalarTower.toAlgHom K (separableClosure K (AlgebraicClosure K)) (AlgebraicClosure K)
  intro τ hτ x hx
  haveI : Normal K (AlgebraicClosure K) := IsAlgClosure.normal K (AlgebraicClosure K)
  let σ : (AlgebraicClosure K) ≃ₐ[K] (AlgebraicClosure K) := τ.liftNormal (AlgebraicClosure K)
  have hres : ∀ y : (separableClosure K (AlgebraicClosure K)), σ (y : (AlgebraicClosure K)) =
      ((τ y : (separableClosure K (AlgebraicClosure K))) : (AlgebraicClosure K)) :=
    fun y => AlgEquiv.liftNormal_commutes τ (AlgebraicClosure K) y
  have hσ := isInertia_extend K w τ hτ σ hres
  let x' : B.Pt (separableClosure K (AlgebraicClosure K)) := x
  have hx' : x' ^ m = 1 := hx
  have hfix : B.galAct σ (extPt B κ x') = extPt B κ x' := by
    refine h σ hσ (extPt B κ x') ?_
    show (extPt B κ x') ^ m = 1
    rw [← map_pow, hx', map_one]
  show B.galAct τ x' = x'
  apply extPt_injective B κ
  rw [extPt_galAct B κ τ σ (fun y => (hres y).symm) x', hfix]

end Transfer

/-- **LEAF `NOSConverseSep` (Serre–Tate 1968, Thm 1, (c) ⇒ (a), over a separable closure; numbering from
memory, UNVERIFIED).** Serre, Tate, *Good reduction of abelian varieties*, Ann. of Math. 88 (1968), 492–517,
§1, Theorem 1 (the criterion of Néron–Ogg–Shafarevich): `K` a field with a discrete valuation, `O` its
valuation ring, `K_s` a separable closure of `K`, `w` a valuation ring of `K_s` over `O` (the print's
extension of the valuation), `I` its inertia group in `Gal(K_s/K)`, `A/K` an abelian variety. If `I` acts
trivially on `A(K_s)[m]` for infinitely many `m ≥ 1` prime to the residue characteristic, then `A` has good
reduction. Lean form: the direction (c) ⇒ (a) of dict-galois's `NOSSepDict.NeronOggShafarevichSep` (good
reduction = an abelian scheme over `O` with generic fibre `A`, as in the chain's `PkgI2.HasGoodReduction`;
"`m` prime to the residue characteristic" = `IsUnit (m : O)`). The other directions are proved
(`inertiaTrivialOn_of_goodReduction`, `infinite_natCast_isUnit`). -/
def NOSConverseSep : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ks : Type) [Field Ks] [Algebra K Ks] [IsSepClosure K Ks]
    (w : ValuationSubring Ks), w.comap (algebraMap K Ks) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m}.Infinite → HasGoodReduction A O

/-- **The chain's field `r7a` from the leaf `NOSConverseSep`**: (a) ⇒ (b) and (b) ⇒ (c) are proved,
(c) ⇒ (a) is the leaf applied to `K^s = separableClosure K K̄` and `w ∩ K^s`. -/
theorem neronOggShafarevich_of_converse (h : NOSConverseSep) : PkgI2.NeronOggShafarevich.{0} := by
  intro K _ O _ w hw A _
  have hw' : (w.comap (algebraMap (separableClosure K (AlgebraicClosure K)) (AlgebraicClosure K))).comap
      (algebraMap K (separableClosure K (AlgebraicClosure K))) = O := by
    rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq]
    exact hw
  -- (c) ⇒ (a)
  have hca : {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m}.Infinite →
      HasGoodReduction A O := by
    intro hinf
    refine h K O (separableClosure K (AlgebraicClosure K)) _ hw' A (hinf.mono ?_)
    rintro m ⟨hm, hu, ht⟩
    exact ⟨hm, hu, inertiaTrivialOn_sep_of A w m ht⟩
  -- (b) ⇒ (c)
  have hbc : (∀ m : ℕ, 0 < m → IsUnit (m : O) → InertiaTrivialOn A w m) →
      {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m}.Infinite := by
    intro hb
    refine (infinite_natCast_isUnit O).mono ?_
    rintro m ⟨hm, hu⟩
    exact ⟨hm, hu, hb m hm hu⟩
  -- (a) ⇒ (b)
  have hab : HasGoodReduction A O → ∀ m : ℕ, 0 < m → IsUnit (m : O) → InertiaTrivialOn A w m :=
    fun hA m hm hu => inertiaTrivialOn_of_goodReduction O w hw A hA m hm hu
  exact ⟨⟨hab, fun hb => hca (hbc hb)⟩, ⟨fun hA => hbc (hab hA), hca⟩⟩



/-! ## 5. (a) ⇒ (b) over any field `Ω ⊇ K` (generalizing av-split's §3-§5 from `K̄` to `Ω`)

The injectivity half of av-split's proof of `PkgI2.ReductionTorsionBijective` (`AvSplit.T4`, TailQ) uses
nothing about `K̄`: the valuative criterion of separatedness and universal closedness for the valuation ring
`w ⊆ Ω`, the adjunction for points of `𝒜_K`, and the proved `UnramifiedSectionsEq` with `[m]` étale. Copied
here with `AlgebraicClosure K` replaced by `Ω`, it gives (a) ⇒ (b) for every valuation ring `w` of every field
`Ω ⊇ K` over `O` (in particular for a separable closure, the form of dict-galois's `NeronOggShafarevichSep`). -/

section Omega

variable {K : Type} [Field K] {O : ValuationSubring K} {Ω : Type} [Field Ω] [Algebra K Ω]
  {w : ValuationSubring Ω} (hw : w.comap (algebraMap K Ω) = O)

/-- `Spec w` over `Spec O`. -/
abbrev PwΩ : Over (Spec (.of O)) := Over.mk (Spec.map (CommRingCat.ofHom (toW O w hw)))

/-- `Spec κ(w)` over `Spec O`. -/
abbrev PkΩ : Over (Spec (.of O)) :=
  Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue w).comp (toW O w hw))))

variable (K O Ω) in
/-- `Spec Ω` over `Spec O`. -/
abbrev PΩ : Over (Spec (.of O)) :=
  (Over.map (AvSplit.T4.fK K O)).obj (PkgI2.specOver K Ω)

/-- `Spec Ω → Spec w` over `O`. -/
def iotaΩ : PΩ K O Ω ⟶ PwΩ hw :=
  Over.homMk (Spec.map (CommRingCat.ofHom w.subtype)) (by
    show Spec.map (CommRingCat.ofHom w.subtype) ≫ Spec.map (CommRingCat.ofHom (toW O w hw)) =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap O K))
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl)

/-- `Spec κ(w) → Spec w` over `O`. -/
def rhoΩ : PkΩ hw ⟶ PwΩ hw :=
  Over.homMk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue w))) (by
    simp only [Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])

variable {A : Grp (Over (Spec (.of K)))} (𝒜 : Grp (Over (Spec (.of O))))
  (e : (Over.pullback (AvSplit.T4.fK K O)).mapGrp.obj 𝒜 ≅ A)

variable (Ω) in
/-- `x ∈ A(Ω)` as an `Ω`-point of `𝒜` over `O` (through `e` and the adjunction). -/
def GΩ : Pts A Ω →* (PΩ K O Ω ⟶ 𝒜.X) :=
  MonoidHom.mk' (fun x => ((Over.mapPullbackAdj (AvSplit.T4.fK K O)).homEquiv _ 𝒜.X).symm
      (x ≫ e.inv.hom.hom)) (fun x y => by
    let u : Pts A Ω →
        (PkgI2.specOver K Ω ⟶ ((Over.pullback (AvSplit.T4.fK K O)).mapGrp.obj 𝒜).X) :=
      fun x => x ≫ e.inv.hom.hom
    have hmul : u (x * y) = u x * u y := MonObj.mul_comp _ _ _
    show ((Over.mapPullbackAdj (AvSplit.T4.fK K O)).homEquiv _ 𝒜.X).symm (u (x * y)) = _
    rw [hmul]
    exact AvSplit.T4.pb_symm_mul' _ 𝒜 _ _ _)

theorem GΩ_left (x : Pts A Ω) :
    (GΩ Ω 𝒜 e x).left = (x ≫ e.inv.hom.hom).left ≫ pullback.fst 𝒜.X.hom (AvSplit.T4.fK K O) := rfl

theorem GΩ_injective : Function.Injective (GΩ Ω 𝒜 e) := by
  intro x y h
  have h1 : x ≫ e.inv.hom.hom = y ≫ e.inv.hom.hom :=
    ((Over.mapPullbackAdj (AvSplit.T4.fK K O)).homEquiv _ 𝒜.X).symm.injective h
  have h2 := congrArg (· ≫ e.hom.hom.hom) h1
  simp only [Category.assoc, AvSplit.T4.inv_hom_hom, Category.comp_id] at h2
  exact h2

theorem PΩ_hom_eq : (PΩ K O Ω).hom =
    Spec.map (CommRingCat.ofHom (algebraMap w Ω)) ≫
      Spec.map (CommRingCat.ofHom (toW O w hw)) := by
  show Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap O K)) = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- The valuative square of an `Ω`-point of `𝒜` over `Spec w → Spec O`. -/
def vsqΩ (t : PΩ K O Ω ⟶ 𝒜.X) : ValuativeCommSq 𝒜.X.hom where
  R := w
  K := Ω
  i₁ := t.left
  i₂ := Spec.map (CommRingCat.ofHom (toW O w hw))
  commSq := ⟨(Over.w t).trans (PΩ_hom_eq hw)⟩

/-- **Uniqueness of lifts** (Mathlib, valuative criterion of separatedness). -/
theorem iotaΩ_comp_injective [h : IsAbelianScheme 𝒜] :
    Function.Injective (fun x' : PwΩ hw ⟶ 𝒜.X => iotaΩ hw ≫ x') := by
  intro x₁ x₂ hx
  haveI := h.proper
  have hU := IsSeparated.valuativeCriterion 𝒜.X.hom (vsqΩ hw 𝒜 (iotaΩ hw ≫ x₁))
  have e1 : (⟨x₁.left, rfl, Over.w x₁⟩ : (vsqΩ hw 𝒜 (iotaΩ hw ≫ x₁)).commSq.LiftStruct) =
      ⟨x₂.left, (congrArg Over.Hom.left hx).symm, Over.w x₂⟩ := Subsingleton.elim _ _
  exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l e1)

/-- **Existence of lifts** (Mathlib, valuative criterion of universal closedness). -/
theorem iotaΩ_comp_surjective [h : IsAbelianScheme 𝒜] (t : PΩ K O Ω ⟶ 𝒜.X) :
    ∃ x' : PwΩ hw ⟶ 𝒜.X, iotaΩ hw ≫ x' = t := by
  haveI := h.proper
  have h1 : (ValuativeCriterion.Existence ⊓ @QuasiCompact) 𝒜.X.hom := by
    rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
  obtain ⟨⟨l, hl1, hl2⟩⟩ := h1.1 (vsqΩ hw 𝒜 t)
  exact ⟨Over.homMk l hl2, Over.OverMorphism.ext hl1⟩

/-- **Reduction is injective on `m`-torsion of `𝒜(w)`** (av-split's `rho_inj` over `Ω`, with the proved
`UnramifiedSectionsEq` and `MulEtaleAbelianScheme`). -/
theorem rhoΩ_inj [h : IsAbelianScheme 𝒜]
    (m : ℕ) (hm : IsUnit (m : O)) (a b : PwΩ hw ⟶ 𝒜.X) (ha : a ^ m = 1) (hb : b ^ m = 1)
    (hab : rhoΩ hw ≫ a = rhoΩ hw ≫ b) : a = b := by
  haveI := h.proper
  haveI : Etale ((𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left) :=
    ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof O 𝒜 m hm
  haveI : IsSeparated ((𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left ≫ 𝒜.X.hom) := by
    rw [Over.w (𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X)]; infer_instance
  haveI : IsSeparated ((𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left) :=
    IsSeparated.of_comp _ 𝒜.X.hom
  have hcomp : a.left ≫ (𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left =
      b.left ≫ (𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left := by
    rw [← Over.comp_left, ← Over.comp_left, AvSplit.T4.comp_mulN, AvSplit.T4.comp_mulN, ha, hb]
  let p : Spec (.of (IsLocalRing.ResidueField w)) ⟶ Spec (.of w) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue w))
  have hp : p ≫ a.left = p ≫ b.left := congrArg Over.Hom.left hab
  have hfac := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField
    (IsLocalRing.ResidueField w) (Spec (.of w)) p
  haveI : Epi (Spec.map ((Spec (.of w)).descResidueField (Scheme.stalkClosedPointTo p))) := by
    have := AvSplit.T4.epi_spec_field ((Spec (.of w)).descResidueField (Scheme.stalkClosedPointTo p)).hom
    rwa [CommRingCat.ofHom_hom] at this
  have hx : (Spec (.of w)).fromSpecResidueField (p (IsLocalRing.closedPoint _)) ≫ a.left =
      (Spec (.of w)).fromSpecResidueField (p (IsLocalRing.closedPoint _)) ≫ b.left := by
    rw [← cancel_epi (Spec.map ((Spec (.of w)).descResidueField (Scheme.stalkClosedPointTo p))),
      ← Category.assoc, hfac, ← Category.assoc, hfac]
    exact hp
  exact Over.OverMorphism.ext (AvSplit.T4.unramifiedSectionsEq (Spec (.of w)) 𝒜.X.left 𝒜.X.left _
    a.left b.left inferInstance hcomp _ hx)

end Omega

section OmegaForward

variable {K : Type} [Field K]

/-- The restriction `σ|_w : w → w` of an element of the decomposition group of `w ⊆ Ω`. -/
def resWΩ {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω)
    (hd : σ ∈ w.decompositionSubgroup K) : w →+* w :=
  MulSemiringAction.toRingHom (w.decompositionSubgroup K) w ⟨σ, hd⟩

/-- **(a) ⇒ (b) of Serre–Tate's Theorem 1 over any field `Ω ⊇ K` (proved).** If `A` has good reduction at
`O`, then for every valuation ring `w` of `Ω` over `O`, every element of the inertia group of `w` in
`Aut(Ω/K)` fixes `A(Ω)[m]` for every `m ≥ 1` invertible in `O`. -/
theorem inertiaTrivialOn_of_goodReduction_any (O : ValuationSubring K)
    (Ω : Type) [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (A : Grp (Over (Spec (.of K)))) (hA : HasGoodReduction A O)
    (m : ℕ) (hmO : IsUnit (m : O)) : InertiaTrivialOn A w m := by
  obtain ⟨𝒜, h𝒜, ⟨e⟩⟩ := hA
  intro σ hσ x hx
  obtain ⟨hd, hi⟩ := hσ
  let s := resWΩ w σ hd
  have hs1 : (CommRingCat.ofHom (toW O w hw) ≫ CommRingCat.ofHom s) =
      CommRingCat.ofHom (toW O w hw) := by
    rw [← CommRingCat.ofHom_comp]
    congr 1
    ext a
    change σ (algebraMap K Ω (a : K)) = algebraMap K Ω (a : K)
    exact σ.commutes _
  have hs2 : (CommRingCat.ofHom s ≫ CommRingCat.ofHom (IsLocalRing.residue w)) =
      CommRingCat.ofHom (IsLocalRing.residue w) := by
    rw [← CommRingCat.ofHom_comp]
    congr 1
    ext a
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hi
    have h1 := RingEquiv.congr_fun hi (IsLocalRing.residue w a)
    change (⟨σ, hd⟩ : w.decompositionSubgroup K) • IsLocalRing.residue w a =
      IsLocalRing.residue w a at h1
    rw [← IsLocalRing.ResidueField.residue_smul] at h1
    exact h1
  obtain ⟨x', hx'⟩ := iotaΩ_comp_surjective hw 𝒜 (GΩ Ω 𝒜 e x)
  let x'' : PwΩ hw ⟶ 𝒜.X :=
    Over.homMk (Spec.map (CommRingCat.ofHom s) ≫ x'.left) (by
      have hx'w := Over.w x'
      simp only [Over.mk_hom] at hx'w ⊢
      rw [Category.assoc, hx'w, ← Spec.map_comp, hs1])
  have hxm : x ^ m = 1 := hx
  have hσx : galAct A σ x ^ m = 1 := by
    rw [← PkgI2.galAct_pow, hxm]
    exact PkgI2.galAct_one _ _
  -- `x''` lifts `σ x`
  have hlift : iotaΩ hw ≫ x'' = GΩ Ω 𝒜 e (galAct A σ x) := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, GΩ_left]
    have h1 : (galAct A σ x ≫ (e.inv.hom.hom : A.X ⟶
          (Over.pullback (AvSplit.T4.fK K O)).obj 𝒜.X)).left =
          Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
            (x ≫ (e.inv.hom.hom : A.X ⟶ (Over.pullback (AvSplit.T4.fK K O)).obj 𝒜.X)).left := by
      simp only [galAct, PkgI2.galHom, Category.assoc, Over.comp_left]
      rfl
    rw [h1]
    have h2 : (x ≫ (e.inv.hom.hom : A.X ⟶ (Over.pullback (AvSplit.T4.fK K O)).obj 𝒜.X)).left ≫
        pullback.fst 𝒜.X.hom (AvSplit.T4.fK K O) = Spec.map (CommRingCat.ofHom w.subtype) ≫ x'.left := by
      rw [← GΩ_left, ← hx']
      rfl
    refine Eq.trans ?_ ((congrArg (fun t => Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ t)
      h2.symm).trans (Category.assoc _ _ _).symm)
    show Spec.map (CommRingCat.ofHom w.subtype) ≫ Spec.map (CommRingCat.ofHom s) ≫ x'.left =
      Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ Spec.map (CommRingCat.ofHom w.subtype) ≫ x'.left
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
  have hpow1 : x' ^ m = 1 := by
    apply iotaΩ_comp_injective hw 𝒜
    show iotaΩ hw ≫ x' ^ m = iotaΩ hw ≫ 1
    rw [MonObj.comp_pow, hx', ← map_pow, hxm, map_one, MonObj.comp_one]
  have hpow2 : x'' ^ m = 1 := by
    apply iotaΩ_comp_injective hw 𝒜
    show iotaΩ hw ≫ x'' ^ m = iotaΩ hw ≫ 1
    rw [MonObj.comp_pow, hlift, ← map_pow, hσx, map_one, MonObj.comp_one]
  have hred : rhoΩ hw ≫ x'' = rhoΩ hw ≫ x' := by
    apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom (IsLocalRing.residue w)) ≫ Spec.map (CommRingCat.ofHom s) ≫ x'.left =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue w)) ≫ x'.left
    rw [← Category.assoc, ← Spec.map_comp, hs2]
  have heq := rhoΩ_inj hw 𝒜 m hmO x'' x' hpow2 hpow1 hred
  apply GΩ_injective 𝒜 e
  rw [← hlift, heq, hx']

end OmegaForward

end NOSProof
