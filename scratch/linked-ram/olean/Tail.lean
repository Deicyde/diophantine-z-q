import GoodRedLR

/-! # linked-ram (scratch/linked-ram/): `KernelFieldBreaks` (ii) proved; `TateRamAtThree` corrected

Section 1 (`LinkedRamWild`) is `scratch/linked-ram/test/Wild.lean` minus `import Mathlib` (Mathlib only). -/

section LinkedRamWildSec

noncomputable section

namespace LinkedRamWild

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K" => PadicAlgCl p

/-- `‖k‖ = 1` in `ℚ̄_p` for `p ∤ k`. -/
theorem norm_natCast_eq_one {k : ℕ} (hk : ¬ p ∣ k) : ‖(k : K)‖ = 1 := by
  have h1 : ‖((k : ℚ_[p]) : K)‖ = ‖(k : ℚ_[p])‖ := PadicAlgCl.norm_extends p _
  rw [map_natCast] at h1
  rw [h1, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hk

/-- A root of unity of order prime to `p` congruent to `1` is `1`. -/
theorem eq_one_of_pow_eq_one {ξ : K} {k : ℕ} (hk0 : 0 < k) (hk : ¬ p ∣ k) (hξ : ξ ^ k = 1)
    (h : ‖ξ - 1‖ < 1) : ξ = 1 := by
  by_contra hne
  have hgeom : ∑ i ∈ Finset.range k, ξ ^ i = 0 := by
    have h2 := geom_sum_mul ξ k
    rw [hξ, sub_self] at h2
    exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hne)
  have hξn : ‖ξ‖ = 1 := by
    have : ‖ξ‖ ^ k = 1 := by rw [← norm_pow, hξ, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk0.ne').mp this
  have hterm : ∀ i, ‖1 - ξ ^ i‖ < 1 := by
    intro i
    have : 1 - ξ ^ i = (1 - ξ) * ∑ j ∈ Finset.range i, ξ ^ j := by
      rw [mul_comm, geom_sum_mul_neg]
    rw [this, norm_mul, norm_sub_rev]
    have hs : ‖∑ j ∈ Finset.range i, ξ ^ j‖ ≤ 1 :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
        (fun j _ => by rw [norm_pow, hξn, one_pow])
    calc ‖ξ - 1‖ * ‖∑ j ∈ Finset.range i, ξ ^ j‖ ≤ ‖ξ - 1‖ * 1 :=
          mul_le_mul_of_nonneg_left hs (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact h
  have hk' : (k : K) = ∑ i ∈ Finset.range k, (1 - ξ ^ i) := by
    rw [Finset.sum_sub_distrib, hgeom, sub_zero]; simp
  obtain ⟨i, -, hi⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (Finset.nonempty_range_iff.mpr hk0.ne') (fun i => 1 - ξ ^ i)
  have := norm_natCast_eq_one (p := p) hk
  rw [hk'] at this
  linarith [hterm i]

/-- The wild set (as in `LadicCond.wildSet`). -/
def IsWild (σ : K ≃ₐ[ℚ_[p]] K) : Prop := ∀ x : K, x ≠ 0 → ‖σ x - x‖ < ‖x‖

theorem norm_apply (σ : K ≃ₐ[ℚ_[p]] K) (x : K) : ‖σ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ x).symm

/-- W1: a wild element fixes the roots of unity of order prime to `p`. -/
theorem wild_fix_root {σ : K ≃ₐ[ℚ_[p]] K} (hσ : IsWild σ) {ζ : K} {k : ℕ} (hk0 : 0 < k)
    (hk : ¬ p ∣ k) (hζ : ζ ^ k = 1) : σ ζ = ζ := by
  have hζ0 : ζ ≠ 0 := by rintro rfl; rw [zero_pow hk0.ne'] at hζ; exact zero_ne_one hζ
  have hξ : (σ ζ * ζ⁻¹) ^ k = 1 := by rw [mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ]; simp
  have hlt : ‖σ ζ * ζ⁻¹ - 1‖ < 1 := by
    have h1 := hσ ζ hζ0
    have : σ ζ * ζ⁻¹ - 1 = (σ ζ - ζ) * ζ⁻¹ := by field_simp
    rw [this, norm_mul, norm_inv]
    have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
    rw [mul_inv_lt_iff₀ hn, one_mul]; exact h1
  have := eq_one_of_pow_eq_one hk0 hk hξ hlt
  field_simp at this
  exact this

/-- `‖c − 1‖ ≥ 1` for a root of unity `c ≠ 1` of order prime to `p`. -/
theorem one_le_norm_sub_one {c : K} {k : ℕ} (hk0 : 0 < k) (hk : ¬ p ∣ k) (hc : c ^ k = 1)
    (hne : c ≠ 1) : 1 ≤ ‖c - 1‖ := by
  by_contra h
  exact hne (eq_one_of_pow_eq_one hk0 hk hc (lt_of_not_ge h))

/-- W2: if `σ` is wild and `σ^k y = y` with `p ∤ k`, then `σ y = y`. -/
theorem wild_fix_of_pow {σ : K ≃ₐ[ℚ_[p]] K} (hσ : IsWild σ) {k : ℕ} (hk0 : 0 < k)
    (hk : ¬ p ∣ k) {y : K} (hy : (σ ^ k) y = y) : σ y = y := by
  classical
  have : NeZero (k : K) := ⟨by exact_mod_cast hk0.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K k
  have hζfix : σ ζ = ζ := wild_fix_root hσ hk0 hk hζ.pow_eq_one
  -- the fixed field of `σ`
  let F : Subfield K := RingHom.eqLocusField σ.toAlgHom.toRingHom (RingHom.id K)
  have hF : ∀ x : F, σ (x : K) = x := fun x => x.2
  let ζF : F := ⟨ζ, hζfix⟩
  have hζF : IsPrimitiveRoot ζF k :=
    IsPrimitiveRoot.of_map_of_injective (f := F.subtype) (by exact hζ) Subtype.val_injective
  -- `σ` as an `F`-linear endomorphism of `K`
  let S : Module.End F K :=
    { toFun := σ
      map_add' := map_add σ
      map_smul' := fun c v => by
        show σ ((c : K) * v) = (c : K) * σ v
        rw [map_mul, hF c] }
  have hS : ∀ v, S v = σ v := fun _ => rfl
  have hSpow : ∀ n v, (S ^ n) v = (σ ^ n) v := by
    intro n v
    rw [Module.End.pow_apply, AlgEquiv.coe_pow]
    rfl
  have hprod := Polynomial.X_pow_sub_one_eq_prod hk0 hζF
  have h1mem : (1 : F) ∈ Polynomial.nthRootsFinset k (1 : F) :=
    (Polynomial.mem_nthRootsFinset hk0 (1 : F)).mpr (one_pow _)
  rw [← Finset.prod_erase_mul _ _ h1mem] at hprod
  have heval := congrArg (fun q => Polynomial.aeval S q) hprod
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, Polynomial.aeval_C] at heval
  have hzero : (Polynomial.aeval S (∏ c ∈ (Polynomial.nthRootsFinset k (1 : F)).erase 1,
      (Polynomial.X - Polynomial.C c))) ((S - 1) y) = 0 := by
    rw [← Module.End.mul_apply, ← heval]
    show (S ^ k) y - y = 0
    rw [hSpow, hy, sub_self]
  -- the other factors are injective
  have hfac : ∀ c ∈ (Polynomial.nthRootsFinset k (1 : F)).erase 1,
      Function.Injective (Polynomial.aeval S (Polynomial.X - Polynomial.C c)) := by
    intro c hc
    obtain ⟨hc1, hc⟩ := Finset.mem_erase.mp hc
    have hck : c ^ k = 1 := (Polynomial.mem_nthRootsFinset hk0 (1 : F)).mp hc
    have hck' : (c : K) ^ k = 1 := by rw [← SubmonoidClass.coe_pow, hck]; rfl
    have hcne : (c : K) ≠ 1 := fun h => hc1 (Subtype.ext h)
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hv' : σ v = (c : K) * v := by
      have : S v - c • v = 0 := hv
      rw [hS, sub_eq_zero] at this
      exact this
    by_contra hv0
    have h1 := hσ v hv0
    rw [hv', ← sub_one_mul, norm_mul] at h1
    have := one_le_norm_sub_one hk0 hk hck' hcne
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    nlinarith
  have hinj : Function.Injective (Polynomial.aeval S
      (∏ c ∈ (Polynomial.nthRootsFinset k (1 : F)).erase 1, (Polynomial.X - Polynomial.C c))) := by
    refine Finset.prod_induction _ (fun q : Polynomial F => Function.Injective (Polynomial.aeval S q))
      ?_ ?_ hfac
    · intro f g hf hg
      rw [map_mul, Module.End.coe_mul]
      exact hf.comp hg
    · rw [map_one, Module.End.coe_one]; exact Function.injective_id
  have h2 : (S - 1) y = 0 := by
    apply hinj
    rw [map_zero]
    exact hzero
  rw [LinearMap.sub_apply, Module.End.one_apply, hS, sub_eq_zero] at h2
  exact h2

/-- Powers of a wild element are wild. -/
theorem IsWild.pow {σ : K ≃ₐ[ℚ_[p]] K} (hσ : IsWild σ) (n : ℕ) : IsWild (σ ^ n) := by
  induction n with
  | zero => intro x hx; simpa using norm_pos_iff.mpr hx
  | succ n ih =>
    intro x hx
    rw [pow_succ, AlgEquiv.mul_apply]
    have h1 := ih x hx
    have hx' : σ x ≠ 0 := by simpa using hx
    have h2 := ih (σ x) hx'
    rw [norm_apply] at h2
    have : (σ ^ n) (σ x) - x = ((σ ^ n) (σ x) - σ x) + (σ x - x) := by ring
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h2 (hσ x hx))

/-- W4: a wild element fixes every root of a nonzero `ℚ`-polynomial of degree `< p`. -/
theorem wild_fix_of_aeval {σ : K ≃ₐ[ℚ_[p]] K} (hσ : IsWild σ) {q : Polynomial ℚ} (hq : q ≠ 0)
    (hdeg : q.natDegree < p) {y : K} (hy : Polynomial.aeval y q = 0) : σ y = y := by
  classical
  let qK := q.map (algebraMap ℚ K)
  have hqK : qK ≠ 0 := Polynomial.map_ne_zero hq
  let R := qK.roots.toFinset
  have hR : R.card < (Finset.range (q.natDegree + 1)).card := by
    rw [Finset.card_range]
    calc R.card ≤ Multiset.card qK.roots := Multiset.toFinset_card_le _
      _ ≤ qK.natDegree := Polynomial.card_roots' _
      _ = q.natDegree := Polynomial.natDegree_map _
      _ < q.natDegree + 1 := Nat.lt_succ_self _
  have hmaps : ∀ i ∈ Finset.range (q.natDegree + 1), (σ ^ i) y ∈ R := by
    intro i _
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hqK, Polynomial.IsRoot,
      Polynomial.eval_map_algebraMap]
    have : Polynomial.aeval ((σ ^ i) y) q = (σ ^ i) (Polynomial.aeval y q) :=
      Polynomial.aeval_algHom_apply (((σ ^ i).toAlgHom).restrictScalars ℚ) y q
    rw [this, hy, map_zero]
  obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hR hmaps
  rw [Finset.mem_range] at hi hj
  -- reduce to `i < j`
  have key : ∀ i j : ℕ, i < j → j < q.natDegree + 1 → (σ ^ i) y = (σ ^ j) y → σ y = y := by
    intro i j hlt hj heq
    have hk : (σ ^ (j - i)) y = y := by
      have : σ ^ j = σ ^ i * σ ^ (j - i) := by rw [← pow_add]; congr 1; omega
      rw [this, AlgEquiv.mul_apply] at heq
      exact ((σ ^ i).injective heq).symm
    refine wild_fix_of_pow hσ (k := j - i) (by omega) ?_ hk
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hj heq
  · exact key j i h hi heq.symm

/-- W5: a wild element fixes `y` with `y ^ N = 1` when `p² ∤ N`. -/
theorem wild_fix_of_pow_eq_one {σ : K ≃ₐ[ℚ_[p]] K} (hσ : IsWild σ) {N : ℕ} (hN : 0 < N)
    (hN2 : ¬ p ^ 2 ∣ N) {y : K} (hy : y ^ N = 1) : σ y = y := by
  obtain ⟨b, N', hN', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p hp.out.one_lt.ne'
  have hb : b ≤ 1 := by
    by_contra hb
    exact hN2 (Dvd.dvd.mul_right (pow_dvd_pow p (by omega)) _)
  have hN'0 : 0 < N' := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
  have hy0 : y ≠ 0 := by rintro rfl; rw [zero_pow hN.ne'] at hy; exact zero_ne_one hy
  -- `y1 = y ^ N'` is fixed
  have hy1 : σ (y ^ N') = y ^ N' := by
    have hp1 : (y ^ N') ^ p = 1 := by
      interval_cases b
      · simp at hy; rw [hy, one_pow]
      · rw [← pow_mul, mul_comm]; simpa using hy
    by_cases h1 : y ^ N' = 1
    · rw [h1, map_one]
    · refine wild_fix_of_aeval hσ (q := ∑ i ∈ Finset.range p, Polynomial.X ^ i) ?_ ?_ ?_
      · intro h0
        have := congrArg (Polynomial.eval (1 : ℚ)) h0
        simp [Polynomial.eval_finsetSum] at this
        exact hp.out.ne_zero this
      · have h := Polynomial.natDegree_sum_le_of_forall_le (Finset.range p)
          (fun i => (Polynomial.X : Polynomial ℚ) ^ i) (n := p - 1) (fun i hi => by
            rw [Polynomial.natDegree_X_pow]; have := Finset.mem_range.mp hi; omega)
        have := hp.out.one_lt
        omega
      · simp only [map_sum, map_pow, Polynomial.aeval_X]
        have h2 := geom_sum_mul (y ^ N') p
        rw [hp1, sub_self] at h2
        exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr h1)
  have hξ : (σ y * y⁻¹) ^ N' = 1 := by
    rw [mul_pow, ← map_pow, hy1, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hy0)]
  have hlt : ‖σ y * y⁻¹ - 1‖ < 1 := by
    have h1 := hσ y hy0
    have : σ y * y⁻¹ - 1 = (σ y - y) * y⁻¹ := by field_simp
    rw [this, norm_mul, norm_inv]
    have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    rw [mul_inv_lt_iff₀ hn, one_mul]; exact h1
  have := eq_one_of_pow_eq_one hN'0 hN' hξ hlt
  field_simp at this
  exact this

/-! ### Transfer to `G_ℚ` along an embedding -/

section Global



theorem pow_compat {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (e : AlgebraicClosure ℚ →+* PadicAlgCl p)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (he : ∀ x : AlgebraicClosure ℚ, e (g x) = σ (e x)) (n : ℕ) (x : AlgebraicClosure ℚ) :
    e ((g ^ n) x) = (σ ^ n) (e x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [pow_succ g n, AlgEquiv.mul_apply, ih, he, ← AlgEquiv.mul_apply, ← pow_succ]

/-- `g` fixes every element whose minimal polynomial has degree `< p`. -/
theorem fix_of_minpoly {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (e : AlgebraicClosure ℚ →+* PadicAlgCl p)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : IsWild σ) (he : ∀ x : AlgebraicClosure ℚ, e (g x) = σ (e x)) {x : AlgebraicClosure ℚ}
    (hx : (minpoly ℚ x).natDegree < p) : g x = x := by
  apply e.injective
  rw [he]
  refine wild_fix_of_aeval hσ (minpoly.ne_zero (Algebra.IsIntegral.isIntegral x)) hx ?_
  rw [show Polynomial.aeval (e x) (minpoly ℚ x) = e.toRatAlgHom (Polynomial.aeval x (minpoly ℚ x))
    from (Polynomial.aeval_algHom_apply e.toRatAlgHom x _), minpoly.aeval, map_zero]

/-- `g` fixes a finite-dimensional `L` with `[L:ℚ] < p`. -/
theorem fix_of_finrank {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (e : AlgebraicClosure ℚ →+* PadicAlgCl p)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : IsWild σ) (he : ∀ x : AlgebraicClosure ℚ, e (g x) = σ (e x))
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] (hL : Module.finrank ℚ L < p) :
    g ∈ L.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  refine fix_of_minpoly e g hσ he (lt_of_le_of_lt ?_ hL)
  rw [show x = ((⟨x, hx⟩ : L) : AlgebraicClosure ℚ) from rfl, ← IntermediateField.minpoly_eq]
  exact minpoly.natDegree_le _

/-- `g` fixes every `N`-th root of unity when `p² ∤ N`. -/
theorem fix_of_pow_eq_one {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (e : AlgebraicClosure ℚ →+* PadicAlgCl p)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : IsWild σ) (he : ∀ x : AlgebraicClosure ℚ, e (g x) = σ (e x)) {N : ℕ} (hN : 0 < N)
    (hN2 : ¬ p ^ 2 ∣ N) {y : AlgebraicClosure ℚ} (hy : y ^ N = 1) : g y = y := by
  apply e.injective
  rw [he]
  exact wild_fix_of_pow_eq_one hσ hN hN2 (by rw [← map_pow, hy, map_one])

/-- Some `p`-power of `g` fixes a finite Galois `L'`. -/
theorem pow_mem_fixing {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (e : AlgebraicClosure ℚ →+* PadicAlgCl p)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : IsWild σ) (he : ∀ x : AlgebraicClosure ℚ, e (g x) = σ (e x))
    (L' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L'] [Normal ℚ L'] :
    ∃ a : ℕ, g ^ (p ^ a) ∈ L'.fixingSubgroup := by
  let r := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) L'
  have hn : 0 < orderOf (r g) := orderOf_pos (r g)
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.out.one_lt.ne'
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hfix : g ^ orderOf (r g) ∈ L'.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  refine ⟨a, ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff] at hfix ⊢
  intro x hx
  apply e.injective
  rw [pow_compat e g he]
  refine wild_fix_of_pow (hσ.pow (p ^ a)) hm0 hm ?_
  rw [← pow_mul, ← hnm, ← pow_compat e g he, hfix x hx]

end Global

end LinkedRamWild

end

end LinkedRamWildSec

section LinkedRamMain

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace UnramTate

open G0ModField

/-- For an odd prime `p` and a set `Tm` of primes, `p² ∤ chiLevel Tm` (`lev q ∈ {q, 4}`). -/
theorem not_sq_dvd_chiLevel {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ Tm : Finset ℕ, (∀ q ∈ Tm, q.Prime) →
      (p ∉ Tm → ¬ p ∣ chiLevel Tm) ∧ ¬ p ^ 2 ∣ chiLevel Tm := by
  intro Tm
  induction Tm using Finset.induction_on with
  | empty =>
    intro _
    simp only [chiLevel, Finset.prod_empty, Nat.dvd_one]
    refine ⟨fun _ => hp.one_lt.ne', fun h => ?_⟩
    have := Nat.pow_eq_one.mp h
    rcases this with h | h
    · exact hp.one_lt.ne' h
    · omega
  | @insert a s ha ih =>
    intro hTm
    have ih' := ih (fun q hq => hTm q (Finset.mem_insert_of_mem hq))
    have haP : a.Prime := hTm a (Finset.mem_insert_self a s)
    have hcl : chiLevel (insert a s) = lev a * chiLevel s := Finset.prod_insert ha
    rw [hcl]
    by_cases hap : a = p
    · subst hap
      have hlev : lev a = a := by unfold lev; simp [hp2]
      rw [hlev]
      have hns : ¬ a ∣ chiLevel s := ih'.1 ha
      refine ⟨fun h => absurd (Finset.mem_insert_self a s) h, fun h => ?_⟩
      rw [pow_two] at h
      exact hns (Nat.dvd_of_mul_dvd_mul_left hp.pos h)
    · have hlev : ¬ p ∣ lev a := by
        unfold lev
        split_ifs with h2
        · intro h
          have : p ∣ 2 ^ 2 := by norm_num; exact h
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this))
        · intro h
          exact hap ((Nat.prime_dvd_prime_iff_eq hp haP).mp h).symm
      have hcop : Nat.Coprime (p ^ 2) (lev a) :=
        Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hlev)
      refine ⟨fun hnot h => ?_, fun h => ih'.2 (hcop.dvd_of_dvd_mul_left h)⟩
      have hps : p ∉ s := fun h' => hnot (Finset.mem_insert_of_mem h')
      rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · exact hlev h
      · exact ih'.1 hps h

/-- `T u` consists of primes. -/
theorem prime_of_mem_T {u : ℚ} {q : ℕ} (hq : q ∈ T u) : q.Prime := by
  obtain ⟨hS, -, -⟩ := admissible_S_mul
  rcases Finset.mem_union.mp hq with h | h
  · exact hS q h
  · exact Nat.prime_of_mem_primeFactors h

/-- A wild `σ` makes `decomp p σ` act trivially on `μ_N` when `p² ∤ N`, so `cyc N` is trivial. -/
theorem cyc_decomp_eq_one {p : ℕ} [Fact p.Prime] {σ : PkgI4.GQp p}
    (hσ : σ ∈ (LadicCond.wildSet : Set (PkgI4.GQp p))) {N : ℕ} [NeZero N]
    (hN2 : ¬ p ^ 2 ∣ N) : cyc N (PkgI4.decomp p σ) = 1 := by
  have hw : LinkedRamWild.IsWild σ := hσ
  have he : ∀ x, embP p (PkgI4.decomp p σ x) = σ (embP p x) := embP_decomp p σ
  have : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  have hc := modularCyclotomicCharacter.unique (L := AlgebraicClosure ℚ) (n := N)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
    (toRingAut (PkgI4.decomp p σ)) (c := 1) (fun (t : (AlgebraicClosure ℚ)ˣ) ht => by
      have ht' : (t : AlgebraicClosure ℚ) ^ N = 1 := by
        rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity N t).mp ht, Units.val_one]
      have hfix := LinkedRamWild.fix_of_pow_eq_one (embP p) (PkgI4.decomp p σ) hw he
        (Nat.pos_of_ne_zero (NeZero.ne N)) hN2 ht'
      show (PkgI4.decomp p σ) (t : AlgebraicClosure ℚ) = _
      rw [hfix]
      rcases Nat.lt_or_ge 1 N with h1 | h1
      · haveI : Fact (1 < N) := ⟨h1⟩
        rw [ZMod.val_one, pow_one]
      · have hN1 : N = 1 := by have := NeZero.ne N; omega
        subst hN1
        have : t = 1 := by
          have := (mem_rootsOfUnity 1 t).mp ht
          simpa using this
        subst this
        simp)
  apply Units.ext
  rw [Units.val_one]
  exact hc.symm

/-- **The tame half of `KernelFieldBreaks`** (its clause for `p > D`). -/
def KernelFieldBreaksHigh : Prop :=
  ∀ (u : ℚ) (P : LeafQM.AV.QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      (ZInQ.heightD : ℝ) < p → ∀ σ ∈ (LadicCond.wildSet : Set (PkgI4.GQp p)),
          PkgI4.decomp p σ ∈ GQL L'

/-- **The wild half of `KernelFieldBreaks`** (its clause for `p ≤ D`); GLUE, unchanged. -/
def KernelFieldBreaksLow : Prop :=
  ∀ (u : ℚ) (P : LeafQM.AV.QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      (p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∀ t : ℝ, G0ModNewform.U0 < t →
          ∀ σ ∈ LadicCond.upperAbs p t, PkgI4.decomp p σ ∈ GQL L'

/-- `KernelFieldBreaks` is the conjunction of its two halves. -/
theorem kernelFieldBreaks_of_halves (hL : KernelFieldBreaksLow) (hH : KernelFieldBreaksHigh) :
    KernelFieldBreaks := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD p hp
  exact ⟨hL u P L A ε N χ β L' hLL' hD p hp, hH u P L A ε N χ β L' hLL' hD p hp⟩

/-- **The `β`-step for a wild element at an odd prime** (shared by both halves): for G7 data, an
odd prime `p` and a wild `σ ∈ G_{ℚ_p}` with `decomp p σ ∈ G_L`, `decomp p σ ∈ G_{L'}`. -/
theorem mem_GQL'_of_wild {u : ℚ} {P : LeafQM.AV.QML3 Qbar} {L : IF} [FiniteDimensional ℚ L]
    [IsGalois ℚ L] {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} [FiniteDimensional ℚ L'] [IsGalois ℚ L']
    {hLL' : L ≤ L'} (hD : G7Data u P L A ε N χ β L' hLL') {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {σ : PkgI4.GQp p} (hσ : σ ∈ (LadicCond.wildSet : Set (PkgI4.GQp p)))
    (hgL : PkgI4.decomp p σ ∈ GQL L) : PkgI4.decomp p σ ∈ GQL L' := by
  have hp : p.Prime := Fact.out
  have hw : LinkedRamWild.IsWild σ := hσ
  have he : ∀ x, embP p (PkgI4.decomp p σ x) = σ (embP p x) := embP_decomp p σ
  obtain ⟨_, hDD, -, -, ⟨Tm, hTm, hNlev⟩, -, hβsq, hβmul, hL', -, -, -, -⟩ := hD
  obtain ⟨-, hinf, h11, -⟩ := hDD
  set g := PkgI4.decomp p σ with hg
  -- `β` is multiplicative on `G_L`
  have hε1 : ∀ x y : GQ, x ∈ GQL L → y ∈ GQL L → ε x y = 1 := by
    intro x y hx hy
    rw [hinf x 1 y 1 (fun z hz => (mem_GQL.mp hx z hz)) (fun z hz => (mem_GQL.mp hy z hz)), h11]
  have hβ1 : β 1 = 1 := by
    have := hβmul 1 1
    rw [h11, _root_.one_mul, _root_.mul_one] at this
    exact mul_left_cancel (this.trans (_root_.mul_one _).symm)
  have hβpow : ∀ n : ℕ, β (g ^ n) = β g ^ n := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact hβ1
    | succ n ih =>
      have h1 := hβmul (g ^ n) g
      have hx : ε (g ^ n) g = 1 := hε1 _ _ (Subgroup.pow_mem _ hgL n) hgL
      rw [hx, _root_.one_mul] at h1
      calc β (g ^ (n + 1)) = β (g ^ n * g) := congrArg β (pow_succ g n)
        _ = β (g ^ n) * β g := h1.symm
        _ = β g ^ n * β g := by rw [ih]
        _ = β g ^ (n + 1) := (pow_succ _ _).symm
  -- `χ(g) = 1`
  have hN2 : ¬ p ^ 2 ∣ N := by
    rw [hNlev]
    exact (not_sq_dvd_chiLevel hp hp2 Tm (fun q hq => prime_of_mem_T (hTm hq))).2
  have hχ : galChar χ g = 1 := by
    show χ.toUnitHom (cyc N g) = 1
    rw [cyc_decomp_eq_one hσ hN2, map_one]
  have hsq : β g ^ 2 = 1 := (hβsq g).trans hχ
  -- a `p`-power of `g` fixes `L'`
  obtain ⟨a, ha⟩ := LinkedRamWild.pow_mem_fixing (embP p) g hw he L'
  have hpa : β g ^ (p ^ a) = 1 := by
    rw [← hβpow]; exact ((hL' _).mp ha).2
  have hcop : Nat.Coprime (p ^ a) 2 := by
    apply Nat.Coprime.pow_left
    exact (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have hβg : β g = 1 := by
    have := (pow_gcd_eq_one (a := β g)).mpr ⟨hpa, hsq⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  exact (hL' g).mpr ⟨hgL, hβg⟩

/-- **`KernelFieldBreaksHigh`, proved.** For `p > D ≥ [L:ℚ]`, a wild `σ` fixes `L` (orbits of
size `< p`), acts trivially on `μ_N` (`p² ∤ N`), so `β(decomp σ)² = χ(decomp σ) = 1`; and some
`p`-power of `decomp σ` fixes `L'`, so `β(decomp σ)^{p^a} = 1`; `p` is odd, so `β(decomp σ) = 1`. -/
theorem kernelFieldBreaksHigh : KernelFieldBreaksHigh := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro hpD σ hσ
  have hw : LinkedRamWild.IsWild σ := hσ
  have he : ∀ x, embP p (PkgI4.decomp p σ x) = σ (embP p x) := embP_decomp p σ
  have h3 := three_le_heightD
  have hp2 : p ≠ 2 := by
    rintro rfl; push_cast at hpD; linarith
  have hLp : Module.finrank ℚ L < p := by
    have : (Module.finrank ℚ L : ℝ) < p := lt_of_le_of_lt (by exact_mod_cast hD.2.2.2.2.2.2.2.2.2.2.2.2) hpD
    exact_mod_cast this
  exact mem_GQL'_of_wild hD hp2 hσ (LinkedRamWild.fix_of_finrank (embP p) _ hw he L hLp)

/-! ### The wild half: reduced to a local break bound, wildness of upper groups, and `p = 2` -/

/-- **Leaf candidate (LEAF?, textbook composite): the absolute break bound** (Glazer's
manuscript L796-811, from Serre, *Local Fields*, Ch. III §6 (different bound
`δ ≤ e − 1 + e·v_p(e)`) and Ch. IV §1-§3 (Hilbert's formula `δ = Σ_{i≥0}(|G_i| − 1)`, Herbrand's
function); numbering UNVERIFIED): for a finite extension `F/ℚ_p` of degree `a` inside `ℚ̄_p`, every
element of the absolute upper ramification group `G_{ℚ_p}^u` with `u > 4a²` fixes `F` pointwise.
(The normal closure has degree `≤ a!`; its last upper break is `≤ 2δ/e ≤ 2(1 + log₂ a!) ≤ 4a²`.)
Stated over `LadicCond`'s definitions of `G_{ℚ_p}^u` (Serre IV §3). -/
def UpperBreakBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : LadicCond.Fld p) [FiniteDimensional ℚ_[p] F] (u : ℝ),
    4 * (Module.finrank ℚ_[p] F : ℝ) ^ 2 < u →
      ∀ σ ∈ LadicCond.upperAbs p u, ∀ x ∈ F, σ x = x

/-- **Glue (definitions): positive upper groups are wild.** For `u > 0`, `G_{ℚ_p}^u ⊆ P_p`
(`ψ(u) ≥ u > 0`, so `G^u(M) ⊆ G_1(M)` at every finite Galois level `M`; Serre IV §3). -/
def UpperAbsWild : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (u : ℝ), 0 < u →
    LadicCond.upperAbs p u ⊆ (LadicCond.wildSet : Set (PkgI4.GQp p))

/-- **Glue: `β` on high upper groups at `2`** (Glazer L826-843: local reciprocity, the
`2`-primary factor of `χ` has conductor `≤ 4`, the logarithm on `U_F^{e+1}`, and
`ψ_{F/ℚ_2}(u) ≥ u`). For G7 data and `u > U₀`, `β(decomp₂ σ) = 1` for `σ ∈ G_{ℚ_2}^u` with
`decomp₂ σ ∈ G_L`. GLUE (truth: STANDARD route, Glazer's argument). -/
def BetaTrivialAtTwo : Prop :=
  ∀ (u : ℚ) (P : LeafQM.AV.QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
    ∀ t : ℝ, G0ModNewform.U0 < t → ∀ σ ∈ LadicCond.upperAbs 2 t,
      PkgI4.decomp 2 σ ∈ GQL L → β (PkgI4.decomp 2 σ) = 1

/-- `4 D² < U₀ = 4 (D G₀)²`. -/
theorem four_D_sq_lt_U0 : 4 * ((ZInQ.heightD : ℕ) : ℝ) ^ 2 < G0ModNewform.U0 := by
  unfold G0ModNewform.U0
  have hD : (1 : ℝ) ≤ (ZInQ.heightD : ℝ) := by
    have := three_le_heightD; linarith
  have hG : (2 : ℝ) ≤ (ZInQ.heightG0 : ℝ) := by
    unfold ZInQ.heightG0; norm_num
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hG (show (0 : ℝ) ≤ ZInQ.heightD by linarith)]

/-- **High upper groups fix a number field of degree `≤ D`** (from `UpperBreakBound`): for
`x ∈ L`, `F = ℚ_p(embP x)` has degree `≤ deg minpoly_ℚ x ≤ [L:ℚ] ≤ D`, and `4D² < U₀`. -/
theorem decomp_mem_GQL_of_breaks (hB : UpperBreakBound) {p : ℕ} [Fact p.Prime] (L : IF)
    [FiniteDimensional ℚ L] (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) {t : ℝ}
    (ht : G0ModNewform.U0 < t) {σ : PkgI4.GQp p} (hσ : σ ∈ LadicCond.upperAbs p t) :
    PkgI4.decomp p σ ∈ GQL L := by
  refine (mem_GQL (σ := PkgI4.decomp p σ)).mpr ?_
  intro x hx
  apply (embP p).injective
  rw [show act (PkgI4.decomp p σ) x = PkgI4.decomp p σ x from rfl, embP_decomp]
  let y : PadicAlgCl p := embP p x
  have hyint : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral y
  let F : LadicCond.Fld p := IntermediateField.adjoin ℚ_[p] {y}
  haveI : FiniteDimensional ℚ_[p] F := IntermediateField.adjoin.finiteDimensional hyint
  have hdeg : Module.finrank ℚ_[p] F ≤ ZInQ.heightD := by
    have h1 : Module.finrank ℚ_[p] F = (minpoly ℚ_[p] y).natDegree :=
      IntermediateField.adjoin.finrank hyint
    have hq0 : (minpoly ℚ x).map (algebraMap ℚ ℚ_[p]) ≠ 0 :=
      Polynomial.map_ne_zero (minpoly.ne_zero (Algebra.IsIntegral.isIntegral x))
    have h2 : minpoly ℚ_[p] y ∣ (minpoly ℚ x).map (algebraMap ℚ ℚ_[p]) := by
      apply minpoly.dvd
      rw [Polynomial.aeval_map_algebraMap]
      rw [show Polynomial.aeval y (minpoly ℚ x) = (embP p).toRatAlgHom (Polynomial.aeval x (minpoly ℚ x))
        from Polynomial.aeval_algHom_apply (embP p).toRatAlgHom x _, minpoly.aeval, map_zero]
    have h3 : (minpoly ℚ x).natDegree ≤ Module.finrank ℚ L := by
      rw [show x = ((⟨x, hx⟩ : L) : Qbar) from rfl, ← IntermediateField.minpoly_eq]
      exact minpoly.natDegree_le _
    rw [h1]
    calc (minpoly ℚ_[p] y).natDegree ≤ ((minpoly ℚ x).map (algebraMap ℚ ℚ_[p])).natDegree :=
          Polynomial.natDegree_le_of_dvd h2 hq0
      _ = (minpoly ℚ x).natDegree := Polynomial.natDegree_map _
      _ ≤ Module.finrank ℚ L := h3
      _ ≤ ZInQ.heightD := hLD
  have hlt : 4 * (Module.finrank ℚ_[p] F : ℝ) ^ 2 < t := by
    refine lt_of_le_of_lt ?_ (lt_trans four_D_sq_lt_U0 ht)
    have : (Module.finrank ℚ_[p] F : ℝ) ≤ (ZInQ.heightD : ℝ) := by exact_mod_cast hdeg
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) this 2) (by norm_num)
  exact hB p F t hlt σ hσ y (IntermediateField.mem_adjoin_simple_self ℚ_[p] y)

/-- **`KernelFieldBreaksLow` from the break bound, wildness of positive upper groups, and the
prime `2`.** -/
theorem kernelFieldBreaksLow_of (hB : UpperBreakBound) (hW : UpperAbsWild)
    (h2 : BetaTrivialAtTwo) : KernelFieldBreaksLow := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro _ t ht σ hσ
  have hgL : PkgI4.decomp p σ ∈ GQL L :=
    decomp_mem_GQL_of_breaks hB L hD.2.2.2.2.2.2.2.2.2.2.2.2 ht hσ
  by_cases hp2 : p = 2
  · subst hp2
    have hβ := h2 u P L A ε N χ β L' hLL' hD t ht σ hσ hgL
    exact (hD.2.2.2.2.2.2.2.2.1 _).mpr ⟨hgL, hβ⟩
  · have hU0 : 0 < t := lt_of_le_of_lt U0_nonneg ht
    exact mem_GQL'_of_wild hD hp2 (hW p t hU0 hσ) hgL

/-- **`KernelFieldBreaks` from `UpperBreakBound`, `UpperAbsWild`, `BetaTrivialAtTwo`.** -/
theorem kernelFieldBreaks_of (hB : UpperBreakBound) (hW : UpperAbsWild)
    (h2 : BetaTrivialAtTwo) : KernelFieldBreaks :=
  kernelFieldBreaks_of_halves (kernelFieldBreaksLow_of hB hW h2) kernelFieldBreaksHigh

/-! ### `UpperAbsWild`, proved -/

section UpperWild

open LadicCond

variable {p : ℕ} [Fact p.Prime]

theorem restr_image_finite (M : Fld p) [FiniteDimensional ℚ_[p] M] (S : Set (PkgI4.GQp p)) :
    (restr M '' S).Finite := by
  apply Set.Finite.subset (Set.finite_range (fun f : M →ₐ[ℚ_[p]] Kbar p => (f : M → Kbar p)))
  rintro _ ⟨σ, -, rfl⟩
  exact ⟨(σ.toAlgHom).comp M.val, rfl⟩

theorem ramSet_anti (M : Fld p) {i j : ℕ} (hij : i ≤ j) : ramSet M j ⊆ ramSet M i := by
  rintro σ ⟨ϖ, hϖ, h⟩
  refine ⟨ϖ, hϖ, fun x hx hx1 => (h x hx hx1).trans ?_⟩
  exact pow_le_pow_of_le_one (norm_nonneg _) hϖ.2.1.le (by omega)

theorem ramSetR_anti (M : Fld p) {s t : ℝ} (hst : s ≤ t) : ramSetR M t ⊆ ramSetR M s := by
  unfold ramSetR
  split_ifs with ht hs hs
  · exact le_rfl
  · exact absurd (hst.trans ht) hs
  · exact Set.subset_univ _
  · exact ramSet_anti M (Int.toNat_le_toNat (Int.ceil_mono hst))

theorem ramSetR_sub_zero (M : Fld p) {t : ℝ} (ht : -1 < t) : ramSetR M t ⊆ ramSet M 0 := by
  unfold ramSetR
  rw [if_neg (by linarith)]
  exact ramSet_anti M (Nat.zero_le _)

theorem one_mem_ramSetR (M : Fld p) {ϖ : Kbar p} (hϖ : IsUnif M ϖ) (t : ℝ) :
    (1 : PkgI4.GQp p) ∈ ramSetR M t := by
  unfold ramSetR
  split_ifs
  · exact Set.mem_univ _
  · exact ⟨ϖ, hϖ, fun x _ _ => by simp⟩

theorem one_le_ramCardR (M : Fld p) [FiniteDimensional ℚ_[p] M] {ϖ : Kbar p} (hϖ : IsUnif M ϖ)
    (t : ℝ) : 1 ≤ ramCardR M t := by
  have hfin := restr_image_finite M (ramSetR M t)
  have hne : (restr M '' ramSetR M t).Nonempty := ⟨restr M 1, 1, one_mem_ramSetR M hϖ t, rfl⟩
  haveI := hfin.to_subtype
  haveI := hne.to_subtype
  exact Nat.card_pos

theorem ramCardR_le (M : Fld p) [FiniteDimensional ℚ_[p] M] {t : ℝ} (ht : -1 < t) :
    ramCardR M t ≤ ramCard M 0 :=
  Nat.card_mono (restr_image_finite M _) (Set.image_mono (ramSetR_sub_zero M ht))

theorem ramCardR_zero (M : Fld p) : ramCardR M 0 = ramCard M 0 := by
  unfold ramCardR ramCard ramSetR
  rw [if_neg (by norm_num)]
  simp

theorem integrand_anti (M : Fld p) [FiniteDimensional ℚ_[p] M] :
    Antitone (fun t : ℝ => (ramCardR M t : ℝ) / (ramCard M 0 : ℝ)) := by
  intro s t hst
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Nat.card_mono (restr_image_finite M _) (Set.image_mono (ramSetR_anti M hst))

theorem phiAt_le_self (M : Fld p) [FiniteDimensional ℚ_[p] M] {ϖ : Kbar p} (hϖ : IsUnif M ϖ)
    {v : ℝ} (hv : 0 ≤ v) : phiAt M v ≤ v := by
  have hg0 : 0 < (ramCard M 0 : ℝ) := by
    rw [← ramCardR_zero]; exact_mod_cast one_le_ramCardR M hϖ 0
  unfold phiAt
  calc ∫ t in (0 : ℝ)..v, (ramCardR M t : ℝ) / (ramCard M 0 : ℝ)
      ≤ ∫ t in (0 : ℝ)..v, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on hv ((integrand_anti M).intervalIntegrable)
          intervalIntegrable_const
        intro t ht
        rw [div_le_one hg0]
        exact_mod_cast ramCardR_le M (by linarith [ht.1])
    _ = v := by simp

theorem le_phiAt (M : Fld p) [FiniteDimensional ℚ_[p] M] {ϖ : Kbar p} (hϖ : IsUnif M ϖ)
    {v : ℝ} (hv : 0 ≤ v) : v / (ramCard M 0 : ℝ) ≤ phiAt M v := by
  have hg0 : 0 < (ramCard M 0 : ℝ) := by
    rw [← ramCardR_zero]; exact_mod_cast one_le_ramCardR M hϖ 0
  unfold phiAt
  calc v / (ramCard M 0 : ℝ) = ∫ t in (0 : ℝ)..v, (1 : ℝ) / (ramCard M 0 : ℝ) := by simp [div_eq_mul_inv]
    _ ≤ ∫ t in (0 : ℝ)..v, (ramCardR M t : ℝ) / (ramCard M 0 : ℝ) := by
        apply intervalIntegral.integral_mono_on hv intervalIntegrable_const
          ((integrand_anti M).intervalIntegrable)
        intro t _
        apply div_le_div_of_nonneg_right _ hg0.le
        exact_mod_cast one_le_ramCardR M hϖ t

/-- Elements `z` with `‖z − 1‖ < 1` are closed under products and integer powers. -/
theorem norm_mul_sub_one_lt {a b : Kbar p} (ha : ‖a - 1‖ < 1) (hb : ‖b - 1‖ < 1) :
    ‖a * b - 1‖ < 1 := by
  have hna : ‖a‖ = 1 := by
    have : a = (a - 1) + 1 := by ring
    rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact ha.ne)]
    simp [ha.le]
  have : a * b - 1 = a * (b - 1) + (a - 1) := by ring
  rw [this]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ha)
  rw [norm_mul, hna, _root_.one_mul]; exact hb

theorem norm_pow_sub_one_lt {a : Kbar p} (ha : ‖a - 1‖ < 1) (n : ℕ) : ‖a ^ n - 1‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact norm_mul_sub_one_lt ih ha

theorem norm_inv_sub_one_lt {a : Kbar p} (ha : ‖a - 1‖ < 1) : ‖a⁻¹ - 1‖ < 1 := by
  have hna : ‖a‖ = 1 := by
    have : a = (a - 1) + 1 := by ring
    rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact ha.ne)]
    simp [ha.le]
  have ha0 : a ≠ 0 := by rintro rfl; simp at hna
  have : a⁻¹ - 1 = (1 - a) * a⁻¹ := by field_simp
  rw [this, norm_mul, norm_inv, hna, inv_one, _root_.mul_one, norm_sub_rev]; exact ha

theorem norm_zpow_sub_one_lt {a : Kbar p} (ha : ‖a - 1‖ < 1) (k : ℤ) : ‖a ^ k - 1‖ < 1 := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]; exact norm_pow_sub_one_lt ha n
  · rw [zpow_neg, zpow_natCast]; exact norm_inv_sub_one_lt (norm_pow_sub_one_lt ha n)

/-- In `M` with uniformizer `ϖ`, every nonzero absolute value is a power of `‖ϖ‖`. -/
theorem norm_eq_zpow (M : Fld p) {ϖ : Kbar p} (hϖ : IsUnif M ϖ) (hr0 : 0 < ‖ϖ‖) {x : Kbar p}
    (hx : x ∈ M) (hx0 : x ≠ 0) : ∃ k : ℤ, ‖x‖ = ‖ϖ‖ ^ k := by
  set r := ‖ϖ‖ with hr
  have hr1 : r < 1 := hϖ.2.1
  have hϖ0 : ϖ ≠ 0 := norm_pos_iff.mp hr0
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow (norm_pos_iff.mpr hx0) (one_lt_inv_iff₀.mpr ⟨hr0, hr1⟩)
  refine ⟨-(n + 1), ?_⟩
  have h1 : r ^ (-n) < ‖x‖ := by rw [← inv_zpow']; exact hn1
  have h2 : ‖x‖ ≤ r ^ (-(n + 1)) := by rw [← inv_zpow']; exact hn2
  by_contra hne
  have hlt : ‖x‖ < r ^ (-(n + 1)) := lt_of_le_of_ne h2 hne
  let z := x * ϖ ^ (n + 1)
  have hz : z ∈ M := M.mul_mem hx (zpow_mem hϖ.1 _)
  have hzn : ‖z‖ = ‖x‖ * r ^ (n + 1) := by rw [norm_mul, norm_zpow]
  have hpos : 0 < r ^ (n + 1) := zpow_pos hr0 _
  have hz1 : ‖z‖ < 1 := by
    rw [hzn]
    calc ‖x‖ * r ^ (n + 1) < r ^ (-(n + 1)) * r ^ (n + 1) := mul_lt_mul_of_pos_right hlt hpos
      _ = 1 := by rw [← zpow_add₀ hr0.ne']; simp
  have hzr : r < ‖z‖ := by
    rw [hzn]
    calc r = r ^ (-n) * r ^ (n + 1) := by rw [← zpow_add₀ hr0.ne']; simp
      _ < ‖x‖ * r ^ (n + 1) := mul_lt_mul_of_pos_right h1 hpos
  exact absurd (hϖ.2.2 z hz hz1) (not_le.mpr hzr)

/-- At a level `M` with `σ ∈ G_1(M)`, `σ` is wild on `M`. -/
theorem wild_on_of_ramSet (M : Fld p) {ϖ : Kbar p} (hϖ : IsUnif M ϖ) {σ : PkgI4.GQp p}
    (hle : ∀ y ∈ M, ‖y‖ ≤ 1 → ‖σ y - y‖ ≤ ‖ϖ‖ ^ 2) :
    ∀ x ∈ M, x ≠ 0 → ‖σ x - x‖ < ‖x‖ := by
  set r := ‖ϖ‖ with hr
  have hr1 : r < 1 := hϖ.2.1
  have hr0 : 0 < r := by
    have hpM : ((p : ℚ_[p]) : Kbar p) ∈ M := M.algebraMap_mem _
    have hpn : ‖((p : ℚ_[p]) : Kbar p)‖ = (p : ℝ)⁻¹ := by
      rw [PadicAlgCl.norm_extends, Padic.norm_p]
    have hp1 : ‖((p : ℚ_[p]) : Kbar p)‖ < 1 := by
      rw [hpn]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    have := hϖ.2.2 _ hpM hp1
    rw [hpn] at this
    exact lt_of_lt_of_le (inv_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)) this
  have hϖ0 : ϖ ≠ 0 := norm_pos_iff.mp hr0
  intro x hx hx0
  obtain ⟨k, hk⟩ := norm_eq_zpow M hϖ hr0 hx hx0
  let w := x * ϖ ^ (-k)
  have hwM : w ∈ M := M.mul_mem hx (zpow_mem hϖ.1 _)
  have hw1 : ‖w‖ = 1 := by
    rw [norm_mul, norm_zpow, hk, ← zpow_add₀ hr0.ne']; simp
  have hw0 : w ≠ 0 := by rintro h; rw [h, norm_zero] at hw1; exact zero_ne_one hw1
  have hxw : x = w * ϖ ^ k := by
    show x = x * ϖ ^ (-k) * ϖ ^ k
    rw [_root_.mul_assoc, ← zpow_add₀ hϖ0]; simp
  have hb : ‖σ w * w⁻¹ - 1‖ < 1 := by
    have : σ w * w⁻¹ - 1 = (σ w - w) * w⁻¹ := by field_simp
    rw [this, norm_mul, norm_inv, hw1, inv_one, _root_.mul_one]
    exact lt_of_le_of_lt (hle w hwM hw1.le) (pow_lt_one₀ hr0.le hr1 (by norm_num))
  have ha : ‖σ ϖ * ϖ⁻¹ - 1‖ < 1 := by
    have : σ ϖ * ϖ⁻¹ - 1 = (σ ϖ - ϖ) * ϖ⁻¹ := by field_simp
    rw [this, norm_mul, norm_inv, ← hr]
    have h := hle ϖ hϖ.1 hr1.le
    calc ‖σ ϖ - ϖ‖ * r⁻¹ ≤ r ^ 2 * r⁻¹ := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hr0.le)
      _ = r := by field_simp
      _ < 1 := hr1
  have hq : σ x * x⁻¹ = (σ w * w⁻¹) * (σ ϖ * ϖ⁻¹) ^ k := by
    rw [hxw, map_mul, map_zpow₀, mul_zpow, mul_inv, inv_zpow]
    field_simp
  have hlt : ‖σ x * x⁻¹ - 1‖ < 1 := by
    rw [hq]; exact norm_mul_sub_one_lt hb (norm_zpow_sub_one_lt ha k)
  have : σ x - x = (σ x * x⁻¹ - 1) * x := by field_simp
  rw [this, norm_mul]
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  calc ‖σ x * x⁻¹ - 1‖ * ‖x‖ < 1 * ‖x‖ := mul_lt_mul_of_pos_right hlt hxn
    _ = ‖x‖ := _root_.one_mul _

/-- Positive upper groups lie in `G_1` at every finite level, hence act wildly there. -/
theorem upperSet_wild (M : Fld p) [FiniteDimensional ℚ_[p] M] {u : ℝ} (hu : 0 < u)
    {σ : PkgI4.GQp p} (hσ : σ ∈ upperSet M u) : ∀ x ∈ M, x ≠ 0 → ‖σ x - x‖ < ‖x‖ := by
  have h0 := sInf_nonneg_of_pos M hu
  unfold upperSet ramSetR at hσ
  rw [if_neg (show ¬ _ ≤ (-1 : ℝ) by linarith)] at hσ
  obtain ⟨ϖ, hϖ, hle⟩ := hσ
  have hg0 : 0 < (ramCard M 0 : ℝ) := by
    rw [← ramCardR_zero]; exact_mod_cast one_le_ramCardR M hϖ 0
  have hne : {v : ℝ | -1 ≤ v ∧ u ≤ phiAt M v}.Nonempty := by
    refine ⟨u * ramCard M 0, by nlinarith, ?_⟩
    have := le_phiAt M hϖ (v := u * ramCard M 0) (by positivity)
    rwa [mul_div_assoc, div_self hg0.ne', _root_.mul_one] at this
  have hS : u ≤ sInf {v : ℝ | -1 ≤ v ∧ u ≤ phiAt M v} := by
    apply le_csInf hne
    rintro v ⟨-, hv⟩
    by_cases hv0 : v ≤ 0
    · have := phiAt_nonpos M hv0; linarith
    · exact hv.trans (phiAt_le_self M hϖ (le_of_lt (not_le.mp hv0)))
  have hn : 1 ≤ ⌈sInf {v : ℝ | -1 ≤ v ∧ u ≤ phiAt M v}⌉.toNat := by
    have : (0 : ℝ) < sInf {v : ℝ | -1 ≤ v ∧ u ≤ phiAt M v} := lt_of_lt_of_le hu hS
    have : (0 : ℤ) < ⌈sInf {v : ℝ | -1 ≤ v ∧ u ≤ phiAt M v}⌉ := Int.ceil_pos.mpr this
    omega
  apply wild_on_of_ramSet M hϖ
  intro y hy hy1
  refine (hle y hy hy1).trans ?_
  exact pow_le_pow_of_le_one (norm_nonneg _) hϖ.2.1.le (by omega)

end UpperWild

/-- **`UpperAbsWild`, proved.** -/
theorem upperAbsWild : UpperAbsWild := by
  intro p _ u hu σ hσ x hx
  let K : LadicCond.Fld p := IntermediateField.adjoin ℚ_[p] {x}
  haveI hKfin : FiniteDimensional ℚ_[p] K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  let M : LadicCond.Fld p := IntermediateField.normalClosure ℚ_[p] K (LadicCond.Kbar p)
  have hM : LadicCond.IsFinGal M := ⟨inferInstance, inferInstance⟩
  have hxM : x ∈ M :=
    IntermediateField.le_normalClosure K (IntermediateField.mem_adjoin_simple_self ℚ_[p] x)
  haveI : FiniteDimensional ℚ_[p] M := hM.1
  exact upperSet_wild M hu (hσ M hM) x hxM hx

/-- **`KernelFieldBreaks` from `UpperBreakBound` and `BetaTrivialAtTwo`** (`UpperAbsWild` proved). -/
theorem kernelFieldBreaks_of' (hB : UpperBreakBound) (h2 : BetaTrivialAtTwo) : KernelFieldBreaks :=
  kernelFieldBreaks_of_halves (kernelFieldBreaksLow_of hB upperAbsWild h2) kernelFieldBreaksHigh

/-! ### `TateRamAtThree`, corrected -/

/-- **Glue: the Tate module of the QM model at `p = 3`, with `[L:ℚ] ≤ D`** (linked-tate's
`TateRamAtThree` with the degree bound that `G7Data` carries; Glazer L814-821: over
`F = L_v(A[5])`, of degree `≤ D·|GL₄(𝔽₅)| = D G₀`, Raynaud's criterion gives semistable reduction,
wild inertia acts trivially on `V₅`, and `G_{ℚ_3}^t ⊆ G_F ∩ P_3` for `t > U₀ = 4(DG₀)²`). GLUE. -/
def TateRamAtThreeD : Prop :=
  ∀ (K L L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hKL : K ≤ L) (hLL' : L ≤ L')
    (PK : LeafQM.AV.QML3 K), Module.finrank ℚ L ≤ ZInQ.heightD →
    letI : NumberField L' := numberField_of_fd L'
    ∀ t : ℝ, G0ModNewform.U0 < t → ∀ σ ∈ LadicCond.upperAbs 3 t,
      ∀ σ' : Field.absoluteGaloisGroup L', G0Galois.resQ L' σ' = PkgI4.decomp 3 σ →
        G0Galois.tate (@PkgI3.AbVar.baseChange L _
          (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) 5 σ' = 1

/-- The old form implies the corrected one. -/
theorem tateRamAtThreeD_of (h : TateRamAtThree) : TateRamAtThreeD :=
  fun K L L' _ _ hKL hLL' PK _ => h K L L' hKL hLL' PK

/-- **`LinkedRam`, proved** from G3, `KernelFieldBreaks`, the two proved Mathlib Props and the
corrected `TateRamAtThreeD` (linked-tate's `linkedRam_of`, with `[L:ℚ] ≤ D` taken from `G7Data`). -/
theorem linkedRam_of' (hG3 : HSyn.LinkedTate.QMModelG3) (hK : KernelFieldBreaks)
    (hLI : LocalInertiaGlobal) (hUI : UpperAbsInertia) (h3 : TateRamAtThreeD) : LinkedRam := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD Θ h hΘ m a n d h1 h2 hmL h4 h5 h6 h7 h8
    gam g0 g1 g2 g3 hgam1 j5 j3
  haveI hNF : NumberField L' := numberField_of_fd L'
  have hK' := hK u P L A ε N χ β L' hLL' hD
  have hLD : Module.finrank ℚ L ≤ ZInQ.heightD := hD.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨K, hKL, PK, -, rfl⟩ := hD.1
  have hnorm : (L'.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
  -- on `G_{L'}`, `ρ` is the Tate action
  have hρ : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (g : PkgI4.GQ),
      g ∈ GQL L' →
      (∀ σ'' : Field.absoluteGaloisGroup L', G0Galois.resQ L' σ'' = g →
        G0Galois.tate (@PkgI3.AbVar.baseChange L _
          (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) ℓ σ'' = 1) →
      GlueDescent.rho (tmOf hLL' _ Θ h m ℓ) (fun _ => j 1) (fun g => j (gam (h * g * h⁻¹))) g
        = 1 := by
    intro ℓ _ j g hg ht
    obtain ⟨σ'', hσ''⟩ : g ∈ (@GaloisCopy.resQ L' _ hNF).range := by
      rw [resQRange L']; exact hg
    subst hσ''
    have hcj : h * (@GaloisCopy.resQ L' _ hNF σ'') * h⁻¹ ∈ GQL L' := hnorm.conj_mem _ hg h
    unfold GlueDescent.rho
    rw [tmOf_resQ hLL' _ Θ h hΘ m hmL ℓ σ'']
    have ht' : GaloisCopy.tate (@PkgI3.AbVar.baseChange L _
        (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) ℓ σ'' = 1 :=
      ht σ'' rfl
    have hγ : gam (h * (@GaloisCopy.resQ L' _ hNF σ'') * h⁻¹) = 1 := hgam1 _ hcj
    rw [ht']
    show ((j (gam (h * (@GaloisCopy.resQ L' _ hNF σ'') * h⁻¹)))⁻¹ * j 1) • (1 : Module.End _ _) = 1
    rw [hγ, map_one, inv_one, _root_.one_mul, one_smul]
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  have hG5 := hG3 K L L' hKL hLL' PK 5
  have hG3' := hG3 K L L' hKL hLL' PK 3
  refine ⟨fun hp5 => ⟨fun hpD t ht σ hσ => ?_, fun hpD σ hσ => ?_⟩,
    fun hp5 => ⟨fun hpD t ht σ hσ => ?_, fun hpD σ hσ => ?_⟩⟩
  · -- `ρ₅`, `p ≠ 5`, `p ≤ D`
    have hσI := hUI p t (lt_of_le_of_lt U0_nonneg ht) hσ
    refine hρ 5 j5 _ ((hK' p hp).1 hpD t ht σ hσ) (fun σ'' hσ'' => ?_)
    by_cases hp3 : p = 3
    · subst hp3
      exact h3 K L L' hKL hLL' PK hLD t ht σ hσ σ'' hσ''
    · exact tate_trivial_of_g3 hLI hG5 p hp3 hp5 σ hσI σ'' hσ''
  · -- `ρ₅`, `p ≠ 5`, `p > D`
    have hσI := LadicCond.wildSet_subset_inertiaSet hσ
    have hp3 : p ≠ 3 := by
      intro h3'
      subst h3'
      have := three_le_heightD
      push_cast at hpD
      linarith
    exact hρ 5 j5 _ ((hK' p hp).2 hpD σ hσ)
      (fun σ'' hσ'' => tate_trivial_of_g3 hLI hG5 p hp3 hp5 σ hσI σ'' hσ'')
  · -- `ρ₃`, `p = 5`, `p ≤ D`
    have hσI := hUI p t (lt_of_le_of_lt U0_nonneg ht) hσ
    have hp3 : p ≠ 3 := by omega
    exact hρ 3 j3 _ ((hK' p hp).1 hpD t ht σ hσ)
      (fun σ'' hσ'' => tate_trivial_of_g3 hLI hG3' p hp3 hp3 σ hσI σ'' hσ'')
  · -- `ρ₃`, `p = 5`, `p > D`
    have hσI := LadicCond.wildSet_subset_inertiaSet hσ
    have hp3 : p ≠ 3 := by omega
    exact hρ 3 j3 _ ((hK' p hp).2 hpD σ hσ)
      (fun σ'' hσ'' => tate_trivial_of_g3 hLI hG3' p hp3 hp3 σ hσI σ'' hσ'')

/-! ### `TateRamAtThreeD` reduced to Raynaud's criterion at `3` on the model -/

section TateRam

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- Compatibility with an isomorphism `ψ : K̄ ≅ ℚ̄` passes to powers. -/
theorem psi_pow_compat {K : Type} [Field K] (ψ : AlgebraicClosure K ≃+* PkgI4.Qbar)
    (σK : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (h : ∀ y, ψ (σK y) = g (ψ y)) (n : ℕ) (y : AlgebraicClosure K) :
    ψ ((σK ^ n) y) = (g ^ n) (ψ y) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => rw [pow_succ σK n, AlgEquiv.mul_apply, ih, h, ← AlgEquiv.mul_apply, ← pow_succ]

/-- **Points: a `k`-th power with `p ∤ k` fixing a point forces the element itself to fix it**,
for `σK ∈ G_K` matching a wild `σ ∈ G_{ℚ_p}` under some `ψ : K̄ ≅ ℚ̄`. The stabilizer `S` of the
point is open (`PkgI3.RhoCont`), hence closed, so `S = G_{K̄^S}`; `σK^k` fixes `K̄^S`, and W2 moves
this to `σK`. -/
theorem fix_of_pow_fix {K : Type} [Field K] [CharZero K] (A : PkgI3.AbVar K)
    (ψ : AlgebraicClosure K ≃+* PkgI4.Qbar) (σK : Field.absoluteGaloisGroup K)
    {p : ℕ} [Fact p.Prime] (σ : PkgI4.GQp p) (hσ : σ ∈ (LadicCond.wildSet : Set (PkgI4.GQp p)))
    (hc : ∀ y, ψ (σK y) = PkgI4.decomp p σ (ψ y)) {k : ℕ} (hk0 : 0 < k) (hk : ¬ p ∣ k)
    (x : A.Pt (AlgebraicClosure K)) (hx : A.galAct (σK ^ k) x = x) : A.galAct σK x = x := by
  haveI : IsGalois K (AlgebraicClosure K) := {}
  have hone : A.galAct (1 : Field.absoluteGaloisGroup K) x = x := by
    show PkgI3.AbVar.galHom 1 ≫ x = x
    rw [PkgI3.AbVar.galHom_one, Category.id_comp]
  obtain ⟨U, hU⟩ := PkgI3.RhoCont.exists_openSubgroup_galAct_eq A x
  let S : Subgroup (Field.absoluteGaloisGroup K) :=
    { carrier := {g | A.galAct g x = x}
      mul_mem' := fun {a b} ha hb => by
        show A.galAct (a * b) x = x
        rw [PkgI3.RhoCont.galAct_mul, show A.galAct b x = x from hb, show A.galAct a x = x from ha]
      one_mem' := hone
      inv_mem' := fun {a} ha => by
        show A.galAct a⁻¹ x = x
        have ha' : A.galAct a x = x := ha
        conv_lhs => rw [← ha']
        rw [← PkgI3.RhoCont.galAct_mul, inv_mul_cancel, hone] }
  have hSopen : IsOpen (S : Set (Field.absoluteGaloisGroup K)) :=
    Subgroup.isOpen_mono (H₁ := U.toSubgroup) (fun g hg => hU g hg) U.isOpen
  have hSclosed : IsClosed (S : Set (Field.absoluteGaloisGroup K)) :=
    Subgroup.isClosed_of_isOpen S hSopen
  have hfix := InfiniteGalois.fixingSubgroup_fixedField (⟨S, hSclosed⟩ : ClosedSubgroup _)
  have hk' : σK ^ k ∈ S := hx
  have hmem : σK ∈ (IntermediateField.fixedField S).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hyk : (σK ^ k) y = y := (IntermediateField.mem_fixedField_iff S y).mp hy _ hk'
    apply ψ.injective
    rw [hc]
    have he : ∀ z, embP p (PkgI4.decomp p σ z) = σ (embP p z) := embP_decomp p σ
    have h1 : (PkgI4.decomp p σ ^ k) (ψ y) = ψ y := by
      rw [← psi_pow_compat ψ σK (PkgI4.decomp p σ) hc k y, hyk]
    apply (embP p).injective
    rw [he]
    refine LinkedRamWild.wild_fix_of_pow hσ hk0 hk ?_
    rw [← LinkedRamWild.pow_compat (embP p) (PkgI4.decomp p σ) he k, h1]
  rw [hfix] at hmem
  exact hmem

/-- **Glue: Raynaud's criterion at `3` for high upper ramification on the QM model.** For a
`QML3` object over `K` with `[K:ℚ] ≤ D`, an isomorphism `ψ : K̄ ≅ ℚ̄` and `σK ∈ G_K` matching
`σ ∈ G_{ℚ_3}^t` (`t > U₀`), `σK` acts unipotently, `(σK − 1)² = 0`, on `A(K̄)[5ⁿ]`.
Route (STANDARD; Glazer L814-821): `K₁ = K(A[5])` has `[K₁:ℚ] ≤ D·|GL₄(𝔽₅)| = DG₀` (T5, open
stabilizers), so `σK` fixes `K₁` (`UpperBreakBound`, `4(DG₀)² = U₀ < t`); `σK` is in the inertia
group of the place `ψ^*(v)` above `3` (`UpperAbsInertia`, `LocalInertiaGlobal`); Raynaud's
criterion (R6, `PkgI2.RaynaudCriterion`, with `m = 5`) over `K₁` at that place. GLUE (the
transport of R6 along `K ⊆ K₁`, as lt-goodred transported NOS). -/
def RaynaudAtThree : Prop :=
  ∀ (K : IF) [FiniteDimensional ℚ K] (PK : LeafQM.AV.QML3 K), Module.finrank ℚ K ≤ ZInQ.heightD →
    ∀ (ψ : AlgebraicClosure K ≃+* PkgI4.Qbar) (σK : Field.absoluteGaloisGroup K)
      (t : ℝ), G0ModNewform.U0 < t → ∀ σ ∈ LadicCond.upperAbs 3 t,
      (∀ y, ψ (σK y) = PkgI4.decomp 3 σ (ψ y)) →
      ∀ (n : ℕ) (x : PK.A.Pt (AlgebraicClosure K)), x ^ (5 ^ n) = 1 →
        PK.A.galAct σK (PK.A.galAct σK x) * (PK.A.galAct σK x)⁻¹ * (PK.A.galAct σK x)⁻¹ * x = 1

/-- **The model statement at `3`** (over `K` itself): the same `σK` fixes `A(K̄)[5ⁿ]`. -/
def TateRamCore : Prop :=
  ∀ (K : IF) [FiniteDimensional ℚ K] (PK : LeafQM.AV.QML3 K), Module.finrank ℚ K ≤ ZInQ.heightD →
    ∀ (ψ : AlgebraicClosure K ≃+* PkgI4.Qbar) (σK : Field.absoluteGaloisGroup K)
      (t : ℝ), G0ModNewform.U0 < t → ∀ σ ∈ LadicCond.upperAbs 3 t,
      (∀ y, ψ (σK y) = PkgI4.decomp 3 σ (ψ y)) →
      ∀ (n : ℕ) (x : PK.A.Pt (AlgebraicClosure K)), x ^ (5 ^ n) = 1 → PK.A.galAct σK x = x

/-- **`TateRamCore` from `RaynaudAtThree`**: unipotence gives `σK^{5ⁿ} x = x` (with
`y = σK x · x⁻¹` fixed, `σK^m x = y^m x` and `y^{5ⁿ} = 1`), `σ` is wild (`upperAbsWild`), and
`3 ∤ 5ⁿ` (`fix_of_pow_fix`). -/
theorem tateRamCore_of (hR : RaynaudAtThree) : TateRamCore := by
  intro K _ PK hK ψ σK t ht σ hσ hc n x hx
  have hu := hR K PK hK ψ σK t ht σ hσ hc n x hx
  set s := PK.A.galAct σK with hs
  set y := s x * x⁻¹ with hy
  have hsy : s y = y := by
    rw [hy, map_mul, map_inv]
    have h2 : s (s x) * (s x)⁻¹ = ((s x)⁻¹ * x)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hu]; group
    rw [h2, mul_inv_rev, inv_inv, mul_comm]
  have hiter : ∀ m : ℕ, PK.A.galAct (σK ^ m) x = y ^ m * x := by
    intro m
    induction m with
    | zero =>
      show PkgI3.AbVar.galHom 1 ≫ x = 1 * x
      rw [PkgI3.AbVar.galHom_one, Category.id_comp, _root_.one_mul]
    | succ m ih =>
      rw [pow_succ', PkgI3.RhoCont.galAct_mul, ih, map_mul, map_pow, hsy]
      show y ^ m * s x = y ^ (m + 1) * x
      rw [show s x = y * x by rw [hy]; group, pow_succ, _root_.mul_assoc]
  have hy5 : y ^ (5 ^ n) = 1 := by
    rw [hy, mul_pow, ← map_pow, hx, map_one, inv_pow, hx, inv_one, _root_.mul_one]
  have hfix5 : PK.A.galAct (σK ^ (5 ^ n)) x = x := by rw [hiter, hy5, _root_.one_mul]
  have hw : σ ∈ (LadicCond.wildSet : Set (PkgI4.GQp 3)) :=
    upperAbsWild 3 t (lt_of_le_of_lt U0_nonneg ht) hσ
  have h35 : ¬ 3 ∣ 5 ^ n := by
    intro h
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    omega
  exact fix_of_pow_fix PK.A ψ σK σ hw hc (pow_pos (by norm_num) n) h35 x hfix5

set_option maxHeartbeats 1000000 in
/-- **`TateRamAtThreeD` from `TateRamCore`**: transport along `\bar{L'} ≅ K̄` over `K` and
`A_{L,L'}(\bar{L'}) ≅ A(K̄)`, exactly as in lt-goodred's `goodRedTorsion`. -/
theorem tateRamAtThreeD_of_core (hC : TateRamCore) : TateRamAtThreeD := by
  intro K L L' _ _ hKL hLL' PK hLD
  letI hNF : NumberField L' := numberField_of_fd L'
  intro t ht σ hσ σ' hσ'
  haveI hLfd : FiniteDimensional ℚ L := FiniteDimensional.of_injective
    (IntermediateField.inclusion hLL').toLinearMap
    (IntermediateField.inclusion hLL').toRingHom.injective
  haveI hKfd : FiniteDimensional ℚ K := FiniteDimensional.of_injective
    (IntermediateField.inclusion (hKL.trans hLL')).toLinearMap
    (IntermediateField.inclusion (hKL.trans hLL')).toRingHom.injective
  have hKD : Module.finrank ℚ K ≤ ZInQ.heightD :=
    (IntermediateField.finrank_le_of_le_right hKL).trans hLD
  apply HSyn.LinkedTate.tate_eq_one_of_torsion
  intro n x hx
  set A := PK.A with hAdef
  letI iKL : Algebra K L := incAlg hKL
  letI iLL' : Algebra L L' := incAlg hLL'
  letI iKL' : Algebra K L' := incAlg (hKL.trans hLL')
  haveI tKLL' : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI tLΩ : IsScalarTower L L' (AlgebraicClosure L') := inferInstance
  haveI tKL'Ω : IsScalarTower K L' (AlgebraicClosure L') := inferInstance
  haveI tKLΩ : IsScalarTower K L (AlgebraicClosure L') := IsScalarTower.of_algebraMap_eq
    (fun y => by
      rw [IsScalarTower.algebraMap_apply K L' (AlgebraicClosure L'),
        IsScalarTower.algebraMap_apply L L' (AlgebraicClosure L'),
        IsScalarTower.algebraMap_apply K L L'])
  haveI tQKL' : IsScalarTower ℚ K L' := IsScalarTower.of_algebraMap_eq (fun q => by
    rw [eq_ratCast (algebraMap ℚ L') q, eq_ratCast (algebraMap ℚ K) q, map_ratCast])
  haveI : Algebra.IsAlgebraic ℚ L' := Algebra.IsAlgebraic.of_finite ℚ L'
  haveI : Algebra.IsAlgebraic K L' := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : Algebra.IsAlgebraic L' (AlgebraicClosure L') := AlgebraicClosure.isAlgebraic L'
  haveI : Algebra.IsAlgebraic K (AlgebraicClosure L') :=
    Algebra.IsAlgebraic.trans K L' (AlgebraicClosure L')
  haveI : IsAlgClosure K (AlgebraicClosure L') := ⟨inferInstance, inferInstance⟩
  let τ : AlgebraicClosure L' ≃ₐ[K] AlgebraicClosure K :=
    IsAlgClosure.equiv K (AlgebraicClosure L') (AlgebraicClosure K)
  let g : PkgI4.Qbar →ₐ[ℚ] AlgebraicClosure L' := (G0Galois.qEmbRing L').toRatAlgHom
  have hgbij : Function.Bijective g := by
    letI : Algebra PkgI4.Qbar (AlgebraicClosure L') := g.toAlgebra
    haveI : IsScalarTower ℚ PkgI4.Qbar (AlgebraicClosure L') :=
      IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
    haveI : Algebra.IsIntegral ℚ (AlgebraicClosure L') := inferInstance
    haveI : Algebra.IsIntegral PkgI4.Qbar (AlgebraicClosure L') := Algebra.IsIntegral.tower_top ℚ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ge : PkgI4.Qbar ≃+* AlgebraicClosure L' := RingEquiv.ofBijective (G0Galois.qEmbRing L') hgbij
  have hge : ∀ z, ge z = G0Galois.qEmbRing L' z := fun _ => rfl
  let ψ : AlgebraicClosure K ≃+* PkgI4.Qbar := τ.symm.toRingEquiv.trans ge.symm
  let s' : AlgebraicClosure L' ≃ₐ[L'] AlgebraicClosure L' := σ'
  let σK : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
    (τ.symm.trans (s'.restrictScalars K)).trans τ
  have hσK : ∀ y, σK y = τ (s' (τ.symm y)) := fun _ => rfl
  have hres : ∀ y, ψ (σK y) = (G0Galois.resQ L' σ') (ψ y) := by
    intro y
    apply ge.injective
    show ge (ge.symm (τ.symm (σK y))) = ge ((G0Galois.resQ L' σ') (ge.symm (τ.symm y)))
    rw [RingEquiv.apply_symm_apply, hσK, AlgEquiv.symm_apply_apply]
    have hspec := G0Galois.resQ_spec L' σ' (ge.symm (τ.symm y))
    rw [← hge, ← hge, RingEquiv.apply_symm_apply] at hspec
    exact hspec.symm
  have hcomp : ∀ y, ψ (σK y) = PkgI4.decomp 3 σ (ψ y) := by
    intro y; rw [hres, hσ']
  let E := (UnramTate.bcPt (K := L) (L := L') (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL))
    (AlgebraicClosure L')).trans ((UnramTate.bcPt (K := K) (L := L) A (AlgebraicClosure L')).trans
      (UnramTate.trPt A τ))
  have hE : ∀ y, E ((@PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')).galAct s' y) =
      A.galAct σK (E y) := by
    intro y
    show UnramTate.trPt A τ (UnramTate.bcPt (K := K) (L := L) A (AlgebraicClosure L')
        (UnramTate.bcPt (K := L) (L := L') (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL))
          (AlgebraicClosure L')
          ((@PkgI3.AbVar.baseChange L _
            (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')).galAct s' y))) = _
    rw [UnramTate.bcPt_galAct, UnramTate.bcPt_galAct]
    exact UnramTate.trPt_galAct A τ _ σK (fun z => by rw [hσK, AlgEquiv.symm_apply_apply]; rfl) _
  have hEx : E x ^ (5 ^ n) = 1 := by rw [← map_pow, hx, map_one]
  have hfix : A.galAct σK (E x) = E x := hC K PK hKD ψ σK t ht σ hσ hcomp n (E x) hEx
  apply E.injective
  exact (hE x).trans hfix

/-- **`TateRamAtThreeD` from `RaynaudAtThree`.** -/
theorem tateRamAtThreeD_of_raynaud (hR : RaynaudAtThree) : TateRamAtThreeD :=
  tateRamAtThreeD_of_core (tateRamCore_of hR)

/-! #### `RaynaudAtThree` from R6, `UpperBreakBound` and the `5`-torsion field -/

/-- **Glue: the `5`-torsion field of a QM surface has degree `≤ |GL₄(𝔽₅)| = G₀`.** For a `QML3`
object over a number field `K ⊆ ℚ̄`, there is a finite `K₁/K` inside `K̄` with `[K₁:K] ≤ G₀` such
that every `g ∈ G_K` fixing `K₁` fixes `A(K̄)[5]`. Route (STANDARD): `A(K̄)[5] ≅ (ℤ/5)⁴` (T5); the
stabilizer of `A[5]` is open (`PkgI3.RhoCont`), its fixed field `K₁` has `[K₁:K]` = its index =
the order of the image of `G_K` in `Aut(A[5]) ≅ GL₄(𝔽₅)`. GLUE (Galois theory and counting). -/
def TorsionFieldFive : Prop :=
  ∀ (K : IF) [FiniteDimensional ℚ K] (PK : LeafQM.AV.QML3 K),
    ∃ K₁ : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K₁ ∧
      Module.finrank K K₁ ≤ ZInQ.heightG0 ∧
      ∀ g : Field.absoluteGaloisGroup K, (∀ y ∈ K₁, g y = y) →
        ∀ x : PK.A.Pt (AlgebraicClosure K), x ^ 5 = 1 → PK.A.galAct g x = x

/-- `4 (D G₀)² = U₀`. -/
theorem U0_eq : G0ModNewform.U0 = 4 * (((ZInQ.heightD * ZInQ.heightG0 : ℕ) : ℝ)) ^ 2 := rfl

set_option maxHeartbeats 1000000 in
/-- **`RaynaudAtThree`, proved** from R6 (`PkgI2.RaynaudCriterion`), `UpperBreakBound` and
`TorsionFieldFive`: `σK` fixes `K₁` (each `y ∈ K₁` has degree `≤ D G₀` over `ℚ`, so the break bound
applies to `ℚ_3(embP (ψ y))`), lies in the inertia group of `ψ^*(v)` (`upperAbsInertia`,
`localInertiaGlobal`), and Raynaud's criterion over `K₁` with `m = 5` gives `(σK − 1)² = 0` on
`A(K̄)[5ⁿ]`, transported along `A_{K₁}(K̄₁) ≅ A(K̄)`. -/
theorem raynaudAtThree_of (hRay : PkgI2.RaynaudCriterion.{0}) (hB : UpperBreakBound)
    (hT : TorsionFieldFive) : RaynaudAtThree := by
  intro K _ PK hK ψ σK t ht σ hσ hc n x hx
  obtain ⟨K₁, hK₁fd, hK₁deg, hK₁fix⟩ := hT K PK
  haveI := hK₁fd
  set A := PK.A with hAdef
  have ht0 : 0 < t := lt_of_le_of_lt U0_nonneg ht
  -- (1) `σK` fixes `K₁`
  have hfixK₁ : ∀ y ∈ K₁, σK y = y := by
    intro y hy
    apply ψ.injective
    rw [hc]
    set z := ψ y
    -- degree of `z` over `ℚ`
    haveI : FiniteDimensional ℚ K₁ := Module.Finite.trans K K₁
    have hdegz : (minpoly ℚ z).natDegree ≤ ZInQ.heightD * ZInQ.heightG0 := by
      have h1 : minpoly ℚ z = minpoly ℚ y := minpoly.algEquiv_eq ψ.toRatAlgEquiv y
      have h2 : minpoly ℚ y = minpoly ℚ (⟨y, hy⟩ : K₁) :=
        (minpoly.algebraMap_eq (algebraMap K₁ (AlgebraicClosure K)).injective (⟨y, hy⟩ : K₁)).symm
      have h3 : (minpoly ℚ (⟨y, hy⟩ : K₁)).natDegree ≤ Module.finrank ℚ K₁ := minpoly.natDegree_le _
      have h4 : Module.finrank ℚ K₁ = Module.finrank ℚ K * Module.finrank K K₁ :=
        (Module.finrank_mul_finrank ℚ K K₁).symm
      rw [h1, h2]
      calc _ ≤ Module.finrank ℚ K₁ := h3
        _ = Module.finrank ℚ K * Module.finrank K K₁ := h4
        _ ≤ ZInQ.heightD * ZInQ.heightG0 := Nat.mul_le_mul hK hK₁deg
    -- the break bound at `ℚ_3(embP z)`
    have he : ∀ w, embP 3 (PkgI4.decomp 3 σ w) = σ (embP 3 w) := embP_decomp 3 σ
    apply (embP 3).injective
    rw [he]
    let yz : PadicAlgCl 3 := embP 3 z
    have hyint : IsIntegral ℚ_[3] yz := Algebra.IsIntegral.isIntegral yz
    let F : LadicCond.Fld 3 := IntermediateField.adjoin ℚ_[3] {yz}
    haveI : FiniteDimensional ℚ_[3] F := IntermediateField.adjoin.finiteDimensional hyint
    have hdeg : Module.finrank ℚ_[3] F ≤ ZInQ.heightD * ZInQ.heightG0 := by
      have h1 : Module.finrank ℚ_[3] F = (minpoly ℚ_[3] yz).natDegree :=
        IntermediateField.adjoin.finrank hyint
      have hq0 : (minpoly ℚ z).map (algebraMap ℚ ℚ_[3]) ≠ 0 :=
        Polynomial.map_ne_zero (minpoly.ne_zero (Algebra.IsIntegral.isIntegral z))
      have h2 : minpoly ℚ_[3] yz ∣ (minpoly ℚ z).map (algebraMap ℚ ℚ_[3]) := by
        apply minpoly.dvd
        rw [Polynomial.aeval_map_algebraMap]
        rw [show Polynomial.aeval yz (minpoly ℚ z) =
            (embP 3).toRatAlgHom (Polynomial.aeval z (minpoly ℚ z))
          from Polynomial.aeval_algHom_apply (embP 3).toRatAlgHom z _, minpoly.aeval, map_zero]
      rw [h1]
      calc (minpoly ℚ_[3] yz).natDegree ≤ ((minpoly ℚ z).map (algebraMap ℚ ℚ_[3])).natDegree :=
            Polynomial.natDegree_le_of_dvd h2 hq0
        _ = (minpoly ℚ z).natDegree := Polynomial.natDegree_map _
        _ ≤ _ := hdegz
    have hlt : 4 * (Module.finrank ℚ_[3] F : ℝ) ^ 2 < t := by
      refine lt_of_le_of_lt ?_ ht
      rw [U0_eq]
      have : (Module.finrank ℚ_[3] F : ℝ) ≤ ((ZInQ.heightD * ZInQ.heightG0 : ℕ) : ℝ) := by
        exact_mod_cast hdeg
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) this 2) (by norm_num)
    exact hB 3 F t hlt σ hσ yz (IntermediateField.mem_adjoin_simple_self ℚ_[3] yz)
  -- (2) the inertia data at a place above `3`
  have hσI := upperAbsInertia 3 t ht0 hσ
  obtain ⟨v, hv, τv, hτv, hτveq⟩ := localInertiaGlobal 3 σ hσI
  obtain ⟨hv1, hv2⟩ := LTGoodRed.of_mem_inertia ℚ v τv hτv
  rw [hτveq] at hv1 hv2
  -- (3) `K₁`, its algebraic closure `K̄₁ ≅ K̄`, `σ₁`, `ψ₁`
  haveI hK₁NF : NumberField K₁ :=
    { to_charZero := inferInstance, to_finiteDimensional := Module.Finite.trans K K₁ }
  haveI : Algebra.IsAlgebraic K₁ (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) K₁
  haveI : IsAlgClosure K₁ (AlgebraicClosure K) := ⟨inferInstance, inferInstance⟩
  let τ₁ : AlgebraicClosure K₁ ≃ₐ[K₁] AlgebraicClosure K :=
    IsAlgClosure.equiv K₁ (AlgebraicClosure K₁) (AlgebraicClosure K)
  let σK₁ : AlgebraicClosure K ≃ₐ[K₁] AlgebraicClosure K :=
    AlgEquiv.ofRingEquiv (f := σK.toRingEquiv) (fun k => hfixK₁ k k.2)
  let σ₁ : AlgebraicClosure K₁ ≃ₐ[K₁] AlgebraicClosure K₁ := (τ₁.trans σK₁).trans τ₁.symm
  have hσ₁ : ∀ y, τ₁ (σ₁ y) = σK₁ (τ₁ y) := fun y => by
    show τ₁ (τ₁.symm (σK₁ (τ₁ y))) = _
    rw [AlgEquiv.apply_symm_apply]
  have hrs : σK₁.restrictScalars K = σK := AlgEquiv.ext fun _ => rfl
  let ψ₁ : AlgebraicClosure K₁ ≃+* PkgI4.Qbar := τ₁.toRingEquiv.trans ψ
  have hc₁ : ∀ y, ψ₁ (σ₁ y) = PkgI4.decomp 3 σ (ψ₁ y) := fun y => by
    show ψ (τ₁ (σ₁ y)) = _
    rw [hσ₁]
    exact hc (τ₁ y)
  let w₁ : ValuationSubring (AlgebraicClosure K₁) := v.comap (ψ₁ : AlgebraicClosure K₁ →+* PkgI4.Qbar)
  let O₁ : ValuationSubring K₁ := w₁.comap (algebraMap K₁ (AlgebraicClosure K₁))
  have h3w : ((3 : ℕ) : AlgebraicClosure K₁) ∈ w₁.nonunits := by
    rw [LTGoodRed.mem_nonunits_comap v ψ₁, map_natCast]; exact hv
  have hunit : ∀ m : ℕ, Nat.Coprime m 3 → IsUnit (m : O₁) := by
    intro m hm
    obtain ⟨hm0, hmi⟩ := LTGoodRed.inv_mem_of_notMem_nonunits w₁
      (LTGoodRed.natCast_notMem_nonunits w₁ h3w hm)
    have hm0K : (m : K₁) ≠ 0 := by
      intro h; apply hm0
      rw [← map_natCast (algebraMap K₁ (AlgebraicClosure K₁)), h, map_zero]
    have hmO : (m : K₁)⁻¹ ∈ O₁ := by
      rw [ValuationSubring.mem_comap, map_inv₀, map_natCast]; exact hmi
    refine isUnit_iff_exists_inv.mpr ⟨⟨(m : K₁)⁻¹, hmO⟩, Subtype.ext ?_⟩
    push_cast
    exact mul_inv_cancel₀ hm0K
  have hOtop : O₁ ≠ ⊤ := by
    intro htop
    have hpi : ((3 : ℕ) : K₁)⁻¹ ∈ O₁ := by rw [htop]; exact ValuationSubring.mem_top _
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast] at hpi
    rw [ValuationSubring.mem_nonunits_iff_or] at h3w
    rcases h3w with h | h
    · exact (by norm_num : (3 : ℕ) ≠ 0) (by exact_mod_cast h)
    · exact h hpi
  haveI hODVR : IsDiscreteValuationRing O₁ := LTGoodRed.NLG.isDiscreteValuationRing_of_ne_top O₁ hOtop
  have h5 : IsUnit ((5 : ℕ) : O₁) := hunit 5 (by norm_num)
  have hI₁ : PkgI2.IsInertia w₁ σ₁ := by
    refine LTGoodRed.isInertia_of K₁ w₁ σ₁ (fun y => ?_) (fun a ha => ?_)
    · show ψ₁ (σ₁ y) ∈ v ↔ ψ₁ y ∈ v
      rw [hc₁]; exact hv1 (ψ₁ y)
    · rw [LTGoodRed.mem_nonunits_comap v ψ₁, map_sub, hc₁]
      exact hv2 (ψ₁ a) ha
  -- (4) the points: `E₁ : A_{K₁}(K̄₁) ≃* A(K̄)`
  let A₁ : PkgI3.AbVar K₁ := A.baseChange K₁
  let E₁ := (UnramTate.trPt A₁ τ₁).trans (UnramTate.bcPt (K := K) (L := K₁) A (AlgebraicClosure K))
  have hE₁ : ∀ (g : AlgebraicClosure K₁ ≃ₐ[K₁] AlgebraicClosure K₁)
      (g' : AlgebraicClosure K ≃ₐ[K₁] AlgebraicClosure K), (∀ y, τ₁ (g y) = g' (τ₁ y)) →
      ∀ p, E₁ (A₁.galAct g p) = A.galAct (g'.restrictScalars K) (E₁ p) := by
    intro g g' hg p
    show UnramTate.bcPt (K := K) (L := K₁) A (AlgebraicClosure K)
        (UnramTate.trPt A₁ τ₁ (A₁.galAct g p)) = _
    rw [UnramTate.trPt_galAct A₁ τ₁ g g' (fun y => (hg y).symm) p, UnramTate.bcPt_galAct]
    rfl
  -- (5) `A_{K₁}[5]` is rational over `K₁`
  have hrat : ∀ g : AlgebraicClosure K₁ ≃ₐ[K₁] AlgebraicClosure K₁,
      ∀ p ∈ PkgI2.AV.torsion (ObjBridge.toGrp A₁) (AlgebraicClosure K₁) 5,
        PkgI2.AV.galAct (ObjBridge.toGrp A₁) g p = p := by
    intro g p hp
    let g' : AlgebraicClosure K ≃ₐ[K₁] AlgebraicClosure K := (τ₁.symm.trans g).trans τ₁
    have hg : ∀ y, τ₁ (g y) = g' (τ₁ y) := fun y => by
      show τ₁ (g y) = τ₁ (g (τ₁.symm (τ₁ y))); rw [AlgEquiv.symm_apply_apply]
    have hp5 : (E₁ p) ^ 5 = 1 := by
      have : p ^ 5 = 1 := hp
      rw [← map_pow, this, map_one]
    have hfix := hK₁fix (g'.restrictScalars K) (fun y hy => g'.commutes ⟨y, hy⟩) (E₁ p) hp5
    apply E₁.injective
    exact (hE₁ g g' hg p).trans hfix
  -- (6) Raynaud
  have hx₁ : E₁.symm x ∈ PkgI2.AV.torsion (ObjBridge.toGrp A₁) (AlgebraicClosure K₁) (5 ^ n) := by
    show (E₁.symm x) ^ (5 ^ n) = 1
    rw [← map_pow, hx, map_one]
  have hu := hRay K₁ O₁ w₁ rfl (ObjBridge.toGrp A₁) 5 (by norm_num) h5 hrat σ₁ hI₁ 5
    Nat.prime_five (by exact_mod_cast h5) n (E₁.symm x) hx₁
  -- (7) transport `(σ₁ − 1)² = 0` back
  have hσ' : ∀ p, E₁ (A₁.galAct σ₁ p) = A.galAct σK (E₁ p) := fun p => by
    rw [hE₁ σ₁ σK₁ hσ₁ p, hrs]
  have hu' : A₁.galAct σ₁ (A₁.galAct σ₁ (E₁.symm x)) * (A₁.galAct σ₁ (E₁.symm x))⁻¹ *
      (A₁.galAct σ₁ (E₁.symm x))⁻¹ * E₁.symm x = 1 := hu
  have := congrArg E₁ hu'
  rw [map_mul, map_mul, map_mul, map_inv, map_one, hσ', hσ', MulEquiv.apply_symm_apply] at this
  exact this

/-! #### `TorsionFieldFive`, proved from T5 -/

/-- `|GL₄(𝔽₅)| = (5⁴−1)(5⁴−5)(5⁴−25)(5⁴−125) = G₀`. -/
theorem card_GL4_F5 : Nat.card (GL (Fin 4) (ZMod 5)) = ZInQ.heightG0 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
  unfold ZInQ.heightG0
  norm_num

/-- Additive automorphisms of `𝔽₅⁴` number at most `G₀`. -/
theorem card_addAut_le : Nat.card ((Fin 4 → ZMod 5) ≃+ (Fin 4 → ZMod 5)) ≤ ZInQ.heightG0 := by
  rw [← card_GL4_F5, ← Nat.card_congr (Matrix.GeneralLinearGroup.toLin (n := Fin 4)
    (R := ZMod 5)).symm.toEquiv]
  let ι : ((Fin 4 → ZMod 5) ≃+ (Fin 4 → ZMod 5)) →
      LinearMap.GeneralLinearGroup (ZMod 5) (Fin 4 → ZMod 5) := fun f =>
    { val := f.toAddMonoidHom.toZModLinearMap 5
      inv := f.symm.toAddMonoidHom.toZModLinearMap 5
      val_inv := LinearMap.ext fun v => by simp
      inv_val := LinearMap.ext fun v => by simp }
  have hι : Function.Injective ι := by
    intro f g h
    ext v
    have := congrArg (fun u : LinearMap.GeneralLinearGroup (ZMod 5) (Fin 4 → ZMod 5) =>
      (u : (Fin 4 → ZMod 5) →ₗ[ZMod 5] (Fin 4 → ZMod 5)) v) h
    simpa [ι] using this
  exact Nat.card_le_card_of_injective ι hι

/-- **`TorsionFieldFive`, proved from T5** (`PkgI2.TorsionStructure`): the stabilizer `S` of
`A(K̄)[5] ≅ 𝔽₅⁴` is open (finitely many open point stabilizers), `K₁ = K̄^S` is finite with
`[K₁:K] = [G_K : S]`, and `G_K/S` embeds in `Aut(𝔽₅⁴)`, of order `G₀`. -/
theorem torsionFieldFive_of (hTors : PkgI2.TorsionStructure.{0}) : TorsionFieldFive := by
  intro K _ PK
  haveI : IsGalois K (AlgebraicClosure K) := {}
  set A := PK.A with hAdef
  obtain ⟨e, he⟩ := hTors K (ObjBridge.toGrp A) 2 5 (by rw [← PK.surface]; rfl) (by norm_num)
    (by norm_num)
  let V := Fin 4 → ZMod 5
  have hone : ∀ x : A.Pt (AlgebraicClosure K), A.galAct (1 : Field.absoluteGaloisGroup K) x = x := by
    intro x
    show PkgI3.AbVar.galHom 1 ≫ x = x
    rw [PkgI3.AbVar.galHom_one, Category.id_comp]
  have hinv : ∀ (g : Field.absoluteGaloisGroup K) x, A.galAct g⁻¹ (A.galAct g x) = x := by
    intro g x; rw [← PkgI3.RhoCont.galAct_mul, inv_mul_cancel, hone]
  have hinv' : ∀ (g : Field.absoluteGaloisGroup K) x, A.galAct g (A.galAct g⁻¹ x) = x := by
    intro g x; rw [← PkgI3.RhoCont.galAct_mul, mul_inv_cancel, hone]
  -- membership in `A[5]` is preserved
  have hmem : ∀ (g : Field.absoluteGaloisGroup K) (x : A.Pt (AlgebraicClosure K)),
      x ^ 5 = 1 → (A.galAct g x) ^ 5 = 1 := by
    intro g x hx; rw [← map_pow, hx, map_one]
  let T := PkgI2.AV.torsion (ObjBridge.toGrp A) (AlgebraicClosure K) 5
  haveI hTfin : Finite T := Finite.of_equiv _ e.symm
  -- the stabilizer `S` of `A[5]`
  let S : Subgroup (Field.absoluteGaloisGroup K) :=
    { carrier := {g | ∀ x : A.Pt (AlgebraicClosure K), x ^ 5 = 1 → A.galAct g x = x}
      mul_mem' := fun {a b} ha hb x hx => by
        rw [PkgI3.RhoCont.galAct_mul, hb x hx, ha x hx]
      one_mem' := fun x _ => hone x
      inv_mem' := fun {a} ha x hx => by
        have h1 := ha (A.galAct a⁻¹ x) (hmem _ x hx)
        rw [hinv'] at h1
        exact h1.symm }
  -- `S` is open
  choose U hU using fun x : A.Pt (AlgebraicClosure K) =>
    PkgI3.RhoCont.exists_openSubgroup_galAct_eq A x
  have hSnhds : (S : Set (Field.absoluteGaloisGroup K)) ∈ nhds 1 := by
    have hfinT : (T : Set (A.Pt (AlgebraicClosure K))).Finite := Set.toFinite T
    refine Filter.mem_of_superset ((Filter.biInter_mem hfinT).mpr
      (fun x _ => (U x).isOpen.mem_nhds (U x).one_mem)) ?_
    intro g hg x hx
    exact hU x g (Set.mem_iInter₂.mp hg x hx)
  have hSopen : IsOpen (S : Set (Field.absoluteGaloisGroup K)) := Subgroup.isOpen_of_mem_nhds S hSnhds
  have hSclosed : IsClosed (S : Set (Field.absoluteGaloisGroup K)) :=
    Subgroup.isClosed_of_isOpen S hSopen
  let K₁ := IntermediateField.fixedField S
  have hfix : K₁.fixingSubgroup = S :=
    InfiniteGalois.fixingSubgroup_fixedField (⟨S, hSclosed⟩ : ClosedSubgroup _)
  have hfd : FiniteDimensional K K₁ := by
    rw [← InfiniteGalois.isOpen_iff_finite]
    show IsOpen (K₁.fixingSubgroup : Set (Field.absoluteGaloisGroup K))
    rw [hfix]; exact hSopen
  -- `G_K / S ↪ Aut(𝔽₅⁴)`
  have hesymm : ∀ v w : V, ((e.symm (v + w) : T) : A.Pt (AlgebraicClosure K)) =
      (e.symm v : A.Pt (AlgebraicClosure K)) * (e.symm w : A.Pt (AlgebraicClosure K)) := by
    intro v w
    have h5 : (e.symm v : A.Pt (AlgebraicClosure K)) * (e.symm w : A.Pt (AlgebraicClosure K)) ∈ T := by
      show (_ * _) ^ 5 = 1
      rw [mul_pow, (e.symm v).2, (e.symm w).2, _root_.one_mul]
    have := he (e.symm v) (e.symm w) h5
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    rw [← this, Equiv.symm_apply_apply]
  let act : Field.absoluteGaloisGroup K → V → V := fun g v =>
    e ⟨A.galAct g (e.symm v), hmem g _ (e.symm v).2⟩
  have hact_add : ∀ g v w, act g (v + w) = act g v + act g w := by
    intro g v w
    show e ⟨A.galAct g (e.symm (v + w)), _⟩ = e ⟨A.galAct g (e.symm v), _⟩ + e ⟨A.galAct g (e.symm w), _⟩
    have h5 : A.galAct g (e.symm v) * A.galAct g (e.symm w) ∈ T := by
      show (_ * _) ^ 5 = 1
      rw [mul_pow, hmem g _ (e.symm v).2, hmem g _ (e.symm w).2, _root_.one_mul]
    rw [← he _ _ h5]
    congr 2
    rw [hesymm, map_mul]
  have hact_mul : ∀ g h v, act (g * h) v = act g (act h v) := by
    intro g h v
    show e ⟨A.galAct (g * h) (e.symm v), _⟩ = e ⟨A.galAct g (e.symm (e ⟨A.galAct h (e.symm v), _⟩)), _⟩
    rw [Equiv.symm_apply_apply, PkgI3.RhoCont.galAct_mul]
  have hact_one : ∀ v, act 1 v = v := by
    intro v
    show e ⟨A.galAct 1 (e.symm v), _⟩ = v
    simp only [hone]
    exact e.apply_symm_apply v
  let φ : Field.absoluteGaloisGroup K →* (V ≃+ V) :=
    { toFun := fun g =>
        { toFun := act g
          invFun := act g⁻¹
          left_inv := fun v => by rw [← hact_mul, inv_mul_cancel, hact_one]
          right_inv := fun v => by rw [← hact_mul, mul_inv_cancel, hact_one]
          map_add' := hact_add g }
      map_one' := AddEquiv.ext hact_one
      map_mul' := fun g h => AddEquiv.ext (hact_mul g h) }
  have hker : φ.ker = S := by
    ext g
    rw [MonoidHom.mem_ker]
    constructor
    · intro hg x hx
      have := congrArg (fun f : V ≃+ V => f (e ⟨x, hx⟩)) hg
      simp only [AddEquiv.one_apply] at this
      have h2 : e ⟨A.galAct g x, hmem g x hx⟩ = e ⟨x, hx⟩ := by
        have h3 : act g (e ⟨x, hx⟩) = e ⟨x, hx⟩ := this
        simpa [act] using h3
      exact congrArg Subtype.val (e.injective h2)
    · intro hg
      apply AddEquiv.ext
      intro v
      show act g v = v
      show e ⟨A.galAct g (e.symm v), _⟩ = v
      rw [show (⟨A.galAct g (e.symm v), hmem g _ (e.symm v).2⟩ : T) = e.symm v from
        Subtype.ext (hg _ (e.symm v).2)]
      exact e.apply_symm_apply v
  haveI : Finite (V ≃+ V) :=
    Finite.of_injective (fun f : V ≃+ V => (f : V → V)) (fun f g h => AddEquiv.ext (congrFun h))
  have hidx : S.index ≤ ZInQ.heightG0 := by
    rw [← hker, Subgroup.index_ker]
    exact (Nat.card_le_card_of_injective _ Subtype.val_injective).trans card_addAut_le
  refine ⟨K₁, hfd, ?_, fun g hg x hx => ?_⟩
  · rw [IntermediateField.finrank_eq_fixingSubgroup_index, hfix]; exact hidx
  · have : g ∈ K₁.fixingSubgroup := (IntermediateField.mem_fixingSubgroup_iff K₁ g).mpr hg
    rw [hfix] at this
    exact this x hx

/-- **`TateRamAtThreeD` from the leaves R6, T5 and `UpperBreakBound`.** -/
theorem tateRamAtThreeD_of_leaves (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (hB : UpperBreakBound) : TateRamAtThreeD :=
  tateRamAtThreeD_of_raynaud (raynaudAtThree_of hRay hB (torsionFieldFive_of hTors))

end TateRam

end UnramTate

end

end LinkedRamMain

#print axioms UnramTate.kernelFieldBreaksHigh
#print axioms UnramTate.kernelFieldBreaks_of_halves
#print axioms UnramTate.kernelFieldBreaks_of
#print axioms UnramTate.linkedRam_of'
#print axioms UnramTate.upperAbsWild
#print axioms UnramTate.kernelFieldBreaks_of'
#print axioms UnramTate.fix_of_pow_fix
#print axioms UnramTate.tateRamCore_of
#print axioms UnramTate.tateRamAtThreeD_of_raynaud
#print axioms UnramTate.raynaudAtThree_of
#print axioms UnramTate.torsionFieldFive_of
#print axioms UnramTate.tateRamAtThreeD_of_leaves

/-! ## linked-ram: `GluePieces5` and `sixContactMin_of_leaves5` (from g0-assemble3's part z95, edited as stated) -/

section LinkedRamBundle

noncomputable section

namespace HSyn

open G0Split

/-- **The named Props left after linked-ram** (g0-assemble3's `GluePieces4` with lt-goodred's two proofs folded
and `kernelFieldBreaks`, `tateRamAtThree` replaced: `TateRamAtThreeD` is proved from R6, T5 and
`upperBreakBound`). -/
structure GluePieces5 : Prop where
  -- FibreSimple: FS5 (NoCM on the fibre)
  /-- fs5-nocm, LEAF (N1b′: CM points via optimal embeddings; Shimura 1967, Jordan, González–Rotger). -/
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  /-- x6-kummer, LEAF (N2-L′: `X₆` is the conic `Y² + 3X² + 3Z² = 0` with `π₆ = −16(X² + Z²)/(27Z²)` on
  `ℚ̄`-points of one witness of the leaf bundle; Elkies 1998 §3, Kurihara 1979; a consequence of the published model,
  x6-kummer §3.6). fs5-nocm's glue N2 `X6KummerFibre` is proved from it and `MobiusGlue`. -/
  x6ConicModel : X6Kummer.X6ConicModel
  -- ProductModelHeight (unif-dims, product-unif, infra-smooth-dim)
  /-- metrization (via unif-dims), LEAF (the uniformization theorem with its dimension: `𝒢(ℂ)_τ ≅ ℂ^g/Λ`,
  Mumford §1, §4; GAGA). -/
  analyticUniformizationOfDim : ZInQ.Metrization.AnalyticUniformizationOfDim
  -- StableHeightBaseChange (height-bc; infra-stalks proved the other two)
  /-- height-bc, GLUE (BC-alg: `ψ` is injective on the Hodge line). -/
  hodgeBCInjective : ZInQ.HeightBC.HodgeBCInjective
  /-- height-bc, GLUE (`ω` base-changes along `𝓞_L → 𝓞_{L'}`). -/
  omegaBaseChange : ZInQ.HeightBC.OmegaBaseChange
  -- ThetaPoint (g0-thetapoint, fibre-qm-period, period-map)
  /-- g0-thetapoint, LEAF? (theta-constant ratios at a period matrix are algebraic; Shimura 1976). -/
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  /-- pkg-I1 (via fibre-qm-period), LEAF? (the theta-quotient Hauptmodul of `Γ*`). -/
  qmHauptmodul : PkgI1.QMHauptmodul
  /-- fibre-qm-period, LEAF (Eichler class number one for `𝒪`, lattice form). -/
  qmClassNumberOne : G0Split.FibreQM.QMClassNumberOne
  /-- fibre-qm-period, LEAF (R1(b) in family form; Shimura 1967 Main Thm I). -/
  r1bFamily : ∀ h : LeafAdopt.R1R2fpRep,
    G0Split.FibreQM.R1bFamily (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h))
  /-- period-map, GLUE (base change of QM classes is unique). -/
  baseChangeClassUnique : G0Split.FibreQM.PeriodMapH.BaseChangeClassUnique
  /-- period-map, GLUE (`π` is invariant under the QM twist, complex form), for the leaf's own triple. -/
  piTwistC : ∀ h : LeafAdopt.R1R2fpRep,
    G0Split.FibreQM.PeriodMapH.PiTwistC (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h))
  /-- period-map, GLUE (the QM twist acts on the period lattice). -/
  qmTwistLattice : G0Split.FibreQM.PeriodMapH.QMTwistLattice
  /-- period-map, LEAF? (CM points descend; Shimura's theory of CM). -/
  cmDescends : G0Split.FibreQM.PeriodMapH.CMDescends
  /-- period-map, GLUE (numerical: `Σθ⁸(Ω(√2 + i)) ≠ 0`). -/
  s8Nonzero : G0Split.FibreQM.PeriodMap.S8Nonzero
  /-- period-map, GLUE (textbook complex analysis: a holomorphic map of the sphere factoring affinely). -/
  sphereFactorAffine : G0Split.FibreQM.PeriodMap.SphereFactorAffine
  /-- period-map, GLUE (`Σθ⁸∘Ω` has exact weight 8). -/
  s8WeightExact : G0Split.FibreQM.PeriodMap.S8WeightExact
  /-- period-map, LEAF (the valence formula for `Γ*`). -/
  valenceBoundGammaStar : G0Split.FibreQM.PeriodMap.ValenceBoundGammaStar
  /-- fibre-qm-period, GLUE (transport of complex points along base change). -/
  cPtsTransport : G0Split.FibreQM.CPtsTransport
  -- ModularConstituent: G2 (fibre-cover; Prop. TS by prop-ts, prop-ts-glue)
  /-- prop-ts-glue, GLUE. -/ verticalResidueSeparable : PropTSGlue.VerticalResidueSeparable
  /-- prop-ts-glue, GLUE. -/ snSpecialize : PropTSGlue.SNSpecialize
  /-- prop-ts-glue, GLUE. -/ kummerCompositum : PropTSGlue.KummerCompositum
  /-- prop-ts-glue, GLUE (`AbhyankarDVR → …`). -/ kummerAbhyankarFinGlue : PropTSGlue.KummerAbhyankarFinGlue
  /-- prop-ts-glue, GLUE. -/ kummerOtherBranchFin : PropTSGlue.KummerOtherBranchFin
  /-- prop-ts-glue, GLUE. -/ kummerVerticalFin : PropTSGlue.KummerVerticalFin
  /-- prop-ts-glue, GLUE (`AbhyankarDVR → …`). -/ kummerAbhyankarInfGlue : PropTSGlue.KummerAbhyankarInfGlue
  /-- prop-ts-glue, GLUE. -/ kummerOtherBranchInf : PropTSGlue.KummerOtherBranchInf
  /-- prop-ts-glue, GLUE. -/ kummerVerticalInf : PropTSGlue.KummerVerticalInf
  /-- prop-ts-glue, GLUE (truth SPECULATIVE per its report). -/ heckeIrreducible : PropTSGlue.HeckeIrreducible
  /-- prop-ts-glue, GLUE. -/ heckeNormalizationIrr : PropTSGlue.HeckeNormalizationIrr
  /-- prop-ts-glue, GLUE. -/ heckeDegree : PropTSGlue.HeckeDegree
  /-- prop-ts-glue, GLUE. -/ heckeBranch : PropTSGlue.HeckeBranch
  /-- prop-ts-glue, GLUE (Lemma NV). -/ heckeNoVertRam : PropTSGlue.HeckeNoVertRam
  -- ModularConstituent: G4 (kernel-field, kf-glue)
  /-- kf-glue, GLUE (Galois descent of the twisted isomorphisms). -/
  twistDescent : G0ModField.KernelField.TwistDescent
  -- ModularConstituent: G8-G12
  /-- g0-mod-galois, LEAF (R14 with its determinant clause; Shimura 1971 Thm 7.14; Deligne 1971). -/
  r14Det : G0Galois.R14Det
  /-- conj-twist, LEAF (N2: homomorphisms lift to `ℂ`-linear maps of uniformizations; Birkenhake–Lange 1.2.1). -/
  homLinearLift : G0Galois.HomLinearLift
  /-- g12-det, LEAF (HT weights of a twist shift by a constant; Sen 1980). -/
  senTwist : G0Galois.SenTwist
  /-- g12-det, LEAF (finite image ⇒ HT with weights 0; Tate 1967; Ax–Sen–Tate). -/
  finiteImageHT : G0Galois.FiniteImageHT
  /-- weil-pairing (used by g12-det), LEAF (T9 restated; Mumford §§6, 8, 20, 23). -/
  t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists
  /-- weil-pairing, LEAF (Mumford §7-8). -/
  isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse
  /-- weil-pairing, LEAF (Mumford §4 Appl. 2). -/
  divisiblePoints : WeilPairing.DivisiblePoints
  -- ModularConstituent: G13-G16
  /-- R17 concretely, LEAF (Carayol 1986, Thm (A)). -/
  carayolR17 : LadicCond.CarayolR17'
  -- ModularConstituent: joint glue on G7's data (linked-tate; `goodRedTorsion`, `qmEndRank` proved by lt-goodred)
  /-- linked-tate, GLUE (g14-trace's Frobenius link for the canonical operators). -/
  linkedFrob : UnramTate.LinkedFrob
  /-- linked-ram, LEAF? (textbook composite: the absolute upper-break bound `4a²` for a degree-`a` extension of `ℚ_p`;
  Glazer L796-811 from Serre, *Local Fields*, III §6 and IV §1-§3). With `BetaTrivialAtTwo` it gives linked-tate's
  `KernelFieldBreaks` (`UnramTate.kernelFieldBreaks_of'`). -/
  upperBreakBound : UnramTate.UpperBreakBound
  /-- linked-ram, GLUE (`β` trivial on `G_{ℚ_2}^u ∩ G_L`, `u > U₀`; Glazer L826-843, local reciprocity). -/
  betaTrivialAtTwo : UnramTate.BetaTrivialAtTwo

/-- FS5 (NoCM on the fibre) from `GluePieces5` (fs5-nocm). -/
theorem fibreComTrivial_of_gp5 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces5) :
    G0FibreSimple.FibreComTrivial :=
  fibreComTrivial_of_full (FS5NoCM.fibreComTrivialFull_of_leaves'' (r1r2fpFull_of r.toR3)
    (mobiusGlue_of_t5' t) t.t27 t.t6 gp.cmOptimalEmbedding
    (X6Kummer.x6KummerFibre_of_conic (mobiusGlue_of_t5' t) gp.x6ConicModel) r.r5count)

/-- `FibreSimple` from `GluePieces5` (fs1-descend, mul-rigidity, infra-stalks' `MulIsogeny`, fs5-nocm). -/
theorem fibreSimple_of_gp5 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces5) :
    G0Split.FibreSimple :=
  G0FibreSimple.fibreSimple_of_leaves t MulRigidity.mulIsogeny G0FibreSimple.rigidityHom
    ⟨G0FibreSimple.finiteDescends_proof, fibreComTrivial_of_gp5 r t gp⟩

/-- G3 for `QML3` objects (linked-tate). -/
theorem qmModelG3_of_gp5 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces5) :
    LinkedTate.QMModelG3 :=
  LinkedTate.qmModelG3_of r.r7a r.r6 t.t5 (LinkedTate.goodRedG3Bridge_of_torsion LTGoodRed.goodRedTorsion)

/-- Prop. TS for every admissible cover (prop-ts, prop-ts-glue). -/
theorem propTSAll_of_gp5 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces5) :
    G0ModField.PropTSAll :=
  PropTSGlue.propTSAll_of_pieces'' t.t2 (LeafAdopt.R1R2fp_of_rep r.r1r2) (mobiusGlue_of_t5' t)
    gp.verticalResidueSeparable gp.snSpecialize gp.kummerCompositum gp.kummerAbhyankarFinGlue
    gp.kummerOtherBranchFin gp.kummerVerticalFin gp.kummerAbhyankarInfGlue gp.kummerOtherBranchInf
    gp.kummerVerticalInf gp.heckeIrreducible gp.heckeNormalizationIrr gp.heckeDegree gp.heckeBranch
    gp.heckeNoVertRam

/-- The period map's glue for the leaf's own triple (period-map). -/
theorem periodMapGlue_of_gp5 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces5) :
    G0Split.FibreQM.PeriodMapGlue (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep r.r1r2))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep r.r1r2))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep r.r1r2)) :=
  G0Split.FibreQM.PeriodMapH.periodMapGlue_own _ gp.baseChangeClassUnique (gp.piTwistC r.r1r2)
    gp.qmTwistLattice
    (G0Split.FibreQM.PeriodMapH.piCMC_of _ _ _ (G0Split.FibreQM.own_spec _).1
      (G0Split.FibreQM.own_spec _).2.2 gp.baseChangeClassUnique (gp.piTwistC r.r1r2) gp.cmDescends)
    (G0Split.FibreQM.PeriodMapH.cmFixedHasCM_of t.t11a)

/-- **`GluePieces` from `GluePieces5` and the leaf bundles** (linked-ram; g0-assemble3's proof with lt-goodred's
`goodRedTorsion`, `qmEndRank_of_leaves` and linked-ram's `linkedRam_of'`). -/
theorem gluePieces_of_gluePieces5 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces5) :
    GluePieces where
  dimFinite := G0Split.dimFinite
  dimBaseChange := G0Split.dimBaseChange
  fibreSimple := fibreSimple_of_gp5 r t gp
  productModelHeight := ZInQ.UnifDims.productModelHeight_of_unifOfDim gp.analyticUniformizationOfDim
  stableHeightBaseChange := G0StableBC.stableHeightBaseChange_of_hodgeLine
    (ZInQ.HeightBC.g0_hodgeLine_iff.mpr (ZInQ.HeightBC.hodgeLineBaseChange_of_two
      gp.hodgeBCInjective gp.omegaBaseChange))
  productExists := G0Product.productExists
  reverseIsogeny := G0RevIsog.reverseIsogeny_of_leaves3 r.toR3 G0Split.dimFinite
  thetaPoint := G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios
    (G0Split.FibreQM.fibreQMPeriod_main_rep r.r1r2 (mobiusGlue_of_t5' t) gp.qmHauptmodul
      t.t35 t.t11a gp.qmClassNumberOne (gp.r1bFamily r.r1r2) (periodMapGlue_of_gp5 r t gp)
      (G0Split.FibreQM.PeriodMap.hauptmodulUnique_of' gp.s8Nonzero gp.sphereFactorAffine)
      (G0Split.FibreQM.PeriodMap.qmDenZeroCM3_of'' gp.s8Nonzero gp.s8WeightExact
        gp.valenceBoundGammaStar)
      gp.cPtsTransport)
    gp.thetaRatiosAlgebraic
  modularConstituent := modularConstituent_of_field t
    (G0ModField.fibreCoverExists_of_propTSAll' t.t5 (propTSAll_of_gp5 r t gp)
      G0ModField.unramifiedConjugates)
    (G0ModField.KernelField.kernelFieldExists_of_descent t.t6 r.r7a r.r6 t.t5 t.t27
      (fibreComTrivial_of_gp5 r t gp) MulRigidity.mulIsogeny gp.twistDescent)
    UnramTate.unramifiedSup_mf
    (G0AssembleMod.afterG7_of3 r.toR3 t
      ⟨RvGP2.burnsideAbsIrred, gp.r14Det,
        ZInQ.Contrib.R10.g9Glue_of_deRhamComparisonHT r.r10,
        G0Galois.g10Glue_of_conjTwist
          (G0Galois.conjTwistNontrivial_of_leaves t.t5 t.t26 t.t35 gp.homLinearLift),
        G0Galois.g12Weight_of_senTwist gp.senTwist gp.finiteImageHT,
        G0Galois.detTate_of_leaves gp.t09SymmIsogenyExists gp.isogenyQuasiInverse
          gp.divisiblePoints t.t26,
        G0AssembleMod.resQFiniteIndex⟩
      (G0ModNewform.dirichletOfFinite_of_t17 t.t17) gp.carayolR17
      Swan.swanIndependent_proved Swan.swanIntegral_proved
      Swan.adaptedExists_proved
      (LinkedTate.modelG3G6_of (fibreSimple_of_gp5 r t gp) (qmModelG3_of_gp5 r t gp))
      (LinkedTate.linkedTateData_of_frobRam t.t7 t.t26 (fibreSimple_of_gp5 r t gp)
        (LTGoodRed.QM.qmEndRank_of_leaves t.t6 t.t27)
        (UnramTate.linkedFrobRam_of gp.linkedFrob
          (UnramTate.linkedRam_of' (qmModelG3_of_gp5 r t gp)
            (UnramTate.kernelFieldBreaks_of' gp.upperBreakBound gp.betaTrivialAtTwo)
            UnramTate.localInertiaGlobal UnramTate.upperAbsInertia
            (UnramTate.tateRamAtThreeD_of_leaves r.r6 t.t5 gp.upperBreakBound)))))
  heightCopies := G0HeightCopies.heightCopiesAgree

/-- **G0 after linked-ram**: `ResearchLeaves4`, `TextbookLeaves` and `GluePieces5` imply `ZInQ.SixContactMin`. -/
theorem sixContactMin_of_leaves5 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces5) :
    ZInQ.SixContactMin :=
  sixContactMin_of_leavesR3 r.toR3 t (gluePieces_of_gluePieces5 r t gp)

end HSyn

end

end LinkedRamBundle

#print axioms HSyn.gluePieces_of_gluePieces5
#print axioms HSyn.sixContactMin_of_leaves5
