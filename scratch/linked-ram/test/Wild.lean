import Mathlib

/-! linked-ram: wild elements of `G_{ℚ_p}` fix everything of small orbit (standalone Mathlib check). -/

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
