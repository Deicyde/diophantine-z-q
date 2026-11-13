import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.HDecomp.Descent.B3Assembly

/-!
# g8-local, part A: wild inertia of `G_{ℚ_p}` on roots of unity, on finite sets, and on
locally constant cochains

Task g8-local (2026-11-13). Elementary local-field lemmas for `LadicCond`'s `G_{ℚ_p}`
(`PkgI4.GQp p`), its wild inertia `LadicCond.wildSet` and the decomposition map `PkgI4.decomp`.

* `fix_of_wild_pow` (the averaging argument): a wild `σ` with `σ^m x = x`, `p ∤ m`, fixes `x`.
  Its proof, and those of `norm_aut`, `wildSet_mul`, `wildSet_pow`, `norm_natCast_kbar`,
  `norm_sum_range_lt`, are copied from `scratch/g15-ram/G15Ram.lean` (§2b, §2d), which is a
  scratch file and cannot be imported.
* `exists_ppow_fix`: for a wild `σ` and a finite `S ⊆ ℚ̄_p`, some `σ^{p^a}` fixes `S` (wild inertia
  is pro-`p`, at every finite level).
* `fix_of_wild_rootOfUnity`, `fix_of_wild_pRootOfUnity`, `fix_of_wild_root`: wild inertia fixes
  the `n`-th roots of unity for `n = p^e n'`, `e ≤ 1`, `p ∤ n'`.
* `decomp_ppow_mem`: for `E ⊆ ℚ̄` finite over `ℚ`, `(decomp σ)^{p^a} ∈ G_E`.
* `cyc_decomp_eq_one`: the cyclotomic character mod such an `N` is trivial on `decomp(P_p)`.
* `cochain_eq_one_of_wild`: a locally constant `β : G_ℚ → ℂ^×`, multiplicative on `G_L`, with
  `β(decomp σ)² = 1`, is `1` at `decomp σ` for wild `σ` with `decomp σ ∈ G_L` and `p` odd.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.G8Local

open PkgI4 LadicCond

variable {p : ℕ} [Fact p.Prime]

/-! ### §1. Copied from g15-ram (§2b, §2d) -/

/-- `G_{ℚ_p}` acts isometrically on `ℚ̄_p` (copied from g15-ram's `norm_aut'`). -/
theorem norm_aut (σ : GQp p) (y : Kbar p) : ‖σ y‖ = ‖y‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ y).symm

theorem wildSet_mul {σ τ : GQp p} (hσ : σ ∈ wildSet) (hτ : τ ∈ wildSet) : σ * τ ∈ wildSet := by
  intro x hx
  have hτx : τ x ≠ 0 := (map_ne_zero τ).mpr hx
  have he : (σ * τ) x - x = (σ (τ x) - τ x) + (τ x - x) := by
    rw [AlgEquiv.mul_apply]; ring
  rw [he]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ (hτ x hx))
  have := hσ (τ x) hτx
  rwa [norm_aut] at this

theorem wildSet_pow {σ : GQp p} (hσ : σ ∈ wildSet) (k : ℕ) : σ ^ k ∈ wildSet := by
  induction k with
  | zero => rw [pow_zero]; exact one_mem_wildSet
  | succ k ih => rw [pow_succ]; exact wildSet_mul ih hσ

theorem norm_natCast_kbar {m : ℕ} (hm : ¬ p ∣ m) : ‖(m : Kbar p)‖ = 1 := by
  have h := PadicAlgCl.norm_extends p (m : ℚ_[p])
  have e : ((m : ℚ_[p]) : PadicAlgCl p) = (m : Kbar p) := map_natCast (algebraMap ℚ_[p] _) m
  rw [e] at h
  rw [h, Padic.norm_natCast_eq_one_iff]
  exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hm)

/-- In an ultrametric normed group, a finite sum of terms of norm `< c` has norm `< c`. -/
theorem norm_sum_range_lt {f : ℕ → Kbar p} {c : ℝ} (hc : 0 < c) (m : ℕ)
    (hf : ∀ k < m, ‖f k‖ < c) : ‖∑ k ∈ Finset.range m, f k‖ < c := by
  induction m with
  | zero => simpa using hc
  | succ m ih =>
    rw [Finset.sum_range_succ]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
      (max_lt (ih fun k hk => hf k (by omega)) (hf m (by omega)))

/-- **The averaging argument** (copied from g15-ram). A wild `σ` with `σ^m x = x`, `p ∤ m`,
fixes `x`. -/
theorem fix_of_wild_pow {σ : GQp p} (hσ : σ ∈ wildSet) {m : ℕ} (_hm0 : 0 < m) (hpm : ¬ p ∣ m)
    {x : Kbar p} (hx : (σ ^ m) x = x) : σ x = x := by
  set S := ∑ k ∈ Finset.range m, (σ ^ k) x with hS
  have hσS : σ S = S := by
    have h1 : σ S = ∑ k ∈ Finset.range m, (σ ^ (k + 1)) x := by
      rw [hS, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_succ', AlgEquiv.mul_apply]
    have h2 := Finset.sum_range_succ' (fun k => (σ ^ k) x) m
    have h3 := Finset.sum_range_succ (fun k => (σ ^ k) x) m
    simp only [pow_zero, AlgEquiv.one_apply] at h2
    rw [hx] at h3
    rw [h1]
    rw [← hS] at h3
    linear_combination -(h3.symm.trans h2)
  have hkS : ∀ k : ℕ, (σ ^ k) S = S := by
    intro k
    induction k with
    | zero => rw [pow_zero, AlgEquiv.one_apply]
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hσS]
  have hm : (m : Kbar p) ≠ 0 := by
    intro h
    have := norm_natCast_kbar (p := p) hpm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  set y := (m : Kbar p)⁻¹ * S with hy
  have hky : ∀ k : ℕ, (σ ^ k) y = y := by
    intro k
    rw [hy, map_mul, map_inv₀, map_natCast, hkS]
  set z := x - y with hz
  have hz0 : z = 0 := by
    by_contra hne
    have hsum : ∑ k ∈ Finset.range m, (z - (σ ^ k) z) = (m : Kbar p) * z := by
      have hterm : ∀ k ∈ Finset.range m, z - (σ ^ k) z = x - (σ ^ k) x := by
        intro k _
        rw [hz, map_sub, hky]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← hS, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, hz, hy, mul_sub, ← mul_assoc, mul_inv_cancel₀ hm,
        one_mul]
    have hlt : ‖∑ k ∈ Finset.range m, (z - (σ ^ k) z)‖ < ‖z‖ := by
      apply norm_sum_range_lt (norm_pos_iff.mpr hne)
      intro k _
      rw [norm_sub_rev]
      exact wildSet_pow hσ k z hne
    rw [hsum, norm_mul, norm_natCast_kbar hpm, one_mul] at hlt
    exact lt_irrefl _ hlt
  have hxy : x = y := sub_eq_zero.mp hz0
  rw [hxy]
  have := hky 1
  rwa [pow_one] at this

/-! ### §2. Wild inertia is pro-`p` at every finite level -/

instance isGalois_Kbar : IsGalois ℚ_[p] (Kbar p) := ⟨⟩

/-- Every `σ ∈ G_{ℚ_p}` has a positive power fixing a given finite set. -/
theorem exists_pow_fix (σ : GQp p) (S : Set (Kbar p)) [Finite S] :
    ∃ k : ℕ, 0 < k ∧ ∀ y ∈ S, (σ ^ k) y = y := by
  let F := FiniteGaloisIntermediateField.adjoin ℚ_[p] S
  have : Normal ℚ_[p] F.toIntermediateField := inferInstance
  set s := AlgEquiv.restrictNormalHom F.toIntermediateField σ with hs
  refine ⟨orderOf s, orderOf_pos s, fun y hy => ?_⟩
  have hsm : AlgEquiv.restrictNormalHom F.toIntermediateField (σ ^ orderOf s) = 1 := by
    rw [map_pow, ← hs, pow_orderOf_eq_one]
  have hyF : y ∈ F.toIntermediateField := FiniteGaloisIntermediateField.subset_adjoin ℚ_[p] S hy
  exact (AlgEquiv.restrictNormal_eq_one_iff F.toIntermediateField (σ ^ orderOf s)).mp hsm y hyF

/-- **Wild inertia is pro-`p` (finite level).** For a wild `σ` and a finite `S ⊆ ℚ̄_p`, some
`σ^{p^a}` fixes `S` pointwise. -/
theorem exists_ppow_fix {σ : GQp p} (hσ : σ ∈ wildSet) (S : Set (Kbar p)) [Finite S] :
    ∃ a : ℕ, ∀ y ∈ S, (σ ^ (p ^ a)) y = y := by
  obtain ⟨k, hk, hkS⟩ := exists_pow_fix σ S
  obtain ⟨a, m, hpm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk.ne' p
    (Fact.out : p.Prime).ne_one
  refine ⟨a, fun y hy => ?_⟩
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hkm; omega)
  apply fix_of_wild_pow (wildSet_pow hσ (p ^ a)) hm0 hpm
  rw [← pow_mul, ← hkm]
  exact hkS y hy

/-! ### §3. Wild inertia on roots of unity -/

/-- **Inertia fixes roots of unity of order prime to `p`.** If `σ` is wild, `x^n = 1`, `n > 0`,
`p ∤ n`, then `σ x = x`. (Write `w = σx/x`: `w^n = 1`, and `‖w^j − 1‖ < 1` for all `j` by
wildness at `x^j`; if `w ≠ 1` then `0 = ∑_{j<n} w^j = n + ∑(w^j − 1)` has norm `1`.) -/
theorem fix_of_wild_rootOfUnity {σ : GQp p} (hσ : σ ∈ wildSet) {n : ℕ} (hn : 0 < n)
    (hpn : ¬ p ∣ n) {x : Kbar p} (hx : x ^ n = 1) : σ x = x := by
  have hx0 : x ≠ 0 := by
    rintro rfl; rw [zero_pow hn.ne'] at hx; exact zero_ne_one hx
  set w := σ x * x⁻¹ with hw
  have hwj : ∀ j : ℕ, w ^ j = σ (x ^ j) * (x ^ j)⁻¹ := by
    intro j; rw [hw, mul_pow, inv_pow, map_pow]
  have hwn : w ^ n = 1 := by rw [hwj, hx, map_one, inv_one, mul_one]
  have hlt : ∀ j : ℕ, ‖w ^ j - 1‖ < 1 := by
    intro j
    have hxj : x ^ j ≠ 0 := pow_ne_zero j hx0
    have h := hσ (x ^ j) hxj
    have hnx : 0 < ‖x ^ j‖ := norm_pos_iff.mpr hxj
    have he : w ^ j - 1 = (σ (x ^ j) - x ^ j) * (x ^ j)⁻¹ := by
      rw [hwj]; field_simp
    rw [he, norm_mul, norm_inv, mul_inv_lt_iff₀ hnx, one_mul]
    exact h
  have hw1 : w = 1 := by
    by_contra hne
    have hsum : ∑ j ∈ Finset.range n, w ^ j = 0 := by
      have h := geom_sum_mul w n
      rw [hwn, sub_self] at h
      exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)
    have hsplit : ∑ j ∈ Finset.range n, w ^ j =
        (n : Kbar p) + ∑ j ∈ Finset.range n, (w ^ j - 1) := by
      rw [Finset.sum_sub_distrib]; simp
    have hs : ‖∑ j ∈ Finset.range n, (w ^ j - 1)‖ < ‖(n : Kbar p)‖ := by
      rw [norm_natCast_kbar hpn]
      exact norm_sum_range_lt one_pos n fun j _ => hlt j
    have hnorm : ‖(n : Kbar p) + ∑ j ∈ Finset.range n, (w ^ j - 1)‖ = ‖(n : Kbar p)‖ := by
      rw [add_comm]
      exact IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hs.ne |>.trans
        (max_eq_right hs.le)
    rw [← hsplit, hsum, norm_zero, norm_natCast_kbar hpn] at hnorm
    exact zero_ne_one hnorm
  rw [hw] at hw1
  have := congrArg (· * x) hw1
  simp only [one_mul] at this
  rwa [mul_assoc, inv_mul_cancel₀ hx0, mul_one] at this

/-- `σ^j x = x^{c^j}` when `σ x = x^c`. -/
theorem pow_apply_of_apply_eq_pow {σ : GQp p} {x : Kbar p} {c : ℕ} (h : σ x = x ^ c) (j : ℕ) :
    (σ ^ j) x = x ^ (c ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, h, ← pow_mul, pow_succ', mul_comm]

/-- **Wild inertia fixes the `p`-th roots of unity.** If `σ` is wild and `x^p = 1` then
`σ x = x`: `σ x = x^c` with `p ∤ c`, so `σ^{p−1} x = x^{c^{p−1}} = x` (Fermat), and the averaging
argument applies with `m = p − 1`. -/
theorem fix_of_wild_pRootOfUnity {σ : GQp p} (hσ : σ ∈ wildSet) {x : Kbar p} (hx : x ^ p = 1) :
    σ x = x := by
  have hp := (Fact.out : p.Prime)
  by_cases hx1 : x = 1
  · rw [hx1, map_one]
  have hord : orderOf x = p := orderOf_eq_prime hx hx1
  have hprim : IsPrimitiveRoot x p := IsPrimitiveRoot.iff_orderOf.mpr hord
  have hσx : (σ x) ^ p = 1 := by rw [← map_pow, hx, map_one]
  obtain ⟨c, hcp, hc⟩ := hprim.eq_pow_of_pow_eq_one hσx
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hc
    have : σ x = σ 1 := by rw [← hc, map_one]
    exact hx1 (σ.injective this)
  have hpc : ¬ p ∣ c := fun h => hc0 (Nat.eq_zero_of_dvd_of_lt h hcp)
  apply fix_of_wild_pow hσ (Nat.sub_pos_of_lt hp.one_lt) (m := p - 1)
  · intro h
    have h1 : p ∣ 1 := by
      have := Nat.dvd_sub (dvd_refl p) h
      rwa [Nat.sub_sub_self hp.one_lt.le] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  · rw [pow_apply_of_apply_eq_pow hc.symm]
    have hferm : c ^ (p - 1) ≡ 1 [MOD p] := by
      have := Nat.ModEq.pow_totient (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpc))
      rwa [Nat.totient_prime hp] at this
    have hmod : c ^ (p - 1) % p = 1 := by
      rw [hferm]; exact Nat.mod_eq_of_lt hp.one_lt
    rw [← Nat.div_add_mod (c ^ (p - 1)) p, hmod, pow_add, pow_mul, hx, one_pow, one_mul,
      pow_one]

/-- **Wild inertia fixes the `N`-th roots of unity** for `N = p^e N'`, `e ≤ 1`, `p ∤ N'`. -/
theorem fix_of_wild_root {σ : GQp p} (hσ : σ ∈ wildSet) {N N' : ℕ} (hN' : 0 < N')
    (hpN' : ¬ p ∣ N') (hN : N = N' ∨ N = p * N') {x : Kbar p} (hx : x ^ N = 1) : σ x = x := by
  rcases hN with rfl | rfl
  · exact fix_of_wild_rootOfUnity hσ hN' hpN' hx
  · have hp := (Fact.out : p.Prime)
    have hx0 : x ≠ 0 := by
      rintro rfl; rw [zero_pow (Nat.mul_pos hp.pos hN').ne'] at hx; exact zero_ne_one hx
    have ha : σ (x ^ p) = x ^ p := by
      apply fix_of_wild_rootOfUnity hσ hN' hpN'
      rw [← pow_mul, hx]
    have hb : σ (x ^ N') = x ^ N' := by
      apply fix_of_wild_pRootOfUnity hσ
      rw [← pow_mul, mul_comm, hx]
    have hcop : Nat.Coprime p N' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN'
    have hbez : (p : ℤ) * Nat.gcdA p N' + (N' : ℤ) * Nat.gcdB p N' = 1 := by
      have := Nat.gcd_eq_gcd_ab p N'
      rw [hcop] at this
      exact_mod_cast this.symm
    have hxe : x = (x ^ p) ^ (Nat.gcdA p N') * (x ^ N') ^ (Nat.gcdB p N') := by
      rw [← zpow_natCast, ← zpow_natCast (a := x) N', ← zpow_mul, ← zpow_mul,
        ← zpow_add₀ hx0, hbez, zpow_one]
    rw [hxe, map_mul, map_zpow₀, map_zpow₀, ha, hb]

/-! ### §4. Transport to `ℚ̄` through the decomposition map -/

variable {jQ : AlgebraicClosure ℚ →+* Kbar p}

/-- If `jQ` intertwines `decomp p σ` with `σ`, then `decomp p σ` fixes `x` iff `σ` fixes `jQ x`. -/
theorem decomp_apply_eq_iff
    (hj : ∀ (σ : GQp p) (x : AlgebraicClosure ℚ), jQ (decomp p σ x) = σ (jQ x))
    (σ : GQp p) (x : AlgebraicClosure ℚ) : decomp p σ x = x ↔ σ (jQ x) = jQ x := by
  rw [← hj]
  exact jQ.injective.eq_iff.symm

/-- **`(decomp σ)^{p^a} ∈ G_E`** for a wild `σ` and `E ⊆ ℚ̄` finite over `ℚ`. -/
theorem decomp_ppow_mem
    (hj : ∀ (σ : GQp p) (x : AlgebraicClosure ℚ), jQ (decomp p σ x) = σ (jQ x))
    {σ : GQp p} (hσ : σ ∈ wildSet) (E : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ E] : ∃ a : ℕ, (decomp p σ) ^ (p ^ a) ∈ E.fixingSubgroup := by
  let b := Module.finBasis ℚ E
  let S : Set (Kbar p) := Set.range fun i => jQ (b i : AlgebraicClosure ℚ)
  haveI : Finite S := Set.finite_range _ |>.to_subtype
  obtain ⟨a, ha⟩ := exists_ppow_fix hσ S
  refine ⟨a, ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff]
  have hb : ∀ i, (decomp p σ ^ (p ^ a)) (b i : AlgebraicClosure ℚ) = b i := by
    intro i
    rw [← map_pow, decomp_apply_eq_iff hj]
    exact ha _ ⟨i, rfl⟩
  have hlin : ((decomp p σ ^ (p ^ a) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toLinearMap ∘ₗ
      E.val.toLinearMap) = E.val.toLinearMap := b.ext fun i => hb i
  intro x hx
  exact LinearMap.congr_fun hlin ⟨x, hx⟩

/-! ### §5. The cyclotomic character on `decomp(P_p)` -/

open GlueDescent.B2Q in
/-- **`cyc_N(decomp σ) = 1`** for wild `σ` and `N = p^e N'` with `e ≤ 1`, `p ∤ N'`. -/
theorem cyc_decomp_eq_one
    (hj : ∀ (σ : GQp p) (x : AlgebraicClosure ℚ), jQ (decomp p σ x) = σ (jQ x))
    {σ : GQp p} (hσ : σ ∈ wildSet) {N N' : ℕ} [NeZero N] (hN' : 0 < N') (hpN' : ¬ p ∣ N')
    (hN : N = N' ∨ N = p * N') : cyc N (decomp p σ) = 1 := by
  by_cases h1 : N = 1
  · subst h1; exact Subsingleton.elim _ _
  haveI : Fact (1 < N) := ⟨by have := NeZero.ne N; omega⟩
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  apply Units.ext
  rw [Units.val_one]
  have hfix : ∀ t ∈ rootsOfUnity N (AlgebraicClosure ℚ),
      (toRingAut (decomp p σ)) (t : AlgebraicClosure ℚ) = (t : AlgebraicClosure ℚ) ^ (1 : ZMod N).val := by
    intro t ht
    rw [ZMod.val_one, pow_one]
    change decomp p σ (t : AlgebraicClosure ℚ) = t
    rw [decomp_apply_eq_iff hj]
    apply fix_of_wild_root hσ hN' hpN' hN
    rw [← map_pow]
    have : ((t : AlgebraicClosure ℚ)) ^ N = 1 := by
      have := (mem_rootsOfUnity N t).mp ht
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    rw [this, map_one]
  exact (modularCyclotomicCharacter.unique (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N) _ hfix).symm

open GlueDescent.B2Q in
/-- `galChar χ (decomp σ) = 1` under the same hypotheses. -/
theorem galChar_decomp_eq_one
    (hj : ∀ (σ : GQp p) (x : AlgebraicClosure ℚ), jQ (decomp p σ x) = σ (jQ x))
    {σ : GQp p} (hσ : σ ∈ wildSet) {N N' : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hN' : 0 < N') (hpN' : ¬ p ∣ N') (hN : N = N' ∨ N = p * N') :
    galChar χ (decomp p σ) = 1 := by
  show χ.toUnitHom (cyc N (decomp p σ)) = 1
  rw [cyc_decomp_eq_one hj hσ hN' hpN' hN, map_one]

/-! ### §6. Locally constant cochains on `decomp(P_p)` at odd `p` -/

/-- **A locally constant `β`, multiplicative on `G_L`, with `β(decomp σ)² = 1`, is `1` at
`decomp σ`** for wild `σ` with `decomp σ ∈ G_L`, `p` odd (a pro-`p` group has no quotient of
order two; N5 L833-835). -/
theorem cochain_eq_one_of_wild
    (hj : ∀ (σ : GQp p) (x : AlgebraicClosure ℚ), jQ (decomp p σ x) = σ (jQ x))
    (hp2 : p ≠ 2) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    (β : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℂˣ) (hβl : IsLocallyConstant β)
    (hβm : ∀ x ∈ L.fixingSubgroup, ∀ y ∈ L.fixingSubgroup, β (x * y) = β x * β y)
    {σ : GQp p} (hσ : σ ∈ wildSet) (hσL : decomp p σ ∈ L.fixingSubgroup)
    (hsq : β (decomp p σ) ^ 2 = 1) : β (decomp p σ) = 1 := by
  have hβ1 : β 1 = 1 := by
    have h := hβm 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at h
    exact (mul_eq_left.mp h.symm)
  set K₀ : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    (L.fixingSubgroup : Set _) ∩ β ⁻¹' {1} with hK₀
  have hK₀open : IsOpen K₀ := L.fixingSubgroup_isOpen.inter (hβl.isOpen_fiber 1)
  have hK₀nhds : K₀ ∈ nhds (1 : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    hK₀open.mem_nhds ⟨one_mem _, hβ1⟩
  obtain ⟨E, hEfd, hEsub⟩ := (krullTopology_mem_nhds_one_iff ℚ (AlgebraicClosure ℚ) K₀).mp hK₀nhds
  haveI := hEfd
  obtain ⟨a, ha⟩ := decomp_ppow_mem hj hσ E
  have hmem := hEsub ha
  have hpow : ∀ k : ℕ, β (decomp p σ ^ k) = β (decomp p σ) ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, hβ1]
    | succ k ih =>
      rw [pow_succ, hβm _ (Subgroup.pow_mem _ hσL k) _ hσL, ih, pow_succ]
  have h1 : β (decomp p σ) ^ (p ^ a) = 1 := by rw [← hpow]; exact hmem.2
  have hcop : Nat.Coprime (p ^ a) 2 := by
    apply Nat.Coprime.pow_left
    exact (Nat.coprime_primes (Fact.out) Nat.prime_two).mpr hp2
  have := pow_gcd_eq_one.mpr ⟨h1, hsq⟩
  rwa [hcop, pow_one] at this

end ZInQ.Contrib.G8Local

end
