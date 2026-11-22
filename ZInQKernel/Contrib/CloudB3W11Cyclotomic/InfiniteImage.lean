import ZInQKernel.Contrib.CloudB3W11Cyclotomic.TowerDegree

/-!
# The cyclotomic character has infinite image on `Gal(ℚ̄_p/K)`, and algebraic twisted invariants vanish

Task cloud-b3/w11 (author D, 2026-11-16): the arithmetic edge of H-120
(`ZInQ.Contrib.HodgeSplit.TateTwistInvariants`, `ZInQKernel/Contrib/OneProof/H/TailS.lean` l. 69-72;
Tate 1967 §3.3 Thm 2). Everything is stated over the repository's genuine objects
`ZInQ.Contrib.G9.PkgI4.cyc`, `cycPow` and `cpAct`
(`ZInQKernel/Contrib/G9/I4Layer.lean` l. 829-849); nothing is redefined and nothing of
`ZInQKernel.OneProof` is imported.

## Main results

* `exists_mem_fixingSubgroup_cyc_zpow_ne_one` / `exists_mem_fixingSubgroup_cycPow_ne_one`:
  for `K/ℚ_p` finite inside `ℚ̄_p` and `i ≠ 0` there is `σ ∈ K.fixingSubgroup` with
  `χ(σ)^i ≠ 1`, that is `cycPow p σ i ≠ 1`. **This is the arithmetic infinite-image input**:
  no power `χ^i`, `i ≠ 0`, is trivial on `G_K`.
* `infinite_image_cyc`: equivalently, `χ(G_K) ⊆ ℤ_p^×` is infinite.
* `coe_eq_zero_of_forall_mem_fixingSubgroup_cycPow_smul_cpAct_eq` and
  `tateTwistInvariants_algebraic`: **H-120 for the algebraic elements of `ℂ_p`**, i.e. for `x`
  in the image of `ℚ̄_p → ℂ_p`, proved by passing from `K` to `K(x)`.

## What this does and does not give

`tateTwistInvariants_algebraic` is H-120 restricted to `x ∈ ℚ̄_p ⊆ ℂ_p`. It does **not** give
H-120: the twisted invariants form a closed `ℚ_p`-subspace of `ℂ_p` and `ℚ̄_p` is dense in
`ℂ_p`, but a closed subspace meeting a dense subset only in `0` need not be `0`. Closing H-120
needs Tate's normalised trace on the cyclotomic tower (the `IsTateTrace` construction, whose
`hcyc` and degree hypotheses are `PadicAlgCl.pow_mem_and_not_mem_fixingSubgroup` and
`PadicAlgCl.finrank_cyclotomicTower` of
`ZInQKernel.Contrib.CloudB3W11Cyclotomic.TowerDegree`); that part is not proved here.

## Proof of the infinite-image theorem

Suppose `χ(σ)^i = 1` for every `σ ∈ G_K`, and put `N = |i| > 0`, `m = [K : ℚ_p]`,
`n = N·m + 1`. Let `ζ` be a primitive `p^n`-th root of unity in `ℚ̄_p`.

* Each `χ(σ)`, `σ ∈ G_K`, is a root of `X^N − 1` in the domain `ℤ_p`, so takes at most `N`
  values; and `σ ζ` is determined by `χ(σ)` (`cyclotomicCharacter.spec`). So the `G_K`-orbit of
  `ζ` has at most `N` elements.
* `ℚ̄_p/K` is normal, so every root of `minpoly K ζ` lies in that orbit
  (`minpoly.exists_algEquiv_of_root'`); `minpoly K ζ` is separable and splits in `ℚ̄_p`, so it
  has exactly `deg` distinct roots. Hence `[K(ζ) : K] = deg (minpoly K ζ) ≤ N`.
* `φ(p^n) = [ℚ_p(ζ) : ℚ_p] ≤ [K(ζ) : ℚ_p] = m · [K(ζ) : K] ≤ m · N`, while
  `φ(p^n) = p^{N·m}(p − 1) ≥ 2^{N·m} > N·m`. Contradiction.
-/

set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace ZInQ.Contrib.CloudB3W11Cyclotomic

open Polynomial IntermediateField ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-! ## §1. `cycPow` and the cyclotomic character as a homomorphism -/

/-- The `p`-adic cyclotomic character of `G_{ℚ_p}` as a monoid homomorphism; its underlying
function is the repository's `ZInQ.Contrib.G9.PkgI4.cyc`. -/
def cycHom : GQp p →* ℤ_[p]ˣ :=
  (cyclotomicCharacter (PadicAlgCl p) p).comp (toRingEquivHom p)

theorem cycHom_apply (σ : GQp p) : cycHom p σ = cyc p σ := rfl

/-- `cycPow p σ i = 1` exactly when `χ(σ)^i = 1` in `ℤ_p^×`: the inclusion `ℤ_p → ℚ_p` is
injective. -/
theorem cyc_zpow_eq_one_iff_cycPow_eq_one (σ : GQp p) (i : ℤ) :
    cyc p σ ^ i = 1 ↔ cycPow p σ i = 1 := by
  constructor
  · intro h
    rw [cycPow, h]
    norm_num
  · intro h
    rw [cycPow] at h
    refine Units.ext ?_
    rw [Units.val_one, ← PadicInt.coe_inj]
    rw [h]
    norm_num

/-! ## §2. The arithmetic edge: no power of `χ` is trivial on `G_K` -/

/-- **The infinite-image input for H-120.** For a finite extension `K` of `ℚ_p` inside `ℚ̄_p`
and `i ≠ 0`, some `σ ∈ Gal(ℚ̄_p/K)` has `χ(σ)^i ≠ 1`. -/
theorem exists_mem_fixingSubgroup_cyc_zpow_ne_one
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (i : ℤ) (hi : i ≠ 0) : ∃ σ ∈ K.fixingSubgroup, cyc p σ ^ i ≠ 1 := by
  classical
  by_contra hcontra
  have hcon : ∀ σ ∈ K.fixingSubgroup, cyc p σ ^ i = 1 := by
    intro σ hσ
    by_contra h
    exact hcontra ⟨σ, hσ, h⟩
  have hp : p.Prime := Fact.out
  set N : ℕ := i.natAbs with hNdef
  have hN0 : 0 < N := Int.natAbs_pos.2 hi
  set m : ℕ := Module.finrank ℚ_[p] ↥K with hmdef
  set n : ℕ := N * m + 1 with hndef
  obtain ⟨ζ, hζ⟩ := PadicAlgCl.exists_isPrimitiveRoot_pow p n
  -- Every `χ(σ)`, for `σ` fixing `K`, is an `N`-th root of unity in `ℤ_p`.
  have hNpow : ∀ σ ∈ K.fixingSubgroup, ((cyc p σ : ℤ_[p]ˣ) : ℤ_[p]) ^ N = 1 := by
    intro σ hσ
    have h := hcon σ hσ
    have hunit : cyc p σ ^ N = 1 := by
      rcases Int.natAbs_eq i with he | he
      · rw [he, zpow_natCast] at h
        exact h
      · rw [he, zpow_neg, inv_eq_one, zpow_natCast] at h
        exact h
    rw [← Units.val_pow_eq_pow_val, hunit, Units.val_one]
  -- The `N`-th roots of unity of `ℤ_p`, as a finset of size at most `N`.
  set f : ℤ_[p][X] := X ^ N - Polynomial.C 1 with hfdef
  have hf0 : f ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hN0 1
  set rts : Finset ℤ_[p] := f.roots.toFinset with hrtsdef
  have hrts_card : rts.card ≤ N := by
    calc rts.card ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := Polynomial.card_roots' f
      _ = N := Polynomial.natDegree_X_pow_sub_C
  have hmem_rts : ∀ σ ∈ K.fixingSubgroup, ((cyc p σ : ℤ_[p]ˣ) : ℤ_[p]) ∈ rts := by
    intro σ hσ
    rw [hrtsdef, Multiset.mem_toFinset, Polynomial.mem_roots hf0]
    show Polynomial.eval _ f = 0
    rw [hfdef]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    rw [hNpow σ hσ, sub_self]
  -- The action of `σ` on `ζ` is read off from `χ(σ)` modulo `p ^ n`.
  set Φ : ℤ_[p] → PadicAlgCl p := fun u => ζ ^ (PadicInt.toZModPow n u).val with hΦdef
  -- The distinct roots of `minpoly K ζ`.
  have hζint : IsIntegral (↥K) ζ := Algebra.IsIntegral.isIntegral (R := ↥K) ζ
  set q : Polynomial (PadicAlgCl p) :=
    (minpoly (↥K) ζ).map (algebraMap (↥K) (PadicAlgCl p)) with hqdef
  have hinj : Function.Injective (algebraMap (↥K) (PadicAlgCl p)) :=
    (algebraMap (↥K) (PadicAlgCl p)).injective
  have hq0 : q ≠ 0 := by
    rw [hqdef, Ne, Polynomial.map_eq_zero_iff hinj]
    exact minpoly.ne_zero hζint
  have hqsep : q.Separable := by
    have hsep0 : (minpoly (↥K) ζ).Separable := Algebra.IsSeparable.isSeparable (↥K) ζ
    exact hsep0.map
  have hqsplits : q.Splits := IsAlgClosed.splits q
  have hqroots_card : q.roots.toFinset.card = (minpoly (↥K) ζ).natDegree := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hqsep),
      Polynomial.splits_iff_card_roots.1 hqsplits, hqdef,
      Polynomial.natDegree_map_eq_of_injective hinj]
  -- Each root of `minpoly K ζ` is `σ ζ` for some `σ` fixing `K`, hence in the image of `Φ`.
  have hsub : q.roots.toFinset ⊆ rts.image Φ := by
    intro β hβ
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hq0] at hβ
    have hev : (Polynomial.aeval β) (minpoly (↥K) ζ) = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map]
      exact hβ
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (K := ↥K) (L := PadicAlgCl p)
      hζint.isAlgebraic hev
    have hτmem : ((K.fixingSubgroupEquiv.symm σ : K.fixingSubgroup) : GQp p) ∈
        K.fixingSubgroup := (K.fixingSubgroupEquiv.symm σ).2
    set τ : GQp p := ((K.fixingSubgroupEquiv.symm σ : K.fixingSubgroup) : GQp p) with hτdef
    have hτapp : ∀ x, τ x = σ x :=
      congrFun (IntermediateField.coe_fixingSubgroupEquiv_symm_apply K σ)
    have hspec : τ ζ = ζ ^ (PadicInt.toZModPow n ((cyc p τ : ℤ_[p]ˣ) : ℤ_[p])).val :=
      cyclotomicCharacter.spec p τ.toRingEquiv ζ hζ.pow_eq_one
    refine Finset.mem_image.2 ⟨((cyc p τ : ℤ_[p]ˣ) : ℤ_[p]), hmem_rts τ hτmem, ?_⟩
    show ζ ^ (PadicInt.toZModPow n ((cyc p τ : ℤ_[p]ˣ) : ℤ_[p])).val = β
    rw [← hspec, hτapp ζ]
    exact hσ
  have hdeg_le : (minpoly (↥K) ζ).natDegree ≤ N := by
    rw [← hqroots_card]
    calc q.roots.toFinset.card ≤ (rts.image Φ).card := Finset.card_le_card hsub
      _ ≤ rts.card := Finset.card_image_le
      _ ≤ N := hrts_card
  -- The tower `ℚ_p ⊆ K ⊆ K(ζ)` bounds `φ(p ^ n)` by `m * deg (minpoly K ζ)`.
  set L : IntermediateField (↥K) (PadicAlgCl p) := IntermediateField.adjoin (↥K) {ζ} with hLdef
  haveI hfdL : FiniteDimensional (↥K) ↥L := IntermediateField.adjoin.finiteDimensional hζint
  haveI hfdL' : FiniteDimensional ℚ_[p] ↥L := FiniteDimensional.trans ℚ_[p] (↥K) ↥L
  have htower : m * (minpoly (↥K) ζ).natDegree = Module.finrank ℚ_[p] ↥L := by
    rw [hmdef, ← IntermediateField.adjoin.finrank hζint]
    exact Module.finrank_mul_finrank ℚ_[p] (↥K) ↥L
  have hle : IntermediateField.adjoin ℚ_[p] {ζ} ≤ L.restrictScalars ℚ_[p] := by
    rw [IntermediateField.adjoin_le_iff]
    rintro x rfl
    exact (IntermediateField.mem_restrictScalars ℚ_[p]).2
      (IntermediateField.subset_adjoin (↥K) _ rfl)
  haveI : FiniteDimensional ℚ_[p] ↥(L.restrictScalars ℚ_[p]) := hfdL'
  have hfr : Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ζ}) ≤
      Module.finrank ℚ_[p] ↥L :=
    LinearMap.finrank_le_finrank_of_injective
      (f := (IntermediateField.inclusion hle).toLinearMap)
      (IntermediateField.inclusion_injective hle)
  have htot : Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ζ}) = (p ^ n).totient := by
    rw [← PadicAlgCl.cyclotomicTower_eq_adjoin p n hζ]
    exact PadicAlgCl.finrank_cyclotomicTower_eq_totient p n
  -- `φ(p ^ n) > N * m`, the contradiction.
  have hbig : N * m < (p ^ n).totient := by
    rw [hndef, Nat.totient_prime_pow hp (Nat.succ_pos (N * m))]
    have h1 : N * m < 2 ^ (N * m) := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ (N * m) ≤ p ^ (N * m) := Nat.pow_le_pow_left hp.two_le _
    have h3 : p ^ (N * m + 1 - 1) = p ^ (N * m) := by norm_num
    have h4 : 1 ≤ p - 1 := by have := hp.two_le; omega
    calc N * m < 2 ^ (N * m) := h1
      _ ≤ p ^ (N * m) := h2
      _ = p ^ (N * m + 1 - 1) := h3.symm
      _ ≤ p ^ (N * m + 1 - 1) * (p - 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hchain : (p ^ n).totient ≤ m * N := by
    calc (p ^ n).totient = Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ζ}) := htot.symm
      _ ≤ Module.finrank ℚ_[p] ↥L := hfr
      _ = m * (minpoly (↥K) ζ).natDegree := htower.symm
      _ ≤ m * N := Nat.mul_le_mul_left m hdeg_le
  rw [Nat.mul_comm m N] at hchain
  omega

/-- **The infinite-image input for H-120, over the repository's `cycPow`.** -/
theorem exists_mem_fixingSubgroup_cycPow_ne_one
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (i : ℤ) (hi : i ≠ 0) : ∃ σ ∈ K.fixingSubgroup, cycPow p σ i ≠ 1 := by
  obtain ⟨σ, hσ, hne⟩ := exists_mem_fixingSubgroup_cyc_zpow_ne_one p K i hi
  exact ⟨σ, hσ, fun h => hne ((cyc_zpow_eq_one_iff_cycPow_eq_one p σ i).2 h)⟩

/-- **The cyclotomic character has infinite image on `Gal(ℚ̄_p/K)`** for every finite `K/ℚ_p`
inside `ℚ̄_p`. (A finite subgroup of `ℤ_p^×` is killed by its own order.) -/
theorem infinite_image_cyc (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] :
    (cycHom p '' (K.fixingSubgroup : Set (GQp p))).Infinite := by
  intro hfin
  have hcoe : ((Subgroup.map (cycHom p) K.fixingSubgroup : Subgroup ℤ_[p]ˣ) : Set ℤ_[p]ˣ) =
      cycHom p '' (K.fixingSubgroup : Set (GQp p)) := Subgroup.coe_map _ _
  haveI hfinite : Finite ↥(Subgroup.map (cycHom p) K.fixingSubgroup) := by
    have hfin' : ((Subgroup.map (cycHom p) K.fixingSubgroup : Subgroup ℤ_[p]ˣ) :
        Set ℤ_[p]ˣ).Finite := by rw [hcoe]; exact hfin
    exact hfin'.to_subtype
  set k : ℕ := Nat.card ↥(Subgroup.map (cycHom p) K.fixingSubgroup) with hk
  have hk0 : 0 < k := Nat.card_pos
  obtain ⟨σ, hσ, hne⟩ :=
    exists_mem_fixingSubgroup_cyc_zpow_ne_one p K (k : ℤ) (by exact_mod_cast hk0.ne')
  refine hne ?_
  have hmem : cycHom p σ ∈ Subgroup.map (cycHom p) K.fixingSubgroup :=
    Subgroup.mem_map_of_mem _ hσ
  have hone := pow_card_eq_one' (G := ↥(Subgroup.map (cycHom p) K.fixingSubgroup))
    (x := ⟨cycHom p σ, hmem⟩)
  rw [zpow_natCast, ← cycHom_apply]
  exact congrArg Subtype.val hone

/-! ## §3. The finishing step of Tate's argument -/

/-- **The finishing step.** If some positive power of `χ^k` is trivial on `Gal(ℚ̄_p/K)` for a
finite `K/ℚ_p`, then `k = 0`.

This is the form in which the infinite image is consumed at the end of Tate's argument: the
normalised-trace step produces `n > 0` with `ψ(σ)^n = 1` for every `σ ∈ G_K`, where
`ψ = χ^k` is the twist; this theorem turns that into `k = 0`. -/
theorem eq_zero_of_exists_pow_cyc_zpow_eq_one
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (k : ℤ)
    (h : ∃ n : ℕ, 0 < n ∧ ∀ σ ∈ K.fixingSubgroup, (cyc p σ ^ k) ^ n = 1) : k = 0 := by
  by_contra hk
  obtain ⟨n, hn, hall⟩ := h
  have hkn : k * (n : ℤ) ≠ 0 := mul_ne_zero hk (by exact_mod_cast hn.ne')
  obtain ⟨σ, hσ, hne⟩ := exists_mem_fixingSubgroup_cyc_zpow_ne_one p K (k * (n : ℤ)) hkn
  refine hne ?_
  rw [zpow_mul, zpow_natCast]
  exact hall σ hσ

/-! ## §4. H-120 for the algebraic elements of `ℂ_p` -/

/-- **Algebraic twisted invariants vanish.** If `y ∈ ℚ̄_p` and its image in `ℂ_p` is fixed by
the `i`-twisted action of `Gal(ℚ̄_p/K)` with `i ≠ 0` and `K/ℚ_p` finite, then `y = 0`. The
proof passes from `K` to the still finite `K(y)`, where the twist is a pure scalar. -/
theorem coe_eq_zero_of_forall_mem_fixingSubgroup_cycPow_smul_cpAct_eq
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (i : ℤ) (hi : i ≠ 0) (y : PadicAlgCl p)
    (hy : ∀ σ ∈ K.fixingSubgroup,
      cycPow p σ i • cpAct p σ ((y : ℂ_[p])) = ((y : ℂ_[p]))) :
    ((y : ℂ_[p])) = 0 := by
  classical
  have hyint : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral (R := ℚ_[p]) y
  set E : IntermediateField ℚ_[p] (PadicAlgCl p) := K ⊔ IntermediateField.adjoin ℚ_[p] {y}
    with hEdef
  haveI : FiniteDimensional ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {y}) :=
    IntermediateField.adjoin.finiteDimensional hyint
  haveI : FiniteDimensional ℚ_[p] ↥E :=
    IntermediateField.finiteDimensional_sup K (IntermediateField.adjoin ℚ_[p] {y})
  obtain ⟨σ, hσE, hσne⟩ := exists_mem_fixingSubgroup_cycPow_ne_one p E i hi
  have hσK : σ ∈ K.fixingSubgroup :=
    IntermediateField.fixingSubgroup_le (le_sup_left (b := IntermediateField.adjoin ℚ_[p] {y}))
      hσE
  have hyE : y ∈ E := by
    refine (le_sup_right (a := K) (b := IntermediateField.adjoin ℚ_[p] {y})) ?_
    exact IntermediateField.mem_adjoin_simple_self ℚ_[p] y
  have hfix : σ y = y := (IntermediateField.mem_fixingSubgroup_iff E σ).1 hσE y hyE
  have hcp : cpAct p σ ((y : ℂ_[p])) = ((y : ℂ_[p])) := by
    rw [cpAct_coe, hfix]
  have hsmul : cycPow p σ i • ((y : ℂ_[p])) = ((y : ℂ_[p])) := by
    have h := hy σ hσK
    rwa [hcp] at h
  rw [Algebra.smul_def] at hsmul
  have hfac : (algebraMap ℚ_[p] ℂ_[p] (cycPow p σ i) - 1) * ((y : ℂ_[p])) = 0 := by
    rw [sub_mul, one_mul, hsmul, sub_self]
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd (by
      have : algebraMap ℚ_[p] ℂ_[p] (cycPow p σ i) = algebraMap ℚ_[p] ℂ_[p] 1 := by
        rw [map_one]; linear_combination h
      exact (algebraMap ℚ_[p] ℂ_[p]).injective this) hσne
  · exact h

/-- **H-120 for the algebraic elements of `ℂ_p`**, in the exact shape of
`ZInQ.Contrib.HodgeSplit.TateTwistInvariants` with `x` restricted to the image of `ℚ̄_p`.

This is a genuine partial result on the target and nothing more: see the module docstring for
why density of `ℚ̄_p` in `ℂ_p` does **not** upgrade it to H-120. -/
theorem tateTwistInvariants_algebraic :
    ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
      [FiniteDimensional ℚ_[p] K] (i : ℤ), i ≠ 0 → ∀ y : PadicAlgCl p,
      (∀ σ ∈ K.fixingSubgroup, cycPow p σ i • cpAct p σ ((y : ℂ_[p])) = ((y : ℂ_[p]))) →
        ((y : ℂ_[p])) = 0 :=
  fun p _ K _ i hi y hy =>
    coe_eq_zero_of_forall_mem_fixingSubgroup_cycPow_smul_cpAct_eq p K i hi y hy

end

end ZInQ.Contrib.CloudB3W11Cyclotomic
