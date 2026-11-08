import ZInQKernel.Hypotheses.PrimePattern

/-!
# The prime catalogue

Blueprint: `syntax/constants/prime-catalogue.md`.

For `W ≥ 1`, `k, B ≥ 0` and each unit residue `1 ≤ r < W`, `gcd(r, W) = 1`, the catalogue
primes `p_{r,1} < ⋯ < p_{r,k}` are the first `k` primes `p > B` with `p ≡ r (mod W)`. We index
them from `0`: `cataloguePrime W B r j` is `p_{r,j+1}`, the `j`-th element (in increasing
order) of the set of primes `p > B` with `p % W = r`, defined with `Nat.nth`. Dirichlet's
theorem (in Mathlib) shows that this set is infinite, so `Nat.nth` names genuine primes.

`catalogueProduct W k B = ∏_r ∏_{j<k} p_{r,j}` and `catalogueMax W k B = max_{r,j} p_{r,j}`
(`0` for an empty family). Neither is ever evaluated. For the fixed catalogue
`W = catalogueModulus`, `k = 22`, `B = 324`, the primes agree definitionally with
`ZInQ.cataloguePrime` of the hypothesis file, and the set of catalogue primes is
`ZInQ.catalogueSet`.
-/

namespace ZInQ.Syntax

open scoped BigOperators

/-- The unit residues `1 ≤ r < W` with `gcd(r, W) = 1`. -/
def unitResidues (W : ℕ) : Finset ℕ :=
  (Finset.range W).filter fun r => 1 ≤ r ∧ r.Coprime W

theorem mem_unitResidues {W r : ℕ} : r ∈ unitResidues W ↔ 1 ≤ r ∧ r < W ∧ r.Coprime W := by
  simp [unitResidues, and_left_comm]

/-- For `W ≥ 2` the condition `1 ≤ r` is implied by `gcd(r, W) = 1`. -/
theorem mem_unitResidues_iff_of_two_le {W r : ℕ} (hW : 2 ≤ W) :
    r ∈ unitResidues W ↔ r < W ∧ r.Coprime W := by
  rw [mem_unitResidues]
  refine ⟨fun h => h.2, fun h => ⟨Nat.pos_of_ne_zero ?_, h⟩⟩
  rintro rfl
  have := h.2
  rw [Nat.coprime_zero_left] at this
  omega

/-- `p_{r,j+1}`: the `j`-th prime (from `0`) greater than `B` with `p % W = r`. -/
noncomputable def cataloguePrime (W B r j : ℕ) : ℕ :=
  Nat.nth (fun p => p.Prime ∧ B < p ∧ p % W = r) j

/-- `catalogue_product(W, k, B) = ∏_r ∏_{j=1}^k p_{r,j}`. -/
noncomputable def catalogueProduct (W k B : ℕ) : ℕ :=
  ∏ r ∈ unitResidues W, ∏ j ∈ Finset.range k, cataloguePrime W B r j

/-- `catalogue_max(W, k, B) = max_{r,j} p_{r,j}`, `0` for an empty family. -/
noncomputable def catalogueMax (W k B : ℕ) : ℕ :=
  (unitResidues W).sup fun r => (Finset.range k).sup fun j => cataloguePrime W B r j

/-- Dirichlet: every unit residue class contains infinitely many primes above `B`. -/
theorem infinite_catalogue_class {W B r : ℕ} (hr : r ∈ unitResidues W) :
    (Set.ofPred fun p => p.Prime ∧ B < p ∧ p % W = r).Infinite := by
  obtain ⟨-, hrW, hcop⟩ := mem_unitResidues.1 hr
  have hW : W ≠ 0 := by omega
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨p, hpa, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq (max a B) hW hcop
  refine ⟨p, ⟨hp, lt_of_le_of_lt (le_max_right _ _) hpa, ?_⟩,
    lt_of_le_of_lt (le_max_left _ _) hpa⟩
  rw [hmod, Nat.mod_eq_of_lt hrW]

/-- Every catalogue index names a genuine prime `p > B` with `p ≡ r (mod W)`. -/
theorem cataloguePrime_spec {W B r : ℕ} (hr : r ∈ unitResidues W) (j : ℕ) :
    (cataloguePrime W B r j).Prime ∧ B < cataloguePrime W B r j ∧
      cataloguePrime W B r j % W = r :=
  Nat.nth_mem_of_infinite (infinite_catalogue_class hr) j

theorem cataloguePrime_prime {W B r : ℕ} (hr : r ∈ unitResidues W) (j : ℕ) :
    (cataloguePrime W B r j).Prime :=
  (cataloguePrime_spec hr j).1

theorem lt_cataloguePrime {W B r : ℕ} (hr : r ∈ unitResidues W) (j : ℕ) :
    B < cataloguePrime W B r j :=
  (cataloguePrime_spec hr j).2.1

theorem cataloguePrime_mod {W B r : ℕ} (hr : r ∈ unitResidues W) (j : ℕ) :
    cataloguePrime W B r j % W = r :=
  (cataloguePrime_spec hr j).2.2

theorem cataloguePrime_pos {W B r : ℕ} (hr : r ∈ unitResidues W) (j : ℕ) :
    0 < cataloguePrime W B r j :=
  (cataloguePrime_prime hr j).pos

/-- The catalogue primes of a class are listed in increasing order. -/
theorem cataloguePrime_strictMono {W B r : ℕ} (hr : r ∈ unitResidues W) :
    StrictMono (cataloguePrime W B r) :=
  Nat.nth_strictMono (infinite_catalogue_class hr)

theorem cataloguePrime_lt_cataloguePrime_iff {W B r : ℕ} (hr : r ∈ unitResidues W) {i j : ℕ} :
    cataloguePrime W B r i < cataloguePrime W B r j ↔ i < j :=
  (cataloguePrime_strictMono hr).lt_iff_lt

/-- The catalogue primes of a class are the *first* primes of the class above `B`: every
prime `p > B` with `p ≡ r` below `p_{r,j+1}` is one of `p_{r,1}, …, p_{r,j}`. -/
theorem exists_cataloguePrime_eq_of_lt {W B r p j : ℕ} (hr : r ∈ unitResidues W)
    (hp : p.Prime) (hBp : B < p) (hpr : p % W = r) (hlt : p < cataloguePrime W B r j) :
    ∃ i < j, cataloguePrime W B r i = p := by
  classical
  have hi : cataloguePrime W B r (Nat.count (fun p => p.Prime ∧ B < p ∧ p % W = r) p) = p :=
    Nat.nth_count (p := fun p => p.Prime ∧ B < p ∧ p % W = r) ⟨hp, hBp, hpr⟩
  refine ⟨_, ?_, hi⟩
  rw [← cataloguePrime_lt_cataloguePrime_iff hr (B := B), hi]
  exact hlt

/-- Distinct catalogue indices name distinct primes. -/
theorem cataloguePrime_injOn {W B r r' j j' : ℕ} (hr : r ∈ unitResidues W)
    (hr' : r' ∈ unitResidues W) (h : cataloguePrime W B r j = cataloguePrime W B r' j') :
    r = r' ∧ j = j' := by
  have hrr : r = r' := by
    rw [← cataloguePrime_mod hr j (B := B), ← cataloguePrime_mod hr' j' (B := B), h]
  subst hrr
  exact ⟨rfl, (cataloguePrime_strictMono hr).injective h⟩

/-! ### The catalogue product and maximum -/

theorem catalogueProduct_pos (W k B : ℕ) : 0 < catalogueProduct W k B :=
  Finset.prod_pos fun _ hr => Finset.prod_pos fun j _ => cataloguePrime_pos hr j

theorem catalogueProduct_ne_zero (W k B : ℕ) : catalogueProduct W k B ≠ 0 :=
  (catalogueProduct_pos W k B).ne'

theorem cataloguePrime_dvd_catalogueProduct {W k B r j : ℕ} (hr : r ∈ unitResidues W)
    (hj : j < k) : cataloguePrime W B r j ∣ catalogueProduct W k B :=
  (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hj)).trans (Finset.dvd_prod_of_mem _ hr)

theorem cataloguePrime_le_catalogueMax {W k B r j : ℕ} (hr : r ∈ unitResidues W)
    (hj : j < k) : cataloguePrime W B r j ≤ catalogueMax W k B :=
  (Finset.le_sup (f := fun j => cataloguePrime W B r j) (Finset.mem_range.2 hj)).trans
    (Finset.le_sup (f := fun r => (Finset.range k).sup fun j => cataloguePrime W B r j) hr)

theorem catalogueMax_le_iff {W k B n : ℕ} :
    catalogueMax W k B ≤ n ↔ ∀ r ∈ unitResidues W, ∀ j < k, cataloguePrime W B r j ≤ n := by
  simp [catalogueMax, Finset.sup_le_iff]

theorem catalogueMax_le_catalogueProduct (W k B : ℕ) :
    catalogueMax W k B ≤ catalogueProduct W k B :=
  catalogueMax_le_iff.2 fun _ hr _ hj =>
    Nat.le_of_dvd (catalogueProduct_pos W k B) (cataloguePrime_dvd_catalogueProduct hr hj)

/-- Every catalogue prime exceeds `B`, so `B# = ∏_{p ≤ B} p` is coprime to the product. -/
theorem coprime_primorial_catalogueProduct (W k B : ℕ) :
    Nat.Coprime (primorial B) (catalogueProduct W k B) := by
  refine Nat.Coprime.prod_right fun r hr => Nat.Coprime.prod_right fun j _ => ?_
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (cataloguePrime_prime hr j),
    (cataloguePrime_prime hr j).dvd_primorial_iff, not_le]
  exact lt_cataloguePrime hr j

/-- The finite set of catalogue primes. -/
noncomputable def catalogueFinset (W k B : ℕ) : Finset ℕ :=
  (unitResidues W ×ˢ Finset.range k).image fun rj => cataloguePrime W B rj.1 rj.2

theorem mem_catalogueFinset {W k B p : ℕ} :
    p ∈ catalogueFinset W k B ↔ ∃ r ∈ unitResidues W, ∃ j < k, cataloguePrime W B r j = p := by
  simp [catalogueFinset, and_assoc]

/-- The catalogue product is the product of the distinct catalogue primes. -/
theorem catalogueProduct_eq_prod_catalogueFinset (W k B : ℕ) :
    catalogueProduct W k B = ∏ p ∈ catalogueFinset W k B, p := by
  rw [catalogueFinset, Finset.prod_image, catalogueProduct, Finset.prod_product]
  rintro ⟨_, _⟩ hrj ⟨_, _⟩ hrj' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hrj hrj'
  obtain ⟨rfl, rfl⟩ := cataloguePrime_injOn hrj.1 hrj'.1 h
  rfl

theorem catalogueMax_eq_sup_catalogueFinset (W k B : ℕ) :
    catalogueMax W k B = (catalogueFinset W k B).sup id := by
  apply le_antisymm
  · exact catalogueMax_le_iff.2 fun r hr j hj =>
      Finset.le_sup (f := id) (mem_catalogueFinset.2 ⟨r, hr, j, hj, rfl⟩)
  · refine Finset.sup_le fun p hp => ?_
    obtain ⟨r, hr, j, hj, rfl⟩ := mem_catalogueFinset.1 hp
    exact cataloguePrime_le_catalogueMax hr hj

/-- The maximum is either `0` (empty family) or one of the catalogue primes. -/
theorem catalogueMax_eq_zero_or_exists (W k B : ℕ) :
    catalogueMax W k B = 0 ∨
      ∃ r ∈ unitResidues W, ∃ j < k, catalogueMax W k B = cataloguePrime W B r j := by
  rw [catalogueMax_eq_sup_catalogueFinset]
  rcases (catalogueFinset W k B).eq_empty_or_nonempty with he | hne
  · left; rw [he, Finset.sup_empty]; rfl
  · right
    obtain ⟨p, hp, hpmax⟩ := Finset.exists_mem_eq_sup _ hne id
    obtain ⟨r, hr, j, hj, rfl⟩ := mem_catalogueFinset.1 hp
    exact ⟨r, hr, j, hj, hpmax⟩

/-- A bound on all catalogue primes bounds the maximum. -/
theorem catalogueMax_lt_of_forall {W k B X : ℕ} (hX : 0 < X)
    (h : ∀ r ∈ unitResidues W, ∀ j < k, cataloguePrime W B r j < X) : catalogueMax W k B < X := by
  rcases catalogueMax_eq_zero_or_exists W k B with h0 | ⟨r, hr, j, hj, hrj⟩
  · rw [h0]; exact hX
  · rw [hrj]; exact h r hr j hj

/-! ### The fixed catalogue -/

theorem two_le_catalogueModulus : 2 ≤ catalogueModulus := by
  have := primorial_pos 324
  unfold catalogueModulus
  omega

/-- The catalogue primes of the hypothesis file are those of `(W, 22, 324)`. -/
theorem cataloguePrime_catalogueModulus (r i : ℕ) :
    ZInQ.cataloguePrime r i = cataloguePrime catalogueModulus 324 r i := rfl

theorem mem_unitResidues_catalogueModulus {r : ℕ} :
    r ∈ unitResidues catalogueModulus ↔ r < catalogueModulus ∧ r.Coprime catalogueModulus :=
  mem_unitResidues_iff_of_two_le two_le_catalogueModulus

/-- `𝓗` of the hypothesis file is the set of primes of the fixed catalogue. -/
theorem catalogueSet_eq : catalogueSet = ↑(catalogueFinset catalogueModulus 22 324) := by
  ext h
  simp only [catalogueSet, Set.mem_ofPred_eq, Finset.mem_coe, mem_catalogueFinset,
    mem_unitResidues_catalogueModulus, cataloguePrime_catalogueModulus]
  constructor
  · rintro ⟨r, i, hr, hcop, hi, rfl⟩
    exact ⟨r, ⟨hr, hcop⟩, i, hi, rfl⟩
  · rintro ⟨r, ⟨hr, hcop⟩, i, hi, rfl⟩
    exact ⟨r, i, hr, hcop, hi, rfl⟩

/-- `H_cat = ∏_{h ∈ 𝓗} h`. -/
theorem catalogueProduct_catalogueModulus_eq_prod :
    catalogueProduct catalogueModulus 22 324 = ∏ h ∈ catalogueFinset catalogueModulus 22 324, h :=
  catalogueProduct_eq_prod_catalogueFinset _ _ _

/-- Hypothesis CAT₈ bounds the catalogue maximum: `H_max < 2^(W⁸)`. -/
theorem catalogueMax_lt_of_catalogueBound8 (hCAT : CatalogueBound8) :
    catalogueMax catalogueModulus 22 324 < 2 ^ catalogueModulus ^ 8 := by
  refine catalogueMax_lt_of_forall (pow_pos two_pos _) fun r hr j hj => ?_
  obtain ⟨hr, hcop⟩ := mem_unitResidues_catalogueModulus.1 hr
  exact cataloguePrime_lt_of_catalogueBound8 hCAT hr hcop hj

/- The catalogue is never evaluated: from here on the elaborator may not unfold it. -/
attribute [irreducible] cataloguePrime catalogueProduct catalogueMax

end ZInQ.Syntax
