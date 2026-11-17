import Mathlib

/-!
# Lane RC10 (Heegner algebra), part 2: the relative group, the derivative operators and the
invariant derivative class

Manuscript `diophantine_zq.tex` (11/5), proof of Proposition `ex:arith-finite-heegner`,
paragraph 3 "The relative group and invariant derivative class", tex lines 2969–3002.

* (H5), tex 2970–2985: the kernel of `Pic(𝒪_{f n_I}) → Pic(𝒪_f)` is `∏_{ℓ ∈ I} (𝒪_K/ℓ)^×/(ℤ/ℓ)^×`,
  each factor cyclic of order `ℓ + 1`.  The idelic description of `Pic` is `GLUE`; the finite-field
  algebra (each factor is cyclic of order `ℓ + 1`, and `-1` dies in it) is `PROVED` here.
* (H6), tex 2986–2991: `D_ℓ = ∑_{j=1}^{ℓ} j σ_ℓ^j` and `(σ_ℓ - 1) D_ℓ = (ℓ + 1) - Tr_ℓ`: `PROVED` in
  every ring (via the polynomial identity), in every group ring `R[G]` and for every group action.
* (H7), tex 2992–3002: if `2^a ∣ a_ℓ` and `2^a ∣ ℓ + 1` for all `ℓ ∈ I`, the Kummer class
  `δ_a(C_π D_I y_{f n_I})` is `Gal(M_I/H_f)`-invariant: `PROVED` abstractly, with the Kummer map,
  the norm relations (4.1) and the Artin identification (H5) as hypotheses.
* Gap B1-a (`maps/mcheck-rc-deep.md`): the divisibility must hold for *every* `ℓ ∈ I`, not only for
  the new prime; it is an explicit hypothesis of `H7_derivative_invariant` and is discharged from
  (H12) for every retained prime in `Precision.lean` (`B1a_of_H12`).
-/

namespace ZInQ.Manuscript.RC.HeegnerAlgebra

open Finset

/-! ## (H5): each local factor is cyclic of order `ℓ + 1` -/

/-- The image of `k^×` in `k'^×` for a subfield `k ⊆ k'`. -/
def unitsImage {k' : Type*} [Field k'] (k : Subfield k') : Subgroup k'ˣ :=
  (Units.map k.subtype.toMonoidHom).range

/-- (H5), one factor, tex 2976–2980, `PROVED`.  For finite fields `k ⊆ k'` with `|k'| = |k|²`
(the residue fields `ℤ/ℓ ⊆ 𝒪_K/ℓ` at an inert prime `ℓ`), the group `k'^×/k^×` is cyclic of
order `|k| + 1`. -/
theorem H5_factor {k' : Type*} [Field k'] [Fintype k'] (k : Subfield k') [Fintype k]
    (hcard : Fintype.card k' = Fintype.card k ^ 2) :
    IsCyclic (k'ˣ ⧸ unitsImage k) ∧ Nat.card (k'ˣ ⧸ unitsImage k) = Fintype.card k + 1 := by
  -- `k'^×` is cyclic (finite subgroup of the units of a field), hence so is its quotient
  refine ⟨isCyclic_of_surjective (QuotientGroup.mk' (unitsImage k))
    (QuotientGroup.mk'_surjective _), ?_⟩
  -- Lagrange: `q² - 1 = |k'^×/k^×| · (q - 1)` with `q = |k| ≥ 2`
  have hinj : Function.Injective (Units.map k.subtype.toMonoidHom) := by
    intro a b hab
    ext
    simpa using congrArg Units.val hab
  have h1 : Nat.card k'ˣ = Fintype.card k ^ 2 - 1 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, hcard]
  have h2 : Nat.card (unitsImage k) = Fintype.card k - 1 := by
    rw [unitsImage, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units,
      Nat.card_eq_fintype_card]
  have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup (unitsImage k)
  rw [h1, h2] at hlag
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_lt hq
  rw [hr] at hlag ⊢
  have e1 : (1 + r + 1) ^ 2 - 1 = (1 + r + 1 + 1) * (1 + r + 1 - 1) := by
    have : (1 + r + 1) ^ 2 = (r + 3) * (r + 1) + 1 := by ring
    rw [this, show 1 + r + 1 + 1 = r + 3 by omega, show 1 + r + 1 - 1 = r + 1 by omega]
    omega
  rw [e1] at hlag
  exact (Nat.eq_of_mul_eq_mul_right (by omega) hlag).symm

/-- tex 2982–2983, `PROVED`: there is no extra quotient by global units, since `-1 ∈ (ℤ/ℓ)^×`
already lies in the denominator of every factor. -/
theorem H5_neg_one_mem {k' : Type*} [Field k'] (k : Subfield k') : (-1 : k'ˣ) ∈ unitsImage k :=
  ⟨-1, by ext; simp⟩

/-! ## (H6): the derivative operator -/

/-- The polynomial `D_ℓ(X) = ∑_{j=1}^{ℓ} j X^j` over `ℤ`. -/
noncomputable def Dpoly (ℓ : ℕ) : Polynomial ℤ := ∑ j ∈ Icc 1 ℓ, (j : Polynomial ℤ) * Polynomial.X ^ j

/-- (H6), polynomial form, tex 2988–2990, `PROVED`:
`(X - 1) ∑_{j=1}^{ℓ} j X^j = ℓ X^{ℓ+1} - ∑_{j=1}^{ℓ} X^j` in `ℤ[X]`. -/
theorem H6_poly (ℓ : ℕ) :
    (Polynomial.X - 1) * Dpoly ℓ =
      (ℓ : Polynomial ℤ) * Polynomial.X ^ (ℓ + 1) - ∑ j ∈ Icc 1 ℓ, Polynomial.X ^ j := by
  induction ℓ with
  | zero => simp [Dpoly]
  | succ n ih =>
    rw [Dpoly, Finset.sum_Icc_succ_top (by omega), ← Dpoly, mul_add, ih,
      Finset.sum_Icc_succ_top (by omega)]
    push_cast; ring

/-- The derivative operator `D_ℓ = ∑_{j=1}^{ℓ} j σ^j` in a ring. -/
def Dop {R : Type*} [Ring R] (σ : R) (ℓ : ℕ) : R := ∑ j ∈ Icc 1 ℓ, (j : R) * σ ^ j

/-- The trace `Tr_ℓ = ∑_{j=0}^{ℓ} σ^j` in a ring. -/
def Trop {R : Type*} [Ring R] (σ : R) (ℓ : ℕ) : R := ∑ j ∈ range (ℓ + 1), σ ^ j

/-- (H6), tex 2988–2990, `PROVED`, in any ring: if `σ^{ℓ+1} = 1` then
`(σ - 1) D_ℓ = (ℓ + 1) - Tr_ℓ`. -/
theorem H6 {R : Type*} [Ring R] (σ : R) (ℓ : ℕ) (hσ : σ ^ (ℓ + 1) = 1) :
    (σ - 1) * Dop σ ℓ = ((ℓ : R) + 1) - Trop σ ℓ := by
  have h := congrArg (Polynomial.aeval σ) (H6_poly ℓ)
  simp only [map_mul, map_sub, Polynomial.aeval_X, map_one, Dpoly, map_sum, map_natCast,
    map_pow] at h
  rw [Dop, h, hσ, mul_one, Trop, Finset.range_eq_Ico]
  have : ∑ j ∈ Ico 0 (ℓ + 1), σ ^ j = 1 + ∑ j ∈ Icc 1 ℓ, σ ^ j := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), pow_zero]
    rfl
  rw [this]; abel

/-- (H6), tex 2985–2990, in the group ring `R[G]` of any group with `σ^{ℓ+1} = 1` (here `G = C_{ℓ+1}` or the full
relative group of (H5)), `PROVED`. -/
theorem H6_groupRing {R G : Type*} [CommRing R] [Group G] (σ : G) (ℓ : ℕ)
    (hσ : σ ^ (ℓ + 1) = 1) :
    (MonoidAlgebra.of R G σ - 1) * Dop (MonoidAlgebra.of R G σ) ℓ =
      ((ℓ : MonoidAlgebra R G) + 1) - Trop (MonoidAlgebra.of R G σ) ℓ := by
  apply H6
  rw [← map_pow, hσ, map_one]

/-- (H6) for a group acting additively: the derivative applied to a point. -/
def Dact {G V : Type*} [Monoid G] [AddCommGroup V] [DistribMulAction G V] (σ : G) (ℓ : ℕ)
    (Y : V) : V :=
  ∑ j ∈ Icc 1 ℓ, (j : ℤ) • (σ ^ j • Y)

/-- The trace applied to a point. -/
def Tract {G V : Type*} [Monoid G] [AddCommGroup V] [DistribMulAction G V] (σ : G) (ℓ : ℕ)
    (Y : V) : V :=
  ∑ j ∈ range (ℓ + 1), σ ^ j • Y

/-- (H6) acting on points, tex 2990 and 3138, `PROVED`: if `σ^{ℓ+1} Y = Y`, then
`σ D_ℓ Y - D_ℓ Y = (ℓ + 1) Y - Tr_ℓ Y`. -/
theorem H6_act {G V : Type*} [Monoid G] [AddCommGroup V] [DistribMulAction G V] (σ : G) (ℓ : ℕ)
    (Y : V) (hY : σ ^ (ℓ + 1) • Y = Y) :
    σ • Dact σ ℓ Y - Dact σ ℓ Y = ((ℓ : ℤ) + 1) • Y - Tract σ ℓ Y := by
  -- general identity without the hypothesis, by induction
  have key : ∀ n : ℕ, σ • Dact σ n Y - Dact σ n Y =
      (n : ℤ) • (σ ^ (n + 1) • Y) - ∑ j ∈ Icc 1 n, σ ^ j • Y := by
    intro n
    induction n with
    | zero => simp [Dact]
    | succ n ih =>
      rw [Dact, Finset.sum_Icc_succ_top (by omega), ← Dact, smul_add, smul_comm σ ((n + 1 : ℕ) : ℤ),
        ← mul_smul σ (σ ^ (n + 1)), ← pow_succ',
        Finset.sum_Icc_succ_top (by omega)]
      have : σ • Dact σ n Y + ((n + 1 : ℕ) : ℤ) • (σ ^ (n + 1 + 1) • Y) -
          (Dact σ n Y + ((n + 1 : ℕ) : ℤ) • (σ ^ (n + 1) • Y)) =
          (σ • Dact σ n Y - Dact σ n Y) + ((n + 1 : ℕ) : ℤ) • (σ ^ (n + 1 + 1) • Y) -
            ((n + 1 : ℕ) : ℤ) • (σ ^ (n + 1) • Y) := by abel
      rw [this, ih]; push_cast
      simp only [add_smul, one_smul]; abel
  rw [key, hY, Tract, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), pow_zero,
    one_smul, add_smul, one_smul]
  have : Ico (0 + 1) (ℓ + 1) = Icc 1 ℓ := rfl
  rw [this]; abel

/-! ## (H7): the invariant derivative class -/

/-- tex 2989: `D_I = ∏_{ℓ ∈ I} D_ℓ` in a commutative ring; singling out `ℓ ∈ I`,
`(σ_ℓ - 1) D_I = D_{I∖ℓ} ((ℓ + 1) - Tr_ℓ)` ("the factors in (H5) commute"), `PROVED`. -/
theorem H6_DI {ι 𝒜 : Type*} [DecidableEq ι] [CommRing 𝒜] (σ D Tr : ι → 𝒜) (ℓnum : ι → ℤ)
    (hH6 : ∀ i, (σ i - 1) * D i = ((ℓnum i + 1 : ℤ) : 𝒜) - Tr i) (I : Finset ι) (i : ι)
    (hi : i ∈ I) :
    (σ i - 1) * ∏ j ∈ I, D j = (∏ j ∈ I.erase i, D j) * (((ℓnum i + 1 : ℤ) : 𝒜) - Tr i) := by
  rw [← Finset.mul_prod_erase I D hi, ← hH6 i]; ring

/-- (H7) difference, tex 2998–3002, `PROVED`.  In the module `P = E(M_I)` over the commutative
group ring `𝒜 = ℤ[Gal(M_I/H_f)]`, with `y J = y_{f n_J}` for `J ⊆ I` and the inert norm relation
(4.1) `Tr_ℓ y_{f n_I} = a_ℓ y_{f n_I/ℓ}`, the `σ_ℓ`-difference of `C_π D_I y_{f n_I}` is
`C_π D_{I∖ℓ}((ℓ + 1) y_{f n_I} - a_ℓ y_{f n_I/ℓ})`. -/
theorem H7_difference {ι 𝒜 P : Type*} [DecidableEq ι] [CommRing 𝒜] [AddCommGroup P] [Module 𝒜 P]
    (σ D Tr : ι → 𝒜) (ℓnum a : ι → ℤ)
    (hH6 : ∀ i, (σ i - 1) * D i = ((ℓnum i + 1 : ℤ) : 𝒜) - Tr i)
    (y : Finset ι → P) (I : Finset ι) (i : ι) (hi : i ∈ I)
    (hnorm : Tr i • y I = (a i : 𝒜) • y (I.erase i)) (Cπ : ℤ) :
    σ i • (((Cπ : 𝒜) * ∏ j ∈ I, D j) • y I) - ((Cπ : 𝒜) * ∏ j ∈ I, D j) • y I =
      ((Cπ : 𝒜) * ∏ j ∈ I.erase i, D j) •
        (((ℓnum i + 1 : ℤ) : 𝒜) • y I - (a i : 𝒜) • y (I.erase i)) := by
  have h1 : σ i • (((Cπ : 𝒜) * ∏ j ∈ I, D j) • y I) - ((Cπ : 𝒜) * ∏ j ∈ I, D j) • y I
      = ((σ i - 1) * ((Cπ : 𝒜) * ∏ j ∈ I, D j)) • y I := by
    rw [smul_smul, sub_mul, one_mul, sub_smul]
  rw [h1, mul_left_comm, H6_DI σ D Tr ℓnum hH6 I i hi, ← mul_assoc, mul_smul, sub_smul, hnorm]

/-- (H7), the `2^a`-multiple, tex 2998–3002, `PROVED`: under `2^a ∣ ℓ + 1` and `2^a ∣ a_ℓ` the
difference of `H7_difference` is an actual `2^a`-multiple of a point of `P`. -/
theorem H7_difference_divisible {ι 𝒜 P : Type*} [DecidableEq ι] [CommRing 𝒜] [AddCommGroup P]
    [Module 𝒜 P] (σ D Tr : ι → 𝒜) (ℓnum a : ι → ℤ)
    (hH6 : ∀ i, (σ i - 1) * D i = ((ℓnum i + 1 : ℤ) : 𝒜) - Tr i)
    (y : Finset ι → P) (I : Finset ι) (i : ι) (hi : i ∈ I)
    (hnorm : Tr i • y I = (a i : 𝒜) • y (I.erase i)) (Cπ : ℤ) (e : ℕ)
    (hℓ : (2 : ℤ) ^ e ∣ ℓnum i + 1) (ha : (2 : ℤ) ^ e ∣ a i) :
    ∃ w : P, σ i • (((Cπ : 𝒜) * ∏ j ∈ I, D j) • y I) - ((Cπ : 𝒜) * ∏ j ∈ I, D j) • y I =
      ((2 : ℤ) ^ e) • w := by
  obtain ⟨u, hu⟩ := hℓ
  obtain ⟨v, hv⟩ := ha
  refine ⟨((Cπ : 𝒜) * ∏ j ∈ I.erase i, D j) • ((u : 𝒜) • y I - (v : 𝒜) • y (I.erase i)), ?_⟩
  have key : ∀ (m : ℤ) (z : P), (((2 : ℤ) ^ e * m : ℤ) : 𝒜) • z = ((2 : ℤ) ^ e) • ((m : 𝒜) • z) := by
    intro m z; rw [Int.cast_mul, mul_smul, Int.cast_smul_eq_zsmul]
  rw [H7_difference σ D Tr ℓnum a hH6 y I i hi hnorm Cπ, hu, hv, key, key, ← smul_sub,
    smul_comm]

/-- (H7) invariance, tex 2992–2997, `PROVED`, abstract form.  `Γ = Gal(M_I/H_f)` acts on the
points `P = E(M_I)` and on `H = H^1(M_I, E[2^a])`; the Kummer map `δ_a : P → H` is
`Γ`-equivariant and kills `2^a P` (Kummer exact sequence, `GLUE`).  If the `σ`-difference of `x` is
a `2^a`-multiple for every `σ` in a generating set of `Γ` (the generators `σ_ℓ` of the factors of
(H5)), then `δ_a x` is `Γ`-invariant. -/
theorem H7_invariant {Γ P H : Type*} [Group Γ] [AddCommGroup P] [AddCommGroup H]
    [DistribMulAction Γ P] [DistribMulAction Γ H] (δ : P →+ H)
    (hδ : ∀ γ : Γ, ∀ x, δ (γ • x) = γ • δ x) (a : ℕ) (hker : ∀ x, δ (((2 : ℤ) ^ a) • x) = 0)
    (S : Set Γ) (hS : Subgroup.closure S = ⊤) (x : P)
    (hx : ∀ σ ∈ S, ∃ w : P, σ • x - x = ((2 : ℤ) ^ a) • w) : ∀ γ : Γ, γ • δ x = δ x := by
  have hle : Subgroup.closure S ≤ MulAction.stabilizer Γ (δ x) := by
    rw [Subgroup.closure_le]
    intro σ hσ
    obtain ⟨w, hw⟩ := hx σ hσ
    show σ • δ x = δ x
    rw [← hδ, show σ • x = x + ((2 : ℤ) ^ a) • w by rw [← hw]; abel, map_add, hker, add_zero]
  intro γ
  have : γ ∈ MulAction.stabilizer Γ (δ x) := hle (hS ▸ Subgroup.mem_top γ)
  exact this

end ZInQ.Manuscript.RC.HeegnerAlgebra
