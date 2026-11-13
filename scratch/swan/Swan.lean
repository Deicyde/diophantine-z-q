import ZInQKernel.HDecomp.Conductor.LadicCond

/-!
# swan: the glue Props `SwanIndependent`, `SwanIntegral`, `AdaptedExists`

Task swan. The three Props are stated in the kernel module
`ZInQKernel/HDecomp/Conductor/LadicCond.lean` (namespace `LadicCond`) and used by
`scratch/g0-mod-newform/` (G15). §0 repeats them verbatim (checked equal by `rfl`).

* §1-§4: **`AdaptedExists` is proved** (`Swan.adaptedExists`), from Mathlib only.
* §5: `SwanIntegral` and `SwanIndependent` are reduced to three smaller named Props.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Swan

open PkgI4 LadicCond

/-! ## §0. The three Props, verbatim from `LadicCond.lean` -/

section Verbatim

variable {p : ℕ} [Fact p.Prime]

/-- Verbatim copy of `LadicCond.SwanIndependent`. -/
def SwanIndependent : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (ρ : GQp p →* GL (Fin n) k) (L L' : Fld p),
    IsAdapted L ρ → IsAdapted L' ρ → swanAt L ρ = swanAt L' ρ

/-- Verbatim copy of `LadicCond.AdaptedExists`. -/
def AdaptedExists : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p → ∀ (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl ℓ)),
    Continuous ρ → ∃ L : Fld p, IsAdapted L ρ

/-- Verbatim copy of `LadicCond.SwanIntegral`. -/
def SwanIntegral : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) [Fact p.Prime], p ≠ ℓ →
    ∀ (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl ℓ)), Continuous ρ →
    ∀ L : Fld p, IsAdapted L ρ →
      (swanAt L ρ : ℝ) = ∫ u in Set.Ioi (0 : ℝ), (codimInv ρ (upperAbs p u) : ℝ)

example : SwanIndependent (p := p) = LadicCond.SwanIndependent (p := p) := rfl
example : AdaptedExists (p := p) = LadicCond.AdaptedExists (p := p) := rfl
example : SwanIntegral = LadicCond.SwanIntegral := rfl

end Verbatim

/-! ## §1. Wild elements act through `p`-power order on a finite Galois level -/

section Wild

variable {p : ℕ} [Fact p.Prime]

/-- Ultrametric: `‖a − b‖ < ‖b‖ ⇒ ‖a‖ = ‖b‖`. -/
theorem norm_eq_of_norm_sub_lt {a b : Kbar p} (h : ‖a - b‖ < ‖b‖) : ‖a‖ = ‖b‖ := by
  have h1 : ‖a‖ ≤ max ‖a - b‖ ‖b‖ := by
    have := IsUltrametricDist.norm_add_le_max (a - b) b
    rwa [sub_add_cancel] at this
  have h2 : ‖b‖ ≤ max ‖b - a‖ ‖a‖ := by
    have := IsUltrametricDist.norm_add_le_max (b - a) a
    rwa [sub_add_cancel] at this
  rw [norm_sub_rev] at h2
  rcases le_total ‖a - b‖ ‖b‖ with h3 | h3
  · rw [max_eq_right h3] at h1
    rcases le_total ‖a - b‖ ‖a‖ with h4 | h4
    · rw [max_eq_right h4] at h2; linarith
    · rw [max_eq_left h4] at h2; linarith
  · linarith

theorem mul_mem_wildSet {σ τ : GQp p} (hσ : σ ∈ wildSet) (hτ : τ ∈ wildSet) :
    σ * τ ∈ wildSet := by
  intro x hx
  have hτx : ‖τ x‖ = ‖x‖ := norm_eq_of_norm_sub_lt (hτ x hx)
  have hτx0 : τ x ≠ 0 := by
    intro h; rw [h, norm_zero] at hτx; exact hx (norm_eq_zero.1 hτx.symm)
  have e : (σ * τ) x - x = (σ (τ x) - τ x) + (τ x - x) := by
    rw [AlgEquiv.mul_apply]; ring
  rw [e]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ (hτ x hx))
  rw [← hτx]; exact hσ _ hτx0

theorem pow_mem_wildSet {σ : GQp p} (hσ : σ ∈ wildSet) (m : ℕ) : σ ^ m ∈ wildSet := by
  induction m with
  | zero => rw [pow_zero]; exact one_mem_wildSet
  | succ m ih => rw [pow_succ]; exact mul_mem_wildSet ih hσ

/-- On a finite Galois `L`, every `γ` has finite order: some `γ^m`, `m > 0`, fixes `L`. -/
theorem exists_pow_fix {L : Fld p} (hL : IsFinGal L) (γ : GQp p) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, (γ ^ m) x = x := by
  have hfin := (finite_restr hL (Set.univ : Set (GQp p))).to_subtype
  let f : ℕ → restr L '' (Set.univ : Set (GQp p)) := fun j => ⟨restr L (γ ^ j), γ ^ j, trivial, rfl⟩
  obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite f
  have he' : restr L (γ ^ i) = restr L (γ ^ j) := congrArg Subtype.val he
  -- symmetric: reduce to `i < j`
  have key : ∀ a b : ℕ, a < b → restr L (γ ^ a) = restr L (γ ^ b) →
      ∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, (γ ^ m) x = x := by
    intro a b hab hrab
    refine ⟨b - a, by omega, fun x hx => ?_⟩
    have h1 : (γ ^ b) x = (γ ^ a) x := (congrFun hrab ⟨x, hx⟩).symm
    have h2 : γ ^ b = γ ^ a * γ ^ (b - a) := by rw [← pow_add]; congr 1; omega
    rw [h2, AlgEquiv.mul_apply] at h1
    exact (γ ^ a).injective h1
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h he'
  · exact key j i h he'.symm

/-- `‖m‖ = 1` in `ℚ̄_p` for `p ∤ m`. -/
theorem norm_natCast_eq_one {m : ℕ} (hm : ¬ p ∣ m) : ‖(m : Kbar p)‖ = 1 := by
  have e : ((m : ℚ_[p]) : PadicAlgCl p) = (m : Kbar p) := map_natCast (algebraMap ℚ_[p] _) m
  rw [← e, PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm

/-- **A wild element of order prime to `p` on `L` is trivial on `L`.** The map
`T x = ∑_{j<m} δ^j x` satisfies `‖T x‖ = ‖x‖` (`T x = m x + ∑ (δ^j x − x)`, `‖m‖ = 1`), so `T` is
an injective, hence surjective, `ℚ_p`-linear endomorphism of `L`; its image is `δ`-fixed. -/
theorem wild_fix_of_coprime {L : Fld p} (hL : IsFinGal L) {δ : GQp p} (hδ : δ ∈ wildSet)
    {m : ℕ} (hm0 : 0 < m) (hpm : ¬ p ∣ m) (hfix : ∀ x ∈ L, (δ ^ m) x = x) :
    ∀ x ∈ L, δ x = x := by
  have : FiniteDimensional ℚ_[p] L := hL.1
  have hmemj : ∀ (j : ℕ) {x : Kbar p}, x ∈ L → (δ ^ j) x ∈ L := fun j x hx => apply_mem hL _ hx
  let T : L →ₗ[ℚ_[p]] L :=
    { toFun := fun x => ⟨∑ j ∈ Finset.range m, (δ ^ j) (x : Kbar p),
        L.sum_mem fun j _ => hmemj j x.2⟩
      map_add' := by
        intro x y; ext
        simp only [IntermediateField.coe_add, map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x; ext
        simp only [IntermediateField.coe_smul, RingHom.id_apply, map_smul, Finset.smul_sum] }
  have hT : ∀ x : L, ((T x : L) : Kbar p) = ∑ j ∈ Finset.range m, (δ ^ j) (x : Kbar p) :=
    fun _ => rfl
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have hx0' : (x : Kbar p) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hsum : ∑ j ∈ Finset.range m, (δ ^ j) (x : Kbar p) =
        (m : Kbar p) * x + ∑ j ∈ Finset.range m, ((δ ^ j) (x : Kbar p) - x) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    have hlt : ‖∑ j ∈ Finset.range m, ((δ ^ j) (x : Kbar p) - x)‖ < ‖(x : Kbar p)‖ := by
      obtain ⟨j, -, hj⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
        (Finset.nonempty_range_iff.2 hm0.ne') (fun j => (δ ^ j) (x : Kbar p) - x)
      exact lt_of_le_of_lt hj (pow_mem_wildSet hδ j _ hx0')
    have hmx : ‖(m : Kbar p) * x‖ = ‖(x : Kbar p)‖ := by
      rw [norm_mul, norm_natCast_eq_one hpm, one_mul]
    have hTx : ‖((T x : L) : Kbar p)‖ = ‖(x : Kbar p)‖ := by
      rw [hT, hsum, ← hmx]
      apply norm_eq_of_norm_sub_lt
      rw [add_sub_cancel_left, hmx]; exact hlt
    rw [hx, IntermediateField.coe_zero, norm_zero] at hTx
    exact hx0' (norm_eq_zero.1 hTx.symm)
  have hsurj : Function.Surjective T := LinearMap.injective_iff_surjective.1 hinj
  intro y hy
  obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
  have hy' : y = ∑ j ∈ Finset.range m, (δ ^ j) (x : Kbar p) := by
    rw [← hT, hx]
  rw [hy', map_sum]
  have hshift : ∀ j, δ ((δ ^ j) (x : Kbar p)) = (δ ^ (j + 1)) (x : Kbar p) := by
    intro j; rw [pow_succ', AlgEquiv.mul_apply]
  simp_rw [hshift]
  have h1 := Finset.sum_range_succ' (fun j => (δ ^ j) (x : Kbar p)) m
  have h2 := Finset.sum_range_succ (fun j => (δ ^ j) (x : Kbar p)) m
  rw [hfix x x.2, pow_zero, AlgEquiv.one_apply] at *
  rw [h2] at h1
  simp only at h1
  linear_combination h1.symm

/-- **Wild elements have `p`-power order on every finite Galois level** (the image of `P_p` in
`Gal(L/ℚ_p)` is a `p`-group). -/
theorem wild_pow_fix {L : Fld p} (hL : IsFinGal L) {γ : GQp p} (hγ : γ ∈ wildSet) :
    ∃ k : ℕ, ∀ x ∈ L, (γ ^ (p ^ k)) x = x := by
  obtain ⟨m, hm0, hm⟩ := exists_pow_fix hL γ
  obtain ⟨k, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0.ne' p
    (Fact.out : p.Prime).one_lt.ne'
  refine ⟨k, wild_fix_of_coprime hL (pow_mem_wildSet hγ _) (Nat.pos_of_ne_zero ?_) hm' ?_⟩
  · rintro rfl; simp at hm0
  · intro x hx; rw [← pow_mul]; exact hm x hx

end Wild

/-! ## §2. Ultrametric matrix estimate -/

section Matrix

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)

/-- All entries of `A` have norm `≤ c`. -/
def Bd (c : ℝ) (A : Mat) : Prop := ∀ i j, ‖A i j‖ ≤ c

theorem Bd.add {c : ℝ} {A B : Mat} (hA : Bd c A) (hB : Bd c B) : Bd c (A + B) := fun i j =>
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA i j) (hB i j))

theorem Bd.mul {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) {A B : Mat} (hA : Bd c A) (hB : Bd d B) :
    Bd (c * d) (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hc hd) fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) hc

theorem Bd.nsmul {c : ℝ} {A : Mat} (hA : Bd c A) (m : ℕ) : Bd c (m • A) := fun i j => by
  rw [Matrix.smul_apply, nsmul_eq_mul, norm_mul]
  calc ‖(m : PadicAlgCl ℓ)‖ * ‖A i j‖ ≤ 1 * ‖A i j‖ :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_natCast_le_one _ m) (norm_nonneg _)
    _ ≤ c := by rw [one_mul]; exact hA i j

theorem Bd.zero {c : ℝ} (hc : 0 ≤ c) : Bd c (0 : Mat) := fun i j => by simpa using hc

theorem Bd.one_add {A : Mat} (hA : Bd 1 A) : Bd 1 (1 + A) := by
  refine Bd.add (fun i j => ?_) hA
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

/-- `(1 + A)^m − 1 − m A` has entries `≤ a²` when `A` has entries `≤ a ≤ 1`. -/
theorem Bd.pow_sub {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {A : Mat} (hA : Bd a A) (m : ℕ) :
    Bd (a ^ 2) ((1 + A) ^ m - 1 - m • A) := by
  induction m with
  | zero => simpa using Bd.zero (sq_nonneg a)
  | succ m ih =>
    have e : (1 + A) ^ (m + 1) - 1 - (m + 1) • A =
        (1 + A) * ((1 + A) ^ m - 1 - m • A) + m • (A * A) := by
      rw [pow_succ']; noncomm_ring
    rw [e]
    have hA1 : Bd 1 A := fun i j => (hA i j).trans ha1
    refine Bd.add ?_ ?_
    · simpa using Bd.mul zero_le_one (sq_nonneg a) (Bd.one_add hA1) ih
    · have h := (Bd.mul ha0 ha0 hA hA).nsmul m
      rwa [← sq] at h

end Matrix

end Swan
