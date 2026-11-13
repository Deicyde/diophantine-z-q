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
        simp only [IntermediateField.coe_smul, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, ← Algebra.smul_def] }
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
      rw [pow_succ', mul_sub, mul_sub, mul_one, mul_smul_comm, add_mul, one_mul, add_mul,
        one_mul, smul_add, add_smul, one_smul]
      abel
    rw [e]
    have hA1 : Bd 1 A := fun i j => (hA i j).trans ha1
    refine Bd.add ?_ ?_
    · simpa using Bd.mul zero_le_one (sq_nonneg a) (Bd.one_add hA1) ih
    · have h := (Bd.mul ha0 ha0 hA hA).nsmul m
      rwa [← sq] at h

end Matrix

/-! ## §3. Continuity gives a finite Galois level -/

section Topo

open scoped Topology

variable {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)

/-- The neighbourhood `{g : ‖g_{ij} − δ_{ij}‖ < r ∀ i j}` of `1` in `GL_n(ℚ̄_ℓ)`. -/
def nbhd (r : ℝ) : Set (GL (Fin n) (PadicAlgCl ℓ)) :=
  {g | ∀ i j, ‖(g : Mat) i j - (1 : Mat) i j‖ < r}

theorem isOpen_nbhd (r : ℝ) : IsOpen (nbhd (ℓ := ℓ) (n := n) r) := by
  have e : nbhd (ℓ := ℓ) (n := n) r =
      ⋂ i, ⋂ j, {g : GL (Fin n) (PadicAlgCl ℓ) | ‖(g : Mat) i j - (1 : Mat) i j‖ < r} := by
    ext g; simp [nbhd]
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact isOpen_lt (((Units.continuous_val.matrix_elem i j).sub continuous_const).norm)
    continuous_const

theorem one_mem_nbhd {r : ℝ} (hr : 0 < r) : (1 : GL (Fin n) (PadicAlgCl ℓ)) ∈ nbhd r := by
  intro i j; simp [hr]

/-- **Continuity gives a level.** For continuous `ρ` and `r > 0` there is a finite Galois
`L/ℚ_p` with `ρ(G_L) ⊆ nbhd r` (Krull topology, `krullTopology_mem_nhds_one_iff_of_normal`). -/
theorem exists_level (ρ : GQp p →* GL (Fin n) (PadicAlgCl ℓ)) (hρ : Continuous ρ) {r : ℝ}
    (hr : 0 < r) : ∃ L : Fld p, IsFinGal L ∧ ∀ σ ∈ fixSet L, ρ σ ∈ nbhd r := by
  have hmem : ρ ⁻¹' nbhd r ∈ 𝓝 (1 : GQp p) := by
    apply hρ.continuousAt.preimage_mem_nhds
    rw [map_one]; exact (isOpen_nbhd r).mem_nhds (one_mem_nbhd hr)
  obtain ⟨E, hEf, hEn, hE⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ_[p] (PadicAlgCl p) _).1 hmem
  refine ⟨E, ⟨hEf, isGalois_iff.2 ⟨inferInstance, hEn⟩⟩, fun σ hσ => ?_⟩
  exact hE ((IntermediateField.mem_fixingSubgroup_iff E σ).2 hσ)

end Topo

/-! ## §4. `AdaptedExists` -/

section Main

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)

/-- Ultrametric, for `ℚ̄_ℓ`: `‖a − b‖ < ‖b‖ ⇒ ‖a‖ = ‖b‖`. -/
theorem norm_eq_of_norm_sub_lt' {a b : PadicAlgCl ℓ} (h : ‖a - b‖ < ‖b‖) : ‖a‖ = ‖b‖ :=
  norm_eq_of_norm_sub_lt (p := ℓ) h

/-- **The key estimate.** If all entries of `A` have norm `≤ a = ‖A_{ij}‖`, `0 < a < 1`, and
`ℓ ∤ m`, then `‖((1 + A)^m − 1)_{ij}‖ = a`. -/
theorem norm_pow_sub_one_entry {A : Mat} {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hA : Bd a A)
    {i j : Fin n} (hij : ‖A i j‖ = a) {m : ℕ} (hm : ¬ ℓ ∣ m) :
    ‖((1 + A) ^ m - 1) i j‖ = a := by
  have hB := Bd.pow_sub ha0.le ha1.le hA m i j
  set B := (1 + A) ^ m - 1 - m • A with hBdef
  have e : ((1 + A) ^ m - 1) i j = B i j + (m : PadicAlgCl ℓ) * A i j := by
    have hs : (m • A) i j = (m : PadicAlgCl ℓ) * A i j := by
      rw [Matrix.smul_apply, nsmul_eq_mul]
    simp only [hBdef, Matrix.sub_apply, hs]; ring
  have hmA : ‖(m : PadicAlgCl ℓ) * A i j‖ = a := by
    rw [norm_mul, norm_natCast_eq_one (p := ℓ) hm, one_mul, hij]
  rw [e, ← hmA]
  apply norm_eq_of_norm_sub_lt'
  rw [add_sub_cancel_right, hmA]
  calc ‖B i j‖ ≤ a ^ 2 := hB
    _ < a := by nlinarith

/-- **`AdaptedExists` (proved).** For `ℓ ≠ p` and continuous `ρ : G_{ℚ_p} → GL_n(ℚ̄_ℓ)` there is a
finite Galois `L/ℚ_p` with `ρ` trivial on `P_p ∩ G_L`. Take `L` with `ρ(G_L) ⊆ nbhd 1`. If
`γ ∈ P_p ∩ G_L` had `ρ(γ) = 1 + A ≠ 1`, let `a = max ‖A_{ij}‖ ∈ (0, 1)`, and take `L'` with
`ρ(G_{L'}) ⊆ nbhd a`. Some `γ^{p^k}` fixes `L'` (`wild_pow_fix`), so `‖((1+A)^{p^k} − 1)_{ij}‖ < a`,
against `norm_pow_sub_one_entry` (`ℓ ∤ p^k`). -/
theorem adaptedExists {p : ℕ} [Fact p.Prime] : LadicCond.AdaptedExists (p := p) := by
  intro ℓ _ hℓp n ρ hρ
  obtain ⟨L, hL, hL1⟩ := exists_level ρ hρ one_pos
  refine ⟨L, hL, fun γ hγ => ?_⟩
  obtain ⟨hw, hf⟩ := hγ
  by_contra hne
  set A : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ) := (ρ γ : Matrix (Fin n) (Fin n) _) - 1 with hAdef
  have hρA : (ρ γ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) = 1 + A := by
    rw [hAdef]; abel
  obtain ⟨i0, j0, h0⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hne
    apply Units.ext
    rw [Units.val_one, hρA]
    have : A = 0 := Matrix.ext fun i j => by simpa using hc i j
    rw [this, add_zero]
  have : Nonempty (Fin n × Fin n) := ⟨(i0, j0)⟩
  obtain ⟨⟨i1, j1⟩, hmax⟩ := Finite.exists_max (fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖)
  set a := ‖A i1 j1‖ with hadef
  have hBd : Bd a A := fun i j => hmax (i, j)
  have ha0 : 0 < a := lt_of_lt_of_le (norm_pos_iff.2 h0) (hmax (i0, j0))
  have ha1 : a < 1 := by
    have := hL1 γ hf i1 j1
    rwa [hadef, hAdef, Matrix.sub_apply]
  obtain ⟨L', hL', hL'a⟩ := exists_level ρ hρ ha0
  obtain ⟨k, hk⟩ := wild_pow_fix hL' hw
  have hlt := hL'a (γ ^ (p ^ k)) hk i1 j1
  rw [map_pow, Units.val_pow_eq_pow_val, hρA, ← Matrix.sub_apply] at hlt
  have hℓ : ¬ ℓ ∣ p ^ k := by
    intro h
    have h1 := (Fact.out : ℓ.Prime).dvd_of_dvd_pow h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1 h1)
  rw [norm_pow_sub_one_entry ha0 ha1 hBd rfl hℓ] at hlt
  exact lt_irrefl _ hlt

end Main

/-! ## §5. `SwanIntegral` and `SwanIndependent` from three smaller Props

Both follow from: for `L` adapted to `ρ` and `u > 0`, `V^{G^u} = V^{G^u(L) ∩ P}` (the absolute
upper group acts through its image in `Gal(L/ℚ_p)`), plus the finite-level integral formula. -/

section Reduction

/-- **H1 (GLUE: finite-level change of variables; Serre, *Corps locaux* IV §3 and VI §2,
numbering UNVERIFIED).** At an adapted finite Galois level `L`, the Swan conductor
`∑_{i ≥ 1} (g_i/g_0) codim V^{G_i ∩ P}` equals `∫₀^∞ codim V^{G^u(L) ∩ P} du`: substitute
`u = φ_{L/ℚ_p}(t)`, `dφ = (g_{⌈t⌉}/g_0) dt`, `G^{φ(t)} = G_{⌈t⌉}`. A statement about one finite
extension and real step functions; no theorem of ramification theory beyond the definitions. -/
def SwanAtIntegral : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (n : ℕ) (ρ : GQp p →* GL (Fin n) k) (L : Fld p),
    IsAdapted L ρ →
      (swanAt L ρ : ℝ) = ∫ u in Set.Ioi (0 : ℝ), (codimInv ρ (upperSet L u ∩ wildSet) : ℝ)

/-- **H2 (GLUE from the definitions; Serre, *Corps locaux* IV §1-§3).** For `u > 0` the absolute
upper ramification group lies in wild inertia: `G^u ⊆ P_p`. (For `x ≠ 0` take a finite Galois `L ∋ x`;
`ψ_L(u) > 0`, so `σ ∈ G_1(L)`, and `G_1(L)` acts by `σx/x ≡ 1` mod the maximal ideal.) -/
def UpperAbsWild : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (u : ℝ), 0 < u → upperAbs p u ⊆ wildSet

/-- **H3 (GLUE from Herbrand's theorem plus compactness; Serre, *Corps locaux* IV §3, Prop. 14 and
the remark defining `G^v` for infinite Galois extensions, numbering UNVERIFIED).** The projection
`G^u → G^u(L/ℚ_p)` is onto: every `σ` in `G^u(L) ∩ P` (preimage in `G_{ℚ_p}`) agrees on `L` with
an element of the absolute `G^u`. -/
def UpperAbsSurj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : Fld p), IsFinGal L → ∀ u : ℝ, 0 < u →
    ∀ σ ∈ upperSet L u ∩ wildSet, ∃ τ ∈ upperAbs p u, ∀ x ∈ L, τ x = σ x

variable {p : ℕ} [Fact p.Prime]

theorem inv_mem_wildSet {σ : GQp p} (hσ : σ ∈ wildSet) : σ⁻¹ ∈ wildSet := by
  intro x hx
  have hy : σ (σ⁻¹ x) = x := σ.apply_symm_apply x
  have hy0 : σ⁻¹ x ≠ 0 := fun h => hx (by rw [← hy, h, map_zero])
  have h1 := hσ _ hy0
  rw [hy] at h1
  have h2 : ‖x‖ = ‖σ⁻¹ x‖ := norm_eq_of_norm_sub_lt h1
  rw [h2, norm_sub_rev]
  exact h1

/-- **The absolute upper group acts through `L`.** For `L` adapted to `ρ` and `u > 0`,
`V^{G^u} = V^{G^u(L) ∩ P}`. -/
theorem invariants_upperAbs (h2 : UpperAbsWild) (h3 : UpperAbsSurj) {k : Type} [Field k] {n : ℕ}
    {ρ : GQp p →* GL (Fin n) k} {L : Fld p} (hL : IsAdapted L ρ) {u : ℝ} (hu : 0 < u) :
    invariants ρ (upperAbs p u) = invariants ρ (upperSet L u ∩ wildSet) := by
  apply le_antisymm
  · intro v hv σ hσ
    obtain ⟨τ, hτ, hτσ⟩ := h3 p L hL.1 u hu σ hσ
    have hτw : τ ∈ wildSet := h2 p u hu hτ
    have h1 : τ⁻¹ * σ ∈ wildSet ∩ fixSet L := by
      refine ⟨mul_mem_wildSet (inv_mem_wildSet hτw) hσ.2, fun x hx => ?_⟩
      rw [AlgEquiv.mul_apply, ← hτσ x hx]
      exact τ.symm_apply_apply x
    have h2' : ρ σ = ρ τ * ρ (τ⁻¹ * σ) := by rw [← map_mul, mul_inv_cancel_left]
    rw [h2', hL.2 _ h1, mul_one]
    exact hv τ hτ
  · intro v hv σ hσ
    exact hv σ ⟨hσ L hL.1, h2 p u hu hσ⟩

/-- At any adapted level, `Sw_L(ρ) = ∫₀^∞ codim V^{G^u} du` (absolute upper filtration). -/
theorem swanAt_eq_integral_upperAbs (h1 : SwanAtIntegral) (h2 : UpperAbsWild)
    (h3 : UpperAbsSurj) {k : Type} [Field k] {n : ℕ} {ρ : GQp p →* GL (Fin n) k} {L : Fld p}
    (hL : IsAdapted L ρ) :
    (swanAt L ρ : ℝ) = ∫ u in Set.Ioi (0 : ℝ), (codimInv ρ (upperAbs p u) : ℝ) := by
  rw [h1 p k n ρ L hL]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  rw [codimInv, codimInv, invariants_upperAbs h2 h3 hL hu]

/-- **`SwanIntegral` (L8) from H1-H3.** (Continuity and `p ≠ ℓ` are not used.) -/
theorem swanIntegral_of (h1 : SwanAtIntegral) (h2 : UpperAbsWild) (h3 : UpperAbsSurj) :
    LadicCond.SwanIntegral := by
  intro ℓ _ p _ _ n ρ _ L hL
  exact swanAt_eq_integral_upperAbs h1 h2 h3 hL

/-- **`SwanIndependent` from H1-H3**, for every field `k` and every homomorphism `ρ`: both levels
compute the same integral over the absolute upper filtration. -/
theorem swanIndependent_of (h1 : SwanAtIntegral) (h2 : UpperAbsWild) (h3 : UpperAbsSurj) :
    LadicCond.SwanIndependent (p := p) := by
  intro k _ n ρ L L' hL hL'
  have e := (swanAt_eq_integral_upperAbs h1 h2 h3 hL).trans
    (swanAt_eq_integral_upperAbs h1 h2 h3 hL').symm
  exact_mod_cast e

/-- **All three glue Props of G15** from H1-H3 (`AdaptedExists` needs nothing). -/
theorem swan_all (h1 : SwanAtIntegral) (h2 : UpperAbsWild) (h3 : UpperAbsSurj) :
    (∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p)) ∧ LadicCond.SwanIntegral ∧
      (∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p)) :=
  ⟨fun _ _ => swanIndependent_of h1 h2 h3, swanIntegral_of h1 h2 h3, fun _ _ => adaptedExists⟩

end Reduction

/-! ## §6. H3 from Herbrand's theorem and the compactness of `G_{ℚ_p}` -/

section Herbrand

open scoped Topology

/-- **Leaf H3a: Herbrand's theorem** (Serre, *Corps locaux* IV §3, Prop. 14, numbering UNVERIFIED;
the same theorem as pkg-I6's leaf I6.8 `PkgI6.HerbrandQuotient`, here over the finite Galois
subfields of `ℚ̄_p` and the upper numbering `LadicCond.upperSet`). For `L ⊆ M` finite Galois over
`ℚ_p` and every `v`, the image of `G^v(M/ℚ_p)` in `Gal(L/ℚ_p)` is `G^v(L/ℚ_p)`:
`(G/H)^v = G^v H/H`. Preimages in `G_{ℚ_p}` restricted to `L`. Stated only for `v > 0`, the
range the proof uses (Serre's statement covers every `v ≥ −1`). -/
def HerbrandUpper : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L M : Fld p), IsFinGal L → IsFinGal M → L ≤ M → ∀ v : ℝ, 0 < v →
    restr L '' upperSet M v = restr L '' upperSet L v

variable {p : ℕ} [Fact p.Prime]

/-- Membership in `ramSet L i` depends only on the restriction to `L`. -/
theorem mem_ramSet_of_restr {L : Fld p} {σ τ : GQp p} (h : ∀ x ∈ L, τ x = σ x) {i : ℕ}
    (hσ : σ ∈ ramSet L i) : τ ∈ ramSet L i := by
  obtain ⟨ϖ, hϖ, hb⟩ := hσ
  exact ⟨ϖ, hϖ, fun x hx hx1 => by rw [h x hx]; exact hb x hx hx1⟩

/-- Membership in `upperSet L v` depends only on the restriction to `L`. -/
theorem mem_upperSet_of_restr {L : Fld p} {σ τ : GQp p} (h : ∀ x ∈ L, τ x = σ x) {v : ℝ}
    (hσ : σ ∈ upperSet L v) : τ ∈ upperSet L v := by
  unfold upperSet ramSetR at *
  split_ifs at * with h1
  · trivial
  · exact mem_ramSet_of_restr h hσ

theorem restr_eq_iff {L : Fld p} {σ τ : GQp p} : restr L τ = restr L σ ↔ ∀ x ∈ L, τ x = σ x :=
  ⟨fun h x hx => congrFun h ⟨x, hx⟩, fun h => funext fun x => h x x.2⟩

/-- A finite Galois `E` containing `L` and every member of a finite family of finite Galois
fields. -/
theorem exists_finGal_above {L : Fld p} (hL : IsFinGal L)
    (u : Finset {M : Fld p // IsFinGal M}) :
    ∃ E : Fld p, IsFinGal E ∧ L ≤ E ∧ ∀ i ∈ u, i.1 ≤ E := by
  classical
  induction u using Finset.induction_on with
  | empty => exact ⟨L, hL, le_rfl, fun _ h => absurd h (Finset.notMem_empty _)⟩
  | @insert i u _ ih =>
    obtain ⟨E, ⟨hEf, hEg⟩, hLE, hu⟩ := ih
    have : FiniteDimensional ℚ_[p] E := hEf
    have : IsGalois ℚ_[p] E := hEg
    have : FiniteDimensional ℚ_[p] i.1 := i.2.1
    have : IsGalois ℚ_[p] i.1 := i.2.2
    refine ⟨E ⊔ i.1, ⟨IntermediateField.finiteDimensional_sup _ _, inferInstance⟩,
      hLE.trans le_sup_left, fun j hj => ?_⟩
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact le_sup_right
    · exact (hu j hj).trans le_sup_left

/-- A set of `τ` determined by `τ|_E` for a finite `E` is closed. -/
theorem isClosed_of_restr {E : Fld p} (hE : FiniteDimensional ℚ_[p] E) {S : Set (GQp p)}
    (hS : ∀ σ τ, (∀ x ∈ E, τ x = σ x) → σ ∈ S → τ ∈ S) : IsClosed S := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro τ hτ
  have hU : (E.fixingSubgroup : Set (GQp p)) ∈ 𝓝 (1 : GQp p) :=
    (krullTopology_mem_nhds_one_iff ℚ_[p] (PadicAlgCl p) _).2 ⟨E, hE, subset_rfl⟩
  have hf : ContinuousAt (fun g : GQp p => τ⁻¹ * g) τ :=
    (continuous_const.mul continuous_id).continuousAt
  have hmem : (fun g : GQp p => τ⁻¹ * g) ⁻¹' (E.fixingSubgroup : Set (GQp p)) ∈ 𝓝 τ := by
    apply hf.preimage_mem_nhds
    simp only [inv_mul_cancel]; exact hU
  refine Filter.mem_of_superset hmem fun g hg hgS => hτ (hS g τ (fun x hx => ?_) hgS)
  have h1 : (τ⁻¹ * g) x = x := (IntermediateField.mem_fixingSubgroup_iff E _).1 hg x hx
  rw [AlgEquiv.mul_apply] at h1
  calc τ x = τ ((τ⁻¹) (g x)) := by rw [h1]
    _ = g x := τ.apply_symm_apply (g x)

/-- **H3 from Herbrand's theorem (GLUE, proved).** If `σ ∈ G^u(L)` (preimage), then some `τ` in
the absolute `G^u` agrees with `σ` on `L`: the closed sets
`C_M = {τ : τ|_L = σ|_L, τ ∈ G^u(M)}` have the finite intersection property (Herbrand, at a finite
Galois `E` containing `L` and the `M`s), and `G_{ℚ_p}` is compact (Mathlib). -/
theorem upperAbsSurj_of_herbrand (hH : HerbrandUpper) : UpperAbsSurj := by
  intro p _ L hL u hu σ hσ
  let ι := {M : Fld p // IsFinGal M}
  let t : ι → Set (GQp p) := fun M => {τ | (∀ x ∈ L, τ x = σ x) ∧ τ ∈ upperSet M.1 u}
  have htc : ∀ M, IsClosed (t M) := by
    intro M
    have : FiniteDimensional ℚ_[p] L := hL.1
    have : FiniteDimensional ℚ_[p] M.1 := M.2.1
    refine isClosed_of_restr (E := L ⊔ M.1) (IntermediateField.finiteDimensional_sup _ _) ?_
    intro a b hab ⟨ha1, ha2⟩
    refine ⟨fun x hx => (hab x (le_sup_left (a := L) hx)).trans (ha1 x hx), ?_⟩
    exact mem_upperSet_of_restr (fun x hx => hab x (le_sup_right (b := M.1) hx)) ha2
  have hst : ∀ s : Finset ι, ((Set.univ : Set (GQp p)) ∩ ⋂ i ∈ s, t i).Nonempty := by
    intro s
    obtain ⟨E, hE, hLE, hsE⟩ := exists_finGal_above hL s
    have h1 : restr L σ ∈ restr L '' upperSet E u := by
      rw [hH p L E hL hE hLE u hu]; exact ⟨σ, hσ.1, rfl⟩
    obtain ⟨τ, hτE, hτσ⟩ := h1
    refine ⟨τ, trivial, Set.mem_iInter₂.2 fun M hM => ⟨restr_eq_iff.1 hτσ, ?_⟩⟩
    have h2 : restr M.1 τ ∈ restr M.1 '' upperSet M.1 u := by
      rw [← hH p M.1 E M.2 hE (hsE M hM) u hu]; exact ⟨τ, hτE, rfl⟩
    obtain ⟨τ', hτ', he⟩ := h2
    exact mem_upperSet_of_restr (restr_eq_iff.1 he.symm) hτ'
  obtain ⟨τ, -, hτ⟩ := isCompact_univ.inter_iInter_nonempty t htc hst
  rw [Set.mem_iInter] at hτ
  refine ⟨τ, fun M hM => (hτ ⟨M, hM⟩).2, ?_⟩
  obtain ⟨M0, hM0⟩ : ∃ M : ι, True := ⟨⟨L, hL⟩, trivial⟩
  exact (hτ M0).1

/-- **`SwanIntegral` and `SwanIndependent` from H1, H2 and Herbrand's theorem.** -/
theorem swan_all' (h1 : SwanAtIntegral) (h2 : UpperAbsWild) (hH : HerbrandUpper) :
    (∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p)) ∧ LadicCond.SwanIntegral ∧
      (∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p)) :=
  swan_all h1 h2 (upperAbsSurj_of_herbrand hH)

end Herbrand

/-! ## §7. H2 (`UpperAbsWild`) from the definitions -/

section Wild2

variable {p : ℕ} [Fact p.Prime]

/-- `z ≠ 0` and `‖σz − z‖ < ‖z‖`. -/
def WildAt (σ : GQp p) (z : Kbar p) : Prop := z ≠ 0 ∧ ‖σ z - z‖ < ‖z‖

theorem WildAt.norm_eq {σ : GQp p} {z : Kbar p} (h : WildAt σ z) : ‖σ z‖ = ‖z‖ :=
  norm_eq_of_norm_sub_lt h.2

theorem WildAt.mul {σ : GQp p} {a b : Kbar p} (ha : WildAt σ a) (hb : WildAt σ b) :
    WildAt σ (a * b) := by
  refine ⟨mul_ne_zero ha.1 hb.1, ?_⟩
  have e : σ (a * b) - a * b = σ a * (σ b - b) + (σ a - a) * b := by rw [map_mul]; ring
  rw [e]
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha.1
  have hb0 : 0 < ‖b‖ := norm_pos_iff.2 hb.1
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul, norm_mul, ha.norm_eq]; exact mul_lt_mul_of_pos_left hb.2 ha0
  · rw [norm_mul, norm_mul]; exact mul_lt_mul_of_pos_right ha.2 hb0

theorem WildAt.inv {σ : GQp p} {a : Kbar p} (ha : WildAt σ a) : WildAt σ a⁻¹ := by
  refine ⟨inv_ne_zero ha.1, ?_⟩
  have hσa : σ a ≠ 0 := fun h => ha.1 (by simpa using congrArg σ.symm h)
  have e : σ a⁻¹ - a⁻¹ = (a - σ a) * (σ a)⁻¹ * a⁻¹ := by
    have h1 : a * a⁻¹ = 1 := mul_inv_cancel₀ ha.1
    have h2 : σ a * (σ a)⁻¹ = 1 := mul_inv_cancel₀ hσa
    rw [map_inv₀]; linear_combination -(σ a)⁻¹ * h1 + a⁻¹ * h2
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha.1
  rw [e, norm_mul, norm_mul, norm_inv, norm_inv, ha.norm_eq, norm_sub_rev]
  calc ‖σ a - a‖ * ‖a‖⁻¹ * ‖a‖⁻¹ < ‖a‖ * ‖a‖⁻¹ * ‖a‖⁻¹ := by
        have : 0 < ‖a‖⁻¹ := inv_pos.2 ha0
        exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right ha.2 this) this
    _ = ‖a‖⁻¹ := by field_simp

theorem wildAt_one (σ : GQp p) : WildAt σ 1 := ⟨one_ne_zero, by simp⟩

theorem WildAt.zpow {σ : GQp p} {a : Kbar p} (ha : WildAt σ a) (n : ℤ) : WildAt σ (a ^ n) := by
  have hn : ∀ m : ℕ, WildAt σ (a ^ m) := by
    intro m
    induction m with
    | zero => simpa using wildAt_one σ
    | succ m ih => rw [pow_succ]; exact ih.mul ha
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]; exact hn m
  · rw [zpow_neg, zpow_natCast]; exact (hn m).inv

/-- **`G_1(L)` acts wildly on `L`.** If `σ ∈ ramSet L 1` then `‖σx − x‖ < ‖x‖` for every
`x ∈ L`, `x ≠ 0`: write `x = y ϖ^a` with `‖y‖ = 1` (discreteness of `‖L^×‖`, from `IsUnif`); then
`‖σy − y‖ ≤ ‖ϖ‖² < 1` and `‖σϖ − ϖ‖ ≤ ‖ϖ‖² < ‖ϖ‖`, and `WildAt` is multiplicative. -/
theorem wildAt_of_ramSet_one {L : Fld p} {σ : GQp p} (hσ : σ ∈ ramSet L 1) {x : Kbar p}
    (hx : x ∈ L) (hx0 : x ≠ 0) : WildAt σ x := by
  obtain ⟨ϖ, hϖ, hb⟩ := hσ
  set r := ‖ϖ‖ with hrdef
  have hr1 : r < 1 := hϖ.2.1
  have hpL : (p : Kbar p) ∈ L := by
    rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
    exact IntermediateField.algebraMap_mem _ _
  have hr0 : 0 < r := by
    have h1 := hϖ.2.2 (p : Kbar p) hpL isUnif_bot.2.1
    have h2 : 0 < ‖(p : Kbar p)‖ := by
      rw [norm_p_kbar]; exact inv_pos.2 (Nat.cast_pos.2 (Fact.out : p.Prime).pos)
    exact lt_of_lt_of_le h2 h1
  have hϖ0 : ϖ ≠ 0 := norm_pos_iff.1 hr0
  have hr2 : r ^ (1 + 1) < r :=
    calc r ^ (1 + 1) = r * r := by ring
      _ < r * 1 := mul_lt_mul_of_pos_left hr1 hr0
      _ = r := mul_one r
  have hwϖ : WildAt σ ϖ := ⟨hϖ0, lt_of_le_of_lt (hb ϖ hϖ.1 hr1.le) hr2⟩
  have hx0' : 0 < ‖x‖ := norm_pos_iff.2 hx0
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hx0' (one_lt_inv₀ hr0 |>.2 hr1)
  set y := x * ϖ ^ (n + 1) with hydef
  have hyL : y ∈ L := L.mul_mem hx (zpow_mem hϖ.1 _)
  have hy : ‖y‖ = ‖x‖ * r ^ (n + 1) := by rw [hydef, norm_mul, norm_zpow]
  have hrn : r ^ (n + 1) = r ^ n * r := by rw [zpow_add_one₀ hr0.ne']
  have hrinv : ∀ m : ℤ, r⁻¹ ^ m * r ^ m = 1 := by
    intro m; rw [← mul_zpow, inv_mul_cancel₀ hr0.ne', one_zpow]
  have hrpos : 0 < r ^ (n + 1) := zpow_pos hr0 _
  have hyle : ‖y‖ ≤ 1 := by
    rw [hy, ← hrinv (n + 1)]
    exact mul_le_mul_of_nonneg_right hn2 hrpos.le
  have hygt : r < ‖y‖ := by
    rw [hy]
    calc r = r⁻¹ ^ n * r ^ (n + 1) := by rw [hrn, ← mul_assoc, hrinv n, one_mul]
      _ < ‖x‖ * r ^ (n + 1) := mul_lt_mul_of_pos_right hn1 hrpos
  have hy1 : ‖y‖ = 1 := by
    rcases hyle.lt_or_eq with h | h
    · exact absurd (hϖ.2.2 y hyL h) (not_le.2 hygt)
    · exact h
  have hy0 : y ≠ 0 := by intro h; rw [h, norm_zero] at hy1; exact zero_ne_one hy1
  have hwy : WildAt σ y := ⟨hy0, by
    rw [hy1]; exact lt_of_le_of_lt (hb y hyL hyle) (hr2.trans hr1)⟩
  have hxe : x = y * ϖ ^ (-(n + 1)) := by
    rw [hydef, mul_assoc, ← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero, mul_one]
  rw [hxe]
  exact hwy.mul (hwϖ.zpow _)

/-! ### `ψ_L(u) > 0` for `u > 0`, so `G^u(L) ⊆ G_1(L)` -/

theorem ramSet_anti {L : Fld p} {i j : ℕ} (h : i ≤ j) : ramSet L j ⊆ ramSet L i := by
  rintro σ ⟨ϖ, hϖ, hb⟩
  exact ⟨ϖ, hϖ, fun x hx h1 => (hb x hx h1).trans
    (pow_le_pow_of_le_one (norm_nonneg _) hϖ.2.1.le (by omega))⟩

theorem ramSetR_anti {L : Fld p} {t t' : ℝ} (h : t ≤ t') : ramSetR L t' ⊆ ramSetR L t := by
  unfold ramSetR
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (h.trans h1) h2
  · exact Set.subset_univ _
  · exact ramSet_anti (Int.toNat_le_toNat (Int.ceil_mono h))

theorem one_mem_ramSetR {L : Fld p} (hL : IsFinGal L) (t : ℝ) : (1 : GQp p) ∈ ramSetR L t := by
  unfold ramSetR
  split_ifs
  · trivial
  · obtain ⟨ϖ, hϖ⟩ := exists_isUnif hL.1
    exact fixSet_subset_ramSet hϖ _ (fun x _ => rfl)

theorem one_le_ramCardR {L : Fld p} (hL : IsFinGal L) (t : ℝ) : 1 ≤ ramCardR L t := by
  have hfin := (finite_restr hL (ramSetR L t)).to_subtype
  have hne : Nonempty (restr L '' ramSetR L t) := ⟨⟨restr L 1, 1, one_mem_ramSetR hL t, rfl⟩⟩
  exact Nat.one_le_iff_ne_zero.2 (Nat.card_ne_zero.2 ⟨hne, hfin⟩)

theorem ramCardR_le {L : Fld p} (hL : IsFinGal L) (t : ℝ) :
    ramCardR L t ≤ Nat.card (restr L '' (Set.univ : Set (GQp p))) :=
  Nat.card_mono (finite_restr hL _) (Set.image_mono (Set.subset_univ _))

theorem ramCardR_anti {L : Fld p} (hL : IsFinGal L) :
    Antitone (fun t => (ramCardR L t : ℝ) / (ramCard L 0 : ℝ)) := by
  intro t t' h
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast Nat.card_mono (finite_restr hL _) (Set.image_mono (ramSetR_anti h))

theorem phiAt_nonpos {L : Fld p} {t : ℝ} (ht : t ≤ 0) : phiAt L t ≤ 0 := by
  rw [phiAt, intervalIntegral.integral_symm, neg_nonpos]
  exact intervalIntegral.integral_nonneg ht fun x _ => by positivity

theorem phiAt_ge {L : Fld p} (hL : IsFinGal L) {t : ℝ} (ht : 0 ≤ t) :
    t / (ramCard L 0 : ℝ) ≤ phiAt L t := by
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) ht
    (f := fun _ => 1 / (ramCard L 0 : ℝ))
    (g := fun t => (ramCardR L t : ℝ) / (ramCard L 0 : ℝ))
    intervalIntegrable_const (ramCardR_anti hL).intervalIntegrable
    (fun x _ => div_le_div_of_nonneg_right (by exact_mod_cast one_le_ramCardR hL x)
      (Nat.cast_nonneg _))
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one_div] at h
  exact h

theorem phiAt_le {L : Fld p} (hL : IsFinGal L) {t : ℝ} (ht : 0 ≤ t) :
    phiAt L t ≤ t * ((Nat.card (restr L '' (Set.univ : Set (GQp p))) : ℝ) / (ramCard L 0 : ℝ)) := by
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) ht
    (g := fun _ => (Nat.card (restr L '' (Set.univ : Set (GQp p))) : ℝ) / (ramCard L 0 : ℝ))
    (f := fun t => (ramCardR L t : ℝ) / (ramCard L 0 : ℝ))
    (ramCardR_anti hL).intervalIntegrable intervalIntegrable_const
    (fun x _ => div_le_div_of_nonneg_right (by exact_mod_cast ramCardR_le hL x)
      (Nat.cast_nonneg _))
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  exact h

/-- **`G^u(L) ⊆ G_1(L)` for `u > 0`** (preimages in `G_{ℚ_p}`): `ψ_L(u) > 0`, from
`t/g_0 ≤ φ_L(t) ≤ t·|Gal(L/ℚ_p)|/g_0` for `t ≥ 0` and `φ_L ≤ 0` on `[−1, 0]`. -/
theorem upperSet_subset_ramSet_one {L : Fld p} (hL : IsFinGal L) {u : ℝ} (hu : 0 < u) :
    upperSet L u ⊆ ramSet L 1 := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hL.1
  set g0 : ℝ := (ramCard L 0 : ℝ) with hg0
  have hg0pos : 0 < g0 := by
    rw [hg0]; exact_mod_cast Nat.pos_of_ne_zero (ramCard_ne_zero hL hϖ 0)
  set C : ℝ := (Nat.card (restr L '' (Set.univ : Set (GQp p))) : ℝ) with hC
  have hC1 : 1 ≤ C := by
    rw [hC]; exact_mod_cast (one_le_ramCardR hL 0).trans (ramCardR_le hL 0)
  have hCg : 0 < C / g0 := div_pos (by linarith) hg0pos
  set S := {t : ℝ | -1 ≤ t ∧ u ≤ phiAt L t} with hS
  have hne : S.Nonempty := by
    refine ⟨u * g0, by nlinarith, ?_⟩
    have := phiAt_ge hL (t := u * g0) (by positivity)
    rwa [mul_div_assoc, div_self hg0pos.ne', mul_one] at this
  have hlb : ∀ t ∈ S, u / (C / g0) ≤ t := by
    rintro t ⟨-, ht⟩
    by_cases h0 : t ≤ 0
    · exact absurd (ht.trans (phiAt_nonpos h0)) (not_le.2 hu)
    · rw [div_le_iff₀ hCg]
      exact ht.trans (phiAt_le hL (le_of_lt (not_le.1 h0)))
  have hs : 0 < sInf S := lt_of_lt_of_le (div_pos hu hCg) (le_csInf hne hlb)
  intro σ hσ
  unfold upperSet ramSetR at hσ
  rw [← hS] at hσ
  split_ifs at hσ with hle
  · exact absurd hle (by linarith)
  refine ramSet_anti ?_ hσ
  have : 0 < ⌈sInf S⌉ := Int.ceil_pos.2 hs
  omega

/-- Every `x ∈ ℚ̄_p` lies in a finite Galois `L/ℚ_p` (the normal closure of `ℚ_p(x)`). -/
theorem exists_finGal_mem (x : Kbar p) : ∃ L : Fld p, IsFinGal L ∧ x ∈ L := by
  have hint : IsIntegral ℚ_[p] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  set K : Fld p := IntermediateField.adjoin ℚ_[p] {x} with hK
  have : FiniteDimensional ℚ_[p] K := IntermediateField.adjoin.finiteDimensional hint
  refine ⟨IntermediateField.normalClosure ℚ_[p] K (Kbar p),
    ⟨normalClosure.is_finiteDimensional _ _ _, isGalois_iff.2 ⟨inferInstance, inferInstance⟩⟩, ?_⟩
  exact K.le_normalClosure (IntermediateField.mem_adjoin_simple_self ℚ_[p] x)

/-- **H2 (`UpperAbsWild`) is proved.** -/
theorem upperAbsWild : UpperAbsWild := by
  intro p _ u hu σ hσ x hx0
  obtain ⟨L, hL, hxL⟩ := exists_finGal_mem x
  exact (wildAt_of_ramSet_one (upperSet_subset_ramSet_one hL hu (hσ L hL)) hxL hx0).2

end Wild2

/-! ## §7b. H1 (`SwanAtIntegral`): the finite-level change of variables -/

section ChangeVar

variable {p : ℕ} [Fact p.Prime]

open MeasureTheory

/-- `g_i/g_0`. -/
def wt (L : Fld p) (i : ℕ) : ℝ := (ramCard L i : ℝ) / (ramCard L 0 : ℝ)

/-- `Φ_j = φ_L(j) = ∑_{i=1}^{j} g_i/g_0`. -/
def Phi (L : Fld p) (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, wt L (i + 1)

theorem Phi_zero (L : Fld p) : Phi L 0 = 0 := by simp [Phi]

theorem Phi_succ (L : Fld p) (j : ℕ) : Phi L (j + 1) = Phi L j + wt L (j + 1) := by
  simp [Phi, Finset.sum_range_succ]

theorem wt_pos {L : Fld p} (hL : IsFinGal L) (i : ℕ) : 0 < wt L i := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hL.1
  unfold wt
  exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero (ramCard_ne_zero hL hϖ i))
    (by exact_mod_cast Nat.pos_of_ne_zero (ramCard_ne_zero hL hϖ 0))

theorem wt_ge {L : Fld p} (hL : IsFinGal L) (i : ℕ) : 1 / (ramCard L 0 : ℝ) ≤ wt L i := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hL.1
  unfold wt
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (ramCard_ne_zero hL hϖ i)) (Nat.cast_nonneg _)

theorem Phi_strictMono {L : Fld p} (hL : IsFinGal L) : StrictMono (Phi L) :=
  strictMono_nat_of_lt_succ fun j => by rw [Phi_succ]; linarith [wt_pos hL (j + 1)]

theorem Phi_nonneg {L : Fld p} (hL : IsFinGal L) (j : ℕ) : 0 ≤ Phi L j := by
  rw [← Phi_zero L]; exact (Phi_strictMono hL).monotone (Nat.zero_le j)

theorem Phi_ge {L : Fld p} (hL : IsFinGal L) (j : ℕ) :
    (j : ℝ) * (1 / (ramCard L 0 : ℝ)) ≤ Phi L j := by
  induction j with
  | zero => simp [Phi_zero]
  | succ j ih => rw [Phi_succ]; push_cast; linarith [wt_ge hL (j + 1)]

/-- On `(j, j+1]` the integrand of `φ_L` is `g_{j+1}/g_0`. -/
theorem integrand_eq {L : Fld p} {j : ℕ} {t : ℝ} (h1 : (j : ℝ) < t) (h2 : t ≤ j + 1) :
    (ramCardR L t : ℝ) / (ramCard L 0 : ℝ) = wt L (j + 1) := by
  have hc : ⌈t⌉ = (j : ℤ) + 1 := Int.ceil_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
  have ht : ¬ t ≤ -1 := by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
  unfold ramCardR ramSetR wt
  rw [if_neg ht, hc]
  rfl

theorem integral_piece {L : Fld p} (j : ℕ) {t : ℝ} (h1 : (j : ℝ) ≤ t) (h2 : t ≤ j + 1) :
    ∫ x in (j : ℝ)..t, (ramCardR L x : ℝ) / (ramCard L 0 : ℝ) = (t - j) * wt L (j + 1) := by
  rw [intervalIntegral.integral_congr_ae (g := fun _ => wt L (j + 1)) ?_]
  · rw [intervalIntegral.integral_const, smul_eq_mul]
  · refine Filter.Eventually.of_forall fun x hx => ?_
    rw [Set.uIoc_of_le h1] at hx
    exact integrand_eq hx.1 (hx.2.trans h2)

theorem integrable_phi {L : Fld p} (hL : IsFinGal L) (a b : ℝ) :
    IntervalIntegrable (fun t => (ramCardR L t : ℝ) / (ramCard L 0 : ℝ)) volume a b :=
  (ramCardR_anti hL).intervalIntegrable

theorem phiAt_nat {L : Fld p} (hL : IsFinGal L) (j : ℕ) : phiAt L j = Phi L j := by
  induction j with
  | zero => simp [phiAt, Phi_zero]
  | succ j ih =>
    rw [phiAt] at ih ⊢
    rw [← intervalIntegral.integral_add_adjacent_intervals (integrable_phi hL 0 j)
      (integrable_phi hL j (j + 1 : ℕ)), ih, Phi_succ]
    push_cast
    rw [integral_piece j (t := (j : ℝ) + 1) (by linarith) le_rfl (L := L)]
    ring

theorem phiAt_piece {L : Fld p} (hL : IsFinGal L) (j : ℕ) {t : ℝ} (h1 : (j : ℝ) ≤ t)
    (h2 : t ≤ j + 1) : phiAt L t = Phi L j + (t - j) * wt L (j + 1) := by
  rw [← phiAt_nat hL j, phiAt, phiAt, ← intervalIntegral.integral_add_adjacent_intervals
    (integrable_phi hL 0 j) (integrable_phi hL j t), integral_piece j h1 h2]

theorem phiAt_mono {L : Fld p} (hL : IsFinGal L) {t t' : ℝ} (h : t ≤ t') :
    phiAt L t ≤ phiAt L t' := by
  rw [phiAt, phiAt, ← intervalIntegral.integral_add_adjacent_intervals
    (integrable_phi hL 0 t) (integrable_phi hL t t')]
  have : 0 ≤ ∫ x in t..t', (ramCardR L x : ℝ) / (ramCard L 0 : ℝ) :=
    intervalIntegral.integral_nonneg h fun x _ => by positivity
  linarith

/-- **`G^u(L) = G_{j+1}(L)` for `Φ_j < u ≤ Φ_{j+1}`** (i.e. `⌈ψ_L(u)⌉ = j + 1`). -/
theorem upperSet_eq {L : Fld p} (hL : IsFinGal L) {j : ℕ} {u : ℝ} (h1 : Phi L j < u)
    (h2 : u ≤ Phi L (j + 1)) : upperSet L u = ramSet L (j + 1) := by
  set S := {t : ℝ | -1 ≤ t ∧ u ≤ phiAt L t} with hS
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hw := wt_pos hL (j + 1)
  have hmem : ((j : ℝ) + 1) ∈ S := by
    refine ⟨by linarith, ?_⟩
    have := phiAt_nat hL (j + 1)
    push_cast at this
    rw [this]; exact h2
  have hbdd : BddBelow S := ⟨-1, fun t ht => ht.1⟩
  have hle : sInf S ≤ j + 1 := csInf_le hbdd hmem
  set t0 := (j : ℝ) + (u - Phi L j) / wt L (j + 1) with ht0
  have ht0j : (j : ℝ) < t0 := by
    have : 0 < (u - Phi L j) / wt L (j + 1) := div_pos (by linarith) hw
    linarith
  have ht0le : t0 ≤ j + 1 := by
    have : (u - Phi L j) / wt L (j + 1) ≤ 1 := by
      rw [div_le_one hw]; rw [Phi_succ] at h2; linarith
    linarith
  have hlb : ∀ t ∈ S, t0 ≤ t := by
    rintro t ⟨-, ht⟩
    by_contra hlt
    push Not at hlt
    by_cases htj : t ≤ j
    · have := phiAt_mono hL htj
      rw [phiAt_nat hL] at this
      linarith
    · push Not at htj
      rw [phiAt_piece hL j htj.le (by linarith)] at ht
      have : (t - j) * wt L (j + 1) < (t0 - j) * wt L (j + 1) :=
        mul_lt_mul_of_pos_right (by linarith) hw
      have e : (t0 - j) * wt L (j + 1) = u - Phi L j := by
        rw [ht0]; field_simp; ring
      linarith
  have hgt : (j : ℝ) < sInf S := lt_of_lt_of_le ht0j (le_csInf ⟨_, hmem⟩ hlb)
  have hc : ⌈sInf S⌉ = (j : ℤ) + 1 :=
    Int.ceil_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
  show ramSetR L (sInf S) = _
  unfold ramSetR
  rw [if_neg (by linarith), hc]
  rfl

theorem exists_piece {L : Fld p} (hL : IsFinGal L) {u : ℝ} (hu : 0 < u) :
    ∃ j : ℕ, Phi L j < u ∧ u ≤ Phi L (j + 1) := by
  classical
  have hg0 : 0 < (ramCard L 0 : ℝ) := by
    have := wt_pos hL 0
    unfold wt at this
    rcases (div_pos_iff.1 this) with h | h
    · exact h.2
    · exact absurd h.2 (not_lt.2 (Nat.cast_nonneg _))
  have hex : ∃ j : ℕ, u ≤ Phi L (j + 1) := by
    obtain ⟨m, hm⟩ := exists_nat_gt (u * (ramCard L 0 : ℝ))
    refine ⟨m, le_trans ?_ (Phi_ge hL (m + 1))⟩
    rw [mul_one_div, le_div_iff₀ hg0]; push_cast; linarith
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_eq_succ_pred (Nat.find hex) with h | h
  · rw [h, Phi_zero]; exact hu
  · have hmin := Nat.find_min hex (show (Nat.find hex).pred < Nat.find hex by omega)
    push Not at hmin
    rw [h]; exact hmin

/-- **H1 (`SwanAtIntegral`) is proved.** -/
theorem swanAtIntegral : SwanAtIntegral := by
  intro p _ k _ n ρ L hL
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hL.1.1
  obtain ⟨N, hN⟩ := eventuallyTrivial hL.1 hϖ
  set c : ℕ → ℕ := fun i => codimInv ρ (ramSet L i ∩ wildSet) with hcdef
  have hc0 : ∀ i, N ≤ i → c i = 0 := fun i hi =>
    codimInv_eq_zero fun σ hσ => hL.2 σ ⟨hσ.2, hN i hi hσ.1⟩
  -- left side: a finite sum
  have hsupp : Function.support (fun i : ℕ => ((ramCard L (i + 1) : ℚ) / ramCard L 0) *
      (codimInv ρ (ramSet L (i + 1) ∩ wildSet) : ℚ)) ⊆ ↑(Finset.range N) := by
    intro i hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hi
    have : c (i + 1) = 0 := hc0 (i + 1) (by omega)
    simp only [hcdef] at this
    simp [this]
  have hLHS : (swanAt L ρ : ℝ) = ∑ i ∈ Finset.range N, wt L (i + 1) * (c (i + 1) : ℝ) := by
    rw [swanAt, finsum_eq_sum_of_support_subset _ hsupp]
    push_cast
    rfl
  -- right side: the integrand is a finite sum of indicators
  have hpt : ∀ u ∈ Set.Ioi (0 : ℝ), (codimInv ρ (upperSet L u ∩ wildSet) : ℝ) =
      ∑ j ∈ Finset.range N,
        (Set.Ioc (Phi L j) (Phi L (j + 1))).indicator (fun _ => (c (j + 1) : ℝ)) u := by
    intro u hu
    obtain ⟨j, h1, h2⟩ := exists_piece hL.1 hu
    rw [upperSet_eq hL.1 h1 h2]
    have hmono := (Phi_strictMono hL.1).monotone
    have hterm : ∀ m, (Set.Ioc (Phi L m) (Phi L (m + 1))).indicator
        (fun _ => (c (m + 1) : ℝ)) u = if j = m then (c (m + 1) : ℝ) else 0 := by
      intro m
      by_cases hm : j = m
      · subst hm
        rw [Set.indicator_of_mem (show u ∈ Set.Ioc (Phi L j) (Phi L (j + 1)) from ⟨h1, h2⟩),
          if_pos rfl]
      · rw [Set.indicator_of_notMem, if_neg hm]
        rintro ⟨hm1, hm2⟩
        rcases lt_or_gt_of_ne hm with hlt | hlt
        · have := hmono (show j + 1 ≤ m by omega); linarith
        · have := hmono (show m + 1 ≤ j by omega); linarith
    rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_ite_eq (Finset.range N) j]
    split_ifs with hj
    · rfl
    · have : c (j + 1) = 0 := hc0 (j + 1) (by simp at hj; omega)
      simp only [hcdef] at this
      simp [this]
  have hint : ∀ j ∈ Finset.range N, Integrable
      ((Set.Ioc (Phi L j) (Phi L (j + 1))).indicator (fun _ => (c (j + 1) : ℝ)))
      (volume.restrict (Set.Ioi 0)) := by
    intro j _
    rw [integrable_indicator_iff measurableSet_Ioc]
    refine IntegrableOn.restrict ?_
    exact integrableOn_const (by simp [Real.volume_Ioc])
  rw [hLHS, setIntegral_congr_fun measurableSet_Ioi hpt, integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsub : Set.Ioc (Phi L j) (Phi L (j + 1)) ⊆ Set.Ioi 0 :=
    Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi (Phi_nonneg hL.1 j))
  rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr hsub, setIntegral_const,
    Real.volume_real_Ioc_of_le ((Phi_strictMono hL.1).monotone (Nat.le_succ j)), smul_eq_mul,
    Phi_succ]
  ring

end ChangeVar

/-! ## §8. Final form -/

/-- **Main result.** `AdaptedExists` holds outright; `SwanIndependent` (every `p`) and
`SwanIntegral` (L8) follow from one glue Prop, H1 `SwanAtIntegral` (the finite-level change of
variables), and one leaf, `HerbrandUpper` (Herbrand's theorem). -/
theorem swan_final (h1 : SwanAtIntegral) (hH : HerbrandUpper) :
    (∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p)) ∧ LadicCond.SwanIntegral ∧
      (∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p)) :=
  swan_all h1 upperAbsWild (upperAbsSurj_of_herbrand hH)

/-- **Main result (final form).** `AdaptedExists` holds outright; `SwanIndependent` (every `p`)
and `SwanIntegral` (L8) follow from the single leaf `HerbrandUpper` (Herbrand's theorem). -/
theorem swan_main (hH : HerbrandUpper) :
    (∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p)) ∧ LadicCond.SwanIntegral ∧
      (∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p)) :=
  swan_final swanAtIntegral hH

end Swan

#print axioms Swan.adaptedExists
#print axioms Swan.swanIntegral_of
#print axioms Swan.swanIndependent_of
#print axioms Swan.swan_all
#print axioms Swan.upperAbsSurj_of_herbrand
#print axioms Swan.swan_all'
#print axioms Swan.upperAbsWild
#print axioms Swan.swan_final
#print axioms Swan.swanAtIntegral
#print axioms Swan.swan_main
