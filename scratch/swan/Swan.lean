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

end Swan

#print axioms Swan.adaptedExists
#print axioms Swan.swanIntegral_of
#print axioms Swan.swanIndependent_of
#print axioms Swan.swan_all
