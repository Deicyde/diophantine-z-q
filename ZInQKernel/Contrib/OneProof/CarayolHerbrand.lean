import ZInQKernel.Contrib.OneProof.CarayolPrintedIrr
import ZInQKernel.Contrib.OneProof.H.TailB

/-!
# carayol-herbrand: the Serre–Tate `condExp` is Darmon–Diamond–Taylor's conductor exponent

Task carayol-herbrand (2026-11-17), report `docs/research/carayol-herbrand.md`, scratch
`scratch/carayol-herbrand/`.

The leaf `CarayolPrinted.CarayolThmAIrr` (r17-rebase) states its conductor clause with the kernel's
`LadicCond.condExp`: `codim V^{I_p}` plus the Swan conductor computed at a finite Galois level
`L/ℚ_p` adapted to `ρ`, as the **lower-numbering** sum `∑_{i ≥ 1} (g_i/g_0) codim V^{G_i(L) ∩ P_p}`.
Darmon–Diamond–Taylor, *Fermat's Last Theorem* (1997), §2 (p. 54, reading supplied with the task;
UNVERIFIED here, no network), define the exponent at `p ≠ ℓ` as
`codim V^{I_p} + ∫₀^∞ codim V^{I_p^u} du` with the **upper-numbering** ramification groups `I_p^u`
of `G_{ℚ_p}`. The two agree by Herbrand's theorem; this file proves it in Lean for the
representations the leaf quantifies over, and restates the leaf with DDT's integral.

* §1 (new): `AdaptedExists` for an ultrametric normed coefficient field `K` with `‖ℓ‖ < 1` (the
  kernel's `Swan.adaptedExists` covers only `ℚ̄_ℓ`); the proof is `Swan.adaptedExists`'s, with
  `‖m‖ = 1` for `ℓ ∤ m` derived from `‖ℓ‖ < 1` by Bézout.
* §2 (new): `condExp_eq_ddt`: for continuous `ρ : G_{ℚ_p} → GL_n(K)`, `p ≠ ℓ`,
  `condExp ρ = codim V^{I_p} + ∫₀^∞ codim V^{G_{ℚ_p}^u} du` (as reals). The Swan part is the kernel's
  `Swan.swanAt_eq_integral_upperAbs` (finite-level change of variables `Swan.swanAtIntegral`,
  `G^u ⊆ P_p` for `u > 0` `Swan.upperAbsWild`, surjectivity of `G^u → G^u(L/ℚ_p)` from Herbrand's
  theorem `SwanBridge.herbrandUpper_of_quotient PkgI6.herbrandQuotient` and compactness), all proved
  in `ZInQKernel/Contrib/OneProof/H/TailB.lean`; the level is independent by `Swan.swanIndependent_proved`.
* §3: `K_{f,λ}` (Mathlib's `adicCompletion`, normed by `instNormedFieldValuedAdicCompletion`) has
  `‖ℓ‖ < 1` for `λ ∣ ℓ`.
* §4: the leaf `CarayolThmAIrrDDT` (DDT 1997 Thm 3.1 with DDT's conductor), the equivalence
  `carayolThmAIrr_iff_DDT`, and `carayolR17'_of_DDT`.

No `sorry`, no `axiom`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace CarayolHerbrand

open PkgI4 LadicCond

/-! ## §1. Adapted levels for ultrametric coefficient fields -/

section Adapted

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) K

/-- `‖m‖ = 1` for `ℓ ∤ m`, when `‖ℓ‖ < 1` (Bézout: `a m + b ℓ = 1`). -/
theorem norm_natCast_eq_one_of (hℓ : ‖(ℓ : K)‖ < 1) {m : ℕ} (hm : ¬ ℓ ∣ m) : ‖(m : K)‖ = 1 := by
  have hcop : Nat.Coprime m ℓ :=
    (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm))
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have h1 : ((a : K) * m + (b : K) * ℓ) = 1 := by
    have := congrArg (Int.cast : ℤ → K) hab
    push_cast at this
    exact this
  have hle : ‖(m : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K m
  refine le_antisymm hle ?_
  by_contra hlt
  push Not at hlt
  have h2 : ‖((a : K) * m + (b : K) * ℓ)‖ < 1 := by
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul]
      calc ‖(a : K)‖ * ‖(m : K)‖ ≤ 1 * ‖(m : K)‖ :=
            mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_intCast_le_one K a) (norm_nonneg _)
        _ < 1 := by rw [one_mul]; exact hlt
    · rw [norm_mul]
      calc ‖(b : K)‖ * ‖(ℓ : K)‖ ≤ 1 * ‖(ℓ : K)‖ :=
            mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_intCast_le_one K b) (norm_nonneg _)
        _ < 1 := by rw [one_mul]; exact hℓ
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

/-- Ultrametric: `‖a − b‖ < ‖b‖ ⇒ ‖a‖ = ‖b‖`. -/
theorem norm_eq_of_norm_sub_lt {a b : K} (h : ‖a - b‖ < ‖b‖) : ‖a‖ = ‖b‖ := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := a - b) (y := b) (ne_of_lt h)
  rw [sub_add_cancel] at this
  rw [this, max_eq_right h.le]

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
  calc ‖(m : K)‖ * ‖A i j‖ ≤ 1 * ‖A i j‖ :=
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
  | zero => simpa using Bd.zero (K := K) (n := n) (sq_nonneg a)
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

/-- **The key estimate.** If all entries of `A` have norm `≤ a = ‖A_{ij}‖`, `0 < a < 1`, and
`ℓ ∤ m`, then `‖((1 + A)^m − 1)_{ij}‖ = a`. -/
theorem norm_pow_sub_one_entry (hℓ : ‖(ℓ : K)‖ < 1) {A : Mat} {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hA : Bd a A) {i j : Fin n} (hij : ‖A i j‖ = a) {m : ℕ} (hm : ¬ ℓ ∣ m) :
    ‖((1 + A) ^ m - 1) i j‖ = a := by
  have hB := Bd.pow_sub ha0.le ha1.le hA m i j
  set B := (1 + A) ^ m - 1 - m • A with hBdef
  have e : ((1 + A) ^ m - 1) i j = B i j + (m : K) * A i j := by
    have hs : (m • A) i j = (m : K) * A i j := by
      rw [Matrix.smul_apply, nsmul_eq_mul]
    simp only [hBdef, Matrix.sub_apply, hs]; ring
  have hmA : ‖(m : K) * A i j‖ = a := by
    rw [norm_mul, norm_natCast_eq_one_of hℓ hm, one_mul, hij]
  rw [e, ← hmA]
  apply norm_eq_of_norm_sub_lt
  rw [add_sub_cancel_right, hmA]
  calc ‖B i j‖ ≤ a ^ 2 := hB
    _ < a := by nlinarith

open scoped Topology

variable {p : ℕ} [Fact p.Prime]

/-- The neighbourhood `{g : ‖g_{ij} − δ_{ij}‖ < r ∀ i j}` of `1` in `GL_n(K)`. -/
def nbhd (r : ℝ) : Set (GL (Fin n) K) :=
  {g | ∀ i j, ‖(g : Mat) i j - (1 : Mat) i j‖ < r}

theorem isOpen_nbhd (r : ℝ) : IsOpen (nbhd (K := K) (n := n) r) := by
  have e : nbhd (K := K) (n := n) r =
      ⋂ i, ⋂ j, {g : GL (Fin n) K | ‖(g : Mat) i j - (1 : Mat) i j‖ < r} := by
    ext g; simp [nbhd]
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact isOpen_lt (((Units.continuous_val.matrix_elem i j).sub continuous_const).norm)
    continuous_const

theorem one_mem_nbhd {r : ℝ} (hr : 0 < r) : (1 : GL (Fin n) K) ∈ nbhd r := by
  intro i j; simp [hr]

/-- **Continuity gives a level.** For continuous `ρ` and `r > 0` there is a finite Galois
`L/ℚ_p` with `ρ(G_L) ⊆ nbhd r`. -/
theorem exists_level (ρ : GQp p →* GL (Fin n) K) (hρ : Continuous ρ) {r : ℝ}
    (hr : 0 < r) : ∃ L : Fld p, IsFinGal L ∧ ∀ σ ∈ fixSet L, ρ σ ∈ nbhd r := by
  have hmem : ρ ⁻¹' nbhd r ∈ 𝓝 (1 : GQp p) := by
    apply hρ.continuousAt.preimage_mem_nhds
    rw [map_one]; exact (isOpen_nbhd r).mem_nhds (one_mem_nbhd hr)
  obtain ⟨E, hEf, hEn, hE⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ_[p] (PadicAlgCl p) _).1 hmem
  refine ⟨E, ⟨hEf, isGalois_iff.2 ⟨inferInstance, hEn⟩⟩, fun σ hσ => ?_⟩
  exact hE ((IntermediateField.mem_fixingSubgroup_iff E σ).2 hσ)

/-- **Adapted levels exist (GLUE, proved)** for continuous `ρ : G_{ℚ_p} → GL_n(K)`, `K` ultrametric
with `‖ℓ‖ < 1`, `ℓ ≠ p`: some finite Galois `L/ℚ_p` has `ρ` trivial on `P_p ∩ G_L`. The proof of the
kernel's `Swan.adaptedExists` (coefficients `ℚ̄_ℓ`), for general `K`. -/
theorem adaptedExists_of_norm (hℓ : ‖(ℓ : K)‖ < 1) (hℓp : ℓ ≠ p) (ρ : GQp p →* GL (Fin n) K)
    (hρ : Continuous ρ) : ∃ L : Fld p, IsAdapted L ρ := by
  obtain ⟨L, hL, hL1⟩ := exists_level ρ hρ one_pos
  refine ⟨L, hL, fun γ hγ => ?_⟩
  obtain ⟨hw, hf⟩ := hγ
  by_contra hne
  set A : Matrix (Fin n) (Fin n) K := (ρ γ : Matrix (Fin n) (Fin n) K) - 1 with hAdef
  have hρA : (ρ γ : Matrix (Fin n) (Fin n) K) = 1 + A := by
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
  obtain ⟨k, hk⟩ := HDec.Swan.wild_pow_fix hL' hw
  have hlt := hL'a (γ ^ (p ^ k)) hk i1 j1
  rw [map_pow, Units.val_pow_eq_pow_val, hρA, ← Matrix.sub_apply] at hlt
  have hℓ' : ¬ ℓ ∣ p ^ k := by
    intro h
    have h1 := (Fact.out : ℓ.Prime).dvd_of_dvd_pow h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1 h1)
  rw [norm_pow_sub_one_entry hℓ ha0 ha1 hBd rfl hℓ'] at hlt
  exact lt_irrefl _ hlt

end Adapted

/-! ## §2. `condExp` is DDT's conductor exponent (Herbrand) -/

section DDT

variable {p : ℕ} [Fact p.Prime]

/-- **Darmon–Diamond–Taylor's conductor exponent** at `p` of `ρ : G_{ℚ_p} → GL_n(k)`
(DDT 1997 §2, p. 54, as read for the task; UNVERIFIED here): `codim V^{I_p} + ∫₀^∞ codim V^{I_p^u} du`,
with the upper-numbering ramification groups of `G_{ℚ_p}` (`LadicCond.upperAbs p u`: `σ` with
`σ|_L ∈ Gal(L/ℚ_p)^u` for every finite Galois `L`, Serre, *Corps locaux* IV §3). For `u > 0`,
`G_{ℚ_p}^u ⊆ P_p ⊆ I_p`, so `I_p^u = G_{ℚ_p}^u` on the range of integration. -/
def ddtCondExp {k : Type*} [Field k] {n : ℕ} (ρ : GQp p →* GL (Fin n) k) : ℝ :=
  (codimInv ρ inertiaSet : ℝ) + ∫ u in Set.Ioi (0 : ℝ), (codimInv ρ (upperAbs p u) : ℝ)

/-- **Herbrand: the Serre–Tate `condExp` is DDT's conductor exponent at an adapted level (GLUE,
proved).** No continuity needed once an adapted level exists. -/
theorem condExp_eq_ddt_of_adapted {k : Type} [Field k] {n : ℕ} (ρ : GQp p →* GL (Fin n) k)
    {L : Fld p} (hL : IsAdapted L ρ) : (condExp ρ : ℝ) = ddtCondExp ρ := by
  rw [condExp_eq_condAt (HDec.Swan.swanIndependent_proved p) hL, condAt, Rat.cast_add,
    Rat.cast_natCast, ddtCondExp,
    HDec.Swan.swanAt_eq_integral_upperAbs HDec.Swan.swanAtIntegral HDec.Swan.upperAbsWild
      (HDec.Swan.upperAbsSurj_of_herbrand
        (HDec.SwanBridge.herbrandUpper_of_quotient PkgI6.herbrandQuotient)) hL]

/-- **`condExp ρ = ddtCondExp ρ` for every continuous `ρ : G_{ℚ_p} → GL_n(K)`, `K` ultrametric
with `‖ℓ‖ < 1`, `ℓ ≠ p` (GLUE, proved).** -/
theorem condExp_eq_ddt {K : Type} [NormedField K] [IsUltrametricDist K] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : ‖(ℓ : K)‖ < 1) (hℓp : ℓ ≠ p) {n : ℕ} (ρ : GQp p →* GL (Fin n) K) (hρ : Continuous ρ) :
    (condExp ρ : ℝ) = ddtCondExp ρ := by
  obtain ⟨L, hL⟩ := adaptedExists_of_norm hℓ hℓp ρ hρ
  exact condExp_eq_ddt_of_adapted ρ hL

end DDT

/-! ## §3. `K_{f,λ}` is ultrametric with `‖ℓ‖ < 1` -/

section Completion

open NumberField IsDedekindDomain

variable {F : Type*} [Field F] [NumberField F] (lam : HeightOneSpectrum (𝓞 F))

/-- Mathlib's norm on `K_λ` is ultrametric (found by instance search). -/
example : IsUltrametricDist (lam.adicCompletion F) := inferInstance

/-- For `λ ∣ ℓ`, `‖ℓ‖ < 1` in `K_λ` (Mathlib's norm on `adicCompletion`). -/
theorem norm_natCast_lt_one {ℓ : ℕ} (h : (ℓ : 𝓞 F) ∈ lam.asIdeal) :
    ‖(ℓ : lam.adicCompletion F)‖ < 1 := by
  have := (FinitePlace.norm_lt_one_iff_mem (K := F) lam (ℓ : 𝓞 F)).2 h
  rwa [map_natCast, map_natCast] at this

end Completion

/-! ## §4. The leaf with DDT's conductor, and the discharge of `r17` -/

section Leaf

open HeckeRing.GL2 NumberField IsDedekindDomain

/-- **LEAF (published): Darmon–Diamond–Taylor, *Fermat's Last Theorem* (Current Developments in
Mathematics 1995, International Press 1997), Theorem 3.1 (a)–(d), pp. 85–86, with DDT's definition of the
conductor (§2, p. 54); page numbers as read for the task, UNVERIFIED here.** For `F = ℚ`, weight 2: for a
newform `f ∈ S₂(Γ₁(N))` (Tau Ceti's `Newform N 2`) whose coefficient field `K_f` is a number field, a prime
`ℓ` and a place `λ ∣ ℓ` of `K_f`, there is a continuous `ρ = ρ_{f,λ} : G_ℚ → GL₂(K_{f,λ})` that is
irreducible, odd, unramified at `p ∤ Nℓ` with arithmetic Frobenius trace `a_p(f)`, and whose conductor is
the prime-to-`ℓ` part of `N`: at every prime `p ≠ ℓ`,
`codim V^{I_p} + ∫₀^∞ codim V^{I_p^u} du = v_p(N)`, with the upper-numbering ramification groups
`I_p^u = G_{ℚ_p}^u` (`LadicCond.upperAbs`; `u > 0`) of `ρ|_{G_{ℚ_p}}` (through `decomp p`). This is DDT's
exponent verbatim (as transcribed for the task); `CarayolPrinted.CarayolThmAIrr` is the same statement
with the Serre–Tate lower-numbering form `LadicCond.condExp`, and the two are equivalent
(`carayolThmAIrr_iff_DDT`, Herbrand's theorem, proved). Sources of the clauses as in `CarayolThmAIrr`
(Carayol 1986 Théorème (A), Casselman 1973, Ribet 1977 Thm 2.3, Shimura 1971 Thm 7.14, Deligne 1971);
DDT Thm 3.1 packages them. Not stronger than the print: one representation, only the listed properties. -/
def CarayolThmAIrrDDT : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2)
    [NumberField (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))]
    (ℓ : ℕ) [Fact ℓ.Prime] (lam : HeightOneSpectrum (𝓞 (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))),
    (ℓ : 𝓞 (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))) ∈ lam.asIdeal →
    ∃ ρ : GQ →* GL (Fin 2) (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))),
      Continuous ρ ∧
      (∀ W : Submodule (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))
          (Fin 2 → lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))),
        (∀ σ : GQ, ∀ v ∈ W, (ρ σ : Matrix (Fin 2) (Fin 2)
          (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))).mulVec v ∈ W) →
        W = ⊥ ∨ W = ⊤) ∧
      (∃ c : GQ, c * c = 1 ∧ (ρ c : Matrix (Fin 2) (Fin 2)
          (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))).det = -1) ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
        (∀ v : ValuationSubring Qbar, LiesOver v p →
          ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : GQ) = 1) ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ σ : Matrix (Fin 2) (Fin 2)
            (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))).trace =
            algebraMap (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))
              (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))
              ⟨coeff (f.toCuspForm : CF N 2) p, DSCoeffExt.coeff_mem_coeffField _ p⟩) ∧
      ∀ (p : ℕ) [Fact p.Prime], p ≠ ℓ →
        (codimInv (ρ.comp (decomp p)) inertiaSet : ℝ) +
          ∫ u in Set.Ioi (0 : ℝ), (codimInv (ρ.comp (decomp p)) (upperAbs p u) : ℝ) =
          (N.factorization p : ℝ)

/-- The conductor clause in the two forms, for the representations the leaf quantifies over
(continuous, coefficients `K_λ`, `λ ∣ ℓ`, `p ≠ ℓ`). -/
theorem condExp_decomp_eq_ddt {F : Type} [Field F] [NumberField F] (lam : HeightOneSpectrum (𝓞 F))
    {ℓ : ℕ} [Fact ℓ.Prime] (hlam : (ℓ : 𝓞 F) ∈ lam.asIdeal)
    (ρ : GQ →* GL (Fin 2) (lam.adicCompletion F)) (hρ : Continuous ρ) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ ℓ) :
    (condExp (ρ.comp (decomp p)) : ℝ) =
      (codimInv (ρ.comp (decomp p)) inertiaSet : ℝ) +
        ∫ u in Set.Ioi (0 : ℝ), (codimInv (ρ.comp (decomp p)) (upperAbs p u) : ℝ) :=
  condExp_eq_ddt (norm_natCast_lt_one lam hlam) hp.symm _
    (hρ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous_toFun)

/-- **`CarayolThmAIrr` is DDT 1997 Thm 3.1 with DDT's conductor (GLUE, proved; Herbrand's theorem).** -/
theorem carayolThmAIrr_iff_DDT : CarayolPrinted.CarayolThmAIrr ↔ CarayolThmAIrrDDT := by
  constructor
  · intro h N _ f _ ℓ _ lam hlam
    obtain ⟨ρ, hc, hirr, hodd, hatt, hcond⟩ := h N f ℓ lam hlam
    refine ⟨ρ, hc, hirr, hodd, hatt, fun p _ hp => ?_⟩
    rw [← condExp_decomp_eq_ddt lam hlam ρ hc p hp, hcond p hp, Rat.cast_natCast]
  · intro h N _ f _ ℓ _ lam hlam
    obtain ⟨ρ, hc, hirr, hodd, hatt, hcond⟩ := h N f ℓ lam hlam
    refine ⟨ρ, hc, hirr, hodd, hatt, fun p _ hp => ?_⟩
    have e := (condExp_decomp_eq_ddt lam hlam ρ hc p hp).trans (hcond p hp)
    exact_mod_cast e

theorem carayolThmAIrr_of_DDT (h : CarayolThmAIrrDDT) : CarayolPrinted.CarayolThmAIrr :=
  carayolThmAIrr_iff_DDT.2 h

/-- **`r17` (`LadicCond.CarayolR17'`) from DDT 1997 Thm 3.1 with DDT's conductor and the bundle leaf
`EigenformCoeffFieldFinite`.** -/
theorem carayolR17'_of_DDT (h : CarayolThmAIrrDDT) (hK : DSCoeffExt.EigenformCoeffFieldFinite) :
    LadicCond.CarayolR17' :=
  CarayolPrinted.carayolR17'_of_printedIrr (carayolThmAIrr_of_DDT h) hK

end Leaf

end CarayolHerbrand
