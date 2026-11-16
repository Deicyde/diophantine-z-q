import ZInQKernel.OneProof.H.TailT

/-! # ds965-weak: `DSThm965` from its weakest printed reading

Task ds965-weak (2026-11-15), report `docs/research/ds965-weak.md`.

The field `dsThm965 : ZInQ.Contrib.HodgeSplit.DSThm965` (Diamond–Shurman Thm 9.6.5, Deligne) says
that arithmetic Frobenius has characteristic polynomial `x² − a_p x + χ(p) p^{k−1}`. Its statement
review flags the reading in which the print says only that `ρ(Frob_𝔭)` *satisfies* that polynomial.
This file states that weakest reading as the leaf `DSThm965Weak` and proves `DSThm965` from it with
no further leaf: the glue uses only the kernel's proved Chebotarev density (T18, via
`frobeniusDense_C9`) and Mathlib's cyclotomic characters (through hodge-split's `eps0`, `cycQ`).

Proof. Let `ρ` be the weak leaf's representation.
* If some `ρ(σ₀)` is not scalar: on the open set `W` of `σ` with `ρ(σ)` not scalar, a `2 × 2`
  matrix satisfying the monic quadratic `P_p` has characteristic polynomial `P_p`, so
  `det ρ(Frob_𝔭) = χ(p) p^{k−1} = ε₀ χ_ℓ^{k−1}(Frob_𝔭)` for Frobenius elements in `W`; by Chebotarev
  density `det ρ = ε₀ χ_ℓ^{k−1}` on `W`, and on all of `G_ℚ` since `σ = (σσ₀)σ₀⁻¹` with `σσ₀ ∈ W`
  when `ρ(σ)` is scalar. A matrix satisfying `P_p` with determinant `P_p(0) ≠ 0` has
  characteristic polynomial `P_p`, so `ρ` itself works.
* If every `ρ(σ)` is scalar, `ρ = ψ₀ · 1` with `ψ₀(Frob_𝔭)` a root of `P_p`; then
  `ρ' = diag(ψ₀, ε₀ χ_ℓ^{k−1} ψ₀⁻¹)` is continuous, unramified outside `Nℓ`, and `ρ'(Frob_𝔭)` has
  eigenvalues the two roots of `P_p` (their product is `χ(p) p^{k−1}`).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace DS965Weak

open Polynomial
open ZInQ.Contrib.HodgeSplit (eps0 eps0_arithFrob eps0_continuous cycQ_arithFrob continuous_cycQ
  frobeniusDense_C9 diagHom modCycQ chiL pow_eq_pow_mod_of val_eq_one_of_pow)

/-! ## 1. The leaf -/

/-- **The `aeval` form (Deligne's theorem in its weakest printed reading: Frobenius *satisfies* the Hecke
polynomial).** Diamond–Shurman, *A First Course in Modular Forms*, GTM 228 (2005), Thm 9.6.5
(`k ≥ 2`; from Deligne, Sém. Bourbaki 355 (1969, publ. 1971), and Shimura 1971 Thm 7.14 for
`k = 2`; numbering UNVERIFIED): for a normalized eigenform `f ∈ S_k(N, χ)`, `k ≥ 2`, and `λ ∣ ℓ` in
`K_f`, there is a continuous `ρ_{f,λ} : G_ℚ → GL₂(K_{f,λ})`, unramified at every `p ∤ ℓN`, such that
for every maximal ideal `𝔭` of `ℤ̄` over `p`, `ρ_{f,λ}(Frob_𝔭)` satisfies (this wording UNVERIFIED; it may print "characteristic polynomial") the polynomial equation
`x² − a_p(f) x + χ(p) p^{k−1} = 0`. Lean form as `ZInQ.Contrib.HodgeSplit.DSThm965` (coefficients
extended along `K_{f,λ} → ℚ̄_ℓ` given by `ιL ∘ ιC⁻¹`, places of `ℚ̄` as valuation subrings,
arithmetic Frobenius as pkg-I4's `IsArithFrob`), with the conclusion
`P(ρ(σ)) = 0` (`Polynomial.aeval`) in place of `charpoly ρ(σ) = P`. It is the print under the
weakest reading, and a consequence of the print under every stronger one (Cayley–Hamilton). -/
def DSThm965WeakAeval : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : ZInQ.Contrib.G9.PkgI4.CF N k),
    0 < N → 2 ≤ k → ZInQ.Contrib.G9.PkgI4.IsNormalizedEigenform g χ →
    ∃ ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ 2, ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
      ρ.UnramifiedAt p ∧ ∃ α β : ZInQ.Contrib.G9.PkgI4.Qbar, ιC α = ZInQ.Contrib.G9.PkgI4.coeff g p ∧
        ιC β = χ (p : ZMod N) * (p : ℂ) ^ (k - 1) ∧
        ∀ (v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar) (σ : ZInQ.Contrib.G9.PkgI4.GQ), ZInQ.Contrib.G9.PkgI4.LiesOver v p →
          ZInQ.Contrib.G9.PkgI4.IsArithFrob σ v p →
          aeval (ρ.mat σ) (X ^ 2 - C (ιL α) * X + C (ιL β)) = 0

/-- **LEAF (Deligne's theorem, either printed wording).** As `DSThm965WeakAeval`, with the per-Frobenius conclusion
`charpoly ρ(σ) = P ∨ P(ρ(σ)) = 0`: both printed wordings of Diamond–Shurman Thm 9.6.5 ("characteristic polynomial"
or "satisfies") give it by or-introduction, so it is a direct instance of the print under either reading. The
`α` clause rests on Diamond–Shurman printing the theorem with the number field `K_f` (page check pending). -/
def DSThm965Weak : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : ZInQ.Contrib.G9.PkgI4.CF N k),
    0 < N → 2 ≤ k → ZInQ.Contrib.G9.PkgI4.IsNormalizedEigenform g χ →
    ∃ ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ 2, ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
      ρ.UnramifiedAt p ∧ ∃ α β : ZInQ.Contrib.G9.PkgI4.Qbar, ιC α = ZInQ.Contrib.G9.PkgI4.coeff g p ∧
        ιC β = χ (p : ZMod N) * (p : ℂ) ^ (k - 1) ∧
        ∀ (v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar) (σ : ZInQ.Contrib.G9.PkgI4.GQ), ZInQ.Contrib.G9.PkgI4.LiesOver v p →
          ZInQ.Contrib.G9.PkgI4.IsArithFrob σ v p →
          (ρ.mat σ).charpoly = X ^ 2 - C (ιL α) * X + C (ιL β) ∨
            aeval (ρ.mat σ) (X ^ 2 - C (ιL α) * X + C (ιL β)) = 0

/-- The disjunctive leaf gives the `aeval` form (left disjunct: Cayley–Hamilton). -/
theorem dsThm965WeakAeval_of_weak (h : DSThm965Weak) : DSThm965WeakAeval := by
  intro ℓ _ ιC ιL N k χ g hN hk hg
  obtain ⟨ρ, hρ⟩ := h ℓ ιC ιL N k χ g hN hk hg
  refine ⟨ρ, fun p hp hpN => ?_⟩
  obtain ⟨hu, α, β, hα, hβ, hc⟩ := hρ p hp hpN
  refine ⟨hu, α, β, hα, hβ, fun v σ hv hσ => ?_⟩
  rcases hc v σ hv hσ with hc | hc
  · rw [← hc]
    exact Matrix.aeval_self_charpoly _
  · exact hc

/-- The leaf is a consequence of `DSThm965` (or-introduction): it is never stronger. -/
theorem dsThm965Weak_of_dsThm965 (h : ZInQ.Contrib.HodgeSplit.DSThm965) : DSThm965Weak := by
  intro ℓ _ ιC ιL N k χ g hN hk hg
  obtain ⟨ρ, hρ⟩ := h ℓ ιC ιL N k χ g hN hk hg
  refine ⟨ρ, fun p hp hpN => ?_⟩
  obtain ⟨hu, α, β, hα, hβ, hc⟩ := hρ p hp hpN
  exact ⟨hu, α, β, hα, hβ, fun v σ hv hσ => Or.inl (hc v σ hv hσ)⟩

/-! ## 2. `2 × 2` matrices satisfying a monic quadratic -/

section Mat

variable {K : Type*} [Field K]

/-- `M` is not a scalar matrix. -/
def NonScalar (M : Matrix (Fin 2) (Fin 2) K) : Prop :=
  M 0 1 ≠ 0 ∨ M 1 0 ≠ 0 ∨ M 0 0 ≠ M 1 1

theorem charpoly_fin_two (M : Matrix (Fin 2) (Fin 2) K) :
    M.charpoly = X ^ 2 - C (M 0 0 + M 1 1) * X + C (M 0 0 * M 1 1 - M 0 1 * M 1 0) := by
  rw [Matrix.charpoly, Matrix.det_fin_two]
  simp only [Matrix.charmatrix_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _
    (show (0 : Fin 2) ≠ 1 by decide), Matrix.diagonal_apply_ne _ (show (1 : Fin 2) ≠ 0 by decide),
    RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  simp only [map_sub, map_add, map_mul]
  ring

theorem aeval_quad_apply (M : Matrix (Fin 2) (Fin 2) K) (a b : K) (i j : Fin 2) :
    (aeval M (X ^ 2 - C a * X + C b)) i j =
      (M * M) i j - a * M i j + (if i = j then b else 0) := by
  simp [sq, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply]

theorem quad_entries {M : Matrix (Fin 2) (Fin 2) K} {a b : K}
    (h : aeval M (X ^ 2 - C a * X + C b) = 0) :
    M 0 0 * M 0 0 + M 0 1 * M 1 0 - a * M 0 0 + b = 0 ∧
    M 0 0 * M 0 1 + M 0 1 * M 1 1 - a * M 0 1 = 0 ∧
    M 1 0 * M 0 0 + M 1 1 * M 1 0 - a * M 1 0 = 0 ∧
    M 1 0 * M 0 1 + M 1 1 * M 1 1 - a * M 1 1 + b = 0 := by
  have e : ∀ i j, (aeval M (X ^ 2 - C a * X + C b)) i j = 0 := fun i j => by rw [h]; rfl
  have e00 := e 0 0; have e01 := e 0 1; have e10 := e 1 0; have e11 := e 1 1
  simp only [aeval_quad_apply, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  simp only [Fin.isValue, ite_true, show ((0 : Fin 2) = 1) = False by decide,
    show ((1 : Fin 2) = 0) = False by decide, ite_false, add_zero] at e00 e01 e10 e11
  exact ⟨e00, e01, e10, e11⟩

/-- A non-scalar `2 × 2` matrix satisfying a monic quadratic has it as characteristic polynomial. -/
theorem charpoly_of_aeval_nonScalar {M : Matrix (Fin 2) (Fin 2) K} {a b : K} (hM : NonScalar M)
    (h : aeval M (X ^ 2 - C a * X + C b) = 0) : M.charpoly = X ^ 2 - C a * X + C b := by
  obtain ⟨h00, h01, h10, h11⟩ := quad_entries h
  have ha : a = M 0 0 + M 1 1 := by
    by_contra hne
    have ht : M 0 0 + M 1 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have e01 : M 0 1 * (M 0 0 + M 1 1 - a) = 0 := by linear_combination h01
    have e10 : M 1 0 * (M 0 0 + M 1 1 - a) = 0 := by linear_combination h10
    have e00 : (M 0 0 - M 1 1) * (M 0 0 + M 1 1 - a) = 0 := by linear_combination h00 - h11
    rcases hM with h' | h' | h'
    · exact h' ((mul_eq_zero.mp e01).resolve_right ht)
    · exact h' ((mul_eq_zero.mp e10).resolve_right ht)
    · exact h' (sub_eq_zero.mp ((mul_eq_zero.mp e00).resolve_right ht))
  have hb : b = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by linear_combination h00 + M 0 0 * ha
  rw [charpoly_fin_two, ← ha, ← hb]

/-- A `2 × 2` matrix satisfying a monic quadratic whose constant term is its (nonzero) determinant
has it as characteristic polynomial. -/
theorem charpoly_of_aeval_det {M : Matrix (Fin 2) (Fin 2) K} {a b : K}
    (h : aeval M (X ^ 2 - C a * X + C b) = 0) (hd : M.det = b) (hb : b ≠ 0) :
    M.charpoly = X ^ 2 - C a * X + C b := by
  by_cases hM : NonScalar M
  · exact charpoly_of_aeval_nonScalar hM h
  · simp only [NonScalar, not_or, not_not] at hM
    obtain ⟨h01, h10, h0011⟩ := hM
    obtain ⟨h00, -, -, -⟩ := quad_entries h
    rw [Matrix.det_fin_two, h01, h10, ← h0011] at hd
    have hc : M 0 0 ≠ 0 := by
      intro hc; apply hb; rw [← hd, hc]; ring
    have e : M 0 0 * (a - 2 * M 0 0) = 0 := by
      rw [h01, h10] at h00; linear_combination -h00 - hd
    have ha : a = M 0 0 + M 1 1 := by
      rw [← h0011]; linear_combination (mul_eq_zero.mp e).resolve_left hc
    rw [charpoly_fin_two, ← ha, h01, h10, ← h0011, ← hd]

/-- The `(0,0)` entry of a scalar matrix satisfying a monic quadratic is a root of it. -/
theorem root_of_aeval_scalar {M : Matrix (Fin 2) (Fin 2) K} {a b : K} (hM : ¬ NonScalar M)
    (h : aeval M (X ^ 2 - C a * X + C b) = 0) : M 0 0 * M 0 0 - a * M 0 0 + b = 0 := by
  simp only [NonScalar, not_or, not_not] at hM
  obtain ⟨h00, -, -, -⟩ := quad_entries h
  rw [hM.1] at h00
  linear_combination h00

/-- A scalar matrix times a non-scalar one is non-scalar. -/
theorem nonScalar_mul {M M' : Matrix (Fin 2) (Fin 2) K} (hM : ¬ NonScalar M) (hd : M.det ≠ 0)
    (hM' : NonScalar M') : NonScalar (M * M') := by
  simp only [NonScalar, not_or, not_not] at hM
  obtain ⟨h01, h10, h0011⟩ := hM
  have hc : M 0 0 ≠ 0 := by
    intro hc; apply hd; rw [Matrix.det_fin_two, h01, h10, hc]; ring
  simp only [NonScalar, Matrix.mul_apply, Fin.sum_univ_two, h01, h10, ← h0011, zero_mul,
    add_zero, zero_add]
  rcases hM' with h' | h' | h'
  · exact Or.inl (mul_ne_zero hc h')
  · exact Or.inr (Or.inl (mul_ne_zero hc h'))
  · exact Or.inr (Or.inr fun e => h' (mul_left_cancel₀ hc e))

end Mat

/-! ## 3. Chebotarev density on an open set -/

open ZInQ.Contrib.G9.PkgI4 in
/-- Two continuous functions on `G_ℚ` that agree at the arithmetic Frobenius elements (above primes
outside `S`) lying in an open set `W` agree on `W` (GLUE, from the kernel's T18). -/
theorem eq_on_open_of_eq_on_arithFrob {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (S : Finset ℕ) (f₁ f₂ : GQ → Y) (h₁ : Continuous f₁) (h₂ : Continuous f₂) (W : Set GQ)
    (hW : IsOpen W)
    (hfr : ∀ p, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p →
      IsArithFrob τ v p → τ ∈ W → f₁ τ = f₂ τ) : ∀ g ∈ W, f₁ g = f₂ g := by
  intro g hg
  by_contra hne
  have hopen : IsOpen ({x | f₁ x ≠ f₂ x} ∩ W) := (isOpen_ne_fun h₁ h₂).inter hW
  have hmem : (fun y => g * y) ⁻¹' ({x | f₁ x ≠ f₂ x} ∩ W) ∈ nhds (1 : GQ) := by
    apply (hopen.preimage (continuous_const.mul continuous_id)).mem_nhds
    simpa using ⟨hne, hg⟩
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Qbar _).mp hmem
  have hU : IsOpen (E.fixingSubgroup : Set GQ) := IntermediateField.fixingSubgroup_isOpen E
  obtain ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩ := frobeniusDense_C9 E.fixingSubgroup hU g S
  have hfix : g⁻¹ * τ ∈ E.fixingSubgroup := by
    have := E.fixingSubgroup.inv_mem hU'
    simpa using this
  have := hsub hfix
  simp only [Set.mem_preimage, mul_inv_cancel_left, Set.mem_inter_iff, Set.mem_ofPred_eq] at this
  exact this.1 (hfr p hp hpS v τ hv hτ this.2)

/-! ## 4. `ε₀` and `χ_ℓ` are unramified outside `Nℓ` -/

section Inertia

open ZInQ.Contrib.G9.PkgI4

theorem sub_mem_nonunits_of_inertia {v : ValuationSubring Qbar} {σ : v.decompositionSubgroup ℚ}
    (hσ : σ ∈ v.inertiaSubgroup ℚ) {x : Qbar} (hx : x ∈ v) :
    (σ : GQ) x - x ∈ v.nonunits := by
  let y : v := ⟨x, hx⟩
  have hres : IsLocalRing.residue v (σ • y) = IsLocalRing.residue v y := by
    rw [IsLocalRing.ResidueField.residue_smul]
    have h1 : MulSemiringAction.toRingAut _ (IsLocalRing.ResidueField v) σ = 1 := hσ
    exact congrArg (fun f => f (IsLocalRing.residue v y)) h1
  have h0 : σ • y - y ∈ IsLocalRing.maximalIdeal v := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hres, sub_self]
  rw [ValuationSubring.mem_nonunits_iff]
  exact (ValuationSubring.valuation_lt_one_iff v (σ • y - y)).mp h0

/-- Roots of unity of order prime to `p` stay distinct modulo a place above `p`. -/
theorem eq_of_sub_mem_nonunits {v : ValuationSubring Qbar} {p : ℕ} (hp : p.Prime)
    (hv : LiesOver v p) {ζ y : Qbar} {m : ℕ} (hm : m ≠ 0) (hζ : ζ ^ m = 1) (hy : y ^ m = 1)
    (hpm : ¬ p ∣ m) (h : y - ζ ∈ v.nonunits) : y = ζ := by
  set val := v.valuation
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp [hm] at hζ
  set ξ := y / ζ with hξ
  have hξm : ξ ^ m = 1 := by rw [hξ, div_pow, hy, hζ, div_one]
  have hζ1 : val ζ = 1 := val_eq_one_of_pow hm hζ
  have hlt : val (y - ζ) < 1 := (v.mem_nonunits_iff).mp h
  have hξ1 : val (ξ - 1) < 1 := by
    have : ξ - 1 = (y - ζ) / ζ := by rw [hξ]; field_simp
    rw [this, map_div₀, hζ1, div_one]
    exact hlt
  by_contra hne
  have hξne : ξ ≠ 1 := by
    intro h; apply hne
    rw [hξ, div_eq_one_iff_eq hζ0] at h
    exact h
  have hgeom : ∑ j ∈ Finset.range m, ξ ^ j = 0 := by
    have := geom_sum_mul ξ m
    rw [hξm, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hξne)
  have hj : ∀ j, val (ξ ^ j - 1) < 1 := by
    intro j
    have : ξ ^ j - 1 = (ξ - 1) * ∑ i ∈ Finset.range j, ξ ^ i := by
      rw [mul_comm, geom_sum_mul]
    rw [this, map_mul]
    have hs : val (∑ i ∈ Finset.range j, ξ ^ i) ≤ 1 := by
      apply Valuation.map_sum_le
      intro i _
      rw [map_pow]
      have : val ξ = 1 := val_eq_one_of_pow hm hξm
      rw [this, one_pow]
    calc val (ξ - 1) * val (∑ i ∈ Finset.range j, ξ ^ i) ≤ val (ξ - 1) * 1 :=
          mul_le_mul_of_nonneg_left hs zero_le
      _ < 1 := by rw [mul_one]; exact hξ1
  have hmval : val (m : Qbar) < 1 := by
    have : (m : Qbar) = -∑ j ∈ Finset.range m, (ξ ^ j - 1) := by
      rw [Finset.sum_sub_distrib, hgeom]; simp
    rw [this, Valuation.map_neg]
    exact Valuation.map_sum_lt' _ zero_lt_one fun j _ => hj j
  have hpval : val (p : Qbar) < 1 := (v.mem_nonunits_iff).mp hv
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * m + b * p = 1 := by
    have := Nat.Coprime.isCoprime hcop.symm
    obtain ⟨a, b, h⟩ := this
    exact ⟨a, b, by exact_mod_cast h⟩
  have h1 : val (1 : Qbar) < 1 := by
    have : (1 : Qbar) = (a : Qbar) * m + (b : Qbar) * p := by exact_mod_cast hab.symm
    rw [this]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (v.valuation_le_one ⟨_, intCast_mem v a⟩))
        hmval
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (v.valuation_le_one ⟨_, intCast_mem v b⟩))
        hpval
  rw [map_one] at h1
  exact lt_irrefl _ h1

/-- An inertia element at `v ∣ p` fixes the roots of unity of order prime to `p`. -/
theorem inertia_fix_rootOfUnity {v : ValuationSubring Qbar} {p : ℕ} (hp : p.Prime)
    (hv : LiesOver v p) {σ : v.decompositionSubgroup ℚ} (hσ : σ ∈ v.inertiaSubgroup ℚ)
    {ζ : Qbar} {m : ℕ} (hm : m ≠ 0) (hζ : ζ ^ m = 1) (hpm : ¬ p ∣ m) : (σ : GQ) ζ = ζ := by
  have hζv : ζ ∈ v := (v.valuation_le_one_iff ζ).mp (val_eq_one_of_pow hm hζ).le
  refine eq_of_sub_mem_nonunits hp hv hm hζ ?_ hpm (sub_mem_nonunits_of_inertia hσ hζv)
  rw [← map_pow, hζ, map_one]

theorem cycQ_inertia {ℓ : ℕ} [Fact ℓ.Prime] {v : ValuationSubring Qbar} {p : ℕ} (hp : p.Prime)
    (hpl : p ≠ ℓ) (hv : LiesOver v p) {σ : v.decompositionSubgroup ℚ}
    (hσ : σ ∈ v.inertiaSubgroup ℚ) : ZInQ.Contrib.HodgeSplit.G0Galois.cycQ ℓ (σ : GQ) = 1 := by
  have hc : ((cyclotomicCharacter Qbar ℓ (σ : GQ).toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = 1 := by
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [cyclotomicCharacter.toZModPow, map_one, ← Nat.cast_one]
    have hl : (ℓ ^ n) ≠ 0 := pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero
    haveI : NeZero (ℓ ^ n) := ⟨hl⟩
    refine (modularCyclotomicCharacter.unique Qbar _ (σ : GQ).toRingEquiv fun t ht => ?_).symm
    have htn : (t : Qbar) ^ (ℓ ^ n) = 1 := by
      have := (mem_rootsOfUnity _ _).mp ht
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    have hpm : ¬ p ∣ ℓ ^ n := fun h =>
      hpl ((Nat.prime_dvd_prime_iff_eq hp (Fact.out : ℓ.Prime)).mp (hp.dvd_of_dvd_pow h))
    change (σ : GQ) (t : Qbar) = ((t ^ (((1 : ℕ) : ZMod (ℓ ^ n))).val : Qbarˣ) : Qbar)
    rw [inertia_fix_rootOfUnity hp hv hσ hl htn hpm, Units.val_pow_eq_pow_val, ZMod.val_natCast,
      ← pow_eq_pow_mod_of htn, pow_one]
  apply Units.ext
  change algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)
    (((cyclotomicCharacter Qbar ℓ (σ : GQ).toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) = _
  rw [hc]
  simp

theorem eps0_inertia {ℓ : ℕ} [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {v : ValuationSubring Qbar} {p : ℕ}
    (hp : p.Prime) (hpN : ¬ p ∣ N) (hv : LiesOver v p) {σ : v.decompositionSubgroup ℚ}
    (hσ : σ ∈ v.inertiaSubgroup ℚ) : eps0 ιC ιL χ (σ : GQ) = 1 := by
  have h1 : modCycQ (N := N) (σ : GQ) = 1 := by
    apply Units.ext
    rw [Units.val_one, ← Nat.cast_one]
    refine (modularCyclotomicCharacter.unique Qbar _ (σ : GQ).toRingEquiv fun t ht => ?_).symm
    have htn : (t : Qbar) ^ N = 1 := by
      have := (mem_rootsOfUnity _ _).mp ht
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    change (σ : GQ) (t : Qbar) = ((t ^ (((1 : ℕ) : ZMod N)).val : Qbarˣ) : Qbar)
    rw [inertia_fix_rootOfUnity hp hv hσ (NeZero.ne N) htn hpN, Units.val_pow_eq_pow_val,
      ZMod.val_natCast, ← pow_eq_pow_mod_of htn, pow_one]
  change chiL ιC ιL χ (modCycQ (σ : GQ)) = 1
  rw [h1, map_one]

end Inertia

/-! ## 5. The scalar case: `diag(ψ₀, ε₀ χ_ℓ^{k−1} ψ₀⁻¹)` -/

section Scalar

open ZInQ.Contrib.G9.PkgI4

variable {ℓ : ℕ} [Fact ℓ.Prime]

theorem mat_mul (ρ : GaloisRep ℓ 2) (σ τ : GQ) : ρ.mat (σ * τ) = ρ.mat σ * ρ.mat τ := by
  simp [GaloisRep.mat, map_mul, Units.val_mul]

theorem mat_one (ρ : GaloisRep ℓ 2) : ρ.mat 1 = 1 := by
  simp [GaloisRep.mat]

theorem continuous_mat (ρ : GaloisRep ℓ 2) : Continuous ρ.mat :=
  Units.continuous_val.comp ρ.continuous_toHom

theorem mul_apply00 {M M' : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)} (h : M 0 1 = 0) :
    (M * M') 0 0 = M 0 0 * M' 0 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, h]

theorem scalar01 (ρ : GaloisRep ℓ 2) (hsc : ∀ σ, ¬ NonScalar (ρ.mat σ)) (σ : GQ) :
    ρ.mat σ 0 1 = 0 := by
  have := hsc σ
  simp only [NonScalar, not_or, not_not] at this
  exact this.1

theorem mat00_mul (ρ : GaloisRep ℓ 2) (hsc : ∀ σ, ¬ NonScalar (ρ.mat σ)) (σ τ : GQ) :
    ρ.mat (σ * τ) 0 0 = ρ.mat σ 0 0 * ρ.mat τ 0 0 := by
  rw [mat_mul]
  exact mul_apply00 (scalar01 ρ hsc σ)

theorem mat00_one (ρ : GaloisRep ℓ 2) : ρ.mat 1 0 0 = 1 := by
  rw [mat_one]; rfl

/-- `σ ↦ ρ(σ)₀₀` for a representation by scalar matrices. -/
def psi0 (ρ : GaloisRep ℓ 2) (hsc : ∀ σ, ¬ NonScalar (ρ.mat σ)) : GQ →* (PadicAlgCl ℓ)ˣ where
  toFun σ := ⟨ρ.mat σ 0 0, ρ.mat σ⁻¹ 0 0,
    by rw [← mat00_mul ρ hsc, mul_inv_cancel, mat00_one],
    by rw [← mat00_mul ρ hsc, inv_mul_cancel, mat00_one]⟩
  map_one' := Units.ext (mat00_one ρ)
  map_mul' σ τ := Units.ext (mat00_mul ρ hsc σ τ)

theorem psi0_val (ρ : GaloisRep ℓ 2) (hsc : ∀ σ, ¬ NonScalar (ρ.mat σ)) (σ : GQ) :
    ((psi0 ρ hsc σ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = ρ.mat σ 0 0 := rfl

theorem continuous_psi0 (ρ : GaloisRep ℓ 2) (hsc : ∀ σ, ¬ NonScalar (ρ.mat σ)) :
    Continuous (psi0 ρ hsc) := by
  rw [Units.continuous_iff]
  exact ⟨(continuous_mat ρ).matrix_elem 0 0,
    ((continuous_mat ρ).matrix_elem 0 0).comp continuous_inv⟩

/-- `ψ₁ = ε₀ χ_ℓ^{k−1} ψ₀⁻¹`. -/
def psi1 (a b c : GQ →* (PadicAlgCl ℓ)ˣ) (k : ℤ) : GQ →* (PadicAlgCl ℓ)ˣ where
  toFun σ := a σ * b σ ^ (k - 1) * (c σ)⁻¹
  map_one' := by simp
  map_mul' σ τ := by
    simp only [map_mul, mul_zpow, mul_inv]
    ac_rfl

theorem diagHom_continuous (a d : GQ →* (PadicAlgCl ℓ)ˣ) (ha : Continuous a)
    (hd : Continuous d) : Continuous (diagHom a d) := by
  have hdiagc : ∀ (f g : GQ → PadicAlgCl ℓ), Continuous f → Continuous g →
      Continuous fun σ => !![f σ, 0; 0, g σ] := by
    intro f g hf hg
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j
    · simpa using hf
    · simpa using continuous_const
    · simpa using continuous_const
    · simpa using hg
  have hac : Continuous fun σ => (a σ : PadicAlgCl ℓ) := Units.continuous_val.comp ha
  have hdc : Continuous fun σ => (d σ : PadicAlgCl ℓ) := Units.continuous_val.comp hd
  rw [Units.continuous_iff]
  refine ⟨hdiagc _ _ hac hdc, ?_⟩
  have : (fun σ => (((diagHom a d σ)⁻¹ : GL (Fin 2) (PadicAlgCl ℓ)) :
      Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)))
      = fun σ => !![(a σ⁻¹ : PadicAlgCl ℓ), 0; 0, (d σ⁻¹ : PadicAlgCl ℓ)] := by
    funext σ; rw [← map_inv]; rfl
  rw [this]
  exact hdiagc _ _ (hac.comp continuous_inv) (hdc.comp continuous_inv)

end Scalar

/-! ## 6. `DSThm965` from the weak leaf -/

section Main

open ZInQ.Contrib.G9.PkgI4

/-- **`DSThm965` from its weakest printed reading** (GLUE proved: the kernel's T18 and Mathlib's
cyclotomic characters; no other leaf). -/
theorem dsThm965_of_weakAeval (hW : DSThm965WeakAeval) : ZInQ.Contrib.HodgeSplit.DSThm965 := by
  intro ℓ _ ιC ιL N k χ g hN hk hg
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨ρ, hρ⟩ := hW ℓ ιC ιL N k χ g hN hk hg
  have hNl : N * ℓ ≠ 0 := Nat.mul_ne_zero hN.ne' (Fact.out : ℓ.Prime).ne_zero
  -- `F(σ) = ε₀(σ) χ_ℓ(σ)^{k−1}`
  let F : GQ → (PadicAlgCl ℓ)ˣ := fun σ => eps0 ιC ιL χ σ * ZInQ.Contrib.HodgeSplit.G0Galois.cycQ ℓ σ ^ (k - 1)
  have hFc : Continuous F := (eps0_continuous ιC ιL χ).mul ((continuous_cycQ ℓ).zpow _)
  have hFmul : ∀ σ τ, F (σ * τ) = F σ * F τ := by
    intro σ τ
    simp only [F, map_mul, mul_zpow]
    ac_rfl
  -- `F(Frob_𝔭) = χ(p) p^{k−1}` through `ιL ∘ ιC⁻¹`
  have hFfrob : ∀ p, p.Prime → ¬ p ∣ N * ℓ → ∀ β : Qbar, ιC β = χ (p : ZMod N) * (p : ℂ) ^ (k - 1) →
      ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
      ((F τ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = ιL β := by
    intro p hp hpNl β hβ v τ hv hτ
    have hpN : ¬ p ∣ N := fun h => hpNl (Dvd.dvd.mul_right h ℓ)
    have hpl : p ≠ ℓ := fun h => hpNl (h ▸ Dvd.intro_left N rfl)
    obtain ⟨γ, hγ, hε⟩ := eps0_arithFrob ιC ιL χ hp hpN hv hτ
    have hβγ : β = γ * (p : Qbar) ^ (k - 1) := by
      apply ιC.toRingHom.injective
      change ιC β = ιC (γ * (p : Qbar) ^ (k - 1))
      rw [hβ, map_mul, map_zpow₀, map_natCast ιC, hγ]
    simp only [F, Units.val_mul]
    rw [hε, Units.val_zpow_eq_zpow_val, cycQ_arithFrob hp hpl hv hτ, hβγ, map_mul, map_zpow₀,
      map_natCast]
  by_cases hns : ∃ σ₀, NonScalar (ρ.mat σ₀)
  · -- Case 1: `ρ` has a non-scalar value; `det ρ = F`, and `ρ` itself works.
    obtain ⟨σ₀, hσ₀⟩ := hns
    let detU : GQ →* (PadicAlgCl ℓ)ˣ := Matrix.GeneralLinearGroup.det.comp ρ.toHom
    have hdetU : ∀ σ, ((detU σ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = (ρ.mat σ).det := fun σ => rfl
    have hdetc : Continuous detU := by
      rw [Units.continuous_iff]
      refine ⟨(Units.continuous_val.comp ρ.continuous_toHom).matrix_det, ?_⟩
      have : (fun σ => (((detU σ)⁻¹ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ)) =
          fun σ => (((ρ.toHom σ)⁻¹ : GL (Fin 2) (PadicAlgCl ℓ)) : Matrix (Fin 2) (Fin 2) _).det := by
        funext σ; rfl
      rw [this]
      exact (Units.continuous_coe_inv.comp ρ.continuous_toHom).matrix_det
    let W : Set GQ := {σ | NonScalar (ρ.mat σ)}
    have hWo : IsOpen W := by
      have hm := continuous_mat ρ
      exact (isOpen_ne_fun (hm.matrix_elem 0 1) continuous_const).union
        ((isOpen_ne_fun (hm.matrix_elem 1 0) continuous_const).union
          (isOpen_ne_fun (hm.matrix_elem 0 0) (hm.matrix_elem 1 1)))
    have hW : ∀ σ ∈ W, detU σ = F σ := by
      refine eq_on_open_of_eq_on_arithFrob (N * ℓ).primeFactors detU F hdetc hFc W hWo ?_
      intro p hp hpS v τ hv hτ hτW
      have hpNl : ¬ p ∣ N * ℓ := fun h => hpS (Nat.mem_primeFactors.mpr ⟨hp, h, hNl⟩)
      obtain ⟨-, α, β, -, hβ, hfr⟩ := hρ p hp hpNl
      have hcp := charpoly_of_aeval_nonScalar hτW (hfr v τ hv hτ)
      apply Units.ext
      rw [hdetU, hFfrob p hp hpNl β hβ v τ hv hτ, ← ZInQ.Contrib.HodgeSplit.det_of_charpoly _ _ _ hcp]
    have hall : ∀ σ, detU σ = F σ := by
      intro σ
      by_cases hσ : σ ∈ W
      · exact hW σ hσ
      · have h1 : σ * σ₀ ∈ W := by
          change NonScalar (ρ.mat (σ * σ₀))
          rw [mat_mul]
          exact nonScalar_mul hσ (by rw [← hdetU]; exact (detU σ).ne_zero) hσ₀
        have h2 := hW _ h1
        rw [map_mul, hFmul, hW σ₀ hσ₀] at h2
        exact mul_right_cancel h2
    refine ⟨ρ, fun p hp hpNl => ?_⟩
    obtain ⟨hu, α, β, hα, hβ, hfr⟩ := hρ p hp hpNl
    refine ⟨hu, α, β, hα, hβ, fun v τ hv hτ => ?_⟩
    have hd : (ρ.mat τ).det = ιL β := by
      rw [← hdetU, hall τ, hFfrob p hp hpNl β hβ v τ hv hτ]
    refine charpoly_of_aeval_det (hfr v τ hv hτ) hd ?_
    rw [← hd, ← hdetU]
    exact (detU τ).ne_zero
  · -- Case 2: every `ρ(σ)` is scalar; `ρ' = diag(ψ₀, F ψ₀⁻¹)`.
    push_neg at hns
    have hsc : ∀ σ, ¬ NonScalar (ρ.mat σ) := hns
    let ψ₀ := psi0 ρ hsc
    let ψ₁ := psi1 (eps0 ιC ιL χ) (ZInQ.Contrib.HodgeSplit.G0Galois.cycQ ℓ) ψ₀ k
    have hψ₁ : ∀ σ, ψ₁ σ = F σ * (ψ₀ σ)⁻¹ := fun σ => rfl
    have hψ₁c : Continuous ψ₁ :=
      ((eps0_continuous ιC ιL χ).mul ((continuous_cycQ ℓ).zpow _)).mul
        (continuous_psi0 ρ hsc).inv
    let ρ' : GaloisRep ℓ 2 := ⟨diagHom ψ₀ ψ₁, diagHom_continuous ψ₀ ψ₁ (continuous_psi0 ρ hsc) hψ₁c⟩
    have hρ'mat : ∀ σ, ρ'.mat σ = !![(ψ₀ σ : PadicAlgCl ℓ), 0; 0, (ψ₁ σ : PadicAlgCl ℓ)] :=
      fun σ => rfl
    refine ⟨ρ', fun p hp hpNl => ?_⟩
    have hpN : ¬ p ∣ N := fun h => hpNl (Dvd.dvd.mul_right h ℓ)
    have hpl : p ≠ ℓ := fun h => hpNl (h ▸ Dvd.intro_left N rfl)
    obtain ⟨hu, α, β, hα, hβ, hfr⟩ := hρ p hp hpNl
    refine ⟨fun v hv σ hσ => ?_, α, β, hα, hβ, fun v τ hv hτ => ?_⟩
    · -- unramified
      have h1 := hu v hv σ hσ
      have h0 : ψ₀ (σ : GQ) = 1 := by
        apply Units.ext
        change ρ.mat (σ : GQ) 0 0 = 1
        simp [GaloisRep.mat, h1]
      have h1' : ψ₁ (σ : GQ) = 1 := by
        rw [hψ₁, h0]
        simp only [F, eps0_inertia ιC ιL χ hp hpN hv hσ, cycQ_inertia hp hpl hv hσ, one_zpow,
          mul_one, inv_one]
      apply Units.ext
      change !![(ψ₀ _ : PadicAlgCl ℓ), 0; 0, (ψ₁ _ : PadicAlgCl ℓ)] = 1
      rw [Matrix.one_fin_two, h0, h1']
      simp
    · -- characteristic polynomial at Frobenius
      have hroot := root_of_aeval_scalar (hsc τ) (hfr v τ hv hτ)
      have hc0 : (ψ₀ τ : PadicAlgCl ℓ) ≠ 0 := (ψ₀ τ).ne_zero
      have hc : (ψ₀ τ : PadicAlgCl ℓ) = ρ.mat τ 0 0 := rfl
      have hd : (ψ₁ τ : PadicAlgCl ℓ) = ιL β * (ψ₀ τ : PadicAlgCl ℓ)⁻¹ := by
        rw [hψ₁, Units.val_mul, hFfrob p hp hpNl β hβ v τ hv hτ, Units.val_inv_eq_inv_val]
      rw [charpoly_fin_two, hρ'mat]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const,
        mul_zero, sub_zero]
      rw [hd]
      rw [← hc] at hroot
      have e1 : (ψ₀ τ : PadicAlgCl ℓ) + ιL β * (ψ₀ τ : PadicAlgCl ℓ)⁻¹ = ιL α := by
        field_simp
        linear_combination hroot
      have e2 : (ψ₀ τ : PadicAlgCl ℓ) * (ιL β * (ψ₀ τ : PadicAlgCl ℓ)⁻¹) = ιL β := by
        field_simp
      rw [e1, e2]

end Main

/-- **`DSThm965` from the disjunctive leaf.** -/
theorem dsThm965_of_weak (hW : DSThm965Weak) : ZInQ.Contrib.HodgeSplit.DSThm965 :=
  dsThm965_of_weakAeval (dsThm965WeakAeval_of_weak hW)

end DS965Weak
