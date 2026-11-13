/-! ## g8-local: `LocalDataS` (WildTateTrivial, BetaUpperC, BetaTameC, the field `F`) proved from
three smaller named Props

Task g8-local (2026-11-13). g8-object's `LocalDataS p L A ℓ β` (part_split.lean) asks, at every
prime `p`, for a finite Galois `F ⊆ ℚ̄_p` with `e(F/ℚ_p) ≤ (DG₀)!` (`p ≤ D`) resp. `p ∤ e(F/ℚ_p)`
(`p > D`), `F ⊇ j(L)`, `WildTateTrivial p L A ℓ F`, and `BetaUpperC` resp. `BetaTameC` on G7Data's
`β`. This part proves it, for every G7 datum with `[L:ℚ] ≤ D`, from
* `RaynaudNF` (R6, Raynaud's criterion, at a place of a number field; published),
* `TorsionFieldBound` (glue: the field of `A[m]`, `m ∈ {3,5}`, has degree `≤ [L:ℚ]·G₀`, and
  `G_L` acts on `A[m]` through a group whose order has prime factors `≤ 31`; T5 + open
  stabilizers),
* `Char2UpperBreak` (T16(b) + D3 + Herbrand at `p = 2`; published),
and the closed lemmas of `ZInQKernel/Contrib/G8Local/`. At odd `p` the `β`-clauses are proved
outright (no Prop), and so is the existence of `F`.
-/

noncomputable section

namespace G8Local

open PkgI4 (GQ GQp decomp)
open LadicCond
open G0ModField G8Object
open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent.B2
open ZInQ.Contrib.G8Local

/-! ### §1. The three named Props -/

/-- **Leaf R6 (Raynaud's criterion, Galois form) at a place of a number field.** SGA 7 I,
Exp. IX, Prop. 4.7 (Raynaud: `A[m] ⊆ A(K)`, `m ≥ 3` prime to the residue characteristic, gives
semistable reduction), with the direction "semistable ⇒ `(σ−1)² = 0` on `T_ℓ`" of Prop. 3.5
(numbers UNVERIFIED; Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995), Thm 3.5, is N5's
citation). PUBLISHED THEOREM, transported: this is `PkgI2.RaynaudCriterion` for the number field
`K = L(A[m]) ⊆ L̄` (the fixed field of the `σ_L` fixing `A(L̄)[m]`, over which `A[m]` is rational by
Galois descent) and its DVR at the place `w` of `L̄` induced by `ℚ̄ → ℚ̄_p` (`decomp`) and
`resQ L`: an element `σ_L ∈ G_K` with `resQ L σ_L ∈ decomp(I_p)` lies in the inertia group of `w`
in `G_K`. -/
def RaynaudNF : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L) (p : ℕ) [Fact p.Prime] (m : ℕ),
    3 ≤ m → ¬ p ∣ m →
    ∀ σ : GQp p, σ ∈ inertiaSet → ∀ σL : Field.absoluteGaloisGroup L,
      @G0Galois.resQ L _ (numberField_of_fd L) σL = decomp p σ →
      (∀ x : A.Pt (AlgebraicClosure L), x ^ m = 1 →
        A.galAct (L := AlgebraicClosure L) σL x = x) →
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ n : ℕ, ∀ x : A.Pt (AlgebraicClosure L), x ^ (ℓ ^ n) = 1 →
        A.galAct (L := AlgebraicClosure L) σL (A.galAct (L := AlgebraicClosure L) σL x) *
          (A.galAct (L := AlgebraicClosure L) σL x)⁻¹ *
          (A.galAct (L := AlgebraicClosure L) σL x)⁻¹ * x = 1

/-- **Glue: the field of `A[m]` (`m = 3, 5`) for a QM model `A/L` (N5 L814-815: "This extension
has degree at most `DG₀`").** There is `M ⊆ ℚ̄`, `L ≤ M`, `[M:ℚ] ≤ [L:ℚ]·G₀`, such that
`σ_L` fixes `A(L̄)[m]` whenever `resQ L σ_L` fixes `M` (`M` is the fixed field of the image of the
stabilizer; only "fixers of `M` fix `A[m]`" is asserted), and `G_L` acts on `A[m]` through a
finite group of exponent dividing `k`, whose prime factors are `≤ 31`. Why true: `A` is an abelian surface (a QM model), so `A(L̄)[m] ≅ (ℤ/m)⁴` (T5,
Mumford §4) and `G_L` acts through a subgroup of `GL₄(ℤ/m)`, of order dividing
`|GL₄(𝔽₃)| = 2⁹·3⁶·5·13` resp. `|GL₄(𝔽₅)| = 2¹¹·3²·5⁶·13·31 = G₀`; the stabilizer is open
(glue-rho-cont, `PkgI3.RhoCont.exists_openSubgroup_galAct_eq`, with `A[m]` finite) and of index
`≤ G₀`, and Galois theory gives `[M:ℚ] = [L:ℚ]·[G_L : Stab]`. GLUE (T5 + open stabilizers +
infinite Galois theory), not a published theorem. -/
def TorsionFieldBound : Prop :=
  ∀ (P : LeafQM.AV.QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L), IsQMModel L A P → ∀ m : ℕ, m = 3 ∨ m = 5 →
    (∃ M : IF, FiniteDimensional ℚ M ∧ L ≤ M ∧
      Module.finrank ℚ M ≤ Module.finrank ℚ L * ZInQ.heightG0 ∧
      ∀ σL : Field.absoluteGaloisGroup L,
        @G0Galois.resQ L _ (numberField_of_fd L) σL ∈ M.fixingSubgroup →
          ∀ x : A.Pt (AlgebraicClosure L), x ^ m = 1 →
            A.galAct (L := AlgebraicClosure L) σL x = x) ∧
    ∃ k : ℕ, 0 < k ∧ (∀ q : ℕ, q.Prime → q ∣ k → q ≤ 31) ∧
      ∀ σL : Field.absoluteGaloisGroup L, ∀ x : A.Pt (AlgebraicClosure L), x ^ m = 1 →
        A.galAct (L := AlgebraicClosure L) (σL ^ k) x = x

/-- **Local class field theory at `p = 2` with the upper numbering theorem, D3 and Herbrand
(N5 L835-847).** Let `F ⊆ ℚ̄_2` be finite Galois with `e(F/ℚ_2) ≤ e` and `e(F/ℚ_2) ≤ a!`, and
`ψ : G_{ℚ_2} → ℂ^×` locally constant, multiplicative on `G_F`, with `ψ⁴ = 1` on `G_F ∩ I_2`. Then
`ψ` is trivial on `G_{ℚ_2}^t ∩ G_F` for `t > max(4a², 3e)`. Proof (published ingredients): by
local reciprocity `ψ|_{G_F}` is a character of `F^×` killing `(U_F)⁴ ⊇ (U_F^{e+1})⁴ = U_F^{3e+1}`
(D3, `GlueConductor.fourth_pow_mem`), so its conductor is `≤ 3e + 1` and by the upper numbering
theorem with Hasse–Arf (T16(b), `PkgI6.LocalReciprocityUpper`; Serre, *Corps locaux* XV §2,
V §7) `ψ` is trivial on `G_F^v`, `v > 3e`; Herbrand's `G_{ℚ_2}^t ∩ G_F = G_F^{ψ_{F/ℚ_2}(t)}` with
`ψ_{F/ℚ_2}(t) ≥ t` (Serre IV §3) moves this to the absolute numbering; `4a²` bounds the last upper
break of `F/ℚ_2` (D1). PUBLISHED THEOREMS (T16(b), Herbrand) + proved D3; the transport of
T16(b) to `LadicCond`'s norm-defined filtrations is part of the statement. -/
def Char2UpperBreak : Prop :=
  ∀ (F : Fld 2), IsFinGal F → ∀ ψ : GQp 2 → ℂˣ, IsLocallyConstant ψ →
    (∀ x ∈ fixSet F, ∀ y ∈ fixSet F, ψ (x * y) = ψ x * ψ y) →
    (∀ x ∈ fixSet F ∩ inertiaSet, ψ x ^ 4 = 1) →
    ∀ (e a : ℕ), 1 ≤ a → ramCard F 0 ≤ e → ramCard F 0 ≤ a.factorial →
    ∀ t : ℝ, 4 * (a : ℝ) ^ 2 < t → 3 * (e : ℝ) < t → ∀ σ ∈ upperAbs 2 t ∩ fixSet F, ψ σ = 1

/-! ### §2. Arithmetic of the data -/

theorem T_primes (u : ℚ) : ∀ p ∈ G0ModField.T u, p.Prime := by
  obtain ⟨hS, -, -⟩ := admissible_S_mul
  intro p hp
  rcases Finset.mem_union.mp hp with h | h
  · exact hS p h
  · exact Nat.prime_of_mem_primeFactors h

/-- `N = chiLevel T₋` is `N'` or `p N'` with `p ∤ N'`, for odd primes `p`. -/
theorem chiLevel_split {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (Tm : Finset ℕ)
    (hTm : ∀ q ∈ Tm, q.Prime) :
    ∃ N', 0 < N' ∧ ¬ p ∣ N' ∧
      (GlueDescent.chiLevel Tm = N' ∨ GlueDescent.chiLevel Tm = p * N') := by
  have hlev_pos : ∀ q ∈ Tm, 0 < GlueDescent.lev q := by
    intro q hq
    unfold GlueDescent.lev
    split_ifs
    · omega
    · exact (hTm q hq).pos
  have hpos : ∀ S ⊆ Tm, 0 < ∏ q ∈ S, GlueDescent.lev q :=
    fun S hS => Finset.prod_pos fun q hq => hlev_pos q (hS hq)
  have hndvd : ∀ S ⊆ Tm, p ∉ S → ¬ p ∣ ∏ q ∈ S, GlueDescent.lev q := by
    intro S hS hpS hdvd
    obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).exists_mem_finset_dvd hdvd
    unfold GlueDescent.lev at hpq
    split_ifs at hpq with hq2
    · have h4 : p ∣ 2 ^ 2 := by simpa using hpq
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4))
    · have := (Nat.prime_dvd_prime_iff_eq hp (hTm q (hS hq))).mp hpq
      exact hpS (this ▸ hq)
  by_cases hpT : p ∈ Tm
  · refine ⟨∏ q ∈ Tm.erase p, GlueDescent.lev q, hpos _ (Finset.erase_subset _ _),
      hndvd _ (Finset.erase_subset _ _) (Finset.notMem_erase p Tm), Or.inr ?_⟩
    have hlevp : GlueDescent.lev p = p := by simp [GlueDescent.lev, hp2]
    unfold GlueDescent.chiLevel
    rw [← Finset.mul_prod_erase Tm _ hpT, hlevp]
  · exact ⟨GlueDescent.chiLevel Tm, hpos Tm le_rfl, hndvd Tm le_rfl hpT, Or.inl rfl⟩

/-- `N = chiLevel T₋` is `N'` or `4 N'` with `N'` odd. -/
theorem chiLevel_split_two (Tm : Finset ℕ) (hTm : ∀ q ∈ Tm, q.Prime) :
    ∃ N', 0 < N' ∧ ¬ 2 ∣ N' ∧
      (GlueDescent.chiLevel Tm = N' ∨ GlueDescent.chiLevel Tm = 4 * N') := by
  have hlev_pos : ∀ q ∈ Tm, 0 < GlueDescent.lev q := by
    intro q hq
    unfold GlueDescent.lev
    split_ifs
    · omega
    · exact (hTm q hq).pos
  have hpos : ∀ S ⊆ Tm, 0 < ∏ q ∈ S, GlueDescent.lev q :=
    fun S hS => Finset.prod_pos fun q hq => hlev_pos q (hS hq)
  have hndvd : ∀ S ⊆ Tm, 2 ∉ S → ¬ 2 ∣ ∏ q ∈ S, GlueDescent.lev q := by
    intro S hS hpS hdvd
    obtain ⟨q, hq, hpq⟩ := (Nat.prime_two.prime).exists_mem_finset_dvd hdvd
    unfold GlueDescent.lev at hpq
    split_ifs at hpq with hq2
    · exact hpS (hq2 ▸ hq)
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (hTm q (hS hq))).mp hpq
      exact hq2 this.symm
  by_cases hpT : 2 ∈ Tm
  · refine ⟨∏ q ∈ Tm.erase 2, GlueDescent.lev q, hpos _ (Finset.erase_subset _ _),
      hndvd _ (Finset.erase_subset _ _) (Finset.notMem_erase 2 Tm), Or.inr ?_⟩
    have hlevp : GlueDescent.lev 2 = 4 := by simp [GlueDescent.lev]
    unfold GlueDescent.chiLevel
    rw [← Finset.mul_prod_erase Tm _ hpT, hlevp]
  · exact ⟨GlueDescent.chiLevel Tm, hpos Tm le_rfl, hndvd Tm le_rfl hpT, Or.inl rfl⟩

theorem heightD_gt : 31 < ZInQ.heightD := by
  have h1 : 324 ≤ ZInQ.heightF0 := by unfold ZInQ.heightF0; exact Nat.self_le_factorial 324
  have h2 : 1 ≤ 3 ^ (256 * ZInQ.heightF0 ^ 4) := Nat.one_le_pow _ _ (by norm_num)
  have : ZInQ.heightF0 ≤ ZInQ.heightD := by
    unfold ZInQ.heightD; exact Nat.le_mul_of_pos_right _ h2
  omega

theorem U0_nonneg : 0 ≤ G0ModNewform.U0 := by unfold G0ModNewform.U0; positivity

theorem heightG0_pos : 0 < ZInQ.heightG0 := by unfold ZInQ.heightG0; norm_num

/-- `β` is multiplicative on `G_L` (`ε` is inflated from `Gal(L/ℚ)` and normalized). -/
theorem beta_mul {L : IF} {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} (hD : DescentDatum L A ε)
    {β : GQ → ℂˣ} (hβe : ∀ x y, β x * β y = ε x y * β (x * y)) :
    ∀ x ∈ L.fixingSubgroup, ∀ y ∈ L.fixingSubgroup, β (x * y) = β x * β y := by
  obtain ⟨-, hinf, h11, -⟩ := hD
  intro x hx y hy
  have hε : ε x y = 1 := by
    rw [← h11]
    apply hinf
    · intro z hz
      exact ((IntermediateField.mem_fixingSubgroup_iff L x).mp hx z hz).trans rfl
    · intro z hz
      exact ((IntermediateField.mem_fixingSubgroup_iff L y).mp hy z hz).trans rfl
  rw [hβe, hε, one_mul]

/-! ### §3. The `β`-clauses at odd `p` (proved outright) -/

/-- **`β(decomp σ) = 1` on `G_F ∩ P_p` at odd `p`** (N5 L832-835, L850-851), for any `F ⊇ j(L)`. -/
theorem beta_wild_eq_one {u : ℚ} {P : LeafQM.AV.QML3 Qbar} {L : IF} [FiniteDimensional ℚ L]
    {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {β : GQ → ℂˣ} {L' : IF} {hLL' : L ≤ L'} (h : G7Data u P L A ε N χ β L' hLL')
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {F : Fld p} (hL : ContainsL p L F) :
    BetaTameC p β F := by
  obtain ⟨-, hD, -, -, ⟨Tm, hTm, hN⟩, hβl, hβs, hβe, -⟩ := h
  intro σ hσ
  have hσL := decomp_mem_fixing p L hL hσ.1
  obtain ⟨j, hj, -⟩ := hL
  have hTmP : ∀ q ∈ Tm, q.Prime := fun q hq => T_primes u q (hTm hq)
  obtain ⟨N', hN'0, hpN', hNN'⟩ := chiLevel_split (Fact.out) hp2 Tm hTmP
  rw [← hN] at hNN'
  have hsq : β (decomp p σ) ^ 2 = 1 := by
    rw [hβs]; exact galChar_decomp_eq_one hj hσ.2 χ hN'0 hpN' hNN'
  exact cochain_eq_one_of_wild hj hp2 L β hβl (beta_mul hD hβe) hσ.2 hσL hsq

/-- **`BetaUpperC` at odd `p`** (N5 L832-835): positive upper groups are wild
(`G15Ram.upperWild`). -/
theorem betaUpper_odd {u : ℚ} {P : LeafQM.AV.QML3 Qbar} {L : IF} [FiniteDimensional ℚ L]
    {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {β : GQ → ℂˣ} {L' : IF} {hLL' : L ≤ L'} (h : G7Data u P L A ε N χ β L' hLL')
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {F : Fld p} (hL : ContainsL p L F) :
    BetaUpperC p β F G0ModNewform.U0 := by
  intro t ht σ hσ
  have hw : σ ∈ wildSet := G15Ram.upperWild (p := p) t (lt_of_le_of_lt U0_nonneg ht) hσ.1
  exact beta_wild_eq_one h p hp2 hL σ ⟨hσ.2, hw⟩

/-! ### §4. The `β`-clause at `p = 2` (from `Char2UpperBreak`) -/

/-- Inertia fixes roots of unity of order prime to `p`. -/
theorem fix_of_inertia_rootOfUnity {p : ℕ} [Fact p.Prime] {σ : GQp p} (hσ : σ ∈ inertiaSet)
    {n : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n) {x : Kbar p} (hx : x ^ n = 1) : σ x = x := by
  have hxn : ‖x‖ = 1 := by
    have h := congrArg norm hx
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp h
  have hx0 : x ≠ 0 := by
    rintro rfl; rw [norm_zero] at hxn; exact zero_ne_one hxn
  set w := σ x * x⁻¹ with hw
  have hwj : ∀ j : ℕ, w ^ j = σ (x ^ j) * (x ^ j)⁻¹ := by
    intro j; rw [hw, mul_pow, inv_pow, map_pow]
  have hwn : w ^ n = 1 := by rw [hwj, hx, map_one, inv_one, mul_one]
  have hlt : ∀ j : ℕ, ‖w ^ j - 1‖ < 1 := by
    intro j
    have hxj : x ^ j ≠ 0 := pow_ne_zero j hx0
    have hnj : ‖x ^ j‖ = 1 := by rw [norm_pow, hxn, one_pow]
    have h := hσ (x ^ j) hnj.le
    have he : w ^ j - 1 = (σ (x ^ j) - x ^ j) * (x ^ j)⁻¹ := by
      rw [hwj]; field_simp
    rw [he, norm_mul, norm_inv, hnj, inv_one, mul_one]
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

/-- `σ²` fixes the fourth roots of unity, for any `σ ∈ G_{ℚ_p}`. -/
theorem sq_fix_fourth {p : ℕ} [Fact p.Prime] (σ : GQp p) {y : Kbar p} (hy : y ^ 4 = 1) :
    σ (σ y) = y := by
  have hy2 : σ (y ^ 2) = y ^ 2 := by
    have : (y ^ 2 - 1) * (y ^ 2 + 1) = 0 := by linear_combination hy
    rcases mul_eq_zero.mp this with h | h
    · rw [sub_eq_zero.mp h, map_one]
    · rw [eq_neg_of_add_eq_zero_left h, map_neg, map_one]
  have h1 : (σ y - y) * (σ y + y) = 0 := by
    have : (σ y) ^ 2 = y ^ 2 := by rw [← map_pow, hy2]
    linear_combination this
  rcases mul_eq_zero.mp h1 with h | h
  · rw [sub_eq_zero.mp h, sub_eq_zero.mp h]
  · have hσy : σ y = -y := eq_neg_of_add_eq_zero_left h
    rw [hσy, map_neg, hσy, neg_neg]

open GlueDescent.B2Q in
/-- `cyc N g = 1` when `g` fixes every `N`-th root of unity. -/
theorem cyc_eq_one_of_fix {N : ℕ} [NeZero N] (g : GQ)
    (h : ∀ t : AlgebraicClosure ℚ, t ^ N = 1 → g t = t) : cyc N g = 1 := by
  by_cases h1 : N = 1
  · subst h1; exact Subsingleton.elim _ _
  haveI : Fact (1 < N) := ⟨by have := NeZero.ne N; omega⟩
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  apply Units.ext
  rw [Units.val_one]
  have hfix : ∀ t ∈ rootsOfUnity N (AlgebraicClosure ℚ),
      (toRingAut g) (t : AlgebraicClosure ℚ) = (t : AlgebraicClosure ℚ) ^ (1 : ZMod N).val := by
    intro t ht
    rw [ZMod.val_one, pow_one]
    apply h
    have := (mem_rootsOfUnity N t).mp ht
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  exact (modularCyclotomicCharacter.unique (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N) _ hfix).symm

/-- **`χ(decomp σ)² = 1` on `I_2`** (`χ` has `2`-part of level dividing `4`). -/
theorem galChar_sq_inertia_two {jQ : AlgebraicClosure ℚ →+* Kbar 2}
    (hj : ∀ (σ : GQp 2) (x : AlgebraicClosure ℚ), jQ (decomp 2 σ x) = σ (jQ x))
    {σ : GQp 2} (hσ : σ ∈ inertiaSet) {N N' : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hN' : 0 < N') (h2N' : ¬ 2 ∣ N') (hN : N = N' ∨ N = 4 * N') :
    (GlueDescent.B2Q.galChar χ (decomp 2 σ)) ^ 2 = 1 := by
  have hfixN' : ∀ x : Kbar 2, x ^ N' = 1 → σ x = x :=
    fun x hx => fix_of_inertia_rootOfUnity hσ hN' h2N' hx
  have hfix : ∀ x : Kbar 2, x ^ N = 1 → σ (σ x) = x := by
    intro x hx
    rcases hN with rfl | rfl
    · rw [hfixN' x hx, hfixN' x hx]
    · have hx0 : x ≠ 0 := by
        rintro rfl; rw [zero_pow (by omega)] at hx; exact zero_ne_one hx
      have ha : σ (x ^ 4) = x ^ 4 := hfixN' _ (by rw [← pow_mul, hx])
      have hb : σ (σ (x ^ N')) = x ^ N' := sq_fix_fourth σ (by rw [← pow_mul, mul_comm, hx])
      have hcop : Nat.Coprime 4 N' := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2N')
      have hbez : (4 : ℤ) * Nat.gcdA 4 N' + (N' : ℤ) * Nat.gcdB 4 N' = 1 := by
        have := Nat.gcd_eq_gcd_ab 4 N'
        rw [hcop] at this
        exact_mod_cast this.symm
      have hxe : x = (x ^ 4) ^ (Nat.gcdA 4 N') * (x ^ N') ^ (Nat.gcdB 4 N') := by
        rw [← zpow_natCast, ← zpow_natCast (a := x) N', ← zpow_mul, ← zpow_mul,
          ← zpow_add₀ hx0]
        push_cast
        rw [hbez, zpow_one]
      rw [hxe, map_mul, map_zpow₀, map_zpow₀, map_mul, map_zpow₀, map_zpow₀, ha, ha, hb]
  have hg : GlueDescent.B2Q.cyc N ((decomp 2 σ) ^ 2) = 1 := by
    apply cyc_eq_one_of_fix
    intro t ht
    apply jQ.injective
    rw [pow_two, AlgEquiv.mul_apply, hj, hj]
    exact hfix _ (by rw [← map_pow, ht, map_one])
  rw [← map_pow]
  show χ.toUnitHom (GlueDescent.B2Q.cyc N (decomp 2 σ ^ 2)) = 1
  rw [hg, map_one]

theorem decomp_continuous (p : ℕ) [Fact p.Prime] : Continuous (decomp p) :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous

theorem fourD_le_U0 : 4 * (ZInQ.heightD : ℝ) ^ 2 ≤ G0ModNewform.U0 := by
  unfold G0ModNewform.U0
  have h1 : (ZInQ.heightD : ℝ) ≤ ((ZInQ.heightD * ZInQ.heightG0 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_right _ heightG0_pos
  have h0 : (0 : ℝ) ≤ ZInQ.heightD := Nat.cast_nonneg _
  nlinarith

theorem threeD_le_U0 : 3 * (ZInQ.heightD : ℝ) ≤ G0ModNewform.U0 := by
  have h := fourD_le_U0
  have h1 : (1 : ℝ) ≤ ZInQ.heightD := by
    have := heightD_gt
    exact_mod_cast (by omega : 1 ≤ ZInQ.heightD)
  nlinarith

/-- `BetaUpperC` passes to larger fields. -/
theorem betaUpper_mono {p : ℕ} [Fact p.Prime] {β : GQ → ℂˣ} {F F' : Fld p} {U : ℝ}
    (hFF : ∀ x ∈ F, x ∈ F') (h : BetaUpperC p β F U) : BetaUpperC p β F' U :=
  fun t ht σ hσ => h t ht σ ⟨hσ.1, fun x hx => hσ.2 x (hFF x hx)⟩

/-- **`BetaUpperC` at `p = 2` on a field `F₀ ⊇ j(L)` with `e(F₀/ℚ_2) ≤ D`** (N5 L835-847), from
`Char2UpperBreak` with `e = a = D` (`max(4D², 3D) ≤ U₀`). -/
theorem betaUpper_two (hC : Char2UpperBreak) {u : ℚ} {P : LeafQM.AV.QML3 Qbar} {L : IF}
    [FiniteDimensional ℚ L] {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} {hLL' : L ≤ L'}
    (h : G7Data u P L A ε N χ β L' hLL') {F₀ : Fld 2} (hF₀ : IsFinGal F₀)
    (hcont : ContainsL 2 L F₀) (he : ramCard F₀ 0 ≤ ZInQ.heightD) :
    BetaUpperC 2 β F₀ G0ModNewform.U0 := by
  obtain ⟨-, hD, -, -, ⟨Tm, hTm, hN⟩, hβl, hβs, hβe, -⟩ := h
  obtain ⟨N', hN'0, h2N', hNN'⟩ := chiLevel_split_two Tm (fun q hq => T_primes u q (hTm hq))
  rw [← hN] at hNN'
  have hD1 : 1 ≤ ZInQ.heightD := by have := heightD_gt; omega
  obtain ⟨j, hj, -⟩ := hcont
  intro t ht σ hσ
  refine hC _ hF₀ (fun σ => β (decomp 2 σ)) (hβl.comp_continuous (decomp_continuous 2)) ?_ ?_
    ZInQ.heightD ZInQ.heightD hD1 he (he.trans (Nat.self_le_factorial _)) t
    (lt_of_le_of_lt fourD_le_U0 ht) (lt_of_le_of_lt threeD_le_U0 ht) σ hσ
  · intro x hx y hy
    simp only [map_mul]
    exact beta_mul hD hβe _ (decomp_mem_fixing 2 L hcont hx) _ (decomp_mem_fixing 2 L hcont hy)
  · intro x hx
    show β (decomp 2 x) ^ (2 * 2) = 1
    rw [pow_mul, hβs]
    exact galChar_sq_inertia_two hj hx.2 χ hN'0 h2N' hNN'

/-! ### §5. `WildTateTrivial` from `RaynaudNF` -/

/-- **Wild inertia moves a point by a `p`-power period**: for wild `σ` and `σ_L` over `decomp σ`,
some `σ_L^{p^a}` fixes a given `x ∈ A(L̄)` (`exists_fix_field` + `decomp_ppow_mem`). -/
theorem exists_ppow_fix_point {L : IF} [FiniteDimensional ℚ L] (A : PkgI3.AbVar L)
    (p : ℕ) [Fact p.Prime] {σ : GQp p} (hσ : σ ∈ wildSet) (σL : Field.absoluteGaloisGroup L)
    (hres : @G0Galois.resQ L _ (numberField_of_fd L) σL = decomp p σ)
    (x : A.Pt (AlgebraicClosure L)) :
    ∃ a : ℕ, A.galAct (L := AlgebraicClosure L) (σL ^ (p ^ a)) x = x := by
  letI := numberField_of_fd L
  obtain ⟨E, hEfd, hE⟩ := exists_fix_field A x (G0Galois.qEmbRing L)
    (algClosure_surjective L _) (fun τ => G0Galois.resQ L τ) (G0Galois.resQ_spec L)
  haveI := hEfd
  obtain ⟨jQ, hjQ⟩ := ZInQ.Contrib.G8Local.decomp_spec p
  obtain ⟨a, ha⟩ := decomp_ppow_mem hjQ hσ E
  refine ⟨a, hE _ ?_⟩
  show G0Galois.resQ L (σL ^ (p ^ a)) ∈ E.fixingSubgroup
  rw [map_pow, hres]
  exact ha

/-- **A wild `σ` fixes a point that a prime-to-`p` power of it fixes** (periods `p^a` and `k`
with `p ∤ k`). -/
theorem fix_of_pow_coprime_wild {L : IF} [FiniteDimensional ℚ L] (A : PkgI3.AbVar L)
    (p : ℕ) [Fact p.Prime] {σ : GQp p} (hσ : σ ∈ wildSet) (σL : Field.absoluteGaloisGroup L)
    (hres : @G0Galois.resQ L _ (numberField_of_fd L) σL = decomp p σ)
    (x : A.Pt (AlgebraicClosure L)) {k : ℕ} (hpk : ¬ p ∣ k)
    (hk : A.galAct (L := AlgebraicClosure L) (σL ^ k) x = x) :
    A.galAct (L := AlgebraicClosure L) σL x = x := by
  obtain ⟨a, ha⟩ := exists_ppow_fix_point A p hσ σL hres x
  have h1 : Function.IsPeriodicPt (A.galAct (L := AlgebraicClosure L) σL) (p ^ a) x := by
    show (A.galAct (L := AlgebraicClosure L) σL)^[p ^ a] x = x
    rw [← galAct_pow_apply]; exact ha
  have h2 : Function.IsPeriodicPt (A.galAct (L := AlgebraicClosure L) σL) k x := by
    show (A.galAct (L := AlgebraicClosure L) σL)^[k] x = x
    rw [← galAct_pow_apply]; exact hk
  have hcop : Nat.Coprime (p ^ a) k :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpk)
  have := h1.gcd h2
  rw [hcop] at this
  exact this

/-- **`WildTateTrivial` (R6 + D2 transported to `LadicCond`'s `G_{ℚ_p}`).** If every
`σ_L` over `decomp σ`, `σ ∈ G_F ∩ P_p`, fixes `A[m]` (`m ≥ 3`, `p ∤ m`), then wild inertia of
`G_F` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)` for `ℓ ≠ p`: Raynaud gives `(σ_L − 1)² = 0` on `A[ℓⁿ]`,
wild inertia gives `σ_L^{p^a} x = x`, and D2's algebra concludes. -/
theorem wildTate_of (hR : RaynaudNF) {L : IF} [FiniteDimensional ℚ L] (A : PkgI3.AbVar L)
    (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (m : ℕ) (hm3 : 3 ≤ m)
    (hpm : ¬ p ∣ m) (F : Fld p)
    (hfixm : ∀ σ ∈ fixSet F ∩ wildSet, ∀ σL : Field.absoluteGaloisGroup L,
      @G0Galois.resQ L _ (numberField_of_fd L) σL = decomp p σ →
      ∀ x : A.Pt (AlgebraicClosure L), x ^ m = 1 → A.galAct (L := AlgebraicClosure L) σL x = x) :
    WildTateTrivial p L A ℓ F := by
  letI := numberField_of_fd L
  intro σ hσ σL hres
  show GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ) σL = 1
  apply repBaseChange_galRep_eq_one_of_fix
  intro n x hx
  have hU := hR L A p m hm3 hpm σ (wildSet_subset_inertiaSet hσ.2) σL hres
    (hfixm σ hσ σL hres) ℓ Fact.out hℓp n x hx
  obtain ⟨a, hit⟩ := exists_ppow_fix_point A p hσ.2 σL hres x
  have hcop : Nat.Coprime (p ^ a) (ℓ ^ n) :=
    Nat.Coprime.pow a n ((Nat.coprime_primes Fact.out Fact.out).mpr hℓp.symm)
  exact fixed_of_unipSq_of_pow A σL x ℓ n p a hcop hx hU hit

/-! ### §6. `LocalDataS` -/

/-- **`LocalDataS p L A ℓ β` for a G7 datum with `[L:ℚ] ≤ D`** (proved from the three Props).
`p ≤ D`: `F` = the normal closure of `ℚ_p(jQ M)`, `M` the field of `A[m]`. `p > D`:
`F = F₀`, the normal closure of `ℚ_p(jQ L)` (`[F₀:ℚ_p] ≤ [L:ℚ] ≤ D`). -/
theorem localDataS_of (hR : RaynaudNF) (hT : TorsionFieldBound) (hC : Char2UpperBreak)
    {u : ℚ} {P : LeafQM.AV.QML3 Qbar} {L : IF} [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {β : GQ → ℂˣ} {L' : IF} {hLL' : L ≤ L'} (h : G7Data u P L A ε N χ β L' hLL')
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓp : ℓ ≠ p) (m : ℕ) (hm : m = 3 ∨ m = 5) (hpm : ¬ p ∣ m) : LocalDataS p L A ℓ β := by
  letI := numberField_of_fd L
  have hm3 : 3 ≤ m := by rcases hm with rfl | rfl <;> norm_num
  obtain ⟨jQ, hjQ⟩ := ZInQ.Contrib.G8Local.decomp_spec p
  obtain ⟨⟨M, hMfd, hLM, hMdeg, hM⟩, k, hk0, hkq, hk⟩ := hT P L A h.1 m hm
  haveI := hMfd
  obtain ⟨F₀, hF₀G, hLF₀, -, hF₀gal⟩ := exists_galois_closure jQ L
  obtain ⟨hF₀deg, hF₀le⟩ := hF₀gal inferInstance
  have hcont₀ : ContainsL p L F₀ := ⟨jQ, hjQ, hLF₀⟩
  have he₀ : ramCard F₀ 0 ≤ ZInQ.heightD :=
    ((ramCard_le_finrank F₀ hF₀G).trans hF₀deg).trans hLD
  refine ⟨fun hpD => ?_, fun hDp => ?_⟩
  · obtain ⟨F, hFG, hMF, hFe, -⟩ := exists_galois_closure jQ M
    have hcont : ContainsL p L F := ⟨jQ, hjQ, fun x hx => hMF x (hLM hx)⟩
    refine ⟨F, hFG, ?_, hcont, ?_, ?_⟩
    · exact hFe.trans (Nat.factorial_le (hMdeg.trans (Nat.mul_le_mul_right _ hLD)))
    · refine wildTate_of hR A p ℓ hℓp m hm3 hpm F fun σ hσ σL hres => hM σL ?_
      rw [hres, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact (decomp_apply_eq_iff hjQ σ x).mpr (hσ.1 _ (hMF x hx))
    · by_cases hp2 : p = 2
      · subst hp2
        exact betaUpper_mono (hF₀le F fun x hx => hMF x (hLM hx))
          (betaUpper_two hC h hF₀G hcont₀ he₀)
      · exact betaUpper_odd h p hp2 hcont
  · have hDp' : ZInQ.heightD < p := by exact_mod_cast hDp
    have hp31 : 31 < p := lt_trans heightD_gt hDp'
    have hpk : ¬ p ∣ k := fun hd => by
      have := hkq p Fact.out hd
      omega
    refine ⟨F₀, hF₀G, ?_, hcont₀, ?_, ?_⟩
    · intro hdvd
      obtain ⟨ϖ, hϖ⟩ := exists_isUnif hF₀G.1
      have h0 := ramCard_ne_zero hF₀G hϖ 0
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd
      omega
    · exact wildTate_of hR A p ℓ hℓp m hm3 hpm _ fun σ hσ σL hres x hx =>
        fix_of_pow_coprime_wild A p hσ.2 σL hres x hpk (hk σL x hx)
    · have hp2 : p ≠ 2 := by omega
      exact beta_wild_eq_one h p hp2 hcont₀

/-- **G15's local data on G7Data's objects, at every prime** (`ℓ = 5` at `p ≠ 5`, `ℓ = 3` at
`p = 5`; `m = 3`, or `m = 5` at `p = 3`): the two `LocalDataS` conjuncts of `LinkedTateObjS`. -/
theorem localDataS_all (hR : RaynaudNF) (hT : TorsionFieldBound) (hC : Char2UpperBreak)
    {u : ℚ} {P : LeafQM.AV.QML3 Qbar} {L : IF} [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {β : GQ → ℂˣ} {L' : IF} {hLL' : L ≤ L'} (h : G7Data u P L A ε N χ β L' hLL')
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) :
    (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalDataS p ⟨hp⟩ L _ A 5 _ β) ∧
      LocalDataS 5 L A 3 β := by
  refine ⟨fun p hp hp5 => ?_, ?_⟩
  · haveI : Fact p.Prime := ⟨hp⟩
    by_cases hp3 : p = 3
    · subst hp3
      exact localDataS_of hR hT hC h hLD 3 5 (by norm_num) 5 (Or.inr rfl) (by norm_num)
    · refine localDataS_of hR hT hC h hLD p 5 (Ne.symm hp5) 3 (Or.inl rfl) ?_
      intro hd
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd)
  · exact localDataS_of hR hT hC h hLD 5 3 (by norm_num) 3 (Or.inl rfl) (by norm_num)

end G8Local

end
