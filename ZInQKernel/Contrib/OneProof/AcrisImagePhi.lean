import ZInQKernel.Contrib.OneProof.AcrisImageBasic

/-! # The completed finite divided powers as limits of restricted series

`FontaineComparison.CrystallineCompletion p w` is the `p`-adic completion of
`D = W(R)[w^n/n! : n ≥ 1]`. A restricted series `f = Σ a_n X^n` (`a_n → 0` `p`-adically) gives
the element `phi w hf`, the limit of the partial sums `Σ_{n<N} a_n w^n/n! ∈ D`, and every
element of the completion arises this way (`phi_surjective`; Fontaine, Astérisque 223 (1994),
Exposé II, §4.1.2, p. 83, uses the same description).
-/

noncomputable section

namespace HDec.PkgI4.AcrisImage

open BergerBst FontaineSt BmaxOne PowerSeries Ideal
open PanBergerSplit (Ainf AinfP theta)
open FontaineComparison (finiteDividedPowers CrystallineCompletion)

variable {p : ℕ} [Fact p.Prime] (w : Ainf p)

/-- The ideal `(p)` of `W(R)[w^n/n!]`, along which `CrystallineCompletion` completes. -/
abbrev pIdeal : Ideal (finiteDividedPowers p w) :=
  Ideal.span ({(p : finiteDividedPowers p w)} : Set (finiteDividedPowers p w))

theorem mem_pIdeal_pow_iff (k : ℕ) (d : finiteDividedPowers p w) :
    d ∈ pIdeal w ^ k ↔ ∃ e ∈ finiteDividedPowers p w, (d : AinfP p) = (p : AinfP p) ^ k * e := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a, a.2, ?_⟩
    push_cast
    ring
  · rintro ⟨e, he, hde⟩
    refine ⟨⟨e, he⟩, Subtype.ext ?_⟩
    push_cast
    rw [hde]
    ring

/-- In a commutative ring, `I ^ k • ⊤ = I ^ k`. -/
private theorem mem_pow_smul_top_iff {R : Type*} [CommRing R] (I : Ideal R) (k : ℕ) (r : R) :
    r ∈ (I ^ k • ⊤ : Submodule R R) ↔ r ∈ I ^ k := by
  rw [smul_eq_mul, Ideal.mul_top]

/-- Partial sums as elements of `W(R)[w^n/n!]`. -/
def psumD (f : (Ainf p)⟦X⟧) (N : ℕ) : finiteDividedPowers p w :=
  ⟨psum w f N, psum_mem w f N⟩

/-- A finite sum `Σ_{n ∈ s} a_n γ_n` whose coefficients are all divisible by `p^k` lies
in `p^k D`. -/
private theorem exists_sum_eq_pow_mul_mem {f : (Ainf p)⟦X⟧} {k : ℕ} (s : Finset ℕ)
    (h : ∀ n ∈ s, (p : Ainf p) ^ k ∣ PowerSeries.coeff n f) :
    ∃ e ∈ finiteDividedPowers p w,
      ∑ n ∈ s, algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff n f) * gam w n =
        (p : AinfP p) ^ k * e := by
  obtain ⟨g, hg⟩ := exists_psum_eq_pow_mul w s h
  exact ⟨_, sum_gam_mem w s fun n => PowerSeries.coeff n g, hg⟩

/-- If the coefficients `a_n` with `N ≤ n < M` are divisible by `p^k`, the partial sums at `N`
and at `M` agree modulo `p^k D`. -/
private theorem psumD_sub_psumD_mem {f : (Ainf p)⟦X⟧} {k N M : ℕ} (hNM : N ≤ M)
    (h : ∀ n, N ≤ n → n < M → (p : Ainf p) ^ k ∣ PowerSeries.coeff n f) :
    psumD w f M - psumD w f N ∈ pIdeal w ^ k := by
  rw [mem_pIdeal_pow_iff]
  obtain ⟨e, he, hse⟩ := exists_sum_eq_pow_mul_mem w (Finset.Ico N M) (f := f) (k := k)
    fun n hn => h n (Finset.mem_Ico.mp hn).1 (Finset.mem_Ico.mp hn).2
  refine ⟨e, he, ?_⟩
  show psum w f M - psum w f N = _
  rw [psum_sub_psum w f hNM, hse]

variable {w}

/-- A modulus of `p`-adic decay of a restricted series: `p^k ∣ a_n` for `n ≥ bnd hf k`. -/
def bnd {f : (Ainf p)⟦X⟧} (hf : f ∈ restricted p) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1), Classical.choose (hf j)

theorem bnd_spec {f : (Ainf p)⟦X⟧} (hf : f ∈ restricted p) (k : ℕ) :
    ∀ n, bnd hf k ≤ n → (p : Ainf p) ^ k ∣ PowerSeries.coeff n f := by
  intro n hn
  have h1 : Classical.choose (hf k) ≤ bnd hf k :=
    Finset.single_le_sum (f := fun j => Classical.choose (hf j)) (fun _ _ => Nat.zero_le _)
      (Finset.self_mem_range_succ k)
  exact Classical.choose_spec (hf k) n (h1.trans hn)

theorem bnd_mono {f : (Ainf p)⟦X⟧} (hf : f ∈ restricted p) : Monotone (bnd hf) := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))

variable (w)

/-- Beyond `bnd hf k`, the partial sums of a restricted series are constant modulo `p^k D`. -/
private theorem psumD_sub_psumD_bnd_mem {f : (Ainf p)⟦X⟧} (hf : f ∈ restricted p) {k N M : ℕ}
    (hN : bnd hf k ≤ N) (hNM : N ≤ M) : psumD w f M - psumD w f N ∈ pIdeal w ^ k :=
  psumD_sub_psumD_mem w hNM fun n hn _ => bnd_spec hf k n (hN.trans hn)

/-- The partial sums at the moduli `bnd hf k` form a `p`-adic Cauchy sequence in `D`. -/
private theorem phi_cauchy {f : (Ainf p)⟦X⟧} (hf : f ∈ restricted p) (k : ℕ) :
    psumD w f (bnd hf k) ≡ psumD w f (bnd hf (k + 1))
      [SMOD (pIdeal w ^ k • ⊤ :
        Submodule (finiteDividedPowers p w) (finiteDividedPowers p w))] := by
  rw [SModEq.sub_mem, mem_pow_smul_top_iff, ← neg_mem_iff, neg_sub]
  exact psumD_sub_psumD_bnd_mem w hf le_rfl (bnd_mono hf (Nat.le_succ k))

/-- The element of the completion defined by a restricted series. -/
def phi {f : (Ainf p)⟦X⟧} (hf : f ∈ restricted p) : CrystallineCompletion p w :=
  AdicCompletion.mk (pIdeal w) (finiteDividedPowers p w)
    (AdicCompletion.AdicCauchySequence.mk (pIdeal w) (finiteDividedPowers p w)
      (fun k => psumD w f (bnd hf k)) (phi_cauchy w hf))

theorem evalₐ_phi {f : (Ainf p)⟦X⟧} (hf : f ∈ restricted p) (k N : ℕ) (hN : bnd hf k ≤ N) :
    AdicCompletion.evalₐ (pIdeal w) k (phi w hf) = Ideal.Quotient.mk _ (psumD w f N) := by
  rw [phi, AdicCompletion.evalₐ_mk]
  exact (Ideal.Quotient.eq.mpr (psumD_sub_psumD_bnd_mem w hf le_rfl hN)).symm

/-- Two restricted series give the same element if their partial sums agree modulo every
`p^k D` from some point on. -/
theorem phi_eq_of_forall {f g : (Ainf p)⟦X⟧} (hf : f ∈ restricted p) (hg : g ∈ restricted p)
    (h : ∀ k, ∃ N₀, ∀ N, N₀ ≤ N → ∃ e ∈ finiteDividedPowers p w,
      psum w f N - psum w g N = (p : AinfP p) ^ k * e) :
    phi w hf = phi w hg := by
  refine AdicCompletion.ext_evalₐ fun k => ?_
  obtain ⟨N₀, hN₀⟩ := h k
  rw [evalₐ_phi w hf k (max N₀ (max (bnd hf k) (bnd hg k)))
      (le_max_of_le_right (le_max_left _ _)),
    evalₐ_phi w hg k (max N₀ (max (bnd hf k) (bnd hg k)))
      (le_max_of_le_right (le_max_right _ _)),
    Ideal.Quotient.eq, mem_pIdeal_pow_iff]
  exact hN₀ _ (le_max_left _ _)

theorem phi_zero : phi w (Subring.zero_mem (restricted p)) = 0 := by
  refine AdicCompletion.ext_evalₐ fun k => ?_
  rw [evalₐ_phi w (Subring.zero_mem (restricted p)) k _ le_rfl, map_zero,
    Ideal.Quotient.eq_zero_iff_mem]
  have h0 : psumD w 0 (bnd (Subring.zero_mem (restricted p)) k) = 0 :=
    Subtype.ext (psum_zero_left w _)
  rw [h0]
  exact zero_mem _

/-- **Every element of the completion is the limit of a restricted series.** -/
theorem phi_surjective (x : CrystallineCompletion p w) :
    ∃ (f : (Ainf p)⟦X⟧) (hf : f ∈ restricted p), phi w hf = x := by
  classical
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective (pIdeal w) (finiteDividedPowers p w) x
  -- the consecutive differences `s (j+1) - s j = p^j e_j`
  have hdiff : ∀ j, ∃ e ∈ finiteDividedPowers p w,
      ((s.val (j + 1) : finiteDividedPowers p w) : AinfP p) - (s.val j : AinfP p) =
        (p : AinfP p) ^ j * e := by
    intro j
    have h1 := SModEq.sub_mem.mp (s.property (Nat.le_succ j))
    rw [mem_pow_smul_top_iff, ← neg_mem_iff, neg_sub] at h1
    exact (mem_pIdeal_pow_iff w j _).mp h1
  choose e he hse using hdiff
  -- finite expansions of `s 0` and of the `e_j`
  obtain ⟨F₀, N₀, hF₀, hs₀⟩ := exists_psum w (s.val 0).2
  choose G M hG hGe using fun j => exists_psum w (he j)
  -- the coefficients of the approximations `s K`
  let c : ℕ → ℕ → Ainf p := fun n K =>
    PowerSeries.coeff n F₀ + ∑ j ∈ Finset.range K, (p : Ainf p) ^ j * PowerSeries.coeff n (G j)
  have hc_succ : ∀ n K, c n (K + 1) = c n K + (p : Ainf p) ^ K * PowerSeries.coeff n (G K) := by
    intro n K
    simp only [c, Finset.sum_range_succ, add_assoc]
  have hcauchy : ∀ n, AdicCompletion.IsAdicCauchy (Ideal.span {(p : Ainf p)}) (Ainf p)
      (fun K => c n K) := by
    intro n
    refine (AdicCompletion.isAdicCauchy_iff _ _ _).mpr fun K => ?_
    rw [SModEq.sub_mem, mem_pow_smul_top_iff, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, hc_succ]
    exact ⟨-PowerSeries.coeff n (G K), by ring⟩
  choose a ha using fun n =>
    IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {(p : Ainf p)}) (Ainf p))
      (hcauchy n)
  have ha' : ∀ n K, (p : Ainf p) ^ K ∣ c n K - a n := by
    intro n K
    have h1 := SModEq.sub_mem.mp (ha n K)
    rwa [mem_pow_smul_top_iff, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  -- a common bound for the supports of `s 0, e_0, …, e_{K-1}`
  let B : ℕ → ℕ := fun K => N₀ + ∑ j ∈ Finset.range K, M j
  have hN₀B : ∀ K, N₀ ≤ B K := fun K => Nat.le_add_right _ _
  have hMB : ∀ K j, j < K → M j ≤ B K := by
    intro K j hj
    have h1 : M j ≤ ∑ i ∈ Finset.range K, M i :=
      Finset.single_le_sum (f := M) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
    simp only [B]
    omega
  have hcB : ∀ K n, B K ≤ n → c n K = 0 := by
    intro K n hn
    simp only [c]
    rw [hF₀ n ((hN₀B K).trans hn), zero_add]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [hG j n ((hMB K j (Finset.mem_range.mp hj)).trans hn), mul_zero]
  -- `s K = s 0 + Σ_{j<K} p^j e_j`
  have hTel : ∀ K, (s.val K : AinfP p) =
      s.val 0 + ∑ j ∈ Finset.range K, (p : AinfP p) ^ j * e j := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ← ih, ← hse K]
      ring
  have hA : ∀ K L, psum w (PowerSeries.mk fun n => c n K) L =
      psum w F₀ L + ∑ j ∈ Finset.range K, (p : AinfP p) ^ j * psum w (G j) L := by
    intro K L
    simp only [psum, c, PowerSeries.coeff_mk, map_add, map_sum, map_mul, map_pow, map_natCast,
      add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  have hBpsum : ∀ K L, B K ≤ L → psum w (PowerSeries.mk fun n => c n K) L = s.val K := by
    intro K L hL
    rw [hA, hTel K, psum_eq_of_le w ((hN₀B K).trans hL) hF₀, ← hs₀]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [psum_eq_of_le w ((hMB K j (Finset.mem_range.mp hj)).trans hL) (hG j), ← hGe j]
  -- the limit series is restricted
  have hf : PowerSeries.mk a ∈ restricted p := by
    intro k
    refine ⟨B k, fun n hn => ?_⟩
    have h1 := ha' n k
    rw [hcB k n hn, zero_sub, dvd_neg] at h1
    simpa only [PowerSeries.coeff_mk] using h1
  refine ⟨PowerSeries.mk a, hf, AdicCompletion.ext_evalₐ fun k => ?_⟩
  rw [evalₐ_phi w hf k (max (bnd hf k) (B k)) (le_max_left _ _), AdicCompletion.evalₐ_mk,
    Ideal.Quotient.eq, mem_pIdeal_pow_iff]
  have h1 : ((psumD w (PowerSeries.mk a) (max (bnd hf k) (B k)) - s.val k :
      finiteDividedPowers p w) : AinfP p) =
      psum w (PowerSeries.mk a - PowerSeries.mk fun n => c n k) (max (bnd hf k) (B k)) := by
    rw [psum_sub, hBpsum k _ (le_max_right _ _)]
    rfl
  rw [h1]
  refine exists_sum_eq_pow_mul_mem w _ fun n _ => ?_
  rw [map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_mk, ← dvd_neg, neg_sub]
  exact ha' n k

end HDec.PkgI4.AcrisImage
