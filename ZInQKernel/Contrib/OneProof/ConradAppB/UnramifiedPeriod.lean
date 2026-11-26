import ZInQKernel.Contrib.OneProof.ConradAppB.Defs
import ZInQKernel.Contrib.UnramRoots.Main

/-!
# Hilbert 90 over the completed maximal unramified extension

For a finite extension `L/ℚ_p` inside `ℚ̄_p` and a continuous character `μ : G_{ℚ_p} → L^×` trivial
on inertia, there is `u ≠ 0` in `ℂ_p` with `σ u = μ(σ) u` for every `σ ∈ G_L`.

Proof. Let `φ ∈ G_L` be a Frobenius lift (`φ x = x^q` on the roots of every `X^{q^N} − X`,
`q = |k_L|`) and `a = μ(φ)`, so `|a| = 1` by continuity. Write `T_N` for the roots of
`X^{q^N} − X` and `V_N` for their `L`-span.

* Discreteness: an element of `V_N` of absolute value `< 1` has absolute value at most `|ϖ_L|`.
  With `ζ` a primitive `(q^N − 1)`-th root of unity and `S` the set of its Frobenius conjugates
  `ζ^{q^i}`, the polynomial `∏_{s ∈ S} (X − s)` is fixed by `G_L`, hence has coefficients in `L`,
  so `V_N` is the span of `1, ζ, …, ζ^{n−1}` (`n = |S|`); reducing a relation
  `|∑ d_j ζ^j| < 1` with integral `d_j`, one of them `1`, gives a nonzero polynomial of degree
  `< n` over the residue field vanishing at the `n` distinct residues of `S`.
* Successive approximation (Lang's theorem for `𝔾_m` over the residue field, in additive form):
  `u_{k+1} = u_k + ϖ^{k+1} s_k` with `s_k ∈ T_{N_k}` a Teichmüller approximation of a root of
  `Y^q − aY + (φ u_k − a u_k)/ϖ^{k+1}`; then `|φ u_k − a u_k| ≤ |ϖ|^{k+1}` and the `u_k` converge
  in `ℂ_p` to `v` with `|v| = 1`, `φ v = a v`, fixed by the inertia subgroup of `G_L`.
* Every `σ ∈ G_L` is `φ^j τ g` with `τ` in inertia and `g` in an open subgroup fixing an
  approximation of `v` on which `μ` is close to `1`; hence `σ v = μ(σ) v`.

References: S. Lang, *Algebraic groups over finite fields*, Amer. J. Math. 78 (1956) (Lang's
theorem, whose proof for `𝔾_m` is the approximation step); S. Sen, *Continuous cohomology and
p-adic Galois representations*, Invent. Math. 62 (1980) (context: the weight-zero case).
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.SenWeightZero

open ZInQ.Contrib.CloudB3W11TateTrace
open scoped TensorProduct


namespace UnramifiedPeriodAux


open PkgI4 (GQp)
open LadicCond Polynomial UnramRootsTask

variable {p : ℕ} [Fact p.Prime]

/-- Distinct `M`-th roots of unity with `p ∤ M` are at distance at least `1`. -/
theorem one_le_norm_sub_of_pow_eq_one {M : ℕ} (hM : 0 < M) (hpM : ¬ p ∣ M) {x y : Kbar p}
    (hx : x ^ M = 1) (hy : y ^ M = 1) (hxy : x ≠ y) : 1 ≤ ‖x - y‖ := by
  by_contra h
  have h' : ‖x - y‖ < 1 := lt_of_not_ge h
  have hyn : ‖y‖ = 1 := by
    have h := congrArg norm hy
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg y) hM.ne').mp h
  have hy0 : y ≠ 0 := by rintro rfl; simp at hyn
  have hu : (x * y⁻¹) ^ M = 1 := by rw [mul_pow, inv_pow, hx, hy, inv_one, mul_one]
  have hu1 : ‖x * y⁻¹ - 1‖ < 1 := by
    have : x * y⁻¹ - 1 = (x - y) * y⁻¹ := by field_simp
    rw [this, norm_mul, norm_inv, hyn, inv_one, mul_one]
    exact h'
  have := eq_one_of_pow_eq_one hM hpM hu hu1
  exact hxy ((mul_inv_eq_one₀ hy0).mp this)

/-- **Residue-field root count.** If `∑_{j<n} d_j X^j` has integral coefficients, one of them equal
to `1`, and it is small at every point of a finite set `S` of integral points that are pairwise at
distance `1`, then `|S| < n` (its reduction is a nonzero polynomial of degree `< n` vanishing on
the residues of `S`, which are distinct). -/
theorem card_lt_of_norm_sum_lt_one {n : ℕ} (d : Fin n → Kbar p) (hd : ∀ j, ‖d j‖ ≤ 1)
    (j0 : Fin n) (hj0 : d j0 = 1) (S : Finset (Kbar p)) (hS : ∀ s ∈ S, ‖s‖ ≤ 1)
    (hsep : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → 1 ≤ ‖s - s'‖)
    (hroot : ∀ s ∈ S, ‖∑ j, d j * s ^ (j : ℕ)‖ < 1) : S.card < n := by
  classical
  set r := IsLocalRing.residue (OO p) with hr
  let dd : Fin n → OO p := fun j => ⟨d j, mem_OO.mpr (hd j)⟩
  let Q : (IsLocalRing.ResidueField (OO p))[X] := ∑ j, C (r (dd j)) * X ^ (j : ℕ)
  have hQdeg : Q.natDegree ≤ n - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro j _
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_X_pow]
    omega
  have hQ0 : Q ≠ 0 := by
    intro h
    have hc := congrArg (fun P => P.coeff (j0 : ℕ)) h
    simp only [Q, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hc
    rw [Finset.sum_eq_single j0] at hc
    · have h1 : dd j0 = 1 := Subtype.ext (by simp [dd, hj0])
      rw [ite_eq_left rfl, mul_one, h1, map_one] at hc
      exact one_ne_zero hc
    · intro b _ hb
      rw [ite_eq_right (fun h => hb (Fin.ext h.symm)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ j0) h
  let f : Kbar p → IsLocalRing.ResidueField (OO p) := fun s =>
    if h : ‖s‖ ≤ 1 then r ⟨s, mem_OO.mpr h⟩ else 0
  have hmaps : Set.MapsTo f S Q.roots.toFinset := by
    intro s hs
    rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hQ0, IsRoot.def]
    have hs1 := hS s hs
    simp only [f, dite_eq_left hs1]
    have e1 : Q.eval (r ⟨s, mem_OO.mpr hs1⟩) =
        r (∑ j, dd j * (⟨s, mem_OO.mpr hs1⟩ : OO p) ^ (j : ℕ)) := by
      simp only [Q, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, map_sum, map_mul,
        map_pow]
    rw [e1, residue_eq_zero_iff]
    have e2 : ((∑ j, dd j * (⟨s, mem_OO.mpr hs1⟩ : OO p) ^ (j : ℕ) : OO p) : Kbar p) =
        ∑ j, d j * s ^ (j : ℕ) := by
      change (OO p).subtype (∑ j, dd j * (⟨s, mem_OO.mpr hs1⟩ : OO p) ^ (j : ℕ)) = _
      rw [map_sum]
      rfl
    rw [e2]
    exact hroot s hs
  have hinj : Set.InjOn f S := by
    intro s hs s' hs' hss'
    by_contra hne
    have h1 := hsep s hs s' hs' hne
    simp only [f, dite_eq_left (hS s hs), dite_eq_left (hS s' hs')] at hss'
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff] at hss'
    exact absurd h1 (not_le.mpr hss')
  have h1 := Finset.card_le_card_of_injOn f hmaps hinj
  have h2 := Multiset.toFinset_card_le Q.roots
  have h3 := card_roots' Q
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) j0.isLt
  omega

/-- `x^{q^m}` depends only on `m mod N` when `x^{q^N} = x`. -/
theorem pow_pow_mod {q N : ℕ} {x : Kbar p} (hx : x ^ q ^ N = x) (m : ℕ) :
    x ^ q ^ m = x ^ q ^ (m % N) := by
  have h : ∀ j : ℕ, x ^ (q ^ N) ^ j = x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_mul, ih, hx]
  rw [show q ^ m = (q ^ N) ^ (m / N) * q ^ (m % N) by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod], pow_mul, h]

/-- Powers of a Frobenius lift on the roots of `X^{q^N} − X`. -/
theorem frob_pow_apply {L : Fld p} {q : ℕ} {φ : GQp p} (hD : FrobData L q φ) {N : ℕ}
    (hN : 0 < N) (i : ℕ) {x : Kbar p} (hx : x ^ q ^ N = x) : (φ ^ i) x = x ^ q ^ i := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    have hxq : (x ^ q) ^ q ^ N = x ^ q := by rw [← pow_mul, mul_comm, pow_mul, hx]
    rw [pow_succ', AlgEquiv.mul_apply, ih hx, map_pow, hD.2.2.2.1 N x hN hx, ← pow_mul,
      ← pow_succ']

/-- **Discreteness over the unramified extensions.** An element of the `L`-span of the roots of
`X^{q^N} − X` of absolute value `< 1` has absolute value at most that of a uniformizer of `L`.
(With `ζ` a primitive `(q^N − 1)`-th root of unity, the span is that of `1, ζ, …, ζ^{n−1}`, `n` the
number of Frobenius conjugates of `ζ`, and `|∑ c_j ζ^j| = max |c_j|` by reduction.) -/
theorem norm_le_of_mem_span {L : Fld p} {q : ℕ} {φ : GQp p}
    (hD : FrobData L q φ) {ϖ : Kbar p} (hϖ : IsUnif L ϖ) {N : ℕ} (hN : 0 < N) {w : Kbar p}
    (hw : w ∈ Submodule.span L {x : Kbar p | x ^ q ^ N = x}) (hw1 : ‖w‖ < 1) : ‖w‖ ≤ ‖ϖ‖ := by
  classical
  obtain ⟨hq1, ⟨e, hqe⟩, hφL, _, hS5⟩ := hD
  have : IsGalois ℚ_[p] (Kbar p) := IsAlgClosure.isGalois ℚ_[p] (Kbar p)
  set M := q ^ N - 1 with hMdef
  have hqN : 1 < q ^ N := Nat.one_lt_pow hN.ne' hq1
  have hM : 0 < M := by omega
  have hpq : p ∣ q := by
    rcases e with _ | e
    · rw [pow_zero] at hqe; omega
    · rw [hqe]; exact dvd_pow_self p (Nat.succ_ne_zero e)
  have hpM : ¬ p ∣ M := by
    intro h
    have h1 : p ∣ q ^ N := dvd_pow hpq hN.ne'
    have h2 : p ∣ q ^ N - M := Nat.dvd_sub h1 h
    rw [show q ^ N - M = 1 by omega] at h2
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h2)
  have : NeZero (M : Kbar p) := ⟨by exact_mod_cast hM.ne'⟩
  have : NeZero M := ⟨hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (Kbar p) M
  have hζN : ζ ^ q ^ N = ζ := by
    rw [show q ^ N = M + 1 by omega, pow_succ, hζ.pow_eq_one, one_mul]
  set S : Finset (Kbar p) := (Finset.range N).image (fun i => ζ ^ q ^ i) with hSdef
  have hTN : ∀ i, (ζ ^ q ^ i) ^ q ^ N = ζ ^ q ^ i := by
    intro i; rw [← pow_mul, mul_comm, pow_mul, hζN]
  have hSM : ∀ s ∈ S, s ^ M = 1 := by
    intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  -- `G_L` permutes `S`
  have hσS : ∀ σ ∈ L.fixingSubgroup, S.image σ = S := by
    intro σ hσ
    have hσ' : σ ∈ fixSet L := fun x hx => (IntermediateField.mem_fixingSubgroup_iff L σ).1 hσ x hx
    obtain ⟨k, hk⟩ := hS5 σ hσ' N hN
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
      rw [hk _ (hTN i), ← pow_mul, ← pow_add, pow_pow_mod hζN (i + k)]
      exact Finset.mem_image.2 ⟨(i + k) % N, Finset.mem_range.2 (Nat.mod_lt _ hN), rfl⟩
    · rw [Finset.card_image_of_injective _ σ.injective]
  -- the polynomial `∏_{s ∈ S} (X − s)` has coefficients in `L`
  set P : (Kbar p)[X] := ∏ s ∈ S, (X - C s) with hPdef
  have hPcoeff : ∀ j, P.coeff j ∈ L := by
    intro j
    rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hmap : P.map (σ : Kbar p →+* Kbar p) = P := by
      rw [hPdef, Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C]
      conv_rhs => rw [← hσS σ hσ]
      rw [Finset.prod_image (fun x _ y _ h => σ.injective h)]
      rfl
    have := congrArg (fun Q => Q.coeff j) hmap
    simpa [coeff_map] using this
  have hPmonic : P.Monic := monic_prod_of_monic _ _ (fun s _ => monic_X_sub_C s)
  set n := S.card with hn
  have hPdeg : P.natDegree = n := natDegree_finsetProd_X_sub_C_eq_card S (fun s => s)
  have hζS : ζ ∈ S := Finset.mem_image.2 ⟨0, Finset.mem_range.2 hN, by simp⟩
  have hn0 : 0 < n := Finset.card_pos.2 ⟨ζ, hζS⟩
  have hPζ : P.eval ζ = 0 := by
    rw [hPdef, eval_prod]
    exact Finset.prod_eq_zero hζS (by simp)
  -- the span of `1, ζ, …, ζ^{n-1}`
  set V : Submodule L (Kbar p) := Submodule.span L (Set.range (fun j : Fin n => ζ ^ (j : ℕ)))
    with hVdef
  have hgen : ∀ j : ℕ, j < n → ζ ^ j ∈ V := fun j hj => Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
  have hsmul : ∀ (c : L) (x : Kbar p), c • x = (c : Kbar p) * x := fun c x => rfl
  have hζn : ζ ^ n ∈ V := by
    have h := hPζ
    have hcn : P.coeff n = 1 := hPdeg ▸ hPmonic.coeff_natDegree
    rw [eval_eq_sum_range, hPdeg, Finset.sum_range_succ, hcn, one_mul] at h
    have h2 : ζ ^ n = -∑ i ∈ Finset.range n, P.coeff i * ζ ^ i := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    rw [h2]
    refine V.neg_mem (V.sum_mem fun i hi => ?_)
    have : P.coeff i * ζ ^ i = (⟨P.coeff i, hPcoeff i⟩ : L) • ζ ^ i := rfl
    rw [this]
    exact V.smul_mem _ (hgen i (Finset.mem_range.1 hi))
  have hmulζ : ∀ v ∈ V, ζ * v ∈ V := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [← pow_succ']
      rcases Nat.lt_or_ge ((j : ℕ) + 1) n with h | h
      · exact hgen _ h
      · have : (j : ℕ) + 1 = n := le_antisymm j.isLt h
        rw [this]; exact hζn
    | zero => rw [mul_zero]; exact V.zero_mem
    | add x y _ _ hx hy => rw [mul_add]; exact V.add_mem hx hy
    | smul c x _ hx =>
      rw [hsmul, mul_left_comm, ← hsmul]
      exact V.smul_mem c hx
  have hpow : ∀ m : ℕ, ζ ^ m ∈ V := by
    intro m
    induction m with
    | zero => exact hgen 0 hn0
    | succ m ih => rw [pow_succ']; exact hmulζ _ ih
  have hTV : {x : Kbar p | x ^ q ^ N = x} ⊆ V := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact V.zero_mem
    have hxM : x ^ M = 1 := by
      have : x ^ M * x = 1 * x := by
        rw [← pow_succ, show M + 1 = q ^ N by omega, one_mul]; exact hx
      exact mul_right_cancel₀ hx0 this
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hxM
    exact hpow i
  have hwV : w ∈ V := Submodule.span_le.2 hTV hw
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 hwV
  have hζ1 : ∀ j : ℕ, ‖ζ ^ j‖ = 1 := by
    intro j
    rw [norm_pow]
    have h := congrArg norm hζ.pow_eq_one
    rw [norm_pow, norm_one] at h
    rw [(pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hM.ne').mp h, one_pow]
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ
    (fun j => ‖((c j : L) : Kbar p)‖) ⟨⟨0, hn0⟩, Finset.mem_univ _⟩
  have hwle : ‖w‖ ≤ ‖((c j0 : L) : Kbar p)‖ := by
    rw [← hc]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    intro j _
    rw [hsmul, norm_mul, hζ1, mul_one]
    exact hj0 j (Finset.mem_univ _)
  rcases eq_or_ne ((c j0 : L) : Kbar p) 0 with h0 | h0
  · rw [h0, norm_zero] at hwle; exact hwle.trans (norm_nonneg _)
  have hge : ‖((c j0 : L) : Kbar p)‖ ≤ ‖w‖ := by
    by_contra hlt
    have hlt' : ‖w‖ < ‖((c j0 : L) : Kbar p)‖ := lt_of_not_ge hlt
    set d : Fin n → Kbar p := fun j => ((c j : L) : Kbar p) / ((c j0 : L) : Kbar p) with hd
    have hdL : ∀ j, d j ∈ L := fun j => L.div_mem (c j).2 (c j0).2
    have hd1 : ∀ j, ‖d j‖ ≤ 1 := by
      intro j
      rw [hd, norm_div, div_le_one (norm_pos_iff.2 h0)]
      exact hj0 j (Finset.mem_univ _)
    have hdj0 : d j0 = 1 := div_self h0
    have hsum : ∑ j, d j * ζ ^ (j : ℕ) = w / ((c j0 : L) : Kbar p) := by
      rw [← hc, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hsmul, hd]
      ring
    have hroot : ∀ s ∈ S, ‖∑ j, d j * s ^ (j : ℕ)‖ < 1 := by
      intro s hs
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
      have : ∑ j, d j * (ζ ^ q ^ i) ^ (j : ℕ) = (φ ^ i) (∑ j, d j * ζ ^ (j : ℕ)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, map_pow, frob_pow_apply ⟨hq1, ⟨e, hqe⟩, hφL, ‹_›, hS5⟩ hN i hζN,
          (pow_mem_fixSet hφL i) _ (hdL j)]
      rw [this, norm_aut, hsum, norm_div, div_lt_one (norm_pos_iff.2 h0)]
      exact hlt'
    have hSn : ∀ s ∈ S, ‖s‖ ≤ 1 := by
      intro s hs
      have h := congrArg norm (hSM s hs)
      rw [norm_pow, norm_one] at h
      exact ((pow_eq_one_iff_of_nonneg (norm_nonneg s) hM.ne').mp h).le
    have hsep : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → 1 ≤ ‖s - s'‖ := fun s hs s' hs' hne =>
      one_le_norm_sub_of_pow_eq_one hM hpM (hSM s hs) (hSM s' hs') hne
    have hcard := card_lt_of_norm_sum_lt_one d hd1 j0 hdj0 S hSn hsep hroot
    exact lt_irrefl _ hcard
  have hc1 : ‖((c j0 : L) : Kbar p)‖ < 1 := lt_of_le_of_lt hge hw1
  exact hwle.trans (hϖ.2.2 _ (c j0).2 hc1)


/-! ### Successive approximation -/

theorem span_mono_dvd {L : Fld p} {q N N' : ℕ} (h : N ∣ N') :
    Submodule.span L {x : Kbar p | x ^ q ^ N = x} ≤
      Submodule.span L {x : Kbar p | x ^ q ^ N' = x} :=
  Submodule.span_mono fun _ hx => pow_pow_of_dvd hx h

theorem mul_mem_span {L : Fld p} {S : Set (Kbar p)} {x w : Kbar p} (hx : x ∈ L)
    (hw : w ∈ Submodule.span L S) : x * w ∈ Submodule.span L S :=
  Submodule.smul_mem _ (⟨x, hx⟩ : L) hw

/-- A Frobenius lift preserves the `L`-span of the roots of `X^{q^N} − X`. -/
theorem frob_mem_span {L : Fld p} {q : ℕ} {φ : GQp p} (hD : FrobData L q φ) {N : ℕ}
    (hN : 0 < N) {w : Kbar p} (hw : w ∈ Submodule.span L {x : Kbar p | x ^ q ^ N = x}) :
    φ w ∈ Submodule.span L {x : Kbar p | x ^ q ^ N = x} := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    rw [hD.2.2.2.1 N x hN hx]
    apply Submodule.subset_span
    show (x ^ q) ^ q ^ N = x ^ q
    rw [← pow_mul, mul_comm, pow_mul, hx]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have : φ (c • x) = c • φ x := by
      change φ ((c : Kbar p) * x) = (c : Kbar p) * φ x
      rw [map_mul, hD.2.2.1 _ c.2]
    rw [this]; exact Submodule.smul_mem _ c hx

/-- Inertia in `G_L` fixes the `L`-span of the roots of `X^{q^N} − X` (`p ∣ q`). -/
theorem inertia_fix_span {L : Fld p} {q : ℕ} (hq1 : 1 < q) (hpq : p ∣ q) {N : ℕ} (hN : 0 < N)
    {τ : GQp p} (hτ : τ ∈ fixSet L ∩ inertiaSet) {w : Kbar p}
    (hw : w ∈ Submodule.span L {x : Kbar p | x ^ q ^ N = x}) : τ w = w := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    exact fix_of_mem_inertiaSet_of_pow_eq_self hτ.2 (Nat.one_lt_pow hN.ne' hq1)
      (dvd_pow hpq hN.ne') hx
  | zero => exact map_zero τ
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx =>
    change τ ((c : Kbar p) * x) = (c : Kbar p) * x
    rw [map_mul, hτ.1 _ c.2, hx]

/-- Teichmüller approximation with exponent a power of `q = p^e`. -/
theorem exists_teich_close {q e : ℕ} (hqe : q = p ^ e) {y : Kbar p} (hy : ‖y‖ ≤ 1) :
    ∃ m : ℕ, 0 < m ∧ ∃ s : Kbar p, s ^ q ^ m = s ∧ ‖y - s‖ < 1 := by
  obtain ⟨m, hm, hlt⟩ := exists_pow_sub_lt_one hy
  have hM : 1 < p ^ m := Nat.one_lt_pow hm.ne' (Fact.out : p.Prime).one_lt
  obtain ⟨s, hs, hys⟩ := exists_root_close hy hM hlt
  refine ⟨m, hm, s, ?_, hys⟩
  rw [hqe, ← pow_mul, mul_comm, pow_mul]
  clear hqe
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ, pow_mul, ih, hs]

theorem norm_pow_sub_pow_le {x y : Kbar p} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤ ‖x - y‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  have h : ‖∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => by
      rw [norm_mul, norm_pow, norm_pow]
      calc ‖x‖ ^ i * ‖y‖ ^ (n - 1 - i) ≤ 1 * 1 :=
            mul_le_mul (pow_le_one₀ (norm_nonneg _) hx) (pow_le_one₀ (norm_nonneg _) hy)
              (pow_nonneg (norm_nonneg _) _) zero_le_one
        _ = 1 := one_mul 1
  calc _ ≤ 1 * ‖x - y‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = _ := one_mul _

theorem norm_unif_pos {L : Fld p} {ϖ : Kbar p} (hϖ : IsUnif L ϖ) : 0 < ‖ϖ‖ := by
  have hpL : (p : Kbar p) ∈ L := by
    rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
    exact IntermediateField.algebraMap_mem _ _
  have h1 := hϖ.2.2 _ hpL isUnif_bot.2.1
  have h2 : 0 < ‖(p : Kbar p)‖ := by
    rw [norm_p_kbar]; exact inv_pos.2 (by exact_mod_cast (Fact.out : p.Prime).pos)
  linarith

theorem norm_eq_of_norm_sub_lt {x y : Kbar p} (hx : ‖x‖ = 1) (h : ‖x - y‖ < 1) : ‖y‖ = 1 := by
  have e : y = x + -(x - y) := by ring
  have hne : ‖x‖ ≠ ‖-(x - y)‖ := by rw [norm_neg, hx]; exact h.ne'
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, hx]
  exact max_eq_left h.le

/-- **Start of the approximation:** a root `t` of some `X^{q^N} − X` with `|t^q − a t| < 1`. -/
theorem exists_base {L : Fld p} {q : ℕ} {φ : GQp p} (hD : FrobData L q φ) {ϖ : Kbar p}
    (hϖ : IsUnif L ϖ) {a : Kbar p} (haL : a ∈ L) (ha1 : ‖a‖ = 1) :
    ∃ N : ℕ, 0 < N ∧ ∃ u ∈ Submodule.span L {x : Kbar p | x ^ q ^ N = x},
      ‖u‖ = 1 ∧ ‖φ u - a * u‖ ≤ ‖ϖ‖ := by
  obtain ⟨hq1, ⟨e, hqe⟩, -, hφ, -⟩ := id hD
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq a (show 0 < q - 1 by omega)
  have hyn : ‖y‖ = 1 := by
    have h := congrArg norm hy
    rw [norm_pow, ha1] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg y) (by omega)).mp h
  obtain ⟨m, hm, s, hs, hys⟩ := exists_teich_close hqe hyn.le
  have hsn : ‖s‖ = 1 := norm_eq_of_norm_sub_lt hyn hys
  have hsm : s ∈ Submodule.span L {x : Kbar p | x ^ q ^ m = x} := Submodule.subset_span hs
  have hφs : φ s = s ^ q := hφ m s hm hs
  refine ⟨m, hm, s, hsm, hsn, ?_⟩
  have hmem : φ s - a * s ∈ Submodule.span L {x : Kbar p | x ^ q ^ m = x} :=
    Submodule.sub_mem _ (frob_mem_span hD hm hsm) (mul_mem_span haL hsm)
  refine norm_le_of_mem_span hD hϖ hm hmem ?_
  have e1 : φ s - a * s = s * (s ^ (q - 1) - y ^ (q - 1)) := by
    rw [hφs, hy, mul_sub, ← pow_succ', Nat.sub_add_cancel hq1.le, mul_comm s a]
  rw [e1, norm_mul, hsn, one_mul]
  exact lt_of_le_of_lt (norm_pow_sub_pow_le hsn.le hyn.le _) (by rw [norm_sub_rev]; exact hys)

/-- **One step of the approximation.** -/
theorem exists_step {L : Fld p} {q : ℕ} {φ : GQp p} (hD : FrobData L q φ) {ϖ : Kbar p}
    (hϖ : IsUnif L ϖ) {a : Kbar p} (haL : a ∈ L) (ha1 : ‖a‖ = 1) (k N : ℕ) (hN : 0 < N)
    (u : Kbar p) (hu : u ∈ Submodule.span L {x : Kbar p | x ^ q ^ N = x}) (hu1 : ‖u‖ = 1)
    (hδ : ‖φ u - a * u‖ ≤ ‖ϖ‖ ^ (k + 1)) :
    ∃ N' : ℕ, 0 < N' ∧ ∃ u' ∈ Submodule.span L {x : Kbar p | x ^ q ^ N' = x}, ‖u'‖ = 1 ∧
      ‖φ u' - a * u'‖ ≤ ‖ϖ‖ ^ (k + 2) ∧ ‖u' - u‖ ≤ ‖ϖ‖ ^ (k + 1) := by
  have hϖ0 : 0 < ‖ϖ‖ := norm_unif_pos hϖ
  have hϖ1 : ‖ϖ‖ < 1 := hϖ.2.1
  set c := ϖ ^ (k + 1) with hc
  have hcn : ‖c‖ = ‖ϖ‖ ^ (k + 1) := norm_pow _ _
  have hc0 : c ≠ 0 := pow_ne_zero _ (norm_pos_iff.1 hϖ0)
  have hcL : c ∈ L := pow_mem hϖ.1 _
  set δ := φ u - a * u with hδdef
  set e := δ / c with hedef
  have he1 : ‖e‖ ≤ 1 := by
    rw [hedef, norm_div, hcn, div_le_one (pow_pos hϖ0 _)]; exact hδ
  obtain ⟨hq1, ⟨ee, hqe⟩, hφL, hφ, -⟩ := id hD
  -- a root `y` of `Y^q − aY + e`
  obtain ⟨y, hy⟩ : ∃ y : Kbar p, y ^ q - a * y + e = 0 := by
    have hnat : (X ^ q - C a * X + C e : (Kbar p)[X]).natDegree = q := by
      rw [natDegree_add_C, natDegree_sub_eq_left_of_natDegree_lt]
      · exact natDegree_X_pow q
      · rw [natDegree_X_pow]; exact lt_of_le_of_lt ((natDegree_C_mul_le a X).trans natDegree_X_le) hq1
    have hdeg : (X ^ q - C a * X + C e : (Kbar p)[X]).degree ≠ 0 := by
      intro h
      have h0 : (X ^ q - C a * X + C e : (Kbar p)[X]).natDegree = 0 :=
        natDegree_eq_of_degree_eq_some h
      rw [hnat] at h0
      omega
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
    exact ⟨y, by simpa using hy⟩
  have hy1 : ‖y‖ ≤ 1 := by
    by_contra h
    have h' : 1 < ‖y‖ := lt_of_not_ge h
    have e1 : y ^ q = a * y - e := by linear_combination hy
    have h2 : ‖y ^ q‖ ≤ ‖y‖ := by
      rw [e1]
      refine (norm_sub_le_max' _ _).trans (max_le ?_ ?_)
      · rw [norm_mul, ha1, one_mul]
      · exact he1.trans h'.le
    rw [norm_pow] at h2
    have h3 : ‖y‖ ^ 1 < ‖y‖ ^ q := pow_lt_pow_right₀ h' hq1
    rw [pow_one] at h3
    linarith
  obtain ⟨m, hm, s, hs, hys⟩ := exists_teich_close hqe hy1
  have hs1 : ‖s‖ ≤ 1 := norm_le_one_of_pow_eq_self (Nat.one_lt_pow hm.ne' hq1) hs
  set N' := N * m with hN'def
  have hN' : 0 < N' := Nat.mul_pos hN hm
  have hspan := span_mono_dvd (L := L) (q := q) (dvd_mul_right N m)
  have hsN' : s ∈ Submodule.span L {x : Kbar p | x ^ q ^ N' = x} :=
    Submodule.subset_span (pow_pow_of_dvd hs (dvd_mul_left m N))
  have hD' : FrobData L q φ := hD
  refine ⟨N', hN', u + c * s, Submodule.add_mem _ (hspan hu) (mul_mem_span hcL hsN'), ?_, ?_, ?_⟩
  · have hlt : ‖c * s‖ < ‖u‖ := by
      rw [norm_mul, hcn, hu1]
      calc ‖ϖ‖ ^ (k + 1) * ‖s‖ ≤ ‖ϖ‖ ^ (k + 1) * 1 :=
            mul_le_mul_of_nonneg_left hs1 (pow_nonneg hϖ0.le _)
        _ < 1 := by rw [mul_one]; exact pow_lt_one₀ hϖ0.le hϖ1 (Nat.succ_ne_zero k)
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le, hu1]
  · have hφs : φ s = s ^ q := hφ m s hm hs
    have hφc : φ c = c := hφL c hcL
    have key : φ (u + c * s) - a * (u + c * s) = c * (e + (s ^ q - a * s)) := by
      have h2 : c * (δ / c) = δ := mul_div_cancel₀ δ hc0
      rw [map_add, map_mul, hφc, hφs, hedef]
      linear_combination (-1 : Kbar p) * hδdef - h2
    have hδmem : δ ∈ Submodule.span L {x : Kbar p | x ^ q ^ N = x} :=
      Submodule.sub_mem _ (frob_mem_span hD' hN hu) (mul_mem_span haL hu)
    have hemem : e ∈ Submodule.span L {x : Kbar p | x ^ q ^ N' = x} := by
      have : e = c⁻¹ * δ := by rw [hedef, div_eq_inv_mul]
      rw [this]
      exact mul_mem_span (L.inv_mem hcL) (hspan hδmem)
    have hzmem : e + (s ^ q - a * s) ∈ Submodule.span L {x : Kbar p | x ^ q ^ N' = x} := by
      refine Submodule.add_mem _ hemem (Submodule.sub_mem _ ?_ (mul_mem_span haL hsN'))
      rw [← hφs]; exact frob_mem_span hD' hN' hsN'
    have hzlt : ‖e + (s ^ q - a * s)‖ < 1 := by
      have e2 : e + (s ^ q - a * s) = (s ^ q - y ^ q) - a * (s - y) := by
        linear_combination hy
      rw [e2]
      refine lt_of_le_of_lt (norm_sub_le_max' _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt (norm_pow_sub_pow_le hs1 hy1 q) (by rw [norm_sub_rev]; exact hys)
      · rw [norm_mul, ha1, one_mul, norm_sub_rev]; exact hys
    have hz := norm_le_of_mem_span hD' hϖ hN' hzmem hzlt
    rw [key, norm_mul, hcn]
    calc ‖ϖ‖ ^ (k + 1) * ‖e + (s ^ q - a * s)‖ ≤ ‖ϖ‖ ^ (k + 1) * ‖ϖ‖ :=
          mul_le_mul_of_nonneg_left hz (pow_nonneg hϖ0.le _)
      _ = ‖ϖ‖ ^ (k + 2) := by ring
  · rw [add_sub_cancel_left, norm_mul, hcn]
    exact mul_le_of_le_one_right (pow_nonneg hϖ0.le _) hs1

/-- Dependent choice along `ℕ`. -/
theorem exists_seq_of_step {α : Type*} (P : ℕ → α → Prop) (R : ℕ → α → α → Prop)
    (h0 : ∃ x, P 0 x) (hs : ∀ k x, P k x → ∃ y, P (k + 1) y ∧ R k x y) :
    ∃ f : ℕ → α, ∀ k, P k (f k) ∧ R k (f k) (f (k + 1)) := by
  classical
  let g : (k : ℕ) → {x // P k x} := fun k => Nat.rec (motive := fun k => {x // P k x})
    ⟨h0.choose, h0.choose_spec⟩
    (fun k ih => ⟨(hs k ih.1 ih.2).choose, (hs k ih.1 ih.2).choose_spec.1⟩) k
  exact ⟨fun k => (g k).1, fun k => ⟨(g k).2, (hs k (g k).1 (g k).2).choose_spec.2⟩⟩

/-- **The period in `ℂ_p`.** For `a ∈ L` with `|a| = 1` there is `v ∈ ℂ_p`, `|v| = 1`, with
`φ v = a v`, fixed by the inertia subgroup of `G_L`, and approximable by elements of `ℚ̄_p`. -/
theorem exists_period {L : Fld p} [FiniteDimensional ℚ_[p] L] {q : ℕ} {φ : GQp p}
    (hD : FrobData L q φ) {a : Kbar p} (haL : a ∈ L) (ha1 : ‖a‖ = 1) :
    ∃ v : ℂ_[p], ‖v‖ = 1 ∧ φ • v = (a : ℂ_[p]) * v ∧
      (∀ τ ∈ fixSet L ∩ inertiaSet, τ • v = v) ∧
      ∀ ε > 0, ∃ x : Kbar p, ‖v - (x : ℂ_[p])‖ < ε := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (inferInstance : FiniteDimensional ℚ_[p] L)
  have hϖ0 : 0 < ‖ϖ‖ := norm_unif_pos hϖ
  have hϖ1 : ‖ϖ‖ < 1 := hϖ.2.1
  obtain ⟨f, hf⟩ := exists_seq_of_step (α := ℕ × Kbar p)
    (fun k x => 0 < x.1 ∧ x.2 ∈ Submodule.span L {y : Kbar p | y ^ q ^ x.1 = y} ∧
      ‖x.2‖ = 1 ∧ ‖φ x.2 - a * x.2‖ ≤ ‖ϖ‖ ^ (k + 1))
    (fun k x y => ‖y.2 - x.2‖ ≤ ‖ϖ‖ ^ (k + 1))
    (by
      obtain ⟨N, hN, u, hu, hu1, hδ⟩ := exists_base hD hϖ haL ha1
      exact ⟨(N, u), hN, hu, hu1, by simpa using hδ⟩)
    (by
      rintro k ⟨N, u⟩ ⟨hN, hu, hu1, hδ⟩
      obtain ⟨N', hN', u', hu', hu1', hδ', hd⟩ := exists_step hD hϖ haL ha1 k N hN u hu hu1 hδ
      exact ⟨(N', u'), ⟨hN', hu', hu1', hδ'⟩, hd⟩)
  set U : ℕ → ℂ_[p] := fun k => ((f k).2 : ℂ_[p]) with hU
  have hcoe_sub : ∀ x y : Kbar p, ((x : ℂ_[p]) - (y : ℂ_[p])) = ((x - y : Kbar p) : ℂ_[p]) :=
    fun x y => (UniformSpace.Completion.coe_sub x y).symm
  have hcauchy : CauchySeq U := by
    refine cauchySeq_of_le_geometric ‖ϖ‖ ‖ϖ‖ hϖ1 fun k => ?_
    rw [dist_eq_norm, norm_sub_rev, hU, hcoe_sub, PadicComplex.norm_extends, ← pow_succ']
    exact (hf k).2
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hpq : p ∣ q := by
    obtain ⟨hq1, ⟨e, hqe⟩, -⟩ := hD
    rcases e with _ | e
    · rw [pow_zero] at hqe; omega
    · rw [hqe]; exact dvd_pow_self p (Nat.succ_ne_zero e)
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · have h1 : Filter.Tendsto (fun k => ‖U k‖) Filter.atTop (nhds ‖v‖) :=
      (continuous_norm.tendsto v).comp hv
    have h2 : (fun k => ‖U k‖) = fun _ => (1 : ℝ) := by
      funext k; rw [hU, PadicComplex.norm_extends]; exact (hf k).1.2.2.1
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  · have h1 : Filter.Tendsto (fun k => φ • U k - (a : ℂ_[p]) * U k) Filter.atTop
        (nhds (φ • v - (a : ℂ_[p]) * v)) :=
      (((PadicComplex.continuous_smul_left p φ).tendsto v).comp hv).sub
        (tendsto_const_nhds.mul hv)
    have h2 : Filter.Tendsto (fun k => φ • U k - (a : ℂ_[p]) * U k) Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm (a := fun k => ‖ϖ‖ * ‖ϖ‖ ^ k) (fun k => ?_) ?_
      · rw [hU, PadicComplex.smul_coe, ← UniformSpace.Completion.coe_mul, hcoe_sub,
          PadicComplex.norm_extends, ← pow_succ']
        exact (hf k).1.2.2.2
      · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hϖ0.le hϖ1).const_mul ‖ϖ‖
    exact sub_eq_zero.1 (tendsto_nhds_unique h1 h2)
  · intro τ hτ
    have h1 : Filter.Tendsto (fun k => τ • U k) Filter.atTop (nhds (τ • v)) :=
      ((PadicComplex.continuous_smul_left p τ).tendsto v).comp hv
    have h2 : (fun k => τ • U k) = U := by
      funext k
      rw [hU, PadicComplex.smul_coe,
        inertia_fix_span hD.1 hpq (hf k).1.1 hτ (hf k).1.2.1]
    rw [h2] at h1
    exact tendsto_nhds_unique h1 hv
  · intro ε hε
    obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.1 hv) ε hε
    exact ⟨(f k).2, by rw [← dist_eq_norm, dist_comm]; exact hk k le_rfl⟩


/-! ### The character and inertia -/

theorem cpVal_mul {p : ℕ} [Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (z w : Lˣ) : cpVal p (z * w) = cpVal p z * cpVal p w := by
  simp only [cpVal, Units.val_mul, MulMemClass.coe_mul, UniformSpace.Completion.coe_mul]

theorem cpVal_pow {p : ℕ} [Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (z : Lˣ) (j : ℕ) : cpVal p (z ^ j) = cpVal p z ^ j := by
  induction j with
  | zero => simp [cpVal, UniformSpace.Completion.coe_one]
  | succ j ih => rw [pow_succ, cpVal_mul, ih, pow_succ]

/-- The metric inertia group lies in the inertia subgroup (it fixes the roots of `X^{p^f} − X`). -/
theorem isInertia_of_mem_inertiaSet {p : ℕ} [Fact p.Prime]
    {τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hτ : τ ∈ inertiaSet) : IsInertia p τ := by
  show _ ∈ TauCeti.inertiaSubgroup ℚ_[p]
  rw [TauCeti.mem_inertiaSubgroup_iff_pow_natCard_pow_eq_self]
  intro x f hf hx
  rw [Padic.natCard_residueField] at hx
  exact fix_of_mem_inertiaSet_of_pow_eq_self hτ (Nat.one_lt_pow hf (Fact.out : p.Prime).one_lt)
    (dvd_pow_self p hf) hx

end UnramifiedPeriodAux

open UnramifiedPeriodAux LadicCond in
/-- **Hilbert 90 over the completed maximal unramified extension (proved).** -/
theorem unramifiedPeriod_proof : UnramifiedPeriod := by
  intro p _ L _ μ hcont hinert
  obtain ⟨q, φ, hD⟩ := UnramRootsTask.frobData_exists L
  set F : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → PadicAlgCl p :=
    fun σ => (((μ σ : Lˣ) : L) : PadicAlgCl p) with hF
  have hF1 : F 1 = 1 := by simp [hF]
  have hFpow : ∀ σ (j : ℕ), F (σ ^ j) = F σ ^ j := by intro σ j; simp [hF, map_pow]
  have hFL : ∀ σ, F σ ∈ L := fun σ => ((μ σ : Lˣ) : L).2
  -- continuity of `μ` at the identity
  have hnear : ∀ ε > 0, ∃ E : IntermediateField ℚ_[p] (PadicAlgCl p),
      FiniteDimensional ℚ_[p] E ∧ ∀ g ∈ fixSet E, ‖F g - 1‖ < ε := by
    intro ε hε
    have hU : F ⁻¹' Metric.ball 1 ε ∈ nhds (1 : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) := by
      apply (Metric.isOpen_ball.preimage hcont).mem_nhds
      simp [hF1, hε]
    obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ_[p] (PadicAlgCl p) _).1 hU
    refine ⟨E, hE, fun g hg => ?_⟩
    have := hsub ((IntermediateField.mem_fixingSubgroup_iff E g).2 hg)
    simpa [dist_eq_norm] using this
  -- `|μ(φ)| = 1`
  have ha1 : ‖F φ‖ = 1 := by
    obtain ⟨E, hE, hEg⟩ := hnear 1 one_pos
    obtain ⟨j, hj, hφj⟩ := UnramRootsTask.exists_pow_mem_fixSet hE (σ := φ)
    have h1 := hEg _ hφj
    rw [hFpow] at h1
    have h2 : ‖F φ ^ j‖ = 1 := norm_eq_of_norm_sub_lt norm_one (by rwa [norm_sub_rev])
    rw [norm_pow] at h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hj.ne').mp h2
  obtain ⟨v, hv1, hφv, hτv, happrox⟩ := exists_period hD (hFL φ) ha1
  refine ⟨v, fun h => by rw [h, norm_zero] at hv1; exact zero_ne_one hv1, fun σ hσ => ?_⟩
  have hσ' : σ ∈ fixSet L := fun x hx => (IntermediateField.mem_fixingSubgroup_iff L σ).1 hσ x hx
  refine eq_of_forall_dist_le fun ε hε => le_of_lt ?_
  obtain ⟨E, hE, hEg⟩ := hnear ε hε
  obtain ⟨x, hx⟩ := happrox ε hε
  have hE' : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  obtain ⟨j, τ, hτ, g, hg, rfl⟩ := UnramRootsTask.f1_of_frobData hD
    (L ⊔ E ⊔ IntermediateField.adjoin ℚ_[p] {x}) inferInstance
    (le_sup_left.trans le_sup_left) σ hσ'
  have hgE : g ∈ fixSet E := UnramRootsTask.fixSet_anti (le_sup_right.trans le_sup_left) hg
  have hgx : g x = x :=
    hg x ((le_sup_right : IntermediateField.adjoin ℚ_[p] {x} ≤ _)
      (IntermediateField.subset_adjoin ℚ_[p] {x} rfl))
  have hB := hEg g hgE
  have hτI : μ τ = 1 := hinert τ (isInertia_of_mem_inertiaSet hτ.2)
  set A : ℂ_[p] := ((F φ : PadicAlgCl p) : ℂ_[p]) with hA
  have hA1 : ‖A‖ = 1 := by rw [hA, PadicComplex.norm_extends]; exact ha1
  have hδ : ‖g • v - v‖ < ε := by
    have e1 : g • v - v = g • (v - (x : ℂ_[p])) - (v - (x : ℂ_[p])) := by
      rw [smul_sub, PadicComplex.smul_coe, hgx]; ring
    rw [e1, sub_eq_add_neg]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [PadicComplex.norm_smul_eq]; exact hx
    · rw [norm_neg]; exact hx
  have hφA : φ • A = A := by rw [hA, PadicComplex.smul_coe, hD.2.2.1 _ (hFL φ)]
  have hφjv : ∀ i : ℕ, (φ ^ i) • v = A ^ i * v := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ', mul_smul, ih, smul_mul', hφv, smul_pow', hφA, pow_succ]; ring
  have hval : cpVal p (μ (φ ^ j * τ * g)) = A ^ j * ((F g : PadicAlgCl p) : ℂ_[p]) := by
    rw [map_mul, map_mul, hτI, mul_one, cpVal_mul, map_pow, cpVal_pow]
  have hact : (φ ^ j * τ * g) • v = A ^ j * v + (φ ^ j * τ) • (g • v - v) := by
    rw [mul_smul (φ ^ j * τ) g v, smul_sub, mul_smul (φ ^ j) τ v, hτv τ hτ, hφjv]; ring
  rw [dist_eq_norm, hact, hval]
  have e2 : A ^ j * v + (φ ^ j * τ) • (g • v - v) - A ^ j * ((F g : PadicAlgCl p) : ℂ_[p]) * v =
      A ^ j * v * ((1 - F g : PadicAlgCl p) : ℂ_[p]) + (φ ^ j * τ) • (g • v - v) := by
    rw [UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_one]; ring
  rw [e2]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul, norm_mul, norm_pow, hA1, hv1, one_pow, one_mul, one_mul,
      PadicComplex.norm_extends, norm_sub_rev]
    exact hB
  · rw [PadicComplex.norm_smul_eq]; exact hδ

end ZInQ.Contrib.SenWeightZero
