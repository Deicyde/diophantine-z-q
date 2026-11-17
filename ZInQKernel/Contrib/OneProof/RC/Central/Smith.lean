import Mathlib

/-!
# Lane RC15 (central): the DVR/Smith argument of Lemma `ex:arith-base-zero`

The 11/5 manuscript (`diophantine_zq.tex`, lines 4346–4358):

> Full Selmer corank one gives central dimensions `(1,1)` in degrees one and two and zero in every
> other degree. […] Over the DVR `A`, a bounded finite free complex decomposes, by successive Smith
> reductions, into free zero-differential summands and two-term disks `[A --t^r--> A]`, up to
> units. A disk with `r > 0` contributes one additional residue-field cohomology class in each of
> its two adjacent degrees. Semicontinuity and Euler characteristic therefore leave only two
> generic possibilities: the complex is acyclic, or its dimensions are `(1,1)` in degrees one and
> two. […] In the second case the generic and central dimensions agree in every degree. Hence no
> disk with `r > 0` occurs.

**Form (recorded in the report).** A bounded complex of finite free `A`-modules is a sequence of
matrices `d i : A^{r i} → A^{r (i+1)}`, `i ∈ ℕ`, with `d (i+1) ∘ d i = 0`. Its Smith reduction
has, between degrees `i` and `i + 1`, exactly `rank_F (d i)` disks, of which
`rank_F (d i) − rank_k (d̄ i)` have `r > 0`; these counts are what the argument uses, and they are
read off the ranks without choosing the Smith bases. The cohomology dimensions are those of the
genuine cohomology `ker / im` of the base-changed complex over `F` and over `k`.

Every declaration in this file is `PROVED`.

* `linearIndependent_generic_of_residue`, `rank_map_residue_le` (**semicontinuity**): over a DVR
  `A` with fraction field `F` and residue field `k`, `rank_k (D̄) ≤ rank_F (D)`.
* `cohDim`, `cohDim_add`: the cohomology dimensions over a field and
  `dim H^i + rank d_i + rank d_{i−1} = r_i`.
* `cohDim_residue_eq` (**disk count**): `dim_k H^i(C ⊗ k) = dim_F H^i(C ⊗ F) + δ_i + δ_{i−1}`
  with `δ_i = rank_F d_i − rank_k d̄_i ≥ 0` the number of disks with `r > 0` between degrees `i`
  and `i + 1`; in particular the Euler characteristic is unchanged.
* `smith_dichotomy` and `bounded_complex_dichotomy`: if the central dimensions are `(1,1)` in
  degrees one and two and zero elsewhere, the generic complex is acyclic, or has dimensions
  `(1,1)` in degrees one and two with no disk of `r > 0` at all.
-/

namespace ZInQ.Manuscript.RC.Central

open Matrix

/-! ### Semicontinuity of rank over a DVR -/

section Semicontinuity

variable {A F k : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field F] [Algebra A F] [IsFractionRing A F] [Field k]

/-- **Integral vectors independent modulo the maximal ideal are independent generically.**
A dependence over `F` is cleared of denominators and divided by an entry of least valuation, which
then becomes `1`; reducing modulo the maximal ideal gives a dependence over `k`. PROVED. -/
theorem linearIndependent_generic_of_residue {ι : Type*} [Fintype ι] {m : ℕ}
    (ρ : A →+* k) (v : ι → Fin m → A)
    (h : LinearIndependent k fun j => fun i => ρ (v j i)) :
    LinearIndependent F fun j => fun i => algebraMap A F (v j i) := by
  classical
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  by_contra hne
  rw [not_forall] at hne
  obtain ⟨j1, hj1⟩ := hne
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors A) Finset.univ g
  have hb' : ∀ j, ∃ a : A, algebraMap A F a = (b : A) • g j :=
    fun j => RingHom.mem_rangeS.mp (hb j (Finset.mem_univ j))
  choose a ha using hb'
  have hι := IsFractionRing.injective A F
  have hb0 : (b : A) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hbF : algebraMap A F (b : A) ≠ 0 := by
    intro h0; exact hb0 (hι (by rw [h0, map_zero]))
  -- the integral relation
  have hrel : ∀ i, ∑ j, a j * v j i = 0 := by
    intro i
    apply hι
    have := congrFun hg i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [map_sum, map_zero]
    calc ∑ j, algebraMap A F (a j * v j i)
        = ∑ j, algebraMap A F (b : A) * (g j * algebraMap A F (v j i)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul, ha j, Algebra.smul_def]; ring
      _ = algebraMap A F (b : A) * ∑ j, g j * algebraMap A F (v j i) := by
          rw [Finset.mul_sum]
      _ = 0 := by rw [this, mul_zero]
  have haj1 : a j1 ≠ 0 := by
    intro h0
    have := ha j1
    rw [h0, map_zero, Algebra.smul_def] at this
    exact (mul_ne_zero hbF hj1) this.symm
  -- an entry of least valuation
  set S := Finset.univ.filter fun j => a j ≠ 0
  have hS : S.Nonempty := ⟨j1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, haj1⟩⟩
  obtain ⟨j0, hj0S, hmin⟩ :=
    Finset.exists_min_image S (fun j => IsDiscreteValuationRing.addVal A (a j)) hS
  have haj0 : a j0 ≠ 0 := (Finset.mem_filter.mp hj0S).2
  have hdvd : ∀ j, a j0 ∣ a j := by
    intro j
    by_cases hj : a j = 0
    · rw [hj]; exact dvd_zero _
    · exact IsDiscreteValuationRing.addVal_le_iff_dvd.mp
        (hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩))
  choose a' ha' using hdvd
  have ha'0 : a' j0 = 1 := by
    have := ha' j0
    exact (mul_left_cancel₀ haj0 (this.symm.trans (mul_one _).symm))
  have hrel' : ∀ i, ∑ j, a' j * v j i = 0 := by
    intro i
    have h1 := hrel i
    have : a j0 * ∑ j, a' j * v j i = 0 := by
      rw [Finset.mul_sum, ← h1]
      exact Finset.sum_congr rfl fun j _ => by rw [ha' j]; ring
    exact (mul_eq_zero.mp this).resolve_left haj0
  have hk := h (fun j => ρ (a' j)) (by
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← map_zero ρ, ← hrel' i, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul]) j0
  rw [ha'0, map_one] at hk
  exact one_ne_zero hk

/-- **Semicontinuity of rank** over a DVR: the rank of the reduction of an integral matrix is at
most its generic rank (for any ring map `ρ` to a field; in the use `ρ` is the residue map).
PROVED. -/
theorem rank_map_residue_le {m n : ℕ} (ρ : A →+* k) (D : Matrix (Fin m) (Fin n) A) :
    (D.map ρ).rank ≤ (D.map (algebraMap A F)).rank := by
  classical
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent k (Set.range (D.map ρ).col)
  have hsfin : s.Finite := (Set.finite_range _).subset hs
  have : Fintype s := hsfin.fintype
  have hrk : (D.map ρ).rank = Fintype.card s := by
    rw [rank_eq_finrank_span_cols, ← hspan]
    have := finrank_span_eq_card (R := k) hli
    rwa [Subtype.range_coe] at this
  have hpre : ∀ x : s, ∃ c : Fin n, (D.map ρ).col c = (x : Fin m → k) := fun x => hs x.2
  choose c hc using hpre
  set v : s → Fin m → A := fun x i => D i (c x)
  have hv : (fun x : s => fun i => ρ (v x i)) = fun x : s => (x : Fin m → k) := by
    funext x i
    have := congrFun (hc x) i
    simpa [v, col_apply, map_apply] using this
  have hliF := linearIndependent_generic_of_residue (F := F) ρ v (by rw [hv]; exact hli)
  have hle : Module.finrank F (Submodule.span F (Set.range fun x : s =>
      fun i => algebraMap A F (v x i))) ≤ (D.map (algebraMap A F)).rank := by
    rw [rank_eq_finrank_span_cols]
    apply Submodule.finrank_mono
    apply Submodule.span_mono
    rintro _ ⟨x, rfl⟩
    exact ⟨c x, by funext i; simp [v, col_apply, map_apply]⟩
  rw [finrank_span_eq_card hliF] at hle
  omega

end Semicontinuity

/-! ### Cohomology dimensions of a bounded complex over a field -/

section Cohomology

variable {K : Type*} [Field K]

/-- The rank of the incoming differential `d_{i−1}` (zero in degree `0`). -/
def prevRank (ρ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => ρ j

/-- **The cohomology dimension** `dim_K H^i` of the complex
`K^{r 0} --d 0--> K^{r 1} --d 1--> ⋯`: the dimension of `ker d_i / im d_{i−1}` (with `im` taken
inside `ker`). -/
noncomputable def cohDim (r : ℕ → ℕ) (d : ∀ i, Matrix (Fin (r (i + 1))) (Fin (r i)) K) :
    ℕ → ℕ
  | 0 => Module.finrank K (LinearMap.ker (d 0).mulVecLin)
  | j + 1 => Module.finrank K ((LinearMap.ker (d (j + 1)).mulVecLin) ⧸
      (LinearMap.range (d j).mulVecLin).comap (LinearMap.ker (d (j + 1)).mulVecLin).subtype)

/-- `dim H^i + rank d_i + rank d_{i−1} = r_i` for a complex (`d_{i+1} d_i = 0`). PROVED. -/
theorem cohDim_add (r : ℕ → ℕ) (d : ∀ i, Matrix (Fin (r (i + 1))) (Fin (r i)) K)
    (hd : ∀ i, d (i + 1) * d i = 0) (i : ℕ) :
    cohDim r d i + (d i).rank + prevRank (fun j => (d j).rank) i = r i := by
  have hrn : ∀ j, (d j).rank + Module.finrank K (LinearMap.ker (d j).mulVecLin) = r j := by
    intro j
    have := LinearMap.finrank_range_add_finrank_ker (d j).mulVecLin
    rwa [Module.finrank_fin_fun] at this
  cases i with
  | zero =>
    simp only [cohDim, prevRank]
    have := hrn 0
    omega
  | succ j =>
    simp only [cohDim, prevRank]
    have hle : LinearMap.range (d j).mulVecLin ≤ LinearMap.ker (d (j + 1)).mulVecLin := by
      rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker, mulVecLin_apply, mulVecLin_apply, mulVec_mulVec, hd j, zero_mulVec]
    have hq := Submodule.finrank_quotient_add_finrank
      ((LinearMap.range (d j).mulVecLin).comap (LinearMap.ker (d (j + 1)).mulVecLin).subtype)
    rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at hq
    have h2 := hrn (j + 1)
    have h3 : Module.finrank K (LinearMap.range (d j).mulVecLin) = (d j).rank := rfl
    omega

end Cohomology

/-! ### The dichotomy -/

section Dichotomy

/-- **The dichotomy, as arithmetic of the disk counts** (tex 4350–4358). With
`hF i + ρF i + ρF (i−1) = r i` (generic), `hk i + ρk i + ρk (i−1) = r i` (central) and
`ρk ≤ ρF` (semicontinuity), central dimensions `(1,1)` in degrees one and two and zero elsewhere
leave two generic possibilities: acyclic, or `(1,1)` with `ρF = ρk` in every degree (no disk with
`r > 0`). PROVED. -/
theorem smith_dichotomy (r ρF ρk hF hk : ℕ → ℕ) (hsemi : ∀ i, ρk i ≤ ρF i)
    (hFeq : ∀ i, hF i + ρF i + prevRank ρF i = r i)
    (hkeq : ∀ i, hk i + ρk i + prevRank ρk i = r i)
    (hk1 : hk 1 = 1) (hk2 : hk 2 = 1) (hk0 : ∀ i, i ≠ 1 → i ≠ 2 → hk i = 0) :
    (∀ i, hF i = 0) ∨
      (hF 1 = 1 ∧ hF 2 = 1 ∧ (∀ i, i ≠ 1 → i ≠ 2 → hF i = 0) ∧ ∀ i, ρF i = ρk i) := by
  -- outside degree one every disk has `r = 0`
  have hρ : ∀ i, i ≠ 1 → ρF i = ρk i := by
    intro i hi
    cases i with
    | zero =>
      have h1 := hFeq 0; have h2 := hkeq 0; have h3 := hk0 0 (by omega) (by omega)
      simp only [prevRank] at h1 h2; have := hsemi 0; omega
    | succ j =>
      have h1 := hFeq (j + 2); have h2 := hkeq (j + 2)
      have h3 := hk0 (j + 2) (by omega) (by omega)
      simp only [prevRank] at h1 h2
      have := hsemi (j + 2); have := hsemi (j + 1); omega
  have hF0 : ∀ i, i ≠ 1 → i ≠ 2 → hF i = 0 := by
    intro i hi1 hi2
    cases i with
    | zero =>
      have h1 := hFeq 0; have h2 := hkeq 0; have h3 := hk0 0 (by omega) (by omega)
      simp only [prevRank] at h1 h2; have := hρ 0 (by omega); omega
    | succ j =>
      have h1 := hFeq (j + 1); have h2 := hkeq (j + 1); have h3 := hk0 (j + 1) hi1 hi2
      simp only [prevRank] at h1 h2
      have := hsemi (j + 1); have := hsemi j; omega
  have e1 := hFeq 1; have e1' := hkeq 1; have e2 := hFeq 2; have e2' := hkeq 2
  simp only [prevRank] at e1 e1' e2 e2'
  have r0 := hρ 0 (by omega); have r2 := hρ 2 (by omega); have s1 := hsemi 1
  by_cases hδ : ρF 1 = ρk 1
  · right
    refine ⟨by omega, by omega, hF0, fun i => ?_⟩
    by_cases hi : i = 1
    · subst hi; exact hδ
    · exact hρ i hi
  · left
    intro i
    by_cases hi1 : i = 1
    · subst hi1; omega
    · by_cases hi2 : i = 2
      · subst hi2; omega
      · exact hF0 i hi1 hi2

variable {A F k : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field F] [Algebra A F] [IsFractionRing A F] [Field k]

/-- **The base-zero dichotomy for an actual bounded finite free complex over a DVR**
(tex 4346–4358). Let `d` be a complex of finite free `A`-modules (`d (i+1) * d i = 0`), with
generic and central base changes along `A → F` and `ρ : A → k`. If its central cohomology has
dimensions `(1,1)` in degrees one and two and vanishes in every other degree, then either the
generic complex is acyclic, or its generic dimensions are `(1,1)` in degrees one and two and
every differential has the same generic and central rank (no disk `[A --t^r--> A]` with `r > 0`).
PROVED. -/
theorem bounded_complex_dichotomy (ρ : A →+* k)
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) (r : ℕ → ℕ)
    (d : ∀ i, Matrix (Fin (r (i + 1))) (Fin (r i)) A) (hd : ∀ i, d (i + 1) * d i = 0)
    (hk1 : cohDim r (fun i => (d i).map ρ) 1 = 1) (hk2 : cohDim r (fun i => (d i).map ρ) 2 = 1)
    (hk0 : ∀ i, i ≠ 1 → i ≠ 2 → cohDim r (fun i => (d i).map ρ) i = 0) :
    (∀ i, cohDim r (fun i => (d i).map (algebraMap A F)) i = 0) ∨
      (cohDim r (fun i => (d i).map (algebraMap A F)) 1 = 1 ∧
        cohDim r (fun i => (d i).map (algebraMap A F)) 2 = 1 ∧
        (∀ i, i ≠ 1 → i ≠ 2 → cohDim r (fun i => (d i).map (algebraMap A F)) i = 0) ∧
        ∀ i, ((d i).map (algebraMap A F)).rank = ((d i).map ρ).rank) := by
  have hdF : ∀ i, (d (i + 1)).map (algebraMap A F) * (d i).map (algebraMap A F) = 0 := by
    intro i; rw [← Matrix.map_mul, hd i, Matrix.map_zero _ (map_zero _)]
  have hdk : ∀ i, (d (i + 1)).map ρ * (d i).map ρ = 0 := by
    intro i; rw [← Matrix.map_mul, hd i, Matrix.map_zero _ (map_zero _)]
  exact smith_dichotomy r (fun i => ((d i).map (algebraMap A F)).rank)
    (fun i => ((d i).map ρ).rank) _ _ (fun i => rank_map_residue_le ρ (d i))
    (cohDim_add r (fun i => (d i).map (algebraMap A F)) hdF)
    (cohDim_add r (fun i => (d i).map ρ) hdk) hk1 hk2 hk0

/-- **The disk count** (tex 4349–4351): `dim_k H^i(C ⊗ k) = dim_F H^i(C ⊗ F) + δ_i + δ_{i−1}`,
where `δ_i = rank_F d_i − rank_k d̄_i` is the number of disks with `r > 0` between degrees `i` and
`i + 1`. PROVED. -/
theorem cohDim_residue_eq (ρ : A →+* k) (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0)
    (r : ℕ → ℕ) (d : ∀ i, Matrix (Fin (r (i + 1))) (Fin (r i)) A)
    (hd : ∀ i, d (i + 1) * d i = 0) (i : ℕ) :
    cohDim r (fun i => (d i).map ρ) i =
      cohDim r (fun i => (d i).map (algebraMap A F)) i +
        (((d i).map (algebraMap A F)).rank - ((d i).map ρ).rank) +
        (prevRank (fun j => ((d j).map (algebraMap A F)).rank) i -
          prevRank (fun j => ((d j).map ρ).rank) i) := by
  have hdF : ∀ i, (d (i + 1)).map (algebraMap A F) * (d i).map (algebraMap A F) = 0 := by
    intro i; rw [← Matrix.map_mul, hd i, Matrix.map_zero _ (map_zero _)]
  have hdk : ∀ i, (d (i + 1)).map ρ * (d i).map ρ = 0 := by
    intro i; rw [← Matrix.map_mul, hd i, Matrix.map_zero _ (map_zero _)]
  have h1 := cohDim_add r (fun i => (d i).map (algebraMap A F)) hdF i
  have h2 := cohDim_add r (fun i => (d i).map ρ) hdk i
  have s1 := rank_map_residue_le (F := F) ρ (d i)
  cases i with
  | zero => simp only [prevRank] at h1 h2 ⊢; omega
  | succ j =>
    have s2 := rank_map_residue_le (F := F) ρ (d j)
    simp only [prevRank] at h1 h2 ⊢; omega

end Dichotomy

end ZInQ.Manuscript.RC.Central
