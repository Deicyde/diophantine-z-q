import Mathlib

/-!
# RankCounts: a determinant of bounded valuation survives the inner limit (tex 5336–5343)

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:limits-fixed-field-budget`, tex 5336–5343:

> This comparison is retained before the inner limit. The field `K` and `C_K` are fixed, while the
> two moving Frobenius matrices and the comparison maps may vary with `i` and with the graph.
> Pass to their limit at every coefficient precision using the same retained finite diagram.
> A matrix whose determinant has valuation at most `c_E` cannot acquire a zero determinant in
> this limit: the property is determined modulo `2^{c_E+1}`.

The limit is taken entrywise along one ultrafilter at every precision (Lemma
`ex:limits-inner-limit`, tex 4446–4451), so the limit matrix is congruent modulo `2^{c_E+1}`
to the stage matrices on a set in the ultrafilter. The algebraic content is therefore:
two square matrices over `ℤ_p` congruent modulo `p^{c+1}`, one of whose determinants has
valuation at most `c`, have equal determinant valuations; in particular the other determinant
is nonzero. This file proves it (`DetValuationStable`), and its consequence for the singular
disks `[ℤ₂² --(Φ − r)--> ℤ₂²]` of tex 5326–5334 (`SingularDiskLimit`): the limit matrix again has
nonzero determinant of valuation at most `c_E`, which is what RC7's
`singular_complexes_total_length_le` (Determinant/SmithLength.lean) takes as
hypotheses `hX : X.det ≠ 0` and `hXc : X.det.valuation ≤ c`.

Kinds: everything here is PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.RankCounts

open Matrix

variable {p : ℕ} [Fact p.Prime]

/-- Congruent square matrices have congruent determinants: if every entry of `X − Y` lies in an
ideal `I`, then `det X − det Y ∈ I` (the determinant is a polynomial in the entries). PROVED. -/
theorem det_sub_det_mem_of_entries {R : Type*} [CommRing R] {n : Type*} [Fintype n]
    [DecidableEq n] (I : Ideal R) (X Y : Matrix n n R) (h : ∀ i j, X i j - Y i j ∈ I) :
    X.det - Y.det ∈ I := by
  rw [← Ideal.Quotient.eq]
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  exact Ideal.Quotient.eq.mpr (h i j)

/-- **Tex 5340–5343 (PROVED): the valuation of a determinant of valuation at most `c` is
determined modulo `p^{c+1}`.** For square matrices `X, Y` over `ℤ_p` whose entries are congruent
modulo `p^{c+1}`, if `det X ≠ 0` has valuation at most `c`, then `det Y ≠ 0` and
`v_p(det Y) = v_p(det X)` (so `v_p(det Y) ≤ c` as well). -/
def DetValuationStable : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : Type) [Fintype n] [DecidableEq n] (X Y : Matrix n n ℤ_[p])
    (c : ℕ), (∀ i j, X i j - Y i j ∈ Ideal.span {(p : ℤ_[p]) ^ (c + 1)}) →
    X.det ≠ 0 → X.det.valuation ≤ c →
    Y.det ≠ 0 ∧ Y.det.valuation = X.det.valuation

theorem detValuationStable_proof : DetValuationStable := by
  intro p _ n _ _ X Y c hXY hX hc
  set a := X.det with ha
  set b := Y.det with hb
  have hab : a - b ∈ Ideal.span {(p : ℤ_[p]) ^ (c + 1)} :=
    det_sub_det_mem_of_entries _ X Y hXY
  have hmono : ∀ k, k ≤ c + 1 →
      Ideal.span {(p : ℤ_[p]) ^ (c + 1)} ≤ Ideal.span {(p : ℤ_[p]) ^ k} := fun k hk =>
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hk)
  -- `a ∈ (p^k)` for `k = v(a)`.
  have haK : a ∈ Ideal.span {(p : ℤ_[p]) ^ a.valuation} :=
    (PadicInt.mem_span_pow_iff_le_valuation a hX _).mpr le_rfl
  have hb0 : b ≠ 0 := by
    intro h0
    have : a ∈ Ideal.span {(p : ℤ_[p]) ^ (c + 1)} := by simpa [h0] using hab
    have := (PadicInt.mem_span_pow_iff_le_valuation a hX _).mp this
    omega
  refine ⟨hb0, le_antisymm ?_ ?_⟩
  · -- `v(b) ≤ v(a)`: otherwise `b ∈ (p^{v(a)+1})` and so is `a = b + (a - b)`.
    by_contra hlt
    rw [not_le] at hlt
    have hbK : b ∈ Ideal.span {(p : ℤ_[p]) ^ (a.valuation + 1)} :=
      (PadicInt.mem_span_pow_iff_le_valuation b hb0 _).mpr hlt
    have habK : a - b ∈ Ideal.span {(p : ℤ_[p]) ^ (a.valuation + 1)} :=
      hmono _ (by omega) hab
    have haK1 : a ∈ Ideal.span {(p : ℤ_[p]) ^ (a.valuation + 1)} := by
      have := Ideal.add_mem _ habK hbK
      simpa using this
    have := (PadicInt.mem_span_pow_iff_le_valuation a hX _).mp haK1
    omega
  · -- `v(a) ≤ v(b)`: `b = a - (a - b)` with both terms in `(p^{v(a)})`.
    have habK : a - b ∈ Ideal.span {(p : ℤ_[p]) ^ a.valuation} := hmono _ (by omega) hab
    have hbK : b ∈ Ideal.span {(p : ℤ_[p]) ^ a.valuation} := by
      have := Ideal.sub_mem _ haK habK
      simpa using this
    exact (PadicInt.mem_span_pow_iff_le_valuation b hb0 _).mp hbK

/-- **Tex 5326–5343 (PROVED): the singular disks survive the inner limit.** Let `X` be a
`2 × 2` matrix over `ℤ₂` (a stage matrix `Φ_{r_i} − r_i`, tex 5326–5331) with nonzero
determinant of valuation at most `c` (`c = c_E`, tex 5331–5332), and let `Y` be its limit matrix,
congruent to `X` modulo `2^{c+1}` entrywise (tex 5338–5343). Then `det Y ≠ 0` and
`v₂(det Y) ≤ c`: the hypotheses `hY : Y.det ≠ 0` and `hYc : Y.det.valuation ≤ c` of RC7's
`singular_complexes_total_length_le` (Determinant/SmithLength.lean) hold for
the limit matrix. -/
def SingularDiskLimit : Prop :=
  ∀ (X Y : Matrix (Fin 2) (Fin 2) ℤ_[2]) (c : ℕ),
    (∀ i j, X i j - Y i j ∈ Ideal.span {(2 : ℤ_[2]) ^ (c + 1)}) →
    X.det ≠ 0 → X.det.valuation ≤ c →
    Y.det ≠ 0 ∧ Y.det.valuation ≤ c

theorem singularDiskLimit_proof : SingularDiskLimit := by
  intro X Y c hXY hX hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h0, hv⟩ := detValuationStable_proof 2 (Fin 2) X Y c (by exact_mod_cast hXY) hX hc
  exact ⟨h0, hv ▸ hc⟩

/-- Non-vacuity of `SingularDiskLimit`: the matrix `X = diag(1, 2)` has determinant `2 ≠ 0` of
valuation `1`, and `Y = diag(1 + 4, 2)` is congruent to it modulo `2^{1+1}`. PROVED. -/
theorem singularDiskLimit_nonvacuous :
    ∃ (X Y : Matrix (Fin 2) (Fin 2) ℤ_[2]) (c : ℕ),
      (∀ i j, X i j - Y i j ∈ Ideal.span {(2 : ℤ_[2]) ^ (c + 1)}) ∧
      X.det ≠ 0 ∧ X.det.valuation ≤ c := by
  refine ⟨Matrix.diagonal ![1, 2], Matrix.diagonal ![5, 2], 1, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp
    · rw [Ideal.mem_span_singleton]
      exact ⟨-1, by norm_num⟩
  · simp [Matrix.det_diagonal, Fin.prod_univ_two]
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    simp only [Matrix.det_diagonal, Fin.prod_univ_two]
    norm_num
    have h := PadicInt.valuation_p (p := 2)
    exact_mod_cast h.le

end ZInQ.Contrib.CloudB3RC53.RankCounts
