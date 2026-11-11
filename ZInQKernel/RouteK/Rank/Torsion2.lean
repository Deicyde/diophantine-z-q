import ZInQKernel.RouteK.Rank.Delta

/-!
# The 2-torsion of `C_d`

Over a field `K` with `2 ≠ 0` and `d ≠ 0`, the points `P` of `C_d : y² = x³ − d²x` with `2P = 0`
are exactly `O, (0, 0), (d, 0), (−d, 0)`, so the kernel of doubling has 4 elements
(`card_ker_two_nsmul_eq_four`).
-/

namespace ZInQ.RouteK.Rank

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Descent

variable {K : Type*} [Field K] [DecidableEq K] {d : K}

omit [DecidableEq K] in
theorem delta_root_neg_d (d : K) : (-d) ^ 3 + -d ^ 2 * (-d) = 0 := by ring

variable (h2 : (2 : K) ≠ 0) (hd : d ≠ 0)
include h2 hd

/-- The kernel of doubling on `C_d(K)` is `{O, (0, 0), (d, 0), (−d, 0)}`. -/
theorem ker_two_nsmul_eq :
    (((nsmulAddMonoidHom 2 : (shortCurve (-d ^ 2)).toAffine.Point →+ _).ker :
        AddSubgroup _) : Set (shortCurve (-d ^ 2)).toAffine.Point) =
      {0, tRootPt h2 (delta_b_ne_zero hd) (delta_root_zero d),
        tRootPt h2 (delta_b_ne_zero hd) (delta_root_d d),
        tRootPt h2 (delta_b_ne_zero hd) (delta_root_neg_d d)} := by
  have : NeZero (2 : K) := ⟨h2⟩
  have hb := delta_b_ne_zero hd
  ext P
  simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  rcases P with _ | ⟨x, y, h⟩
  · exact iff_of_true (smul_zero _) (Or.inl rfl)
  rw [shortCurve_two_nsmul_some_eq_zero_iff]
  constructor
  · intro hy
    have e := (shortCurve_equation_iff _ x y).mp h.1
    rw [hy] at e
    have : x * (x - d) * (x + d) = 0 := by linear_combination -e
    right
    rcases mul_eq_zero.mp this with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · left; exact some_eq_tRootPt h2 hb (delta_root_zero d) h h''
      · right; left; exact some_eq_tRootPt h2 hb (delta_root_d d) h (sub_eq_zero.mp h'')
    · right; right
      exact some_eq_tRootPt h2 hb (delta_root_neg_d d) h (by linear_combination h')
  · rintro (h0 | h0 | h0 | h0)
    · exact absurd h0 (by simp)
    all_goals
      obtain ⟨_, ht⟩ := tRootPt_def h2 hb _
      rw [ht] at h0
      simp only [Point.some.injEq] at h0
      exact h0.2

/-- **`#C_d(K)[2] = 4`.** -/
theorem card_ker_two_nsmul_eq_four :
    Nat.card (nsmulAddMonoidHom 2 : (shortCurve (-d ^ 2)).toAffine.Point →+ _).ker = 4 := by
  have hb := delta_b_ne_zero hd
  have hd2 : d ≠ -d := fun h => mul_ne_zero h2 hd (by linear_combination h)
  have hx : ∀ {e e' : K} (he : e ^ 3 + -d ^ 2 * e = 0) (he' : e' ^ 3 + -d ^ 2 * e' = 0),
      tRootPt h2 hb he = tRootPt h2 hb he' → e = e' := by
    intro e e' he he' h
    obtain ⟨_, h₁⟩ := tRootPt_def h2 hb he
    obtain ⟨_, h₂⟩ := tRootPt_def h2 hb he'
    rw [h₁, h₂] at h
    simp only [Point.some.injEq] at h
    exact h.1
  have hz : ∀ {e : K} (he : e ^ 3 + -d ^ 2 * e = 0), (0 : (shortCurve (-d ^ 2)).toAffine.Point) ≠
      tRootPt h2 hb he := by
    intro e he h
    obtain ⟨_, h₁⟩ := tRootPt_def h2 hb he
    rw [h₁] at h
    exact Point.some_ne_zero _ h.symm
  rw [← SetLike.coe_sort_coe, ker_two_nsmul_eq h2 hd, Nat.card_coe_set_eq]
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair]
  · intro h; exact hd2 (hx _ _ h)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hd (hx _ _ h).symm, fun h => hd (by linear_combination (hx _ _ h))⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hz _, hz _, hz _⟩

end ZInQ.RouteK.Rank
