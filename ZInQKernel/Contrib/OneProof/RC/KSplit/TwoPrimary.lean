import ZInQKernel.Contrib.PoleRC.LocalGood

/-!
# Lane RC3: the two-primary part of `E_ℓ(𝔽_p)` (the arithmetic behind the nonempty K-split seed)

Manuscript `diophantine_zq.tex` (11/5), Lemma `ex:sec7-ksplit-seed` (tex 2628–2654) and the end of
Proposition `ex:app-nonempty-seeds` (tex 10482–10500). The curve is
`E_ℓ : y² = x(x − ℓ)(x + 3ℓ)` over a field `F` with `2, 3, ℓ ≠ 0` (the tree's `PoleRC.curveF`),
with the three two-torsion points `T₀ = (0, 0)`, `T₁ = (ℓ, 0)`, `T₂ = (−3ℓ, 0)` (`PoleRC.tPtF`).

* `isSquare_sub_of_two_nsmul_eq` (**halving criterion**, necessary direction): a half of
  `(e_i, 0)` forces `e_i − e_j` to be a square for every other root `e_j`. The proof is the
  tangent-line argument of Version 19 (`quartic_v19.tex` 32244–32248): if `2P = (e_i, 0)` with
  `P = (u, v)` and tangent slope `λ`, the chord-and-tangent identity at the root `e_j`
  (`PoleRC.mul_addX_sub_eq_F`) reads `(u − e_j)²(e_i − e_j) = (v − λ(u − e_j))²`, and `v ≠ 0`,
  `u ≠ e_j`.
* `no_half_T₀`, `no_half_T₁`, `no_half_T₂`: for the roots `0, ℓ, −3ℓ` the required differences
  include `−ℓ, ℓ, −4ℓ` respectively (tex 2647–2649, 10490–10495).
* `eq_zero_or_tPtF_of_two_nsmul_eq_zero`, `card_ker_two_eq_four`: `E_ℓ(F)[2] = {O, T₀, T₁, T₂}`.
* `card_primaryComponent_two_eq_four`: **the two-primary reduction group has order exactly four**
  (tex 2650, 10496–10499) when `−ℓ, ℓ, −4ℓ` are nonsquares; `primaryComponent_two_eq_ker`: an
  element of order four would give a half of a nonzero two-torsion point.
* `card_eq_card_primaryComponent_two_mul_odd`: in a finite abelian group the index of the
  two-primary component is odd (Cauchy); hence `four_dvd_card_of_nonsquares` and
  `not_eight_dvd_card_of_nonsquares`: `v₂ #E_ℓ(F) = 2` (tex 10500: "This gives
  `v₂(p + 1 − a_p) = 2`").
* `four_dvd_card`: full rational two-torsion gives `4 ∣ #E_ℓ(F)` (tex 10475–10476: "full rational
  two-torsion gives `a_p ≡ p + 1 (mod 4)`").
* `nonsquares_of_one_mod_four`, `card_curveF_zmod_of_conditions`: over `𝔽_p` with `p ≡ 1 (mod 4)`
  and `(ℓ/p) = −1`, the three differences are nonsquares (tex 2643–2649);
  `card_primaryComponent_two_zmod`, `v2_card_zmod`: the same with the Legendre symbol.

All results here are `PROVED`.
-/

namespace ZInQ.Manuscript.RC.KSplit

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Manuscript.PoleRC

variable {F : Type*} [Field F] [DecidableEq F] {ℓ : F}

section Halving

variable (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hℓ : ℓ ≠ 0)
include h2 h3 hℓ

/-- **The halving criterion, necessary direction** (`PROVED`; tex 10490–10493: "A half of a nonzero
two-torsion point with root `e_i` on a split cubic requires both differences `e_i − e_j` to be
squares"; the proof is Version 19's, `quartic_v19.tex` 32244–32248). If `2P = (e_i, 0)` then
`e_i − e_j` is a square for every root `e_j` (trivially so for `e_j = e_i`). -/
theorem isSquare_sub_of_two_nsmul_eq {ei ej : F} (hei : IsRootF ℓ ei) (hej : IsRootF ℓ ej)
    {P : (curveF ℓ).toAffine.Point} (hP : 2 • P = tPtF h2 h3 hℓ hei) :
    IsSquare (ei - ej) := by
  rcases P with _ | ⟨u, v, h⟩
  · -- `2 • O = O ≠ (e_i, 0)`
    rw [show (Point.zero : (curveF ℓ).toAffine.Point) = 0 from rfl, smul_zero] at hP
    exact absurd hP.symm (by unfold tPtF; exact Point.some_ne_zero _)
  · -- the tangent at `P = (u, v)` is not vertical, since `2P ≠ O`
    have hv : v ≠ (curveF ℓ).toAffine.negY u v := by
      intro hv
      rw [two_nsmul, Point.add_self_of_Y_eq hv] at hP
      exact absurd hP.symm (by unfold tPtF; exact Point.some_ne_zero _)
    have hv0 : v ≠ 0 := by
      intro h0; apply hv; rw [curveF_negY, h0, neg_zero]
    rw [two_nsmul, Point.add_self_of_Y_ne hv] at hP
    unfold tPtF at hP
    simp only [Point.some.injEq] at hP
    -- `u ≠ e_j`: otherwise `P = (e_j, 0)`, contradicting `v ≠ 0`
    have hu : u ≠ ej := fun hu => hv0 (y_eq_zero_of_rootF h hej hu)
    have hxy : ¬(u = u ∧ v = (curveF ℓ).toAffine.negY u v) := fun hxy => hv hxy.2
    -- the chord-and-tangent identity at the root `e_j`
    have key := mul_addX_sub_eq_F hej h h hxy
    rw [hP.1] at key
    have hue : u - ej ≠ 0 := sub_ne_zero.mpr hu
    refine ⟨(v - (curveF ℓ).toAffine.slope u u v v * (u - ej)) / (u - ej), ?_⟩
    field_simp
    linear_combination key

/-- **`E_ℓ(F)[2] = {O, T₀, T₁, T₂}`** (`PROVED`; the nonzero rational points of order two are the
three points `(e, 0)`, tex 2647–2648). -/
theorem eq_zero_or_tPtF_of_two_nsmul_eq_zero {P : (curveF ℓ).toAffine.Point} (hP : 2 • P = 0) :
    P = 0 ∨ P = tPtF h2 h3 hℓ (isRootF_zero ℓ) ∨ P = tPtF h2 h3 hℓ (isRootF_ell ℓ) ∨
      P = tPtF h2 h3 hℓ (isRootF_neg3 ℓ) := by
  rcases P with _ | ⟨x, y, h⟩
  · left; rfl
  · right
    have hneg : Point.some x y h = -Point.some x y h :=
      eq_neg_of_add_eq_zero_left (by rw [← two_nsmul]; exact hP)
    rw [Point.neg_some] at hneg
    simp only [Point.some.injEq, curveF_negY, true_and] at hneg
    have hy : y = 0 := by
      have : (2 : F) * y = 0 := by linear_combination hneg
      exact (mul_eq_zero.mp this).resolve_left h2
    have hroot : IsRootF ℓ x := by
      have := (curveF_equation_iff x y).mp h.1
      rw [hy] at this
      unfold IsRootF; linear_combination -this
    rcases isRootF_cases hroot with hx | hx | hx
    · left; exact some_eq_tPtF h2 h3 hℓ (isRootF_zero ℓ) h hx
    · right; left; exact some_eq_tPtF h2 h3 hℓ (isRootF_ell ℓ) h hx
    · right; right; exact some_eq_tPtF h2 h3 hℓ (isRootF_neg3 ℓ) h hx

/-- The two-torsion points are killed by `2`. -/
theorem two_nsmul_tPtF {e : F} (he : IsRootF ℓ e) : 2 • tPtF h2 h3 hℓ he = 0 := by
  unfold tPtF
  rw [two_nsmul, Point.add_self_of_Y_eq (by rw [curveF_negY, neg_zero])]

/-- **`#E_ℓ(F)[2] = 4`** (`PROVED`). -/
theorem card_ker_two_eq_four [Finite (curveF ℓ).toAffine.Point] :
    Nat.card (nsmulAddMonoidHom 2 : (curveF ℓ).toAffine.Point →+ _).ker = 4 := by
  refine le_antisymm ?_ (four_le_card_ker_two h2 h3 hℓ)
  set T₀ := tPtF h2 h3 hℓ (isRootF_zero ℓ)
  set T₁ := tPtF h2 h3 hℓ (isRootF_ell ℓ)
  set T₂ := tPtF h2 h3 hℓ (isRootF_neg3 ℓ)
  have hsub : ((nsmulAddMonoidHom 2 : (curveF ℓ).toAffine.Point →+ _).ker : Set _) ⊆
      ({0, T₀, T₁, T₂} : Set (curveF ℓ).toAffine.Point) := by
    intro P hP
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at hP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact eq_zero_or_tPtF_of_two_nsmul_eq_zero h2 h3 hℓ hP
  calc Nat.card (nsmulAddMonoidHom 2 : (curveF ℓ).toAffine.Point →+ _).ker
      = (((nsmulAddMonoidHom 2 : (curveF ℓ).toAffine.Point →+ _).ker :
          Set (curveF ℓ).toAffine.Point)).ncard := by
        rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    _ ≤ ({0, T₀, T₁, T₂} : Set (curveF ℓ).toAffine.Point).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 4 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        refine (Nat.succ_le_succ (Set.ncard_insert_le _ _)).trans ?_
        refine (Nat.succ_le_succ (Nat.succ_le_succ (Set.ncard_insert_le _ _))).trans ?_
        rw [Set.ncard_singleton]

/-- **Full rational two-torsion gives `4 ∣ #E_ℓ(F)`** (`PROVED`; tex 10475–10476 and
App F tex 9585, 9593–9594: "full rational two-torsion gives `a_p ≡ p + 1 (mod 4)`"). Lagrange's
theorem for the subgroup `E_ℓ(F)[2]` of order four. -/
theorem four_dvd_card [Finite (curveF ℓ).toAffine.Point] :
    4 ∣ Nat.card (curveF ℓ).toAffine.Point := by
  rw [← card_ker_two_eq_four h2 h3 hℓ]
  exact AddSubgroup.card_addSubgroup_dvd_card _

variable (hn0 : ¬ IsSquare (-ℓ)) (hn1 : ¬ IsSquare ℓ) (hn2 : ¬ IsSquare (-4 * ℓ))

include hn0 in
/-- **`T₀ = (0, 0)` has no half** when `−ℓ` is a nonsquare (`PROVED`; tex 2647–2649,
10493–10495: the required difference `0 − ℓ = −ℓ`). -/
theorem no_half_T₀ (P : (curveF ℓ).toAffine.Point) : 2 • P ≠ tPtF h2 h3 hℓ (isRootF_zero ℓ) := by
  intro hP
  have := isSquare_sub_of_two_nsmul_eq h2 h3 hℓ (isRootF_zero ℓ) (isRootF_ell ℓ) hP
  exact hn0 (by rwa [zero_sub] at this)

include hn1 in
/-- **`T₁ = (ℓ, 0)` has no half** when `ℓ` is a nonsquare (`PROVED`; the required difference
`ℓ − 0 = ℓ`). -/
theorem no_half_T₁ (P : (curveF ℓ).toAffine.Point) : 2 • P ≠ tPtF h2 h3 hℓ (isRootF_ell ℓ) := by
  intro hP
  have := isSquare_sub_of_two_nsmul_eq h2 h3 hℓ (isRootF_ell ℓ) (isRootF_zero ℓ) hP
  exact hn1 (by rwa [sub_zero] at this)

include hn2 in
/-- **`T₂ = (−3ℓ, 0)` has no half** when `−4ℓ` is a nonsquare (`PROVED`; the required difference
`−3ℓ − ℓ = −4ℓ`). -/
theorem no_half_T₂ (P : (curveF ℓ).toAffine.Point) :
    2 • P ≠ tPtF h2 h3 hℓ (isRootF_neg3 ℓ) := by
  intro hP
  have := isSquare_sub_of_two_nsmul_eq h2 h3 hℓ (isRootF_neg3 ℓ) (isRootF_ell ℓ) hP
  exact hn2 (by rwa [show -3 * ℓ - ℓ = -4 * ℓ by ring] at this)

include hn0 hn1 hn2 in
/-- **No element of order four** (`PROVED`; tex 10496–10499): if `4Q = O` then `2Q = O`, since
`2Q` is a two-torsion point and none of `T₀, T₁, T₂` has a half. -/
theorem two_nsmul_eq_zero_of_four_nsmul_eq_zero {Q : (curveF ℓ).toAffine.Point}
    (hQ : 4 • Q = 0) : 2 • Q = 0 := by
  have h22 : 2 • (2 • Q) = 0 := by rw [← mul_nsmul']; exact hQ
  rcases eq_zero_or_tPtF_of_two_nsmul_eq_zero h2 h3 hℓ h22 with h | h | h | h
  · exact h
  · exact absurd h (no_half_T₀ h2 h3 hℓ hn0 Q)
  · exact absurd h (no_half_T₁ h2 h3 hℓ hn1 Q)
  · exact absurd h (no_half_T₂ h2 h3 hℓ hn2 Q)

include hn0 hn1 hn2 in
/-- **The two-primary subgroup is `E_ℓ(F)[2]`** (`PROVED`; tex 10496–10499: "If the two-primary
subgroup had order greater than four, its structure as a finite abelian group with exactly four
elements killed by two would give an element of order four, and hence such a half"). An element
with `2^(n+2) P = O` gives `Q = 2^n P` with `4Q = O`, hence `2Q = O`; by induction `2P = O`. -/
theorem primaryComponent_two_eq_ker :
    AddCommGroup.primaryComponent (curveF ℓ).toAffine.Point 2 =
      (nsmulAddMonoidHom 2 : (curveF ℓ).toAffine.Point →+ _).ker := by
  ext P
  rw [AddCommGroup.mem_primaryComponent, AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨n, hn⟩
    -- descend: `2^(m+1) • P = 0 → 2 • P = 0`
    have key : ∀ m : ℕ, 2 ^ (m + 1) • P = 0 → 2 • P = 0 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        intro hm
        apply ih
        have h4 : 4 • (2 ^ m • P) = 0 := by
          rw [← mul_nsmul', show 4 * 2 ^ m = 2 ^ (m + 1 + 1) by ring]; exact hm
        have := two_nsmul_eq_zero_of_four_nsmul_eq_zero h2 h3 hℓ hn0 hn1 hn2 h4
        rw [← mul_nsmul', show 2 * 2 ^ m = 2 ^ (m + 1) by ring] at this
        exact this
    rcases n with _ | n
    · simp only [pow_zero, one_smul] at hn; rw [hn, smul_zero]
    · exact key n hn
  · intro h; exact ⟨1, by rw [pow_one]; exact h⟩

include hn0 hn1 hn2 in
/-- **The two-primary reduction group has order exactly four** (`PROVED`; tex 2650, 10499: "Its
order is consequently exactly four"). -/
theorem card_primaryComponent_two_eq_four [Finite (curveF ℓ).toAffine.Point] :
    Nat.card (AddCommGroup.primaryComponent (curveF ℓ).toAffine.Point 2) = 4 := by
  rw [primaryComponent_two_eq_ker h2 h3 hℓ hn0 hn1 hn2, card_ker_two_eq_four h2 h3 hℓ]

end Halving

/-! ### The two-adic valuation of the order of a finite abelian group -/

/-- **The index of the two-primary component is odd** (`PROVED`; `GLUE`-level textbook fact used at
tex 10500): `#G = #G[2^∞] · m` with `m` odd. If `2` divided the index, Cauchy's theorem would give
`z ∉ G[2^∞]` with `2z ∈ G[2^∞]`, which is absurd. -/
theorem card_eq_card_primaryComponent_two_mul_odd (G : Type*) [AddCommGroup G] [Finite G] :
    ∃ m : ℕ, Odd m ∧ Nat.card G = Nat.card (AddCommGroup.primaryComponent G 2) * m := by
  set P := AddCommGroup.primaryComponent G 2
  refine ⟨Nat.card (G ⧸ P), ?_, ?_⟩
  · rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz⟩ := exists_prime_addOrderOf_dvd_card' 2 h2
    obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective z
    have h2g : (2 • g : G) ∈ P := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul, ← hz, addOrderOf_nsmul_eq_zero]
    obtain ⟨n, hn⟩ := AddCommGroup.mem_primaryComponent.mp h2g
    have hg : g ∈ P := AddCommGroup.mem_primaryComponent.mpr
      ⟨n + 1, by rw [pow_succ, mul_nsmul']; exact hn⟩
    have h0 : (g : G ⧸ P) = 0 := (QuotientAddGroup.eq_zero_iff g).mpr hg
    rw [h0, addOrderOf_zero] at hz
    exact absurd hz (by norm_num)
  · rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup P, mul_comm]

/-- If the two-primary component has order four, then `4 ∣ #G` and `8 ∤ #G` (`PROVED`). -/
theorem four_dvd_and_not_eight_dvd_of_card_primaryComponent (G : Type*) [AddCommGroup G]
    [Finite G] (h4 : Nat.card (AddCommGroup.primaryComponent G 2) = 4) :
    4 ∣ Nat.card G ∧ ¬ 8 ∣ Nat.card G := by
  obtain ⟨m, hm, hG⟩ := card_eq_card_primaryComponent_two_mul_odd G
  rw [hG, h4]
  refine ⟨dvd_mul_right 4 m, fun h8 => ?_⟩
  obtain ⟨j, rfl⟩ := hm
  omega

section Halving'

variable (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hℓ : ℓ ≠ 0)
  (hn0 : ¬ IsSquare (-ℓ)) (hn1 : ¬ IsSquare ℓ) (hn2 : ¬ IsSquare (-4 * ℓ))
include h2 h3 hℓ hn0 hn1 hn2

/-- **`v₂ #E_ℓ(F) = 2`, lower half** (`PROVED`). -/
theorem four_dvd_card_of_nonsquares [Finite (curveF ℓ).toAffine.Point] :
    4 ∣ Nat.card (curveF ℓ).toAffine.Point :=
  (four_dvd_and_not_eight_dvd_of_card_primaryComponent _
    (card_primaryComponent_two_eq_four h2 h3 hℓ hn0 hn1 hn2)).1

/-- **`v₂ #E_ℓ(F) = 2`, upper half: `8 ∤ #E_ℓ(F)`** (`PROVED`; tex 2650–2651, 10499–10500:
"This gives `v₂(p + 1 − a_p) = 2`"). -/
theorem not_eight_dvd_card_of_nonsquares [Finite (curveF ℓ).toAffine.Point] :
    ¬ 8 ∣ Nat.card (curveF ℓ).toAffine.Point :=
  (four_dvd_and_not_eight_dvd_of_card_primaryComponent _
    (card_primaryComponent_two_eq_four h2 h3 hℓ hn0 hn1 hn2)).2

end Halving'

/-! ### Over `𝔽_p` with `p ≡ 1 (mod 4)` and `(ℓ/p) = −1` -/

section ZModP

variable {p : ℕ} [hp : Fact p.Prime]

/-- `2 ≠ 0` and `3 ≠ 0` in `𝔽_p` for `p ≡ 1 (mod 4)` (`PROVED`). -/
theorem two_three_ne_zero_of_one_mod_four (hp4 : p % 4 = 1) :
    (2 : ZMod p) ≠ 0 ∧ (3 : ZMod p) ≠ 0 := by
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp4
  have hp3 : p ≠ 3 := by rintro rfl; norm_num at hp4
  constructor
  · intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  · intro h
    have : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp this)

/-- **The three required differences are nonsquares** (`PROVED`; tex 2649, 10494: "All three are
nonsquares under the chosen conditions"): for `p ≡ 1 (mod 4)` (so `−1` is a square) and `L` a
nonsquare in `𝔽_p`, the elements `−L`, `L`, `−4L` are nonsquares. -/
theorem nonsquares_of_one_mod_four (hp4 : p % 4 = 1) {L : ZMod p} (hL : ¬ IsSquare L) :
    ¬ IsSquare (-L) ∧ ¬ IsSquare L ∧ ¬ IsSquare (-4 * L) := by
  obtain ⟨t, ht⟩ : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  have h2 := (two_three_ne_zero_of_one_mod_four hp4).1
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  have hnegL : ¬ IsSquare (-L) := by
    rintro ⟨s, hs⟩
    apply hL
    refine ⟨s / t, ?_⟩
    field_simp
    linear_combination (-L) * ht + hs
  refine ⟨hnegL, hL, ?_⟩
  rintro ⟨s, hs⟩
  apply hnegL
  refine ⟨s / 2, ?_⟩
  field_simp
  linear_combination hs

/-- **`v₂ #E_ℓ(𝔽_p) = 2` under the seed conditions** (`PROVED`; tex 2643–2651, 10482–10500):
for a prime `p ≡ 1 (mod 4)` and `L ∈ 𝔽_p` a nonsquare (`(ℓ/p) = −1` for `L = ℓ mod p`),
`4 ∣ #E_L(𝔽_p)` and `8 ∤ #E_L(𝔽_p)`. -/
theorem card_curveF_zmod_of_conditions (hp4 : p % 4 = 1) {L : ZMod p} (hL : ¬ IsSquare L) :
    4 ∣ Nat.card (curveF L).toAffine.Point ∧ ¬ 8 ∣ Nat.card (curveF L).toAffine.Point := by
  obtain ⟨h2, h3⟩ := two_three_ne_zero_of_one_mod_four hp4
  have hL0 : L ≠ 0 := by rintro rfl; exact hL ⟨0, by ring⟩
  obtain ⟨hn0, hn1, hn2⟩ := nonsquares_of_one_mod_four hp4 hL
  exact ⟨four_dvd_card_of_nonsquares h2 h3 hL0 hn0 hn1 hn2,
    not_eight_dvd_card_of_nonsquares h2 h3 hL0 hn0 hn1 hn2⟩

/-- **The two-primary part of `E_ℓ(𝔽_p)` has order exactly four** when `p ≡ 1 (mod 4)` and
`(ℓ/p) = −1` (`PROVED`; tex 2643–2650, 10482–10499): the lane's headline statement, with the
Legendre symbol written as a Jacobi symbol at the prime `p`. -/
theorem card_primaryComponent_two_zmod (hp4 : p % 4 = 1) {ℓ : ℤ} (hℓ : jacobiSym ℓ p = -1) :
    Nat.card (AddCommGroup.primaryComponent (curveF ((ℓ : ℤ) : ZMod p)).toAffine.Point 2) = 4 := by
  rw [← jacobiSym.legendreSym.to_jacobiSym] at hℓ
  have hL : ¬ IsSquare ((ℓ : ℤ) : ZMod p) := (legendreSym.eq_neg_one_iff p).mp hℓ
  obtain ⟨h2, h3⟩ := two_three_ne_zero_of_one_mod_four hp4
  have hL0 : ((ℓ : ℤ) : ZMod p) ≠ 0 := by rintro h; exact hL (h ▸ ⟨0, by ring⟩)
  obtain ⟨hn0, hn1, hn2⟩ := nonsquares_of_one_mod_four hp4 hL
  exact card_primaryComponent_two_eq_four h2 h3 hL0 hn0 hn1 hn2

/-- **`v₂ #E_ℓ(𝔽_p) = 2`** when `p ≡ 1 (mod 4)` and `(ℓ/p) = −1` (`PROVED`; tex 10500). -/
theorem v2_card_zmod (hp4 : p % 4 = 1) {ℓ : ℤ} (hℓ : jacobiSym ℓ p = -1) :
    4 ∣ Nat.card (curveF ((ℓ : ℤ) : ZMod p)).toAffine.Point ∧
      ¬ 8 ∣ Nat.card (curveF ((ℓ : ℤ) : ZMod p)).toAffine.Point := by
  rw [← jacobiSym.legendreSym.to_jacobiSym] at hℓ
  exact card_curveF_zmod_of_conditions hp4 ((legendreSym.eq_neg_one_iff p).mp hℓ)

end ZModP

end ZInQ.Manuscript.RC.KSplit
