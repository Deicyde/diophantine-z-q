import ZInQKernel.Model.Heights.SearchSound
import ZInQKernel.Model.Heights.SearchKernel
import ZInQKernel.Model.Heights.Translates

/-!
# The finite search for small points on `C`

Blueprint: `model/heights/small-height-search.md`.

`f(x) = x³ - δ² x`. `𝒬` is the set of integer triples `(a, b, c)` with `1 ≤ a ≤ 81`,
`|b| ≤ 162`, `|c| ≤ 81`, `gcd(a, b, c) = 1` and `b² - 4ac = 2k²` for an integer `1 ≤ k ≤ 162`;
`𝒳₂` is the set of the roots `(-b ± k s)/(2a)`, and `𝒳₁` the set of rationals `p/q` with
`gcd(p, q) = 1`, `|p| ≤ 9`, `1 ≤ q ≤ 9`. Then `|𝒬| = 7004`, `|𝒳₂| = 14008`, `|𝒳₁| = 111`, and for
`x ∈ 𝒳₁ ∪ 𝒳₂`, `f(x)` is a square in `K₀` iff `x ∈ {0, δ, -δ, 1 + s, 23 - 17s, 2 + 4s, (5 - 4s)/2}`.

The finite computation is `Search.searchCheck_eq_true` (kernel, about a minute); the rest is the
soundness of the checker.
-/

namespace ZInQ

open Search

/-- `f(x) = x³ - δ² x`, the right side of `C : y² = f(x)`. -/
def fC (x : K0) : K0 := x ^ 3 - delta ^ 2 * x

/-- The set `𝒬` of primitive quadratics `a X² + b X + c` of the search box. -/
def searchQ : Finset (ℤ × ℤ × ℤ) :=
  (Finset.Icc (1 : ℤ) 81 ×ˢ Finset.Icc (-162 : ℤ) 162 ×ˢ Finset.Icc (-81 : ℤ) 81).filter
    fun t => Int.gcd (Int.gcd t.1 t.2.1) t.2.2 = 1 ∧
      ∃ k ∈ Finset.Icc (1 : ℤ) 162, t.2.1 ^ 2 - 4 * t.1 * t.2.2 = 2 * k ^ 2

-- Keep the elaborator from evaluating the box when it checks membership hypotheses.
attribute [irreducible] searchQ

/-- The root `(-b + η k s)/(2a)` of `a X² + b X + c`, `k = √((b² - 4ac)/2)`. -/
def qRoot (t : ℤ × ℤ × ℤ) (η : ℤ) : K0 :=
  ⟨((-t.2.1 : ℤ) : ℚ) / (2 * (t.1 : ℚ)),
    ((η * Int.sqrt ((t.2.1 ^ 2 - 4 * t.1 * t.2.2) / 2) : ℤ) : ℚ) / (2 * (t.1 : ℚ))⟩

/-- The set `𝒳₂` of the roots `(-b ± k s)/(2a)`, `(a, b, c) ∈ 𝒬`. -/
def searchX2 : Finset K0 := (searchQ ×ˢ ({1, -1} : Finset ℤ)).image fun p => qRoot p.1 p.2

/-- The set `𝒳₁` of rationals `p/q` with `gcd(p, q) = 1`, `|p| ≤ 9`, `1 ≤ q ≤ 9`. -/
def searchX1 : Finset ℚ :=
  ((Finset.Icc (-9 : ℤ) 9 ×ˢ Finset.Icc (1 : ℤ) 9).filter fun p => Int.gcd p.1 p.2 = 1).image
    fun p => (p.1 : ℚ) / p.2

/-- The abscissas `0, δ, -δ, 1 + s, 23 - 17s, 2 + 4s, (5 - 4s)/2`. -/
def smallSurvivors : Finset K0 := {0, delta, -delta, ⟨1, 1⟩, ⟨23, -17⟩, ⟨2, 4⟩, ⟨5 / 2, -2⟩}

/-! ### The search box `𝒬` and `qList` -/

theorem searchCheck_parts :
    qList.length = 7004 ∧ (∀ t ∈ qList, tupleOK t = true) ∧ ratCheck = true := by
  have h := searchCheck_eq_true
  simp only [searchCheck, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem mem_searchQ_iff (a b c : ℤ) :
    (a, b, c) ∈ searchQ ↔ ∃ t ∈ qList, a = t.1 ∧ b = 2 * ((t.2.1 : ℤ) - 81) ∧
      c * a = ((t.2.1 : ℤ) - 81) ^ 2 - 2 * (t.2.2 : ℤ) ^ 2 := by
  simp only [searchQ, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, ⟨hc1, hc2⟩⟩, hgcd, k, ⟨hk1, hk2⟩, hk⟩
    have hbe : Even (b ^ 2) := ⟨k ^ 2 + 2 * a * c, by linear_combination hk⟩
    obtain ⟨b', rfl⟩ := (Int.even_pow.mp hbe).1
    have hk2' : k ^ 2 = 2 * (b' ^ 2 - a * c) :=
      Int.eq_of_mul_eq_mul_left (by norm_num : (2 : ℤ) ≠ 0) (by linear_combination -hk)
    have hke : Even (k ^ 2) := ⟨b' ^ 2 - a * c, by linear_combination hk2'⟩
    obtain ⟨K, rfl⟩ := (Int.even_pow.mp hke).1
    have hca : c * a = b' ^ 2 - 2 * K ^ 2 :=
      Int.eq_of_mul_eq_mul_left (by norm_num : (4 : ℤ) ≠ 0) (by linear_combination -hk)
    refine ⟨(a.toNat, (b' + 81).toNat, K.toNat), ?_, by simp; omega, ?_, ?_⟩
    · rw [mem_qList_iff]
      have e1 : ((b' + 81).toNat : ℤ) - 81 = b' := by omega
      have e2 : ((a.toNat : ℕ) : ℤ) = a := by omega
      have e3 : ((K.toNat : ℕ) : ℤ) = K := by omega
      refine ⟨by omega, by omega, by omega, by omega, by omega, c, ?_, ?_, ?_⟩
      · rw [e1, e2, e3]; exact hca
      · rw [abs_le]; constructor <;> omega
      · rw [e1, e2, show 2 * b' = b' + b' by ring]; exact hgcd
    · simp only; omega
    · simp only
      have e1 : ((b' + 81).toNat : ℤ) - 81 = b' := by omega
      have e3 : ((K.toNat : ℕ) : ℤ) = K := by omega
      rw [e1, e3]; exact hca
  · rintro ⟨⟨a', i, K⟩, ht, rfl, rfl, hc⟩
    obtain ⟨ha1, ha2, hi, hK1, hK2, c', hc', habs, hgcd⟩ := mem_qList_iff.mp ht
    simp only at hc ⊢
    have hcc : c = c' := by
      have : (c - c') * (a' : ℤ) = 0 := by linear_combination hc - hc'
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · omega
    subst hcc
    refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩, ?_, 2 * K, ⟨by omega, by omega⟩, ?_⟩
    · rw [abs_le] at habs; exact ⟨by omega, by omega⟩
    · exact hgcd
    · linear_combination -4 * hc

/-- The triple `(a, b, c)` of a tuple `(a, i, K)` of `qList`. -/
def toTriple (t : ℕ × ℕ × ℕ) : ℤ × ℤ × ℤ :=
  (t.1, 2 * ((t.2.1 : ℤ) - 81), (((t.2.1 : ℤ) - 81) ^ 2 - 2 * (t.2.2 : ℤ) ^ 2) / t.1)

theorem toTriple_spec {t : ℕ × ℕ × ℕ} (ht : t ∈ qList) :
    (toTriple t).2.2 * t.1 = ((t.2.1 : ℤ) - 81) ^ 2 - 2 * (t.2.2 : ℤ) ^ 2 := by
  obtain ⟨a, i, K⟩ := t
  obtain ⟨ha1, -, -, -, -, c, hc, -, -⟩ := mem_qList_iff.mp ht
  simp only [toTriple]
  rw [← hc, Int.mul_ediv_cancel _ (by omega)]

theorem searchQ_eq : searchQ = (qList.map toTriple).toFinset := by
  ext ⟨a, b, c⟩
  rw [mem_searchQ_iff, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl, rfl, hc⟩
    refine ⟨t, ht, ?_⟩
    have := toTriple_spec ht
    simp only [toTriple, Prod.mk.injEq, true_and] at this ⊢
    have h1 : (1 : ℤ) ≤ t.1 := by
      obtain ⟨a, i, K⟩ := t; exact_mod_cast (mem_qList_iff.mp ht).1
    rw [← hc, Int.mul_ediv_cancel _ (by omega)]
  · rintro ⟨t, ht, he⟩
    refine ⟨t, ht, ?_⟩
    have := toTriple_spec ht
    rw [he] at this
    simp only [toTriple, Prod.mk.injEq] at he this
    rw [he.1] at this
    exact ⟨he.1.symm, he.2.1.symm, this⟩

theorem toTriple_injOn : ∀ x ∈ qList, ∀ y ∈ qList, toTriple x = toTriple y → x = y := by
  rintro ⟨a, i, K⟩ hx ⟨a', i', K'⟩ hy he
  have hx' := toTriple_spec hx
  have hy' := toTriple_spec hy
  obtain ⟨-, -, -, hK, -⟩ := mem_qList_iff.mp hx
  obtain ⟨-, -, -, hK', -⟩ := mem_qList_iff.mp hy
  simp only [toTriple, Prod.mk.injEq] at he hx' hy'
  obtain ⟨h1, h2, h3⟩ := he
  have ha : a = a' := by exact_mod_cast h1
  have hi : i = i' := by omega
  subst ha hi
  rw [h3] at hx'
  have hKK : (K : ℤ) ^ 2 = (K' : ℤ) ^ 2 := by linarith
  have : (K : ℤ) = K' := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hKK with h | h
    · exact h
    · omega
  have : K = K' := by exact_mod_cast this
  rw [this]

/-- `|𝒬| = 7004`. -/
theorem card_searchQ : searchQ.card = 7004 := by
  rw [searchQ_eq, List.toFinset_card_of_nodup (qList_nodup.map_on toTriple_injOn), List.length_map,
    searchCheck_parts.1]

/-! ### The roots -/

theorem mem_searchQ_props (a b c : ℤ) (ht : (a, b, c) ∈ searchQ) :
    1 ≤ a ∧ Int.gcd (Int.gcd a b) c = 1 ∧
      ∃ k : ℤ, 1 ≤ k ∧ k ≤ 162 ∧ b ^ 2 - 4 * a * c = 2 * k ^ 2 ∧
        Int.sqrt ((b ^ 2 - 4 * a * c) / 2) = k := by
  simp only [searchQ, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht
  obtain ⟨⟨⟨ha1, -⟩, -, -⟩, hgcd, k, ⟨hk1, hk2⟩, hk⟩ := ht
  refine ⟨ha1, hgcd, k, hk1, hk2, hk, ?_⟩
  rw [hk, Int.mul_ediv_cancel_left _ (by norm_num), pow_two, Int.sqrt_eq]
  omega

/-- Bézout for three integers. -/
theorem exists_bezout_three {a b c : ℤ} (h : Int.gcd (Int.gcd a b) c = 1) :
    ∃ x y z : ℤ, x * a + y * b + z * c = 1 := by
  have h1 := Int.gcd_eq_gcd_ab (Int.gcd a b : ℤ) c
  have h2 := Int.gcd_eq_gcd_ab a b
  rw [h, Nat.cast_one] at h1
  refine ⟨Int.gcdA a b * Int.gcdA (Int.gcd a b) c, Int.gcdB a b * Int.gcdA (Int.gcd a b) c,
    Int.gcdB (Int.gcd a b) c, ?_⟩
  rw [h1, h2]; ring

theorem qRoot_inj {a b c η a' b' c' η' : ℤ} (ht : (a, b, c) ∈ searchQ) (hη : η = 1 ∨ η = -1)
    (ht' : (a', b', c') ∈ searchQ) (hη' : η' = 1 ∨ η' = -1)
    (he : qRoot (a, b, c) η = qRoot (a', b', c') η') : ((a, b, c), η) = ((a', b', c'), η') := by
  obtain ⟨ha, hg, k, hk1, -, hk, hks⟩ := mem_searchQ_props a b c ht
  obtain ⟨ha', hg', k', hk1', -, hk', hks'⟩ := mem_searchQ_props a' b' c' ht'
  simp only [qRoot, hks, hks'] at he
  have hre := congrArg QuadraticAlgebra.re he
  have him := congrArg QuadraticAlgebra.im he
  have haq : (0 : ℚ) < a := by exact_mod_cast ha
  have haq' : (0 : ℚ) < a' := by exact_mod_cast ha'
  rw [div_eq_div_iff (by positivity) (by positivity)] at hre him
  push_cast at hre him
  have hb : b * a' = b' * a := by
    have : ((b * a' : ℤ) : ℚ) = ((b' * a : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have hk2 : η * k * a' = η' * k' * a := by
    have : ((η * k * a' : ℤ) : ℚ) = ((η' * k' * a : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  -- the signs agree
  have hηη : η = η' := by
    have hp : 0 < k * a' := by positivity
    have hp' : 0 < k' * a := by positivity
    rcases hη with rfl | rfl <;> rcases hη' with rfl | rfl
    · rfl
    · nlinarith
    · nlinarith
    · rfl
  subst hηη
  have hkk : k * a' = k' * a := by
    rcases hη with rfl | rfl
    · linarith
    · linarith
  -- `c a' = c' a`
  have hc : c * a' = c' * a := by
    have e : 4 * a * a' * (c * a' - c' * a) = 0 := by
      linear_combination (-a' ^ 2) * hk + (a ^ 2) * hk' + (b * a' + b' * a) * hb -
        2 * (k * a' + k' * a) * hkk
    rcases mul_eq_zero.mp e with h | h
    · have : 4 * a * a' ≠ 0 := by positivity
      exact absurd h this
    · linarith
  -- `a ∣ a'` and `a' ∣ a`
  have hdvd : a ∣ a' := by
    obtain ⟨x, y, z, hxyz⟩ := exists_bezout_three hg
    exact ⟨x * a' + y * b' + z * c', by linear_combination -a' * hxyz + y * hb + z * hc⟩
  have hdvd' : a' ∣ a := by
    obtain ⟨x, y, z, hxyz⟩ := exists_bezout_three hg'
    exact ⟨x * a + y * b + z * c, by linear_combination -a * hxyz - y * hb - z * hc⟩
  have haa : a = a' := Int.dvd_antisymm (by omega) (by omega) hdvd hdvd'
  subst haa
  have hbb : b = b' := by
    have : (b - b') * a = 0 := by linear_combination hb
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · omega
  have hcc : c = c' := by
    have : (c - c') * a = 0 := by linear_combination hc
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · omega
  rw [hbb, hcc]

theorem qRoot_injOn :
    Set.InjOn (fun p : (ℤ × ℤ × ℤ) × ℤ => qRoot p.1 p.2)
      (↑(searchQ ×ˢ ({1, -1} : Finset ℤ)) : Set ((ℤ × ℤ × ℤ) × ℤ)) := by
  intro p hp q hq he
  rw [Finset.mem_coe, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] at hp hq
  obtain ⟨⟨a, b, c⟩, η⟩ := p
  obtain ⟨⟨a', b', c'⟩, η'⟩ := q
  dsimp only at hp hq he
  exact qRoot_inj (a := a) (b := b) (c := c) (a' := a') (b' := b') (c' := c') hp.1 hp.2 hq.1 hq.2 he

/-- `|𝒳₂| = 14008`: the `2 · 7004` roots are distinct. -/
theorem card_searchX2 : searchX2.card = 14008 := by
  have h := Finset.card_image_of_injOn qRoot_injOn
  rw [Finset.card_product, card_searchQ, Finset.card_pair (by norm_num)] at h
  exact h

/-- `|𝒳₁| = 111`. -/
theorem card_searchX1 : searchX1.card = 111 := by
  rw [searchX1, Finset.card_image_of_injOn]
  · decide +kernel
  · rintro ⟨p, q⟩ h1 ⟨p', q'⟩ h2 he
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_Icc, Set.mem_ofPred_eq] at h1 h2
    have := Rat.div_int_inj (by omega) (by omega) h1.2 h2.2 he
    rw [this.1, this.2]

/-! ### The square tests -/

theorem fC_mk (p q : ℚ) :
    fC ⟨p, q⟩ = ⟨p ^ 3 + 6 * p * q ^ 2 - (11 * p - 12 * q), 3 * p ^ 2 * q + 2 * q ^ 3 - (11 * q - 6 * p)⟩ := by
  rw [fC, delta_sq]
  ext <;> simp [pow_succ] <;> ring

/-- `a⁴ f((U + V s)/a) = u + v s` with `(u, v) = alpha a U V`. -/
theorem fC_mul_pow (a U V : ℤ) (ha : a ≠ 0) :
    fC ⟨(U : ℚ) / a, (V : ℚ) / a⟩ * (a : K0) ^ 4 =
      ⟨((alpha a U V).1 : ℚ), ((alpha a U V).2 : ℚ)⟩ := by
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have h4 : (a : K0) ^ 4 = ⟨(a : ℚ) ^ 4, 0⟩ := by
    ext <;> simp [pow_succ]
  rw [fC_mk, h4, K0.mk_mul_mk']
  simp only [alpha]
  ext
  · simp only [mul_zero, add_zero]; push_cast; field_simp
  · simp only [mul_zero]; push_cast; field_simp; ring

theorem not_isSquare_fC (a U V : ℤ) (ha : a ≠ 0)
    (h : possSq (alpha a U V).1 (alpha a U V).2 = false) :
    ¬ IsSquare (fC ⟨(U : ℚ) / a, (V : ℚ) / a⟩) := by
  intro hsq
  have : IsSquare (fC ⟨(U : ℚ) / a, (V : ℚ) / a⟩ * (a : K0) ^ 4) :=
    hsq.mul ⟨(a : K0) ^ 2, by ring⟩
  rw [fC_mul_pow a U V ha] at this
  rw [possSq_of_isSquare this] at h
  exact absurd h (by simp)

theorem isSquare_fC_of_point {x y : K0} (h : curveC.toAffine.Nonsingular x y) :
    IsSquare (fC x) := by
  have he := (curveC_equation_iff x y).mp h.1
  exact ⟨y, by rw [fC, ← he, pow_two]⟩

theorem isSquare_fC_of_mem {x : K0} (hx : x ∈ smallSurvivors) : IsSquare (fC x) := by
  simp only [smallSurvivors, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by simp [fC]⟩
  · exact ⟨0, by simp [fC]; ring⟩
  · exact ⟨0, by simp [fC]; ring⟩
  · exact ⟨2 * sqrt2, by rw [fC, ← pow_two, pointR_curve]; rfl⟩
  · obtain ⟨y, h, -⟩ := x_pointR_add_cT0; exact isSquare_fC_of_point h
  · obtain ⟨y, h, -⟩ := x_pointR_add_cTdelta; exact isSquare_fC_of_point h
  · obtain ⟨y, h, -⟩ := x_pointR_add_cTnegdelta; exact isSquare_fC_of_point h

/-- The roots of `𝒳₂` in terms of the tuples of `qList`. -/
theorem qRoot_eq {a b c η : ℤ} (ht : (a, b, c) ∈ searchQ) :
    ∃ t ∈ qList, a = t.1 ∧
      qRoot (a, b, c) η = ⟨((81 - (t.2.1 : ℤ) : ℤ) : ℚ) / a, ((η * t.2.2 : ℤ) : ℚ) / a⟩ := by
  obtain ⟨t, htq, rfl, rfl, hc⟩ := (mem_searchQ_iff a b c).mp ht
  obtain ⟨ha1, -⟩ := mem_qList_iff.mp htq
  refine ⟨t, htq, rfl, ?_⟩
  have hd : (2 * ((t.2.1 : ℤ) - 81)) ^ 2 - 4 * t.1 * c = 2 * (2 * t.2.2) ^ 2 := by
    linear_combination -4 * hc
  have hs : Int.sqrt (((2 * ((t.2.1 : ℤ) - 81)) ^ 2 - 4 * t.1 * c) / 2) = 2 * t.2.2 := by
    rw [hd, Int.mul_ediv_cancel_left _ (by norm_num), pow_two, Int.sqrt_eq]
    omega
  have haq : ((t.1 : ℤ) : ℚ) ≠ 0 := by
    have : (1 : ℤ) ≤ t.1 := by exact_mod_cast ha1
    exact_mod_cast (show (t.1 : ℤ) ≠ 0 by omega)
  simp only [qRoot, hs]
  ext
  · push_cast; field_simp; ring
  · push_cast; field_simp

theorem survivor_roots {a i K : ℕ} {e : Bool} (h : (a, i, K, e) ∈ survivorTuples) :
    (⟨((81 - (i : ℤ) : ℤ) : ℚ) / (a : ℤ), (((bif e then 1 else -1) * K : ℤ) : ℚ) / (a : ℤ)⟩ : K0) ∈
      smallSurvivors := by
  simp only [survivorTuples, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  simp only [smallSurvivors, Finset.mem_insert, Finset.mem_singleton]
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · right; right; right; right; left; ext <;> norm_num
  · right; right; right; right; right; right; ext <;> norm_num
  · right; left; ext <;> norm_num [delta]
  · right; right; right; right; right; left; ext <;> norm_num
  · right; right; right; left; ext <;> norm_num
  · right; right; left; ext <;> norm_num [delta]

/-- The search on `𝒳₂`. -/
theorem isSquare_fC_iff_of_mem_searchX2 {x : K0} (hx : x ∈ searchX2) :
    IsSquare (fC x) ↔ x ∈ smallSurvivors := by
  refine ⟨fun hsq => ?_, isSquare_fC_of_mem⟩
  simp only [searchX2, Finset.mem_image, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton] at hx
  obtain ⟨⟨⟨a, b, c⟩, η⟩, ⟨ht, hη⟩, rfl⟩ := hx
  obtain ⟨⟨a', i, K⟩, htq, rfl, hroot⟩ := qRoot_eq (η := η) ht
  simp only at hroot ⊢
  rw [hroot] at hsq ⊢
  have hok := searchCheck_parts.2.1 _ htq
  have ha : ((a' : ℕ) : ℤ) ≠ 0 := by
    have := (mem_qList_iff.mp htq).1; omega
  simp only [tupleOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok
  rcases hη with rfl | rfl
  · rcases hok.1 with h | h
    · rw [one_mul] at hsq
      exact absurd hsq (not_isSquare_fC a' (81 - i) K ha h)
    · have := survivor_roots (List.mem_of_elem_eq_true h)
      simp only [Bool.cond_true] at this
      exact this
  · rcases hok.2 with h | h
    · rw [neg_one_mul] at hsq
      exact absurd hsq (not_isSquare_fC a' (81 - i) (-K) ha h)
    · have := survivor_roots (List.mem_of_elem_eq_true h)
      simp only [Bool.cond_false] at this
      exact this

theorem ratOK_of_mem {p q : ℤ} (hp : -9 ≤ p ∧ p ≤ 9) (hq : 1 ≤ q ∧ q ≤ 9) : ratOK p q = true := by
  have h := searchCheck_parts.2.2
  simp only [ratCheck, List.all_eq_true, List.mem_range] at h
  have := h (p + 9).toNat (by omega) (q - 1).toNat (by omega)
  have e1 : (((p + 9).toNat : ℕ) : ℤ) - 9 = p := by omega
  have e2 : (((q - 1).toNat : ℕ) : ℤ) + 1 = q := by omega
  rwa [e1, e2] at this

/-- The search on `𝒳₁`. -/
theorem isSquare_fC_iff_of_mem_searchX1 {r : ℚ} (hr : r ∈ searchX1) :
    IsSquare (fC (r : K0)) ↔ (r : K0) ∈ smallSurvivors := by
  refine ⟨fun hsq => ?_, isSquare_fC_of_mem⟩
  simp only [searchX1, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc] at hr
  obtain ⟨⟨p, q⟩, ⟨⟨hp, hq⟩, hpq⟩, rfl⟩ := hr
  have hok := ratOK_of_mem hp hq
  simp only [ratOK, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hok
  have hq0 : q ≠ 0 := by omega
  have hqq : (q : ℚ) ≠ 0 := by exact_mod_cast hq0
  have hrK : (((p : ℚ) / q : ℚ) : K0) = ⟨((p : ℤ) : ℚ) / (q : ℤ), ((0 : ℤ) : ℚ) / (q : ℤ)⟩ := by
    ext
    · simp; field_simp
    · simp
  rcases hok with (h | h) | h
  · exfalso
    rw [← Bool.not_eq_true, Nat.beq_eq] at h
    exact h hpq
  · subst h
    simp [smallSurvivors]
  · have e : alpha q p 0 = (q * p * p * p - 11 * p * q * q * q, 6 * p * q * q * q) := by
      simp only [alpha, Prod.mk.injEq]; constructor <;> ring
    rw [hrK] at hsq
    exact absurd hsq (not_isSquare_fC q p 0 hq0 (by rw [e]; exact h))

/-- **The finite search for small points on `C`.** `|𝒬| = 7004`, the roots `(-b ± k s)/(2a)`
are `14008` distinct elements of `K₀`, `|𝒳₁| = 111`, and for `x ∈ 𝒳₁ ∪ 𝒳₂`, `f(x)` is a square
in `K₀` iff `x ∈ {0, δ, -δ, 1 + s, 23 - 17s, 2 + 4s, (5 - 4s)/2}`. -/
theorem smallHeight_search :
    searchQ.card = 7004 ∧ searchX2.card = 14008 ∧ searchX1.card = 111 ∧
      ∀ x ∈ searchX1.image (fun r : ℚ => (r : K0)) ∪ searchX2,
        (IsSquare (fC x) ↔ x ∈ smallSurvivors) := by
  refine ⟨card_searchQ, card_searchX2, card_searchX1, fun x hx => ?_⟩
  rcases Finset.mem_union.mp hx with h | h
  · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp h
    exact isSquare_fC_iff_of_mem_searchX1 hr
  · exact isSquare_fC_iff_of_mem_searchX2 h

end ZInQ
