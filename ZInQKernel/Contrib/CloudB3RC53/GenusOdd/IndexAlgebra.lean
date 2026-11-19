import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Defs

/-!
# GenusOdd: index valuations in rank-one groups (PROVED algebra behind (3.4))

Abstract facts about `twoDivIndex` (the index valuation `j` of tex L2416, L9422–9425) used to turn
the two height identities of Cai–Shu–Tian into the valuation identity (3.4) (tex L2427–2439):

* `le_twoDivIndex_iff`: `e ≤ j_M(x)` iff `x ≡ 2^e G` modulo torsion for some `G ∈ M` (for `x ∈ M`).
* `twoDivIndex_add_torsion`, `twoDivIndex_two_nsmul`, `twoDivIndex_odd_zsmul`, `twoDivIndex_zsmul`:
  `j(x + t) = j(x)`, `j(2x) = j(x) + 1`, `j(m x) = j(x)` for odd `m`, `j(n x) = j(x) + v₂ n`.
* `twoDivIndex_ne_top`: `j(x) < ∞` for nontorsion `x` when a quadratic height with finite sublevel
  sets is positive on nontorsion points (Northcott).
* `twoDivIndex_transfer`: if `ψ : R → A` is injective, `ψ(R) ⊆ M` and `2M ⊆ ψ(R) + torsion` ("the
  rational free line has index at most two in its native lattice", tex L2433–2435), and
  `2P ≡ ψ(Q)` modulo torsion, then `j_R(Q) - 1 ≤ j_M(P) ≤ j_R(Q)`.
* `index_two_of_decomposition`: Elliot's "conjugation fixes the free class, and the norm makes twice
  the class rational" (tex L2433–2435) in abstract form: `2x = (x + τx) + (x - τx)`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

variable {A : Type*} [AddCommGroup A]

/-! ### Torsion bookkeeping -/

theorem isOfFinAddOrder_sub {x y : A} (hx : IsOfFinAddOrder x) (hy : IsOfFinAddOrder y) :
    IsOfFinAddOrder (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem isOfFinAddOrder_of_nsmul {x : A} {n : ℕ} (hn : n ≠ 0) (h : IsOfFinAddOrder (n • x)) :
    IsOfFinAddOrder x := by
  rw [isOfFinAddOrder_iff_nsmul_eq_zero] at h ⊢
  obtain ⟨m, hm, hmx⟩ := h
  exact ⟨m * n, Nat.mul_pos hm (Nat.pos_of_ne_zero hn), by rw [← smul_smul]; exact hmx⟩

theorem isOfFinAddOrder_of_zsmul {x : A} {n : ℤ} (hn : n ≠ 0) (h : IsOfFinAddOrder (n • x)) :
    IsOfFinAddOrder x := by
  rcases Int.natAbs_eq n with hn' | hn'
  · rw [hn', natCast_zsmul] at h
    exact isOfFinAddOrder_of_nsmul (Int.natAbs_ne_zero.mpr hn) h
  · rw [hn', neg_smul, natCast_zsmul] at h
    exact isOfFinAddOrder_of_nsmul (Int.natAbs_ne_zero.mpr hn) (by simpa using h.neg)

theorem isOfFinAddOrder_map {B : Type*} [AddCommGroup B] (f : A →+ B) {x : A}
    (h : IsOfFinAddOrder x) : IsOfFinAddOrder (f x) := by
  rw [isOfFinAddOrder_iff_nsmul_eq_zero] at h ⊢
  obtain ⟨n, hn, hx⟩ := h
  exact ⟨n, hn, by rw [← map_nsmul, hx, map_zero]⟩

theorem isOfFinAddOrder_of_map {B : Type*} [AddCommGroup B] (f : A →+ B)
    (hf : Function.Injective f) {x : A} (h : IsOfFinAddOrder (f x)) : IsOfFinAddOrder x := by
  rw [isOfFinAddOrder_iff_nsmul_eq_zero] at h ⊢
  obtain ⟨n, hn, hx⟩ := h
  exact ⟨n, hn, hf (by rw [map_nsmul, hx, map_zero])⟩

/-! ### The characterization of `twoDivIndex` -/

/-- The property behind `twoDivIndex`. -/
def DivProp (M : AddSubgroup A) (x : A) (e : ℕ) : Prop :=
  ∃ G ∈ M, IsOfFinAddOrder (x - (2 ^ e : ℕ) • G)

theorem divProp_mono {M : AddSubgroup A} {x : A} {e e' : ℕ} (hle : e' ≤ e) (h : DivProp M x e) :
    DivProp M x e' := by
  obtain ⟨G, hG, ht⟩ := h
  refine ⟨(2 ^ (e - e') : ℕ) • G, M.nsmul_mem hG _, ?_⟩
  rwa [smul_smul, ← pow_add, Nat.add_sub_cancel' hle]

theorem divProp_zero {M : AddSubgroup A} {x : A} (hx : x ∈ M) : DivProp M x 0 :=
  ⟨x, hx, by simp⟩

theorem le_twoDivIndex_iff {M : AddSubgroup A} {x : A} (hx : x ∈ M) (e : ℕ) :
    (e : ℕ∞) ≤ twoDivIndex M x ↔ DivProp M x e := by
  constructor
  · intro he
    by_contra hne
    have hlt : ∀ e', DivProp M x e' → e' < e := fun e' h' =>
      lt_of_not_ge fun hge => hne (divProp_mono hge h')
    have he0 : e ≠ 0 := by
      rintro rfl; exact hne (divProp_zero hx)
    have hle : twoDivIndex M x ≤ ((e - 1 : ℕ) : ℕ∞) := by
      refine iSup₂_le fun e' h' => ?_
      exact_mod_cast Nat.le_sub_one_of_lt (hlt e' h')
    have := he.trans hle
    have : e ≤ e - 1 := by exact_mod_cast this
    omega
  · intro h
    exact le_iSup₂_of_le (f := fun (e : ℕ) (_ : DivProp M x e) => (e : ℕ∞)) e h le_rfl

theorem twoDivIndex_eq_of_iff {M M' : AddSubgroup A} {x x' : A} (hx : x ∈ M) (hx' : x' ∈ M')
    (h : ∀ e, DivProp M x e ↔ DivProp M' x' e) : twoDivIndex M x = twoDivIndex M' x' := by
  refine le_antisymm ?_ ?_
  · refine ENat.forall_natCast_le_iff_le.mp fun e he => ?_
    exact (le_twoDivIndex_iff hx' e).mpr ((h e).mp ((le_twoDivIndex_iff hx e).mp he))
  · refine ENat.forall_natCast_le_iff_le.mp fun e he => ?_
    exact (le_twoDivIndex_iff hx e).mpr ((h e).mpr ((le_twoDivIndex_iff hx' e).mp he))

/-! ### Behaviour under torsion, doubling and odd multiples (in the whole group) -/

theorem twoDivIndex_add_torsion (x t : A) (ht : IsOfFinAddOrder t) :
    twoDivIndex ⊤ (x + t) = twoDivIndex ⊤ x := by
  refine twoDivIndex_eq_of_iff (AddSubgroup.mem_top _) (AddSubgroup.mem_top _) fun e => ?_
  constructor
  · rintro ⟨G, -, hG⟩
    refine ⟨G, AddSubgroup.mem_top _, ?_⟩
    have := isOfFinAddOrder_sub hG ht
    rwa [show x + t - (2 ^ e : ℕ) • G - t = x - (2 ^ e : ℕ) • G by abel] at this
  · rintro ⟨G, -, hG⟩
    refine ⟨G, AddSubgroup.mem_top _, ?_⟩
    have := hG.add ht
    rwa [show x - (2 ^ e : ℕ) • G + t = x + t - (2 ^ e : ℕ) • G by abel] at this

theorem divProp_two_nsmul_succ (x : A) (e : ℕ) :
    DivProp ⊤ ((2 : ℕ) • x) (e + 1) ↔ DivProp ⊤ x e := by
  constructor
  · rintro ⟨G, -, hG⟩
    refine ⟨G, AddSubgroup.mem_top _, isOfFinAddOrder_of_nsmul (n := 2) (by norm_num) ?_⟩
    rwa [nsmul_sub, smul_smul, ← pow_succ']
  · rintro ⟨G, -, hG⟩
    refine ⟨G, AddSubgroup.mem_top _, ?_⟩
    have := hG.nsmul (n := 2)
    rwa [nsmul_sub, smul_smul, ← pow_succ'] at this

theorem twoDivIndex_two_nsmul (x : A) :
    twoDivIndex ⊤ ((2 : ℕ) • x) = twoDivIndex ⊤ x + 1 := by
  have hx := AddSubgroup.mem_top x
  have h2x := AddSubgroup.mem_top ((2 : ℕ) • x)
  refine le_antisymm ?_ ?_
  · refine ENat.forall_natCast_le_iff_le.mp fun e he => ?_
    rcases e with _ | e
    · simp
    · have := (divProp_two_nsmul_succ x e).mp ((le_twoDivIndex_iff h2x _).mp he)
      have := (le_twoDivIndex_iff hx e).mpr this
      push_cast
      exact add_le_add this le_rfl
  · rcases eq_or_ne (twoDivIndex ⊤ x) ⊤ with htop | htop
    · rw [htop, top_add]
      refine top_le_iff.mp ?_ |>.ge
      refine ENat.forall_natCast_le_iff_le.mp fun e _ => ?_
      rcases e with _ | e
      · simp
      · exact (le_twoDivIndex_iff h2x _).mpr ((divProp_two_nsmul_succ x e).mpr
          ((le_twoDivIndex_iff hx e).mp (by rw [htop]; exact le_top)))
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
      rw [← hn]
      have := (le_twoDivIndex_iff hx n).mp (by rw [hn])
      have := (le_twoDivIndex_iff h2x (n + 1)).mpr ((divProp_two_nsmul_succ x n).mpr this)
      exact_mod_cast this

theorem divProp_odd_zsmul (x : A) {m : ℤ} (hm : Odd m) (e : ℕ) :
    DivProp ⊤ (m • x) e ↔ DivProp ⊤ x e := by
  constructor
  · rintro ⟨G, -, hG⟩
    have hcop : IsCoprime m ((2 ^ e : ℕ) : ℤ) := by
      push_cast
      refine IsCoprime.pow_right ?_
      obtain ⟨k, rfl⟩ := hm
      exact ⟨1, -k, by ring⟩
    obtain ⟨u, w, huw⟩ := hcop
    refine ⟨u • G + w • x, AddSubgroup.mem_top _, ?_⟩
    have := (IsOfFinAddOrder.zsmul hG : IsOfFinAddOrder (u • _))
    rwa [show u • (m • x - (2 ^ e : ℕ) • G) = x - (2 ^ e : ℕ) • (u • G + w • x) by
      simp only [← natCast_zsmul]
      linear_combination (norm := module) huw • x] at this
  · rintro ⟨G, -, hG⟩
    refine ⟨m • G, AddSubgroup.mem_top _, ?_⟩
    have := (IsOfFinAddOrder.zsmul hG : IsOfFinAddOrder (m • _))
    rwa [smul_sub, smul_comm m ((2 ^ e : ℕ)) G] at this

theorem twoDivIndex_odd_zsmul (x : A) {m : ℤ} (hm : Odd m) :
    twoDivIndex ⊤ (m • x) = twoDivIndex ⊤ x :=
  twoDivIndex_eq_of_iff (AddSubgroup.mem_top _) (AddSubgroup.mem_top _) (divProp_odd_zsmul x hm)

theorem twoDivIndex_two_pow_nsmul (x : A) (k : ℕ) :
    twoDivIndex ⊤ ((2 ^ k : ℕ) • x) = twoDivIndex ⊤ x + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_nsmul', twoDivIndex_two_nsmul, ih]
    push_cast
    ring

theorem two_pow_zsmul_eq (x : A) (k : ℕ) : ((2 : ℤ) ^ k) • x = (2 ^ k : ℕ) • x := by
  rw [← natCast_zsmul]; push_cast; rfl

theorem twoDivIndex_zsmul (x : A) {n : ℤ} (hn : n ≠ 0) :
    twoDivIndex ⊤ (n • x) = twoDivIndex ⊤ x + (padicValInt 2 n : ℕ) := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (Int.natAbs_ne_zero.mpr hn)
  have hval : padicValInt 2 n = k := by
    rw [padicValInt, hkm, padicValNat.mul (by positivity) (by rintro rfl; simp at hm),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by
        rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hm), add_zero]
  have hmz : Odd (m : ℤ) := by exact_mod_cast hm
  rcases Int.natAbs_eq n with hn' | hn'
  · rw [hval, hn', hkm]
    push_cast
    rw [mul_comm, mul_smul, twoDivIndex_odd_zsmul _ hmz, two_pow_zsmul_eq, twoDivIndex_two_pow_nsmul]
  · have hneg : Odd (-(m : ℤ)) := hmz.neg
    rw [hval, hn', hkm]
    push_cast
    rw [show -((2 : ℤ) ^ k * m) = (-(m : ℤ)) * 2 ^ k by ring, mul_smul,
      twoDivIndex_odd_zsmul _ hneg, two_pow_zsmul_eq, twoDivIndex_two_pow_nsmul]

/-! ### Finiteness from a quadratic height with the Northcott property -/

theorem height_add_torsion {hh : A → ℝ} (hsq : ∀ (n : ℕ) (x : A), hh (n • x) = (n : ℝ) ^ 2 * hh x)
    (x t : A) (ht : IsOfFinAddOrder t) : hh (x + t) = hh x := by
  obtain ⟨n, hn, htn⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp ht
  have h := hsq n (x + t)
  rw [nsmul_add, htn, add_zero, hsq n x] at h
  have hn' : ((n : ℝ) ^ 2) ≠ 0 := by positivity
  exact (mul_left_cancel₀ hn' h).symm

theorem twoDivIndex_ne_top {hh : A → ℝ} (hsq : ∀ (n : ℕ) (x : A), hh (n • x) = (n : ℝ) ^ 2 * hh x)
    (hfin : ∀ B : ℝ, {x : A | hh x ≤ B}.Finite) {x : A} (hx : 0 < hh x) :
    twoDivIndex ⊤ x ≠ ⊤ := by
  intro htop
  have hall : ∀ e : ℕ, DivProp ⊤ x e := fun e =>
    (le_twoDivIndex_iff (AddSubgroup.mem_top x) e).mp (by rw [htop]; exact le_top)
  choose G _ hG using hall
  have hht : ∀ e, hh x = (4 : ℝ) ^ e * hh (G e) := by
    intro e
    have h1 := height_add_torsion hsq ((2 ^ e : ℕ) • G e) _ (hG e)
    rw [show (2 ^ e : ℕ) • G e + (x - (2 ^ e : ℕ) • G e) = x by abel, hsq] at h1
    have h4 : ((2 : ℝ) ^ e) ^ 2 = 4 ^ e := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h1]; push_cast; rw [h4]
  have hinj : Function.Injective G := by
    intro e e' hee
    have h1 := hht e
    have h2 := hht e'
    rw [hee] at h1
    have hG0 : hh (G e') ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h2; exact hx.ne' h2
    have : (4 : ℝ) ^ e = (4 : ℝ) ^ e' := mul_right_cancel₀ hG0 (h1.symm.trans h2)
    exact pow_right_injective₀ (by norm_num : (0 : ℝ) < 4) (by norm_num) this
  refine Set.infinite_of_injective_forall_mem (s := {y : A | hh y ≤ hh x}) hinj (fun e => ?_)
    (hfin (hh x))
  show hh (G e) ≤ hh x
  rw [hht e]
  have hG0 : 0 ≤ hh (G e) := by
    have := hht e
    by_contra hneg
    push Not at hneg
    have : (4 : ℝ) ^ e * hh (G e) < 0 := mul_neg_of_pos_of_neg (by positivity) hneg
    linarith
  calc hh (G e) = 1 * hh (G e) := (one_mul _).symm
    _ ≤ (4 : ℝ) ^ e * hh (G e) := by
      exact mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num)) hG0

/-! ### The rank-one comparison -/

/-- **Two nontorsion points of a rank-one group compare by a rational square whose 2-adic
valuation is the difference of their index valuations** (PROVED). -/
theorem rank_one_ratio {hh : A → ℝ} (hsq : ∀ (n : ℤ) (x : A), hh (n • x) = (n : ℝ) ^ 2 * hh x)
    (hrank : ∀ y z : A, ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ a • y = b • z)
    {z z' : A} (hz : ¬ IsOfFinAddOrder z) (hz' : ¬ IsOfFinAddOrder z')
    (hj : twoDivIndex ⊤ z ≠ ⊤) (hj' : twoDivIndex ⊤ z' ≠ ⊤) :
    ∃ q : ℚ, q ≠ 0 ∧ hh z = ((q : ℝ)) ^ 2 * hh z' ∧
      padicValRat 2 q = ((twoDivIndex ⊤ z).toNat : ℤ) - (twoDivIndex ⊤ z').toNat := by
  obtain ⟨a, b, hab, he⟩ := hrank z z'
  have ha : a ≠ 0 := by
    rintro rfl
    have hb : b ≠ 0 := hab.resolve_left (by simp)
    exact hz' (isOfFinAddOrder_of_zsmul hb (by rw [← he, zero_smul]; simp))
  have hb : b ≠ 0 := by
    rintro rfl
    exact hz (isOfFinAddOrder_of_zsmul ha (by rw [he, zero_smul]; simp))
  refine ⟨(b : ℚ) / a, div_ne_zero (by exact_mod_cast hb) (by exact_mod_cast ha), ?_, ?_⟩
  · have h1 := hsq a z
    have h2 := hsq b z'
    rw [he, h2] at h1
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    push_cast
    field_simp
    linarith
  · have h1 := twoDivIndex_zsmul z ha
    have h2 := twoDivIndex_zsmul z' hb
    rw [he, h2] at h1
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hj
    obtain ⟨n', hn'⟩ := ENat.ne_top_iff_exists.mp hj'
    rw [← hn, ← hn'] at h1
    rw [← hn, ← hn', ENat.toNat_natCast, ENat.toNat_natCast]
    have h3 : n + padicValInt 2 a = n' + padicValInt 2 b := by exact_mod_cast h1.symm
    rw [padicValRat.div (by exact_mod_cast hb) (by exact_mod_cast ha), padicValRat.of_int,
      padicValRat.of_int]
    omega

/-- Rank at most one: any two elements are dependent (PROVED). -/
theorem exists_dep_of_rank_le_one (h : Module.rank ℤ A ≤ 1) (y z : A) :
    ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ a • y = b • z := by
  by_contra hcon
  push Not at hcon
  have hli : LinearIndependent ℤ ![y, z] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have := hcon s (-t)
    by_contra hne
    rw [not_and_or] at hne
    exact this (hne.imp id fun h => neg_ne_zero.mpr h)
      (by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left hst)
  have h2 := hli.cardinal_lift_le_rank
  have h3 := h2.trans (Cardinal.lift_le.{0}.mpr h)
  simp at h3

/-! ### Transfer between the native lattice and the rational line -/

/-- **Index transfer** (PROVED): if `ψ : R → A` is injective with image in `M`,
`2M ⊆ ψ(R) + torsion` (index at most two of the rational line in the native lattice, tex
L2433–2435), and `2P ≡ ψ(Q)` modulo torsion, then `j_M(P) ≤ j_R(Q) ≤ j_M(P) + 1`. -/
theorem twoDivIndex_transfer {R : Type*} [AddCommGroup R] (ψ : R →+ A)
    (hψ : Function.Injective ψ) (M : AddSubgroup A) (hψM : ∀ r, ψ r ∈ M)
    (hidx : ∀ x ∈ M, ∃ r, IsOfFinAddOrder ((2 : ℕ) • x - ψ r))
    {P : A} (hP : P ∈ M) {Q : R} (hPQ : IsOfFinAddOrder ((2 : ℕ) • P - ψ Q)) :
    twoDivIndex M P ≤ twoDivIndex ⊤ Q ∧ twoDivIndex ⊤ Q ≤ twoDivIndex M P + 1 := by
  constructor
  · refine ENat.forall_natCast_le_iff_le.mp fun e he => ?_
    obtain ⟨G, hG, ht1⟩ := (le_twoDivIndex_iff hP e).mp he
    obtain ⟨r, ht2⟩ := hidx G hG
    refine (le_twoDivIndex_iff (AddSubgroup.mem_top Q) e).mpr ⟨r, AddSubgroup.mem_top r, ?_⟩
    refine isOfFinAddOrder_of_map ψ hψ ?_
    have key : ψ (Q - (2 ^ e : ℕ) • r) = -((2 : ℕ) • P - ψ Q) + (2 : ℕ) • (P - (2 ^ e : ℕ) • G) +
        (2 ^ e : ℕ) • ((2 : ℕ) • G - ψ r) := by
      rw [map_sub, map_nsmul]
      simp only [← natCast_zsmul]
      module
    rw [key]
    exact (hPQ.neg.add (ht1.nsmul)).add ht2.nsmul
  · refine ENat.forall_natCast_le_iff_le.mp fun e he => ?_
    rcases e with _ | e
    · simp
    obtain ⟨r, -, ht⟩ := (le_twoDivIndex_iff (AddSubgroup.mem_top Q) (e + 1)).mp he
    have hdiv : DivProp M P e := by
      refine ⟨ψ r, hψM r, isOfFinAddOrder_of_nsmul (n := 2) (by norm_num) ?_⟩
      have key : (2 : ℕ) • (P - (2 ^ e : ℕ) • ψ r) =
          ((2 : ℕ) • P - ψ Q) + ψ (Q - (2 ^ (e + 1) : ℕ) • r) := by
        rw [map_sub, map_nsmul]
        simp only [← natCast_zsmul]
        push_cast
        module
      rw [key]
      exact hPQ.add (isOfFinAddOrder_map ψ ht)
    have := (le_twoDivIndex_iff hP e).mpr hdiv
    push_cast
    exact add_le_add this le_rfl

end ZInQ.Contrib.CloudB3RC53.GenusOdd
