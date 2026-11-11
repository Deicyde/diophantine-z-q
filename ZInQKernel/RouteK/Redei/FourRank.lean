import ZInQKernel.RouteK.Redei.Ambiguous
import ZInQKernel.RouteK.Redei.Dirichlet
import ZInQKernel.RouteK.Redei.Bridge

/-!
# The 4-rank and Rédei's formula (`docs/research/redei-plan.md` §3.2, step 6, and the assembly)

For odd squarefree `n > 1`, with `Cl = Cl(ℚ(√−n))`, `t = #ramSet n` and the genus characters
`χ_q` (`chi n q`, one for each prime `q ∣ n`):

* `chi_psi`: `χ_q(ψ(e)) = Σ_p R_{qp} e_p` (`R = redeiEntry n`);
* `odd_card_range_sq_iff`: for a finite commutative group, `#G²` is odd iff `G[2] ∩ G² = 1`;
* `card_ker_sq_mul_card_range_sq`: `#G[2] · #G² = #G`;
* `range_sq_eq_ker_chi`: `Cl² = ⋂_q ker χ_q` (genus theory, by counting: `[Cl : Cl²] = #Cl[2] ≤
  2^{t−1}` by `card_ker_sq_le`, and `2^{t−1} ≤ #χ(Cl) = [Cl : ⋂ ker χ_q] ≤ [Cl : Cl²]` by
  `exists_chi_eq`); also `card_ker_sq_eq : #Cl[2] = 2^{t−1}`;
* `odd_gCl_iff`: `g(n) = #Cl²` is odd iff the kernel of the Rédei matrix is `{0, e_n}`;
* `oddGClStatement : OddGClStatement`, `redeiFormula : RouteK.Rank5b.RedeiFormula`, and the
  unconditional consequences `T5bCl_eq_T5b'`, `certifiedRankTYZ_iff'` and
  `certifiedRankTYZRk_of_certifiedRankTYZClRk`.
-/

noncomputable section

open NumberField Pointwise
open scoped nonZeroDivisors

namespace ZInQ.RouteK.Redei

open ZInQ.RouteK.Rank5b

/-! ### Group theory -/

/-- Pure group theory: for a finite commutative group, `#G²` is odd iff `G[2] ∩ G² = 1`. -/
theorem odd_card_range_sq_iff {G : Type*} [CommGroup G] [Finite G] :
    Odd (Nat.card (powMonoidHom 2 : G →* G).range) ↔
      (powMonoidHom 2 : G →* G).ker ⊓ (powMonoidHom 2 : G →* G).range = ⊥ := by
  set H := (powMonoidHom 2 : G →* G).range
  constructor
  · intro hodd
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have h2 : x ^ 2 = 1 := hx1
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have hdvdH : orderOf (⟨x, hx2⟩ : H) ∣ Nat.card H := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvdH
    have h1 : orderOf x = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact h
      · exfalso
        rw [h] at hdvdH
        exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvdH)
    exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 h1)
  · intro hbot
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 (even_iff_two_dvd.1 hodd)
    have hker : (y : G) ∈ (powMonoidHom 2 : G →* G).ker := by
      show (y : G) ^ 2 = 1
      rw [← Subgroup.orderOf_coe] at hy
      rw [← hy]
      exact pow_orderOf_eq_one _
    have hmem : (y : G) ∈ (⊥ : Subgroup G) := hbot ▸ ⟨hker, y.2⟩
    have : orderOf (y : G) = 1 := orderOf_eq_one_iff.2 (Subgroup.mem_bot.1 hmem)
    rw [Subgroup.orderOf_coe, hy] at this
    exact absurd this (by norm_num)

/-- `#G[2] · #G² = #G` (first isomorphism theorem for `x ↦ x²`). -/
theorem card_ker_sq_mul_card_range_sq {G : Type*} [CommGroup G] :
    Nat.card (powMonoidHom 2 : G →* G).ker * Nat.card (powMonoidHom 2 : G →* G).range =
      Nat.card G :=
  Subgroup.card_ker_mul_card_range _

/-- In `ℤ/2` (multiplicatively), every square is trivial. -/
theorem fourRank_sq_eq_one (x : Multiplicative (ZMod 2)) : x ^ 2 = 1 := by
  revert x; decide

/-- `a ≤ b`, `c ≤ d`, `a c = b d`, `b, c > 0` give `a = b` and `c = d`. -/
theorem fourRank_eq_of_mul_eq {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) (hb : 0 < b) (hc : 0 < c)
    (h : a * c = b * d) : a = b ∧ c = d := by
  have h1 : b * c ≤ b * d := Nat.mul_le_mul_left b hcd
  have h2 : a * c ≤ b * c := Nat.mul_le_mul_right c hab
  have h3 : b * c = b * d := le_antisymm h1 (h ▸ h2)
  have hcd' : c = d := Nat.eq_of_mul_eq_mul_left hb h3
  subst hcd'
  exact ⟨Nat.eq_of_mul_eq_mul_right hc h, rfl⟩

/-- The sum map `𝔽₂^ι → 𝔽₂`, multiplicatively. -/
def fourRankSum (ι : Type*) [Fintype ι] :
    Multiplicative (ι → ZMod 2) →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative
    (AddMonoidHom.mk' (fun e : ι → ZMod 2 => ∑ q, e q) fun e f => by
      simp only [Pi.add_apply, Finset.sum_add_distrib])

theorem fourRankSum_apply {ι : Type*} [Fintype ι] (e : Multiplicative (ι → ZMod 2)) :
    Multiplicative.toAdd (fourRankSum ι e) = ∑ q, Multiplicative.toAdd e q := rfl

/-- The sum-zero hyperplane of `𝔽₂^ι` has `2^{#ι − 1}` elements (`ι` nonempty). -/
theorem card_ker_fourRankSum {ι : Type*} [Fintype ι] [DecidableEq ι] (hι : Nonempty ι) :
    Nat.card (fourRankSum ι).ker * 2 = 2 ^ Fintype.card ι := by
  have hcard := Subgroup.card_ker_mul_card_range (fourRankSum ι)
  have htop : (fourRankSum ι).range = ⊤ := by
    rw [eq_top_iff]
    intro b _
    obtain ⟨i⟩ := hι
    refine ⟨Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd b)), ?_⟩
    apply Multiplicative.toAdd.injective
    rw [fourRankSum_apply, toAdd_ofAdd, Finset.sum_pi_single']
    simp
  rw [htop, Subgroup.card_top] at hcard
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]; rfl
  rw [h2] at hcard
  rw [hcard, Nat.card_eq_fintype_card]
  simp

section FourRank

variable (n : ℕ) [NeZero n]

local notation "K" => QNeg n
local notation "O" => 𝓞 (QNeg n)

variable {n}

/-! ### The genus characters on the ambiguous classes -/

variable (n) in
/-- `χ_q(ψ(e)) = Σ_p R_{qp} e_p`. -/
theorem chi_psi (hn : Odd n) (hsq : Squarefree n) (q : n.primeFactors)
    (e : ramSet n → ZMod 2) :
    Multiplicative.toAdd (chi n q (psi n (Multiplicative.ofAdd e))) =
      ∑ p, redeiEntry n q p * e p := by
  rw [psi_apply, ← chi_prod_ramIdeal n hn hsq q e]
  simp only [toAdd_ofAdd, ambigClass_eq hn hsq]

/-! ### The genus map -/

variable (n) in
/-- The genus map `Cl → 𝔽₂^{primes of n}`, `c ↦ (χ_q(c))_q`. -/
def genusMap : ClassGroup O →* Multiplicative (n.primeFactors → ZMod 2) where
  toFun c := Multiplicative.ofAdd fun q => Multiplicative.toAdd (chi n q c)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext q
    simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    funext q
    simp

theorem genusMap_apply (c : ClassGroup O) (q : n.primeFactors) :
    Multiplicative.toAdd (genusMap n c) q = Multiplicative.toAdd (chi n q c) := rfl

theorem mem_ker_genusMap {c : ClassGroup O} : c ∈ (genusMap n).ker ↔ ∀ q, chi n q c = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h q
    have := congrFun (congrArg Multiplicative.toAdd h) q
    rw [genusMap_apply] at this
    exact Multiplicative.toAdd.injective this
  · intro h
    apply Multiplicative.toAdd.injective
    funext q
    rw [genusMap_apply, h q]
    rfl

theorem range_sq_le_ker_genusMap :
    (powMonoidHom 2 : ClassGroup O →* ClassGroup O).range ≤ (genusMap n).ker := by
  rintro _ ⟨c, rfl⟩
  rw [mem_ker_genusMap]
  intro q
  rw [powMonoidHom_apply, map_pow]
  exact fourRank_sq_eq_one _

omit [NeZero n] in
theorem fourRank_primeFactors_nonempty (h1 : 1 < n) : Nonempty n.primeFactors := by
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt h1)
  exact ⟨⟨p, Nat.mem_primeFactors.2 ⟨hp, hpn, by omega⟩⟩⟩

omit [NeZero n] in
theorem fourRank_card_ramSet (hn : Odd n) :
    (ramSet n).card = if n % 4 = 3 then n.primeFactors.card else n.primeFactors.card + 1 := by
  unfold ramSet
  split_ifs
  · rfl
  · rw [Finset.card_insert_of_notMem]
    intro h
    exact ne_two_of_mem_primeFactors hn h rfl

/-- `2^{t−1} ≤ #χ(Cl)` (surjectivity of the genus characters, `exists_chi_eq`). -/
theorem pow_le_card_range_genusMap (hn : Odd n) (hsq : Squarefree n) (h1 : 1 < n) :
    2 ^ ((ramSet n).card - 1) ≤ Nat.card (genusMap n).range := by
  classical
  have hne := fourRank_primeFactors_nonempty h1
  rw [fourRank_card_ramSet hn]
  split_ifs with h3
  · -- the sum-zero hyperplane lies in the image
    have hle : (fourRankSum n.primeFactors).ker ≤ (genusMap n).range := by
      intro ε hε
      rw [MonoidHom.mem_ker] at hε
      have hs : ∑ q, Multiplicative.toAdd ε q = 0 := by
        rw [← fourRankSum_apply, hε]; rfl
      obtain ⟨c, hc⟩ := exists_chi_eq n hn hsq (Multiplicative.toAdd ε) fun _ => hs
      refine ⟨c, ?_⟩
      apply Multiplicative.toAdd.injective
      funext q
      rw [genusMap_apply, hc q, toAdd_ofAdd]
    have hk := card_ker_fourRankSum (ι := n.primeFactors) hne
    have hle' := Subgroup.card_le_of_le hle
    have hpos : 0 < Fintype.card n.primeFactors := Fintype.card_pos
    rw [Fintype.card_coe] at hk hpos
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hr, pow_succ] at hk
    rw [hr, Nat.succ_sub_one]
    have : Nat.card (fourRankSum n.primeFactors).ker = 2 ^ r := by omega
    omega
  · -- the image is everything
    have htop : (genusMap n).range = ⊤ := by
      rw [eq_top_iff]
      intro ε _
      obtain ⟨c, hc⟩ := exists_chi_eq n hn hsq (Multiplicative.toAdd ε) fun h => absurd h h3
      refine ⟨c, ?_⟩
      apply Multiplicative.toAdd.injective
      funext q
      rw [genusMap_apply, hc q, toAdd_ofAdd]
    rw [htop, Subgroup.card_top, Nat.add_sub_cancel, Nat.card_eq_fintype_card]
    simp

/-- The counting identity behind genus theory: `Cl² = ker χ` and `#Cl[2] = 2^{t−1}`. -/
theorem range_sq_eq_ker_genusMap_and_card (hn : Odd n) (hsq : Squarefree n) (h1 : 1 < n) :
    (powMonoidHom 2 : ClassGroup O →* ClassGroup O).range = (genusMap n).ker ∧
      Nat.card (powMonoidHom 2 : ClassGroup O →* ClassGroup O).ker =
        2 ^ ((ramSet n).card - 1) := by
  have hA := card_ker_sq_mul_card_range_sq (G := ClassGroup O)
  have hB := Subgroup.card_ker_mul_card_range (genusMap n)
  have hle := range_sq_le_ker_genusMap (n := n)
  have hS := Subgroup.card_le_of_le hle
  have hT := card_ker_sq_le n hn hsq h1
  have hR := pow_le_card_range_genusMap hn hsq h1
  have hpos1 : 0 < Nat.card (genusMap n).ker := Nat.card_pos
  have hpos2 : 0 < Nat.card (powMonoidHom 2 : ClassGroup O →* ClassGroup O).ker := Nat.card_pos
  obtain ⟨e1, e2⟩ := fourRank_eq_of_mul_eq hS (hT.trans hR) hpos1 hpos2
    (by rw [mul_comm, hA, hB])
  refine ⟨Subgroup.eq_of_le_of_card_ge hle e1.ge, le_antisymm hT ?_⟩
  rw [e2]; exact hR

variable (n) in
/-- **Genus theory**: `Cl² = ⋂_q ker χ_q`. -/
theorem range_sq_eq_ker_chi (hn : Odd n) (hsq : Squarefree n) (h1 : 1 < n) :
    (powMonoidHom 2 : ClassGroup O →* ClassGroup O).range = ⨅ q, (chi n q).ker := by
  rw [(range_sq_eq_ker_genusMap_and_card hn hsq h1).1]
  ext c
  rw [mem_ker_genusMap, Subgroup.mem_iInf]
  simp only [MonoidHom.mem_ker]

variable (n) in
/-- `#Cl[2] = 2^{t−1}`. -/
theorem card_ker_sq_eq (hn : Odd n) (hsq : Squarefree n) (h1 : 1 < n) :
    Nat.card (powMonoidHom 2 : ClassGroup O →* ClassGroup O).ker = 2 ^ ((ramSet n).card - 1) :=
  (range_sq_eq_ker_genusMap_and_card hn hsq h1).2

variable (n) in
/-- `ker ψ` has two elements. -/
theorem card_ker_psi (hn : Odd n) (hsq : Squarefree n) (h1 : 1 < n) :
    Nat.card (psi n).ker = 2 := by
  have hcard := Subgroup.card_ker_mul_card_range (psi n)
  rw [range_psi n hn hsq, card_ker_sq_eq n hn hsq h1] at hcard
  have hdom : Nat.card (Multiplicative (ramSet n → ZMod 2)) = 2 ^ (ramSet n).card := by
    rw [Nat.card_eq_fintype_card]; simp
  rw [hdom] at hcard
  have hpos : 0 < (ramSet n).card := by
    obtain ⟨⟨p, hp⟩⟩ := fourRank_primeFactors_nonempty h1
    exact Finset.card_pos.2 ⟨p, mem_ramSet_of_mem_primeFactors hp⟩
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  rw [ht, Nat.succ_sub_one, pow_succ] at hcard
  have : 0 < 2 ^ t := by positivity
  nlinarith

variable (n) in
/-- The vector `e_n` of `(√−n)`. -/
def fourRankVec : ramSet n → ZMod 2 := fun p => if (p : ℕ) ∈ n.primeFactors then 1 else 0

omit [NeZero n] in
theorem fourRankVec_ne_zero (h1 : 1 < n) : fourRankVec n ≠ 0 := by
  obtain ⟨⟨p, hp⟩⟩ := fourRank_primeFactors_nonempty h1
  intro h
  have := congrFun h ⟨p, mem_ramSet_of_mem_primeFactors hp⟩
  simp [fourRankVec, hp] at this

variable (n) in
/-- **Rédei's theorem** (4-rank 0 form): for odd squarefree `n > 1`, `g(n)` is odd iff the kernel
of the Rédei matrix is `{0, e_n}`. -/
theorem odd_gCl_iff (hn : Odd n) (hsq : Squarefree n) (h1 : 1 < n) :
    Odd (gCl n) ↔ ∀ e : ramSet n → ZMod 2, (∀ q, ∑ p, redeiEntry n q p * e p = 0) →
      e = 0 ∨ e = fun p : ramSet n => if (p : ℕ) ∈ n.primeFactors then (1 : ZMod 2) else 0 := by
  have hS := range_sq_eq_ker_chi n hn hsq h1
  have hT := range_psi n hn hsq
  -- `ψ(e) ∈ Cl²` iff `e` solves the Rédei system
  have hmem : ∀ e : ramSet n → ZMod 2,
      psi n (Multiplicative.ofAdd e) ∈ (powMonoidHom 2 : ClassGroup O →* ClassGroup O).range ↔
        ∀ q, ∑ p, redeiEntry n q p * e p = 0 := by
    intro e
    rw [hS, Subgroup.mem_iInf]
    refine forall_congr' fun q => ?_
    rw [MonoidHom.mem_ker, ← chi_psi n hn hsq q e]
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact Multiplicative.toAdd.injective h
  have hv : psi n (Multiplicative.ofAdd (fourRankVec n)) = 1 := psi_ones n hn hsq
  change _ ↔ ∀ e : ramSet n → ZMod 2, _ → e = 0 ∨ e = fourRankVec n
  unfold gCl
  rw [odd_card_range_sq_iff]
  constructor
  · intro hbot e he
    have h1' : psi n (Multiplicative.ofAdd e) ∈
        (powMonoidHom 2 : ClassGroup O →* ClassGroup O).ker ⊓
          (powMonoidHom 2 : ClassGroup O →* ClassGroup O).range :=
      ⟨hT ▸ ⟨_, rfl⟩, (hmem e).2 he⟩
    rw [hbot, Subgroup.mem_bot] at h1'
    -- `ker ψ = {0, e_n}`
    have hk := (Nat.card_eq_two_iff' (1 : (psi n).ker)).1 (card_ker_psi n hn hsq h1)
    obtain ⟨y, -, hy⟩ := hk
    by_cases he0 : e = 0
    · exact Or.inl he0
    right
    have hne1 : ∀ f : ramSet n → ZMod 2, f ≠ 0 → (h : psi n (Multiplicative.ofAdd f) = 1) →
        (⟨Multiplicative.ofAdd f, h⟩ : (psi n).ker) ≠ 1 := by
      intro f hf h hc
      apply hf
      have := congrArg Subtype.val hc
      exact Multiplicative.ofAdd.injective this
    have ha := hy _ (hne1 e he0 h1')
    have hb := hy _ (hne1 _ (fourRankVec_ne_zero h1) hv)
    have := congrArg Subtype.val (ha.trans hb.symm)
    exact Multiplicative.ofAdd.injective this
  · intro hker
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    rw [← hT] at hx1
    obtain ⟨m, rfl⟩ := hx1
    rw [← ofAdd_toAdd m] at hx2 ⊢
    rcases hker _ ((hmem _).1 hx2) with h | h
    · rw [h, ofAdd_zero, map_one]; exact Subgroup.one_mem _
    · rw [h, hv]; exact Subgroup.one_mem _

end FourRank

/-! ### Rédei's formula -/

/-- **The 4-rank statement**, proved. -/
theorem oddGClStatement : OddGClStatement := fun n _ hn hsq h1 => odd_gCl_iff n hn hsq h1

/-- **Rédei's formula** (`RouteK.Rank5b.RedeiFormula`, tyz-5b Proposition 2.3), proved. -/
theorem redeiFormula : RedeiFormula := redeiFormula_of_oddGClStatement oddGClStatement

/-- The genus sum of class numbers is the genus sum of Rédei bits, unconditionally. -/
theorem T5bCl_eq_T5b' {d : ℕ} (hd : Odd d) (hsq : Squarefree d) : T5bCl d = T5b d :=
  T5bCl_eq_T5b redeiFormula hd hsq

/-- CR₃ in class-number form is CR₃^TYZ, unconditionally. -/
theorem certifiedRankTYZ_iff' : CertifiedRankTYZCl ↔ CertifiedRankTYZ :=
  certifiedRankTYZ_iff_of_redeiFormula redeiFormula

/-- CR₃^TYZ_Cl,Rk gives CR₃^TYZ,Rk, unconditionally. -/
theorem certifiedRankTYZRk_of_certifiedRankTYZClRk (hCl : Rank.CertifiedRankTYZClRk) :
    Rank.CertifiedRankTYZRk :=
  certifiedRankTYZRk_of_oddGClStatement oddGClStatement hCl

end ZInQ.RouteK.Redei
