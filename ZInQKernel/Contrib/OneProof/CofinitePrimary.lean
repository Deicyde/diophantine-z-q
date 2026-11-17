import Mathlib

/-!
# Cofinitely generated `p`-primary abelian groups

For a prime `p`, a `p`-primary abelian group `A` (every element is killed by a power of `p`) whose
`p`-torsion `A[p]` is finite is isomorphic to `(ℚ_p/ℤ_p)^t × F` with `F` finite
(`exists_addEquiv_of_isPPrimary`). This is the structure theorem for cofinitely generated
`ℤ_p`-modules in the form needed for Selmer coranks.

The proof is by strong induction on `#A[p]`. If the subgroup `⋂ₙ pⁿA` is zero, `A` is finite. Otherwise it
is divisible (`p`-divisible by a compactness argument on the finite fibres of multiplication by `p`, and
divisible by integers prime to `p` because `A` is `p`-primary); a nonzero `x` of order `p` in it extends to
an injective map `ℚ_p/ℤ_p → A` (injectivity of divisible groups), whose image is a direct summand
(injectivity of `ℚ_p/ℤ_p`), and the complement has smaller `p`-torsion.
-/

noncomputable section

namespace ZInQ.Cofinite

open AddSubgroup

variable (p : ℕ) [hp : Fact p.Prime]

/-- `ℚ_p/ℤ_p`. -/
abbrev Qp : Type := ℚ_[p] ⧸ (PadicInt.subring p).toAddSubgroup

instance : DivisibleBy (Qp p) ℤ := QuotientAddGroup.mk_surjective.divisibleBy _ fun _ _ => rfl

/-- A group is `p`-primary when every element is killed by a power of `p`. -/
def IsPPrimary (A : Type*) [AddCommGroup A] : Prop :=
  ∀ a : A, ∃ k : ℕ, p ^ k • a = 0

/-- The class of `p⁻¹`, of order `p` in `ℚ_p/ℤ_p`. -/
def e₁ : Qp p := QuotientAddGroup.mk (p⁻¹ : ℚ_[p])

variable {p}

theorem mk_eq_zero_iff (q : ℚ_[p]) : (QuotientAddGroup.mk q : Qp p) = 0 ↔ ‖q‖ ≤ 1 := by
  rw [QuotientAddGroup.eq_zero_iff]
  exact Iff.rfl

theorem nsmul_mk (k : ℕ) (q : ℚ_[p]) :
    k • (QuotientAddGroup.mk q : Qp p) = QuotientAddGroup.mk ((k : ℚ_[p]) * q) := by
  rw [← QuotientAddGroup.mk_nsmul, nsmul_eq_mul]

theorem isPPrimary_Qp : IsPPrimary p (Qp p) := by
  intro y
  induction y using QuotientAddGroup.induction_on with
  | H q =>
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖q‖ hp1
    refine ⟨k, ?_⟩
    rw [nsmul_mk, mk_eq_zero_iff, norm_mul, Nat.cast_pow, norm_pow, Padic.norm_p]
    have hpos : (0 : ℝ) < (p : ℝ) ^ k := by positivity
    rw [inv_pow, inv_mul_le_iff₀ hpos, mul_one]
    exact hk.le

theorem p_nsmul_e₁ : p • e₁ p = 0 := by
  rw [e₁, nsmul_mk, mul_inv_cancel₀ (by exact_mod_cast hp.out.ne_zero), mk_eq_zero_iff, norm_one]

theorem nsmul_e₁_eq_zero_iff (k : ℕ) : k • e₁ p = 0 ↔ p ∣ k := by
  rw [e₁, nsmul_mk, mk_eq_zero_iff, norm_mul, norm_inv, Padic.norm_p, inv_inv]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have h := Padic.norm_int_le_pow_iff_dvd (p := p) (k : ℤ) 1
  simp only [Int.cast_natCast, pow_one, Nat.cast_one, zpow_neg, zpow_one] at h
  rw [← le_div_iff₀ hp0, one_div, h]
  exact Int.natCast_dvd_natCast

theorem exists_nsmul_e₁_eq {y : Qp p} (hy : p • y = 0) : ∃ k : ℕ, k • e₁ p = y := by
  induction y using QuotientAddGroup.induction_on with
  | H q =>
    rw [nsmul_mk, mk_eq_zero_iff] at hy
    let u : ℤ_[p] := ⟨(p : ℚ_[p]) * q, hy⟩
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec 1 u)
    refine ⟨PadicInt.appr u 1, ?_⟩
    have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hw' : ((w : ℚ_[p]) * p) = p * q - (PadicInt.appr u 1 : ℚ_[p]) := by
      have := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hw
      simp only [pow_one, PadicInt.coe_mul, PadicInt.coe_sub, PadicInt.coe_natCast] at this
      exact this
    have hq : q - (PadicInt.appr u 1 : ℚ_[p]) * (p : ℚ_[p])⁻¹ = w := by
      field_simp
      linear_combination -hw'
    rw [e₁, nsmul_mk, ← sub_eq_zero, ← QuotientAddGroup.mk_sub, mk_eq_zero_iff]
    rw [show (PadicInt.appr u 1 : ℚ_[p]) * (p : ℚ_[p])⁻¹ - q = -(w : ℚ_[p]) by rw [← hq]; ring]
    rw [norm_neg]
    exact w.2

theorem e₁_ne_zero : e₁ p ≠ 0 := by
  intro h
  have := (nsmul_e₁_eq_zero_iff (p := p) 1).mp (by rw [one_nsmul]; exact h)
  exact hp.out.one_lt.ne' (Nat.dvd_one.mp this)

/-! ### Elementary facts on `p`-primary groups -/

section General

variable {A : Type*} [AddCommGroup A]

/-- In a `p`-primary group, a nonzero element has a nonzero multiple of order `p`. -/
theorem exists_nsmul_ne_zero_p_nsmul_eq_zero (hA : IsPPrimary p A) {a : A} (ha : a ≠ 0) :
    ∃ j : ℕ, p ^ j • a ≠ 0 ∧ p • (p ^ j • a) = 0 := by
  classical
  have hex : ∃ k, p ^ k • a = 0 := hA a
  let k := Nat.find hex
  have hk : p ^ k • a = 0 := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h0
    apply ha
    have : p ^ 0 • a = 0 := h0 ▸ hk
    simpa using this
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  refine ⟨j, Nat.find_min hex (by omega), ?_⟩
  rw [← mul_nsmul', ← pow_succ']
  have hj' : j + 1 = k := hj.symm
  rw [hj']
  exact hk

end General

/-- `A[n] = {a | n • a = 0}`. -/
abbrev tors (A : Type*) [AddCommGroup A] (n : ℕ) : AddSubgroup A :=
  (nsmulAddMonoidHom (α := A) n).ker

theorem mem_tors {A : Type*} [AddCommGroup A] {n : ℕ} {a : A} : a ∈ tors A n ↔ n • a = 0 := by
  rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]

variable (p) in
/-- **The divisible part** `⋂ₙ pⁿ A`. -/
def divPart (A : Type*) [AddCommGroup A] : AddSubgroup A :=
  ⨅ n : ℕ, (nsmulAddMonoidHom (α := A) (p ^ n)).range

theorem mem_divPart {A : Type*} [AddCommGroup A] {d : A} :
    d ∈ divPart p A ↔ ∀ n : ℕ, ∃ b : A, p ^ n • b = d := by
  simp only [divPart, AddSubgroup.mem_iInf, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]

section General2

variable {A : Type*} [AddCommGroup A]

omit hp in
/-- A homomorphism with finite kernel to a finite group has finite domain. -/
theorem finite_of_finite_ker {B : Type*} [AddCommGroup B] [Finite B] (f : A →+ B)
    (hf : Finite f.ker) : Finite A := by
  have h1 : Finite (A ⧸ f.ker) :=
    Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange f).symm.toEquiv
  exact Finite.of_equiv _ (AddSubgroup.addGroupEquivQuotientProdAddSubgroup (s := f.ker)).symm

omit hp in
theorem finite_tors_pow (hfin : Finite (tors A p)) (n : ℕ) : Finite (tors A (p ^ n)) := by
  induction n with
  | zero =>
    have : Subsingleton (tors A (p ^ 0)) := ⟨fun a b => Subtype.ext (by
      have ha := mem_tors.mp a.2; have hb := mem_tors.mp b.2
      simp only [pow_zero, one_nsmul] at ha hb; rw [ha, hb])⟩
    infer_instance
  | succ n ih =>
    let g : tors A (p ^ (n + 1)) →+ tors A (p ^ n) :=
      { toFun := fun x => ⟨p • (x : A), mem_tors.mpr (by
            rw [← mul_nsmul', ← pow_succ]; exact mem_tors.mp x.2)⟩
        map_zero' := Subtype.ext (by simp)
        map_add' := fun x y => Subtype.ext (by simp) }
    refine finite_of_finite_ker g ?_
    refine Finite.of_injective (fun x : g.ker => (⟨(x : tors A (p ^ (n + 1))), ?_⟩ : tors A p)) ?_
    · have := congrArg Subtype.val (AddMonoidHom.mem_ker.mp x.2)
      exact mem_tors.mpr this
    · intro x y h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')

omit hp in
variable (p) in
theorem range_pow_antitone {m n : ℕ} (h : m ≤ n) :
    (nsmulAddMonoidHom (α := A) (p ^ n)).range ≤ (nsmulAddMonoidHom (α := A) (p ^ m)).range := by
  rintro _ ⟨b, rfl⟩
  refine ⟨p ^ (n - m) • b, ?_⟩
  simp only [nsmulAddMonoidHom_apply, ← mul_nsmul', ← pow_add, Nat.add_sub_cancel' h]

/-- **`⋂ₙ pⁿ A` is `p`-divisible** when `A[p]` is finite: the solutions of `p • a = d` form a finite
coset of `A[p]`, and for each `n` one of them lies in `pⁿ A`. -/
theorem exists_mem_divPart_p_nsmul_eq (hfin : Finite (tors A p)) {d : A} (hd : d ∈ divPart p A) :
    ∃ e ∈ divPart p A, p • e = d := by
  classical
  rw [mem_divPart] at hd
  obtain ⟨a₀, ha₀⟩ := hd 1
  rw [pow_one] at ha₀
  let X := {a : A // p • a = d}
  have hX : Finite X := by
    refine Finite.of_injective (fun a : X => (⟨(a : A) - a₀, mem_tors.mpr ?_⟩ : tors A p)) ?_
    · rw [nsmul_sub, a.2, ha₀, sub_self]
    · intro a b h
      exact Subtype.ext (sub_left_injective (congrArg Subtype.val h))
  by_contra hne
  push Not at hne
  have hmiss : ∀ a : X, ∃ n : ℕ, (a : A) ∉ (nsmulAddMonoidHom (α := A) (p ^ n)).range := by
    intro a
    by_contra hall
    push Not at hall
    exact hne a (AddSubgroup.mem_iInf.mpr hall) a.2
  choose n hn using hmiss
  have : Fintype X := Fintype.ofFinite X
  let N := Finset.univ.sup n
  obtain ⟨b, hb⟩ := hd (N + 1)
  let a : X := ⟨p ^ N • b, by rw [← mul_nsmul', ← pow_succ']; exact hb⟩
  apply hn a
  exact range_pow_antitone p (Finset.le_sup (Finset.mem_univ a)) ⟨b, rfl⟩

end General2

section Divisible

variable {A : Type*} [AddCommGroup A]

theorem exists_mem_divPart_pow_nsmul_eq (hfin : Finite (tors A p)) (a : ℕ) {d : A}
    (hd : d ∈ divPart p A) : ∃ e ∈ divPart p A, p ^ a • e = d := by
  induction a generalizing d with
  | zero => exact ⟨d, hd, by simp⟩
  | succ a ih =>
    obtain ⟨e₀, he₀, rfl⟩ := exists_mem_divPart_p_nsmul_eq hfin hd
    obtain ⟨e, he, rfl⟩ := ih he₀
    exact ⟨e, he, by rw [← mul_nsmul', ← pow_succ']⟩

/-- In a `p`-primary group, every element of a subgroup is divisible within that subgroup by any
natural number prime to `p`. -/
theorem exists_mem_nsmul_eq_of_coprime (hA : IsPPrimary p A) (S : AddSubgroup A) {m : ℕ}
    (hm : Nat.Coprime p m) {d : A} (hd : d ∈ S) : ∃ e ∈ S, m • e = d := by
  obtain ⟨k, hk⟩ := hA d
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    simp only [pow_zero, one_nsmul] at hk
    exact ⟨0, S.zero_mem, by rw [hk, nsmul_zero]⟩
  have hp1 : 1 < p ^ k := Nat.one_lt_pow hpos.ne' hp.out.one_lt
  have hcop : Nat.Coprime m (p ^ k) := (Nat.Coprime.pow_left k hm).symm
  obtain ⟨m', -, hm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp1
  refine ⟨m' • d, S.nsmul_mem hd m', ?_⟩
  rw [← mul_nsmul', ← Nat.div_add_mod (m * m') (p ^ k), hm', add_nsmul, one_nsmul, mul_comm,
    mul_nsmul', hk, nsmul_zero, zero_add]

/-- **`⋂ₙ pⁿ A` is divisible by every nonzero natural number** (`A` `p`-primary, `A[p]` finite). -/
theorem exists_mem_divPart_nsmul_eq (hA : IsPPrimary p A) (hfin : Finite (tors A p)) {n : ℕ}
    (hn : n ≠ 0) {d : A} (hd : d ∈ divPart p A) : ∃ e ∈ divPart p A, n • e = d := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.one_lt.ne'
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm
  obtain ⟨e₁, he₁, rfl⟩ := exists_mem_nsmul_eq_of_coprime hA (divPart p A) hcop hd
  obtain ⟨e, he, rfl⟩ := exists_mem_divPart_pow_nsmul_eq hfin a he₁
  exact ⟨e, he, by rw [mul_comm, mul_nsmul']⟩

/-- **`⋂ₙ pⁿ A` is a divisible group** (`A` `p`-primary, `A[p]` finite). -/
@[instance_reducible]
def divisibleByDivPart (hA : IsPPrimary p A) (hfin : Finite (tors A p)) :
    DivisibleBy (divPart p A) ℤ :=
  divisibleByOfSMulRightSurj _ _ fun {n} hn x => by
    obtain ⟨e, he, hed⟩ := exists_mem_divPart_nsmul_eq hA hfin (Int.natAbs_ne_zero.mpr hn) x.2
    rcases Int.natAbs_eq n with h | h
    · refine ⟨⟨e, he⟩, Subtype.ext ?_⟩
      change n • e = (x : A)
      rw [h, natCast_zsmul, hed]
    · refine ⟨⟨-e, neg_mem he⟩, Subtype.ext ?_⟩
      change n • (-e) = (x : A)
      rw [h, smul_neg, neg_zsmul, neg_neg, natCast_zsmul, hed]

end Divisible

/-! ### An injective map `ℚ_p/ℤ_p → A` from a nonzero divisible part, and the splitting -/

section Embed

variable {A : Type*} [AddCommGroup A]

variable (p) in
/-- `ℤ/p → ℚ_p/ℤ_p`, `1 ↦ e₁`. -/
def inclZMod : ZMod p →+ Qp p :=
  ZMod.lift p ⟨zmultiplesHom (Qp p) (e₁ p), by
    rw [zmultiplesHom_apply, natCast_zsmul, p_nsmul_e₁]⟩

theorem inclZMod_natCast (k : ℕ) : inclZMod p (k : ZMod p) = k • e₁ p := by
  rw [← Int.cast_natCast, inclZMod, ZMod.lift_coe, zmultiplesHom_apply, natCast_zsmul]

variable (p) in
theorem inclZMod_injective : Function.Injective (inclZMod p) := by
  rw [injective_iff_map_eq_zero]
  intro k hk
  rw [← ZMod.natCast_zmod_val k, inclZMod_natCast, nsmul_e₁_eq_zero_iff] at hk
  rw [← ZMod.natCast_zmod_val k, ZMod.natCast_eq_zero_iff]
  exact hk

/-- **A nonzero divisible part gives an injective map `ℚ_p/ℤ_p → A`**: a nonzero `x` of order `p`
in `⋂ₙ pⁿ A` defines `ℤ/p → ⋂ₙ pⁿ A`, which extends along `ℤ/p ↪ ℚ_p/ℤ_p` (the divisible part is
divisible, hence injective); the extension is injective since `ℚ_p/ℤ_p` is `p`-primary and its
elements of order `p` are the multiples of `e₁`. -/
theorem exists_injective_of_divPart_ne_bot (hA : IsPPrimary p A) (hfin : Finite (tors A p))
    (hD : divPart p A ≠ ⊥) : ∃ φ : Qp p →+ A, Function.Injective φ := by
  classical
  obtain ⟨⟨d, hd⟩, hd0'⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hD
  have hd0 : d ≠ 0 := fun h => hd0' (Subtype.ext h)
  obtain ⟨j, hj0, hjp⟩ := exists_nsmul_ne_zero_p_nsmul_eq_zero hA hd0
  set x : A := p ^ j • d with hxdef
  have hxD : x ∈ divPart p A := AddSubgroup.nsmul_mem _ hd _
  let _ := divisibleByDivPart hA hfin
  let g : ZMod p →+ divPart p A :=
    ZMod.lift p ⟨zmultiplesHom (divPart p A) ⟨x, hxD⟩, by
      rw [zmultiplesHom_apply, natCast_zsmul]
      exact Subtype.ext hjp⟩
  obtain ⟨φ₀, hφ₀⟩ := (Module.Baer.of_divisible (divPart p A)).extension_property_addMonoidHom
    (inclZMod p) (inclZMod_injective p) g
  refine ⟨(divPart p A).subtype.comp φ₀, ?_⟩
  have hφe : ((divPart p A).subtype.comp φ₀) (e₁ p) = x := by
    have h1 : inclZMod p 1 = e₁ p := by
      rw [← Nat.cast_one, inclZMod_natCast, one_nsmul]
    have h2 := congrArg (fun f => f (1 : ZMod p)) hφ₀
    simp only [AddMonoidHom.coe_comp, Function.comp_apply] at h2
    rw [AddMonoidHom.coe_comp, Function.comp_apply, ← h1, h2]
    change ((g 1 : divPart p A) : A) = x
    rw [← Int.cast_one, ZMod.lift_coe]
    simp [zmultiplesHom_apply]
  have hxord : addOrderOf x = p := addOrderOf_eq_prime hjp hj0
  rw [injective_iff_map_eq_zero]
  intro y hy
  by_contra hy0
  obtain ⟨i, hi0, hip⟩ := exists_nsmul_ne_zero_p_nsmul_eq_zero (isPPrimary_Qp (p := p)) hy0
  obtain ⟨k, hk⟩ := exists_nsmul_e₁_eq hip
  apply hi0
  have hz : ((divPart p A).subtype.comp φ₀) (p ^ i • y) = 0 := by rw [map_nsmul, hy, nsmul_zero]
  rw [← hk, map_nsmul, hφe] at hz
  rw [← hk, nsmul_e₁_eq_zero_iff, ← hxord]
  exact addOrderOf_dvd_of_nsmul_eq_zero hz

/-- **The splitting `A ≃ Q × ker ρ`** for a retraction `ρ` of `φ : Q → A`. -/
def splitEquiv {Q : Type*} [AddCommGroup Q] (φ : Q →+ A) (ρ : A →+ Q) (h : ∀ y, ρ (φ y) = y) :
    A ≃+ Q × ρ.ker where
  toFun a := (ρ a, ⟨a - φ (ρ a), by rw [AddMonoidHom.mem_ker, map_sub, h, sub_self]⟩)
  invFun yb := φ yb.1 + yb.2
  left_inv a := by simp
  right_inv yb := by
    obtain ⟨y, b, hb⟩ := yb
    rw [AddMonoidHom.mem_ker] at hb
    ext
    · simp [h, hb]
    · simp [h, hb]
  map_add' a b := by
    ext
    · simp
    · simp only [map_add, Prod.snd_add, AddSubgroup.coe_add]
      abel

end Embed

/-! ### The base case: zero divisible part -/

section Base

variable {A : Type*} [AddCommGroup A]

/-- **A `p`-primary group with finite `p`-torsion and zero divisible part is finite.** -/
theorem finite_of_divPart_eq_bot (hA : IsPPrimary p A) (hfin : Finite (tors A p))
    (hD : divPart p A = ⊥) : Finite A := by
  classical
  have : Fintype (tors A p) := Fintype.ofFinite _
  have hmiss : ∀ a : tors A p, ∃ n : ℕ, (a : A) = 0 ∨
      (a : A) ∉ (nsmulAddMonoidHom (α := A) (p ^ n)).range := by
    intro a
    by_cases ha : (a : A) = 0
    · exact ⟨0, Or.inl ha⟩
    · by_contra hall
      push Not at hall
      apply ha
      have : (a : A) ∈ divPart p A := AddSubgroup.mem_iInf.mpr fun n => (hall n).2
      rw [hD] at this
      exact this
  choose n hn using hmiss
  let N := Finset.univ.sup n
  have hN : ∀ b : A, p ^ N • b = 0 := by
    intro b
    by_contra hc
    obtain ⟨j, hj0, hjp⟩ := exists_nsmul_ne_zero_p_nsmul_eq_zero hA hc
    let z : tors A p := ⟨p ^ j • p ^ N • b, mem_tors.mpr hjp⟩
    rcases hn z with h | h
    · exact hj0 h
    · apply h
      refine range_pow_antitone p (Finset.le_sup (Finset.mem_univ z)) ⟨p ^ j • b, ?_⟩
      simp only [nsmulAddMonoidHom_apply, z]
      rw [smul_comm]
  have := finite_tors_pow hfin N
  exact Finite.of_injective (fun b : A => (⟨b, mem_tors.mpr (hN b)⟩ : tors A (p ^ N)))
    (fun a b h => congrArg Subtype.val h)

end Base

/-! ### The structure theorem -/

section Structure

/-- `Q × Q^t ≃ Q^{t+1}`. -/
def consAddEquiv (Q : Type*) [AddCommGroup Q] (t : ℕ) : Q × (Fin t → Q) ≃+ (Fin (t + 1) → Q) :=
  { Fin.consEquiv (fun _ : Fin (t + 1) => Q) with
    map_add' := fun x y => by
      funext i
      refine Fin.cases ?_ ?_ i <;> simp [Fin.consEquiv] }

universe u

/-- **Structure of cofinitely generated `p`-primary groups**: a `p`-primary abelian group with
finite `p`-torsion is isomorphic to `(ℚ_p/ℤ_p)^t × F` with `F` finite. -/
theorem exists_addEquiv_of_isPPrimary (A : Type u) [AddCommGroup A] (hA : IsPPrimary p A)
    (hfin : Finite (tors A p)) :
    ∃ (t : ℕ) (F : Type u) (_ : AddCommGroup F) (_ : Finite F),
      Nonempty (A ≃+ (Fin t → Qp p) × F) := by
  classical
  suffices H : ∀ (n : ℕ) (A : Type u) [AddCommGroup A], IsPPrimary p A → Finite (tors A p) →
      Nat.card (tors A p) = n →
      ∃ (t : ℕ) (F : Type u) (_ : AddCommGroup F) (_ : Finite F),
        Nonempty (A ≃+ (Fin t → Qp p) × F) from H _ A hA hfin rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A _ hA hfin hcard
    by_cases hD : divPart p A = ⊥
    · have hAfin := finite_of_divPart_eq_bot hA hfin hD
      exact ⟨0, A, inferInstance, hAfin, ⟨(AddEquiv.uniqueProd).symm⟩⟩
    obtain ⟨φ, hφ⟩ := exists_injective_of_divPart_ne_bot hA hfin hD
    obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Qp p)).extension_property_addMonoidHom φ hφ
      (AddMonoidHom.id _)
    have hρφ : ∀ y, ρ (φ y) = y := fun y => congrArg (fun f => f y) hρ
    let B := ρ.ker
    have hB : IsPPrimary p B := fun b => (hA b).imp fun k hk => Subtype.ext (by simpa using hk)
    let ι : tors B p → tors A p := fun b => ⟨(b : B), mem_tors.mpr (by
      have := congrArg Subtype.val (mem_tors.mp b.2); simpa using this)⟩
    have hι : Function.Injective ι := fun a b h => Subtype.ext (Subtype.ext
      (congrArg (fun z : tors A p => (z : A)) h))
    have hBfin : Finite (tors B p) := Finite.of_injective ι hι
    have hnot : ¬ Function.Surjective ι := by
      intro hs
      obtain ⟨b, hb⟩ := hs ⟨φ (e₁ p), mem_tors.mpr (by rw [← map_nsmul, p_nsmul_e₁, map_zero])⟩
      have h1 : ((b : B) : A) = φ (e₁ p) := congrArg Subtype.val hb
      have h2 : ρ (φ (e₁ p)) = 0 := by rw [← h1]; exact (b : B).2
      exact e₁_ne_zero (by rw [← hρφ (e₁ p), h2])
    have hlt : Nat.card (tors B p) < n := by
      have : Fintype (tors B p) := Fintype.ofFinite _
      have : Fintype (tors A p) := Fintype.ofFinite _
      rw [← hcard, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact Fintype.card_lt_of_injective_not_surjective ι hι hnot
    obtain ⟨t, F, _, hF, ⟨e⟩⟩ := ih _ hlt B hB hBfin rfl
    refine ⟨t + 1, F, inferInstance, hF, ⟨?_⟩⟩
    exact (splitEquiv φ ρ hρφ).trans ((AddEquiv.prodCongr (AddEquiv.refl _) e).trans
      ((AddEquiv.prodAssoc).symm.trans
        (AddEquiv.prodCongr (consAddEquiv (Qp p) t) (AddEquiv.refl F))))

end Structure

end ZInQ.Cofinite
