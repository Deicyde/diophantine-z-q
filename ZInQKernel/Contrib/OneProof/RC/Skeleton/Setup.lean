import ZInQKernel.Contrib.CloudB3RC53.Nodes

/-!
# Theorem 5.3, Lane RC0: vocabulary for Elliot's finer steps behind `BranchPackageNode`

The shared top layer of the Lean proof of Theorem 5.3 (`hyp:RC`, `diophantine_zq.tex` 11/5,
lines 1005–1011) is the blueprint `ZInQ.Contrib.CloudB3RC53` (`Basic`, `Prints`, `Nodes`,
`Assembly`). Its open node `BranchPackageNode` bundles Sections 7–9 and Appendices E–G: Branch 1,
or the fixed-field package `FixedFieldPackage` of Branch 2. This lane proves that node from
Elliot's finer steps (`Steps.lean`, `Skeleton.lean`). This file adds, over the blueprint's
vocabulary (`Adm`, `Ecurve`, `qtwist`, `AnalyticRank`, `ProductOrderGeTwo`, `CoordData`,
`signEval`, `sgn`), the few objects the finer steps need. Everything here is a definition or a
PROVED fact.

* `qtwist_curve : qtwist (curve ℓ) d = curve (d * ℓ)` — twists of `E_ℓ` are curves of the family;
  `qtwist_iso` — over a field containing `√d` the twist is a variable change (a sanity check).
* `v2` (the 2-adic valuation on `ℚ₂`, in `WithTop ℤ`, `v2 0 = ⊤`) and its comparison with norms;
  `omega h` (`ω(h)`); `shaLength E` (`s(h)` of lines 1828–1830, over the tree's genuine Ш).
* Binary families (3.9): `Addr b = 𝔽₂^b`, `qstar`, `Family`, `Family.h`, `Family.Admissible`.
* `Λ[1/2]` inside `ℚ₂[[t]]` (`InLamHalf`), `Λ`-units (`LamUnit`), the central value `central`.
* Restriction of coefficient data to a coordinate subcube (`restrictData`), PROVED to
  preserve every predicate of the blueprint's package (`ClearingIdentity`, `PoleBound`,
  `BaseRegular`, `UpperBound`, `BaseZero`). It is needed because `FixedFieldPackage.coord`
  quantifies over every binary dimension `b` allowed by (5.10), while (3.9) supplies families only
  for every sufficiently large `b` (DEPARTURE of form, not in the text: a family of a larger
  dimension is restricted to a subcube).
-/

noncomputable section

namespace ZInQ.Manuscript.RC

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53 Filter Topology

attribute [local instance] Nat.fact_prime_two

/-! ## Quadratic twists of the family -/

/-- **Twists of `E_ℓ` are curves of the family** (PROVED): `qtwist (curve ℓ) d = curve (d ℓ)`, i.e.
`d y² = x(x − ℓ)(x + 3ℓ)` is `Y² = X(X − dℓ)(X + 3dℓ)` with `X = dx`, `Y = d²y`. -/
theorem qtwist_curve (ℓ d : ℚ) : qtwist (curve ℓ) d = curve (d * ℓ) := by
  simp only [qtwist, curve, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  congr 1 <;> ring

/-- `E^{(1)} = E` for the curves of the family (PROVED). -/
theorem qtwist_one_curve (ℓ : ℚ) : qtwist (curve ℓ) 1 = curve ℓ := by
  rw [qtwist_curve, one_mul]

/-- **The twist is a twist** (PROVED; a sanity check of `qtwist`): over any field `F ⊇ ℚ`
containing a square root `δ ≠ 0` of `d`, the variable change `u = δ⁻¹` carries `E` to `E^{(d)}`,
for every `E` with `a₁ = a₃ = 0`. -/
theorem qtwist_iso {F : Type*} [Field F] [Algebra ℚ F] (E : WeierstrassCurve ℚ)
    (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0) (d : ℚ) (δ : F) (hδ : δ ≠ 0)
    (hδd : δ ^ 2 = algebraMap ℚ F d) :
    ∃ C : WeierstrassCurve.VariableChange F,
      C • E.baseChange F = (qtwist E d).baseChange F := by
  have hq : qtwist E d = ⟨0, d * E.a₂, 0, d ^ 2 * E.a₄, d ^ 3 * E.a₆⟩ := by
    simp only [qtwist, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, h₁, h₃]
    congr 1 <;> ring
  rw [hq]
  refine ⟨⟨Units.mk0 δ⁻¹ (inv_ne_zero hδ), 0, 0, 0⟩, ?_⟩
  ext
  · simp [WeierstrassCurve.variableChange_a₁, h₁]
  · simp [WeierstrassCurve.variableChange_a₂, h₁]
    simp only [← eq_ratCast (algebraMap ℚ F), map_mul]
    linear_combination (algebraMap ℚ F E.a₂) * hδd
  · simp [WeierstrassCurve.variableChange_a₃, h₁, h₃]
  · simp [WeierstrassCurve.variableChange_a₄, h₁, h₃]
    simp only [← eq_ratCast (algebraMap ℚ F), map_mul, map_pow]
    linear_combination (algebraMap ℚ F E.a₄ * (δ ^ 2 + algebraMap ℚ F d)) * hδd
  · simp [WeierstrassCurve.variableChange_a₆, h₁, h₃]
    simp only [← eq_ratCast (algebraMap ℚ F), map_mul, map_pow]
    linear_combination (algebraMap ℚ F E.a₆ * (δ ^ 4 + δ ^ 2 * algebraMap ℚ F d +
      algebraMap ℚ F d ^ 2)) * hδd

/-! ## Valuations, `ω`, `s(h)` -/

/-- The 2-adic valuation on `ℚ₂`, valued in `WithTop ℤ` (`v2 0 = ⊤`). -/
def v2 (x : ℚ_[2]) : WithTop ℤ := Padic.addValuation x

/-- The 2-adic valuation of an integer (`vZ 0 = ⊤`). -/
def vZ (n : ℤ) : WithTop ℤ := v2 (n : ℚ_[2])

/-- `ω(h)`: the number of distinct prime factors of `|h|`. -/
def omega (h : ℤ) : ℕ := ArithmeticFunction.cardDistinctFactors h.natAbs

/-- **`s(h)`** (lines 1828–1830) for `E^{(h)}`: `length_{ℤ₂} Ш(E/ℚ)[2^∞]`, i.e. `log₂` of the
order of the `2`-primary part of the tree's genuine `Ш(E/ℚ)` (`SelmerTwoPower.sha`). It is used
only where `Ш(E^{(h)}/ℚ)[2^∞]` is finite; otherwise `Nat.card = 0` and the value is the junk `0`. -/
def shaLength (E : WeierstrassCurve ℚ) : ℕ :=
  Nat.log 2 (Nat.card (AddCommGroup.primaryComponent (sha E) 2))

/-- `v₂` of a nonzero 2-adic integer is its `PadicInt.valuation` (PROVED). -/
theorem v2_coe_padicInt {z : ℤ_[2]} (hz : z ≠ 0) : v2 (z : ℚ_[2]) = ((z.valuation : ℕ) : ℤ) := by
  rw [v2, Padic.addValuation.apply (by simpa using hz), PadicInt.valuation_coe]

/-- The 2-adic valuation of a unit of `ℤ₂` is `0` (PROVED). -/
theorem v2_coe_of_isUnit {z : ℤ_[2]} (hz : IsUnit z) : v2 (z : ℚ_[2]) = 0 := by
  have hz0 : z ≠ 0 := hz.ne_zero
  have hn := PadicInt.norm_eq_zpow_neg_valuation hz0
  rw [PadicInt.isUnit_iff.mp hz, zpow_neg, zpow_natCast] at hn
  have h2 : ((2 : ℕ) : ℝ) ^ z.valuation = 1 := by
    have := congrArg (·⁻¹) hn
    simpa using this.symm
  have hv : z.valuation = 0 := by
    have h3 : (2 : ℕ) ^ z.valuation = 1 := by exact_mod_cast h2
    simpa using h3
  rw [v2_coe_padicInt hz0, hv]
  rfl

/-- A valuation bound `v₂ y ≤ m` is the norm bound `‖y‖ ≥ 2^{−m}` (PROVED). -/
theorem norm_ge_of_v2_le {y : ℚ_[2]} {m : ℤ} (h : v2 y ≤ (m : WithTop ℤ)) :
    (2 : ℝ) ^ (-m) ≤ ‖y‖ := by
  have hy : y ≠ 0 := by
    rintro rfl
    simp [v2] at h
  rw [v2, Padic.addValuation.apply hy] at h
  have hv : y.valuation ≤ m := WithTop.coe_le_coe.mp h
  rw [Padic.norm_eq_zpow_neg_valuation hy]
  exact_mod_cast zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ ((2 : ℕ) : ℝ)) (by omega)

/-! ## Binary addresses and the final family -/

/-- Binary addresses `x ∈ 𝔽₂^b` (lines 2179–2271). -/
abbrev Addr (b : ℕ) : Type := Fin b → ZMod 2

/-- `q^* = (−1)^{(q−1)/2} q` (the family (3.9)). -/
def qstar (q : ℕ) : ℤ := (-1) ^ ((q - 1) / 2) * q

/-- **A binary family** (Proposition `ex:sec7-final-family`, lines 2695–2715): an address
dimension `b`, a finite set `Q` of primes and linear forms `λ_q : 𝔽₂^b → 𝔽₂`. -/
structure Family where
  /-- the address dimension `b` -/
  b : ℕ
  /-- the finite set of primes -/
  Q : Finset ℕ
  /-- the linear forms `λ_q` -/
  lam : ℕ → Addr b →ₗ[ZMod 2] ZMod 2

/-- The family `h_x = ∏_{q ∈ Q} (q^*)^{λ_q(x)}` of (3.9). -/
def Family.h (F : Family) (x : Addr F.b) : ℤ :=
  ∏ q ∈ F.Q, qstar q ^ (F.lam q x).val

/-- `h_0 = 1` (PROVED). -/
@[simp] theorem Family.h_zero (F : Family) : F.h 0 = 1 := by
  simp [Family.h]

/-- **Admissible family for the companion `k`**: the primes of `Q` are distinct good odd primes
outside the fixed support `S` (which contains the primes of `2N`, of `h_*` and of `k`), split in
`K = ℚ(√k)` (`(k/q) = 1`), and every `λ_q` is a nonzero linear form (lines 2700–2702, 4253–4256). -/
def Family.Admissible (S : Finset ℕ) (k : ℤ) (F : Family) : Prop :=
  ∀ q ∈ F.Q, q.Prime ∧ q ≠ 2 ∧ q ∉ S ∧ jacobiSym k q = 1 ∧ F.lam q ≠ 0

/-- `q^* ≠ 0` for `q ≠ 0` (PROVED). -/
theorem qstar_ne_zero {q : ℕ} (hq : q ≠ 0) : qstar q ≠ 0 := by
  unfold qstar
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast hq)

/-- The members of an admissible family are nonzero (PROVED). -/
theorem Family.h_ne_zero {S : Finset ℕ} {k : ℤ} {F : Family} (hF : F.Admissible S k)
    (x : Addr F.b) : F.h x ≠ 0 := by
  unfold Family.h
  rw [Finset.prod_ne_zero_iff]
  intro q hq
  exact pow_ne_zero _ (qstar_ne_zero (hF q hq).1.ne_zero)

/-- A prime dividing `h_x` belongs to `Q` (PROVED). -/
theorem Family.mem_Q_of_prime_dvd {S : Finset ℕ} {k : ℤ} {F : Family} (hF : F.Admissible S k)
    (x : Addr F.b) {p : ℕ} (hp : p.Prime) (hpd : (p : ℤ) ∣ F.h x) : p ∈ F.Q := by
  unfold Family.h at hpd
  obtain ⟨q, hq, hdvd⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff_prime_int.mp hp) _).mp hpd
  have h1 : (p : ℤ) ∣ qstar q := (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hdvd
  unfold qstar at h1
  have h2 : (p : ℤ) ∣ (q : ℤ) := ((isUnit_neg_one (α := ℤ)).pow _).dvd_mul_left.mp h1
  have h3 : p ∣ q := Int.natCast_dvd_natCast.mp h2
  rwa [(Nat.prime_dvd_prime_iff_eq hp (hF q hq).1).mp h3]

/-! ## `Λ`, `Λ[1/2]` and the central value -/

/-- **`u ∈ Λ[1/2]`** for `u ∈ ℚ₂[[t]]`: bounded denominators, `u = g / 2^e` with `g ∈ ℤ₂[[t]] = Λ`. -/
def InLamHalf (u : PowerSeries ℚ_[2]) : Prop :=
  ∃ (e : ℕ) (g : ℕ → ℤ_[2]), ∀ n : ℕ, PowerSeries.coeff n u = (g n : ℚ_[2]) / 2 ^ e

/-- **`ε ∈ Λ^×`**, viewed in `ℚ₂[[t]]`. -/
def LamUnit (ε : PowerSeries ℚ_[2]) : Prop :=
  ∃ e : (PowerSeries ℤ_[2])ˣ, ε = PowerSeries.map PadicInt.Coe.ringHom (e : PowerSeries ℤ_[2])

/-- The central value `u(0)` of `u ∈ ℚ₂[[t]]` (specialization at `t = 0`). -/
def central (u : PowerSeries ℚ_[2]) : ℚ_[2] := PowerSeries.coeff 0 u

/-- **A `Λ`-unit multiple has the same central valuation** (PROVED; the use of (4.7) at
lines 4153–4155). -/
theorem v2_central_lamUnit_mul {ε u : PowerSeries ℚ_[2]} (hε : LamUnit ε) :
    v2 (central (ε * u)) = v2 (central u) := by
  obtain ⟨e, rfl⟩ := hε
  have hc : IsUnit (PowerSeries.constantCoeff (e : PowerSeries ℤ_[2])) :=
    (PowerSeries.isUnit_iff_constantCoeff).mp e.isUnit
  have h0 : central (PowerSeries.map PadicInt.Coe.ringHom (e : PowerSeries ℤ_[2]) * u) =
      ((PowerSeries.constantCoeff (e : PowerSeries ℤ_[2]) : ℤ_[2]) : ℚ_[2]) * central u := by
    have hm : PowerSeries.constantCoeff (PowerSeries.map PadicInt.Coe.ringHom
        (e : PowerSeries ℤ_[2])) = ((PowerSeries.constantCoeff (e : PowerSeries ℤ_[2]) : ℤ_[2]) :
          ℚ_[2]) := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      rfl
    simp [central, hm]
  rw [h0, v2, AddValuation.map_mul, ← v2, ← v2, v2_coe_of_isUnit hc, zero_add]

/-- Bounded denominators bound the coefficients (PROVED): `u = g/2^e`, `g ∈ Λ`, gives
`‖[tʲ]u‖ ≤ 2^e`. -/
theorem InLamHalf.norm_coeff_le {u : PowerSeries ℚ_[2]} {e : ℕ} {g : ℕ → ℤ_[2]}
    (hg : ∀ n : ℕ, PowerSeries.coeff n u = (g n : ℚ_[2]) / 2 ^ e) (j : ℕ) :
    ‖PowerSeries.coeff j u‖ ≤ (2 : ℝ) ^ e := by
  rw [hg j, norm_div, norm_pow]
  have h2 : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by
    have := Padic.norm_p (p := 2)
    push_cast at this
    exact this
  rw [h2, inv_pow, div_inv_eq_mul]
  have h1 : ‖(g j : ℚ_[2])‖ ≤ 1 := PadicInt.norm_le_one (g j)
  have hpos : (0 : ℝ) < 2 ^ e := by positivity
  nlinarith

/-! ## Restriction of coefficient data to a coordinate subcube -/

/-- The zero-padding embedding `𝔽₂^b → 𝔽₂^{b'}` (`b ≤ b'`). -/
def pad {b b' : ℕ} (x : Fin b → ZMod 2) : Fin b' → ZMod 2 :=
  fun i => if hi : (i : ℕ) < b then x ⟨i, hi⟩ else 0

/-- The coordinate projection `𝔽₂^{b'} → 𝔽₂^b` (`b ≤ b'`). -/
def proj {b b' : ℕ} (h : b ≤ b') (g : Fin b' → ZMod 2) : Fin b → ZMod 2 :=
  fun i => g ⟨i, lt_of_lt_of_le i.2 h⟩

theorem pad_zero {b b' : ℕ} : (pad (b' := b') (0 : Fin b → ZMod 2)) = 0 := by
  funext i
  simp [pad]

theorem pad_ne_zero {b b' : ℕ} {x : Fin b → ZMod 2} (hx : x ≠ 0) :
    (pad (b' := b') x) ≠ 0 ∨ b' < b := by
  by_cases hbb : b ≤ b'
  · left
    intro h
    apply hx
    funext i
    have := congrFun h ⟨i, lt_of_lt_of_le i.2 hbb⟩
    simpa [pad] using this
  · right; omega

/-- The pairing is compatible with padding and projection (PROVED):
`⟨pad x, g⟩ = ⟨x, proj g⟩`. -/
theorem sum_pad_mul {b b' : ℕ} (h : b ≤ b') (x : Fin b → ZMod 2) (g : Fin b' → ZMod 2) :
    (∑ i, pad x i * g i) = ∑ i, x i * proj h g i := by
  have hsub : (Finset.univ.map (Fin.castLEEmb h)) ⊆ (Finset.univ : Finset (Fin b')) :=
    Finset.subset_univ _
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hp : pad (b' := b') x ((Fin.castLEEmb h) i) = x i := by simp [pad, Fin.castLEEmb]
    rw [hp]
    rfl
  · intro i _ hi
    have hib : ¬ (i : ℕ) < b := by
      intro hlt
      apply hi
      exact Finset.mem_map.mpr ⟨⟨i, hlt⟩, Finset.mem_univ _, by ext; simp [Fin.castLEEmb]⟩
    simp [pad, hib]

theorem sgn_pad {b b' : ℕ} (h : b ≤ b') (x : Fin b → ZMod 2) (g : Fin b' → ZMod 2) :
    sgn (pad x) g = sgn x (proj h g) := by
  simp only [sgn, sum_pad_mul h]

/-- Push the group-basis coefficients forward along the projection `G' = 𝔽₂^{b'} → G = 𝔽₂^b`. -/
def pushCoeff {b b' : ℕ} (h : b ≤ b') (F : (Fin b' → ZMod 2) → ℤ → ℤ_[2]) :
    (Fin b → ZMod 2) → ℤ → ℤ_[2] :=
  fun g' i => ∑ g ∈ Finset.univ.filter (fun g => proj h g = g'), F g i

/-- Sign evaluation of the pushed coefficients at `x` is sign evaluation at `pad x` (PROVED). -/
theorem signEval_pushCoeff {b b' : ℕ} (h : b ≤ b') (F : (Fin b' → ZMod 2) → ℤ → ℤ_[2])
    (x : Fin b → ZMod 2) (i : ℤ) :
    signEval (pushCoeff h F) x i = signEval F (pad x) i := by
  unfold signEval pushCoeff
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := proj h)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun g' _ => ?_
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [(Finset.mem_filter.mp hg).2.symm, sgn_pad h]

/-- **Restriction of coefficient data to the subcube `𝔽₂^b ⊆ 𝔽₂^{b'}`**: the group-ring
coefficients are pushed forward along the projection and the coordinates are read at padded
addresses. -/
def restrictData {b b' : ℕ} (h : b ≤ b') (C : CoordData b') : CoordData b where
  F := pushCoeff h C.F
  D := pushCoeff h C.D
  u := fun x j => C.u (pad x) j

theorem restrictData_clearing {b b' : ℕ} (h : b ≤ b') {C : CoordData b'}
    (hC : ClearingIdentity C) : ClearingIdentity (restrictData h C) := by
  obtain ⟨hdec, ⟨e, he⟩, hsum⟩ := hC
  refine ⟨fun g' => ?_, ⟨e, fun x j => he _ j⟩, fun x n => ?_⟩
  · have := tendsto_finsetSum (Finset.univ.filter (fun g => proj h g = g'))
      (fun g _ => hdec g)
    simp only [Finset.sum_const_zero] at this
    exact this
  · simpa [restrictData, signEval_pushCoeff h] using hsum (pad x) n

theorem restrictData_pole {b b' : ℕ} (h : b ≤ b') {C : CoordData b'} {LT M : ℕ}
    (hC : PoleBound C LT M) : PoleBound (restrictData h C) LT M := by
  intro x i hi
  simpa [restrictData, signEval_pushCoeff h] using hC (pad x) i hi

theorem restrictData_base {b b' : ℕ} (h : b ≤ b') {C : CoordData b'} {c : ℕ}
    (hC : BaseRegular C c) : BaseRegular (restrictData h C) c := by
  obtain ⟨h1, h2, h3⟩ := hC
  refine ⟨fun i hi => ?_, ?_, ?_⟩ <;>
    simp only [restrictData, signEval_pushCoeff h, pad_zero] <;> simp_all

theorem restrictData_upper {b b' : ℕ} (h : b ≤ b') {C : CoordData b'} {B : ℕ}
    (hC : UpperBound C B) : UpperBound (restrictData h C) B := by
  intro x hx
  rcases pad_ne_zero (b' := b') hx with h' | h'
  · exact hC _ h'
  · omega

theorem restrictData_baseZero {b b' : ℕ} (h : b ≤ b') {E : WeierstrassCurve ℚ} {k : ℚ}
    {C : CoordData b'} (hC : BaseZero E k C) : BaseZero E k (restrictData h C) := by
  intro hP
  simpa [restrictData, pad_zero] using hC hP

end ZInQ.Manuscript.RC
