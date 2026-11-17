import Mathlib

/-!
# Lane RC6: the outer quotient `𝒪_∞` of (5.3), and what passes to it

This file formalizes the algebra in the last paragraph of the proof of Lemma
`ex:limits-outer-evaluation` (statement tex 4663-4671, proof tex 4719-4744).

## Manuscript dictionary

* `R`, `ϖ` : Elliot's coefficient ring `𝒪 = (Λ_(2))^`, `Λ = ℤ₂[[t]]` (tex 2747-2748), and its
  uniformizer `2`. We work with an arbitrary DVR `R` and an irreducible `ϖ : R`: the only properties of
  `𝒪` used in tex 4719-4744 are that it is a DVR with uniformizer two and of characteristic zero.
  Concrete instances at the end of the file: `R = ℤ_[2]` and `R = Λ_(2)` (section `ScalarRing`,
  where `Λ_(2)` is proved to be a DVR with uniformizer `2`), both with `ϖ = 2`.
  In instances the uniformizer hypothesis is a `[Fact (Irreducible ϖ)]`; theorems take
  `hϖ : Irreducible ϖ`.
* `ι`, `U` : the index `j` of the sequence of ring instances `(K_j, h_j)`, and the one fixed
  ultrafilter `𝒰` (tex 4681). Nonprincipality of `U` is never used (see the example with a principal
  ultrafilter at the end).
* `infinitesimals U ϖ` : the ideal `{(x_j) : v₂(x_j) →_𝒰 ∞}` of (5.3).
* `OInf U ϖ` : the ring `𝒪_∞` of (5.3); `toOInf U ϖ` : the passage `(x_j) ↦ [x_j]` (the quotient map).
* `outerMatrix U ϖ M` : the image in `𝒪_∞` of a sequence `(M_j)` of integral matrices (tex 4732-4738).
* `outerRep U ϖ ρ`, `outerCochain U ϖ w` : `ρ_∞` and `w_∞` on the product group `Γ = ∏_j G_j`
  (tex 4674-4682, 4740-4742); `cocycleDefect` : the degree-two term of (5.2).

## DEPARTURES (of form only)

* Elliot writes `(∏_𝒰 𝒪_j)/{(x_j) : v₂(x_j) →_𝒰 ∞}` with the ultraproduct `∏_𝒰 𝒪_j`. We take the
  quotient of the full product `ι → R` by `infinitesimals U ϖ`. Every `U`-null sequence is
  infinitesimal, so by the third isomorphism theorem this is canonically the same ring; this is proved
  as `ultraproductQuotientEquiv` (with Mathlib's ultraproduct `Filter.Germ U R`).
* Elliot proves principality by "every nonzero ideal has an element of least valuation". We prove
  Elliot's preceding sentence (every nonzero element is a power of the uniformizer times a unit,
  `exists_associated_pow`) and conclude with Mathlib's
  `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization`, whose principality step takes the
  least power of the uniformizer lying in the ideal, i.e. an element of least valuation.
* "Uniformizer two" is stated for the image of `ϖ` (Elliot: `ϖ = 2`, whose image is `2`).
* Elliot's `𝒪` is replaced by an arbitrary DVR `R`. The concrete ring `Λ_(2)` is treated in section
  `ScalarRing`; passing from `Λ_(2)` to its `2`-adic completion `𝒪` is GLUE (not formalized).

## Main results (all PROVED)

* (5.3) is a DVR with uniformizer two and characteristic zero: `instIsDomain`,
  `instIsDiscreteValuationRing`, `irreducible_algebraMap`, `maximalIdeal_eq_span_algebraMap`,
  `ideal_eq_span_pow`, `instCharZero`, `charZero_fractionRing`, built on
  `exists_eventually_eq_pow_mul_unit` and `exists_associated_pow` (tex 4726-4730).
* Passing data: `outerMatrix_mul`, `outerMatrixHom`, `map_toOInf_eq_of_sub_mem`,
  `map_toOInf_eq_of_eventually`, `formula_5_2_outer` (tex 4732-4733); Nakayama and minimal homotopy
  equivalences: `matrix_isUnit_of_isUnit_map_residue`, `isUnit_mul_of_minimal_homotopy`,
  `inverse_of_minimal_homotopy_equivalence`, `outer_inverse_of_minimal_homotopy_equivalence`
  (tex 4734-4738).
* Approximate cycles: `outerRep`, `outer_isCrossedHom`, `cocycleDefect_mem_infinitesimals`,
  `outer_isCrossedHom_of_approximate_cycle`, `outer_isCrossedHom_of_formula_5_2` (tex 4740-4742).
-/

open Filter Topology
open scoped Matrix

namespace ZInQ.Manuscript.RC.Limits

section Recognition

variable {S : Type*} [CommRing S] [IsDomain S]

/-- If every nonzero element of a domain is associated to a power of the nonzero nonunit `p`, then `p`
is irreducible. Used for tex 4726-4729 ("uniformizer two").
Kind: PROVED. -/
theorem irreducible_of_forall_associated_pow {p : S}
    (hp0 : p ≠ 0) (hpu : ¬IsUnit p) (h : ∀ x : S, x ≠ 0 → ∃ n : ℕ, Associated (p ^ n) x) :
    Irreducible p := by
  refine ⟨hpu, fun a b hab => ?_⟩
  have ha : a ≠ 0 := by rintro rfl; exact hp0 (by rw [hab, zero_mul])
  have hb : b ≠ 0 := by rintro rfl; exact hp0 (by rw [hab, mul_zero])
  obtain ⟨k, hk⟩ := h a ha
  obtain ⟨l, hl⟩ := h b hb
  have hkl : Associated (p ^ (k + l)) (p ^ 1) := by
    have h2 : Associated (p ^ k * p ^ l) (a * b) := hk.mul_mul hl
    rw [← hab, ← pow_add] at h2
    rwa [pow_one]
  have h1 : k + l = 1 := le_antisymm ((pow_dvd_pow_iff hp0 hpu).mp hkl.dvd)
    ((pow_dvd_pow_iff hp0 hpu).mp hkl.symm.dvd)
  rcases Nat.add_eq_one_iff.mp h1 with ⟨rfl, -⟩ | ⟨-, rfl⟩
  · left; rw [pow_zero] at hk; exact associated_one_iff_isUnit.mp hk.symm
  · right; rw [pow_zero] at hl; exact associated_one_iff_isUnit.mp hl.symm

/-- A domain in which every nonzero element is associated to a power of one nonzero nonunit `p` is a
DVR (tex 4726-4729: "a nonzero element ... is that power of two times a unit ... Thus (5.3) is a DVR").
Kind: PROVED (via Mathlib's `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization`). -/
theorem isDiscreteValuationRing_of_forall_associated_pow
    {p : S} (hp0 : p ≠ 0) (hpu : ¬IsUnit p)
    (h : ∀ x : S, x ≠ 0 → ∃ n : ℕ, Associated (p ^ n) x) : IsDiscreteValuationRing S :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨p, irreducible_of_forall_associated_pow hp0 hpu h, fun {x} hx => h x hx⟩

end Recognition

section Outer

variable {R : Type*} [CommRing R] {ι : Type*} (U : Ultrafilter ι) (ϖ : R)

/-- The ideal `{(x_j) : v₂(x_j) →_𝒰 ∞}` of (5.3) (tex 4724), written with divisibility:
`x` is infinitesimal iff for every `n`, `ϖ ^ n ∣ x_j` for `𝒰`-almost every `j`. For a DVR this is
literally `v_ϖ(x_j) →_𝒰 ∞`, see `mem_infinitesimals_iff_tendsto_addVal`.
Kind: definition. -/
def infinitesimals : Ideal (ι → R) where
  carrier := {x | ∀ n : ℕ, ∀ᶠ j in (U : Filter ι), ϖ ^ n ∣ x j}
  add_mem' {x y} hx hy n := by
    filter_upwards [hx n, hy n] with j hxj hyj
    exact dvd_add hxj hyj
  zero_mem' n := Eventually.of_forall fun _ => dvd_zero _
  smul_mem' c x hx n := by
    filter_upwards [hx n] with j hxj
    exact Dvd.dvd.mul_left hxj (c j)

variable {U ϖ} in
/-- Membership in `infinitesimals` (tex 4724). Kind: PROVED (by definition). -/
theorem mem_infinitesimals {x : ι → R} :
    x ∈ infinitesimals U ϖ ↔ ∀ n : ℕ, ∀ᶠ j in (U : Filter ι), ϖ ^ n ∣ x j :=
  Iff.rfl

/-- Every `𝒰`-null sequence is infinitesimal (this is why the quotient (5.3) of the ultraproduct is the
same as the quotient of the full product). Kind: PROVED. -/
theorem mem_infinitesimals_of_eventually_eq_zero {x : ι → R}
    (h : ∀ᶠ j in (U : Filter ι), x j = 0) : x ∈ infinitesimals U ϖ := fun n => by
  filter_upwards [h] with j hj
  rw [hj]
  exact dvd_zero _

/-- Elliot's ring `𝒪_∞` of (5.3) (tex 4720-4724), for copies `𝒪_j = R` indexed by `j ∈ ι`.
DEPARTURE: quotient of the full product `ι → R` rather than of the ultraproduct; canonically the same
ring, see `ultraproductQuotientEquiv`. Kind: definition. -/
abbrev OInf : Type _ := (ι → R) ⧸ infinitesimals U ϖ

/-- The passage `π : (x_j) ↦ [x_j]` from sequences to `𝒪_∞` (tex 4732-4738: data "pass to (5.3)").
Kind: definition. -/
abbrev toOInf : (ι → R) →+* OInf U ϖ := Ideal.Quotient.mk (infinitesimals U ϖ)

/-- Kind: PROVED. -/
theorem toOInf_eq_zero_iff {x : ι → R} : toOInf U ϖ x = 0 ↔ x ∈ infinitesimals U ϖ :=
  Ideal.Quotient.eq_zero_iff_mem

/-- Kind: PROVED. -/
theorem toOInf_eq_toOInf_iff {x y : ι → R} :
    toOInf U ϖ x = toOInf U ϖ y ↔ x - y ∈ infinitesimals U ϖ :=
  Ideal.Quotient.eq

/-- Sequences agreeing at `𝒰`-almost every `j` have the same image in `𝒪_∞`. Kind: PROVED. -/
theorem toOInf_eq_of_eventuallyEq {x y : ι → R} (h : ∀ᶠ j in (U : Filter ι), x j = y j) :
    toOInf U ϖ x = toOInf U ϖ y := by
  rw [toOInf_eq_toOInf_iff]
  apply mem_infinitesimals_of_eventually_eq_zero
  filter_upwards [h] with j hj
  rw [Pi.sub_apply, hj, sub_self]

/-- The structure map `𝒪 → 𝒪_∞` is the diagonal (constant sequences). Kind: PROVED. -/
theorem algebraMap_eq_toOInf (r : R) : algebraMap R (OInf U ϖ) r = toOInf U ϖ (fun _ => r) :=
  rfl

variable {ϖ} in
/-- The image of a nonunit `ϖ` is not a unit of `𝒪_∞`. Kind: PROVED. -/
theorem not_isUnit_algebraMap (hϖ : ¬IsUnit ϖ) : ¬IsUnit (algebraMap R (OInf U ϖ) ϖ) := by
  rintro ⟨v, hv⟩
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑v⁻¹ : OInf U ϖ)
  have h1 : toOInf U ϖ ((fun _ : ι => ϖ) * y - 1) = 0 := by
    rw [map_sub, map_mul, map_one, ← algebraMap_eq_toOInf, hy, ← hv, Units.mul_inv, sub_self]
  rw [toOInf_eq_zero_iff] at h1
  obtain ⟨j, hj⟩ := (h1 1).exists
  rw [pow_one, Pi.sub_apply, Pi.mul_apply, Pi.one_apply] at hj
  have h2 : ϖ ∣ 1 := by
    have h3 := dvd_sub (dvd_mul_right ϖ (y j)) hj
    rwa [sub_sub_cancel] at h3
  exact hϖ (isUnit_of_dvd_one h2)

/-! ### The ultraproduct form of (5.3) -/

section Ultraproduct

/-- The kernel of the passage to Mathlib's ultraproduct `∏_𝒰 𝒪_j = Filter.Germ U R` (the `𝒰`-null
sequences) consists of infinitesimals. Kind: PROVED. -/
theorem ker_germ_le_infinitesimals :
    RingHom.ker (Germ.coeRingHom (R := R) (U : Filter ι)) ≤ infinitesimals U ϖ := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  apply mem_infinitesimals_of_eventually_eq_zero
  have h2 : (x : (U : Filter ι).Germ R) = ((0 : ι → R) : (U : Filter ι).Germ R) := by
    rw [Germ.coe_zero]
    exact hx
  exact Germ.coe_eq.mp h2

/-- The passage to the ultraproduct is surjective. Kind: PROVED. -/
theorem germ_coeRingHom_surjective :
    Function.Surjective (Germ.coeRingHom (R := R) (U : Filter ι)) :=
  Quot.mk_surjective

/-- Elliot's ideal `{(x_j) : v₂(x_j) →_𝒰 ∞}` of the ultraproduct `∏_𝒰 𝒪_j` (tex 4723-4724).
Kind: definition. -/
def infinitesimalGerms : Ideal ((U : Filter ι).Germ R) :=
  (infinitesimals U ϖ).map (Germ.coeRingHom (U : Filter ι))

/-- The germ of `(x_j)` lies in `infinitesimalGerms` iff `(x_j)` is infinitesimal: the ideal of the
ultraproduct in (5.3) is exactly the set of germs of infinitesimal sequences. Kind: PROVED. -/
theorem coe_mem_infinitesimalGerms_iff (x : ι → R) :
    (x : (U : Filter ι).Germ R) ∈ infinitesimalGerms U ϖ ↔ x ∈ infinitesimals U ϖ := by
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ :=
      (Ideal.mem_map_iff_of_surjective (Germ.coeRingHom (R := R) (U : Filter ι))
        (germ_coeRingHom_surjective U)).mp hx
    have hd : y - x ∈ RingHom.ker (Germ.coeRingHom (R := R) (U : Filter ι)) := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      exact hyx
    have h3 := (infinitesimals U ϖ).sub_mem hy (ker_germ_le_infinitesimals U ϖ hd)
    rwa [sub_sub_cancel] at h3
  · intro hx
    exact Ideal.mem_map_of_mem _ hx

/-- (5.3) literally: `(∏_𝒰 𝒪_j)/{(x_j) : v₂(x_j) →_𝒰 ∞} ≃ (∏_j 𝒪_j)/{(x_j) : v₂(x_j) →_𝒰 ∞}`
(tex 4722-4724), by the third isomorphism theorem.
Kind: PROVED (justifies the DEPARTURE in `OInf`). -/
noncomputable def ultraproductQuotientEquiv :
    (U : Filter ι).Germ R ⧸ infinitesimalGerms U ϖ ≃+* OInf U ϖ :=
  (Ideal.quotientEquiv _ _ (RingHom.quotientKerEquivOfSurjective (germ_coeRingHom_surjective U))
      (by
        rw [infinitesimalGerms, Ideal.map_map]
        congr 1)).symm.trans
    (DoubleQuot.quotQuotEquivQuotOfLE (ker_germ_le_infinitesimals U ϖ))

/-- The isomorphism `ultraproductQuotientEquiv` is the canonical one: the class of the germ of `(x_j)`
goes to the class of `(x_j)`. Kind: PROVED. -/
theorem ultraproductQuotientEquiv_mk (x : ι → R) :
    ultraproductQuotientEquiv U ϖ
        (Ideal.Quotient.mk (infinitesimalGerms U ϖ) (x : (U : Filter ι).Germ R)) =
      toOInf U ϖ x := by
  have he : (RingHom.quotientKerEquivOfSurjective (germ_coeRingHom_surjective (R := R) U)).symm
      (x : (U : Filter ι).Germ R) =
        Ideal.Quotient.mk (RingHom.ker (Germ.coeRingHom (R := R) (U : Filter ι))) x := by
    rw [RingEquiv.symm_apply_eq]
    exact (RingHom.quotientKerEquivOfSurjective_apply_mk (germ_coeRingHom_surjective U) x).symm
  simp only [ultraproductQuotientEquiv, RingEquiv.trans_apply, Ideal.quotientEquiv_symm_mk]
  rw [he]
  exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk x (ker_germ_le_infinitesimals U ϖ)

end Ultraproduct

/-! ### (5.3) is a DVR with uniformizer two (tex 4726-4730) -/

section DVR

variable [IsDomain R]

variable {ϖ} in
/-- The constant sequences `ϖ ^ k` are not infinitesimal. Kind: PROVED. -/
theorem algebraMap_pow_ne_zero (hϖ : Irreducible ϖ) (k : ℕ) :
    algebraMap R (OInf U ϖ) ϖ ^ k ≠ 0 := by
  intro h
  rw [← map_pow, algebraMap_eq_toOInf, toOInf_eq_zero_iff] at h
  have hk := h (k + 1)
  rw [Filter.eventually_const] at hk
  exact Nat.not_succ_le_self k ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).mp hk)

variable [IsDiscreteValuationRing R]

variable {ϖ} in
/-- In a DVR, an element not divisible by the uniformizer is a unit. Kind: PROVED. -/
theorem isUnit_of_not_dvd (hϖ : Irreducible ϖ) {c : R} (h : ¬ϖ ∣ c) : IsUnit c := by
  by_contra hc
  have hm : c ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal c).mpr hc
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  exact h hm

variable {ϖ} in
/-- An element of exact valuation `m` is `ϖ ^ m` times a unit. Kind: PROVED. -/
theorem exists_isUnit_of_pow_dvd_of_not_pow_succ_dvd (hϖ : Irreducible ϖ) {m : ℕ} {y : R}
    (h1 : ϖ ^ m ∣ y) (h2 : ¬ϖ ^ (m + 1) ∣ y) : ∃ c, IsUnit c ∧ y = ϖ ^ m * c := by
  obtain ⟨c, rfl⟩ := h1
  refine ⟨c, isUnit_of_not_dvd hϖ fun hc => h2 ?_, rfl⟩
  rw [pow_succ]
  exact mul_dvd_mul_left _ hc

variable {ϖ} in
/-- tex 4726-4727: "A nonzero element has valuation one fixed nonnegative integer on a set in `𝒰` and
is that power of two times a unit." For a non-infinitesimal sequence `x` there are `m` and a sequence
of units `u` with `x_j = ϖ ^ m * u_j` for `𝒰`-almost every `j`. (The ultrafilter property turns
"bounded valuation on a `𝒰`-set" into "one fixed valuation `m` on a `𝒰`-set"; nonprincipality is not
used.) Kind: PROVED. -/
theorem exists_eventually_eq_pow_mul_unit (hϖ : Irreducible ϖ) {x : ι → R}
    (hx : x ∉ infinitesimals U ϖ) :
    ∃ (m : ℕ) (u : ι → R), (∀ j, IsUnit (u j)) ∧ ∀ᶠ j in (U : Filter ι), x j = ϖ ^ m * u j := by
  classical
  have hex : ∃ n : ℕ, ¬∀ᶠ j in (U : Filter ι), ϖ ^ n ∣ x j :=
    not_forall.mp fun h => hx (mem_infinitesimals.mpr h)
  have hN0 : Nat.find hex ≠ 0 := by
    intro h0
    have hspec := Nat.find_spec hex
    rw [h0, pow_zero] at hspec
    exact hspec (Eventually.of_forall fun _ => one_dvd _)
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero hN0
  have h1 : ∀ᶠ j in (U : Filter ι), ϖ ^ m ∣ x j :=
    not_not.mp (Nat.find_min hex (show m < Nat.find hex by omega))
  have h2 : ∀ᶠ j in (U : Filter ι), ¬ϖ ^ (m + 1) ∣ x j := by
    rw [Ultrafilter.eventually_not, ← hm]
    exact Nat.find_spec hex
  have hc : ∀ j, ∃ c : R, IsUnit c ∧ (ϖ ^ m ∣ x j → ¬ϖ ^ (m + 1) ∣ x j → x j = ϖ ^ m * c) := by
    intro j
    by_cases hj : ϖ ^ m ∣ x j ∧ ¬ϖ ^ (m + 1) ∣ x j
    · obtain ⟨c, hc1, hc2⟩ := exists_isUnit_of_pow_dvd_of_not_pow_succ_dvd hϖ hj.1 hj.2
      exact ⟨c, hc1, fun _ _ => hc2⟩
    · exact ⟨1, isUnit_one, fun hj1 hj2 => absurd ⟨hj1, hj2⟩ hj⟩
  choose u hu1 hu2 using hc
  refine ⟨m, u, hu1, ?_⟩
  filter_upwards [h1, h2] with j hj1 hj2
  exact hu2 j hj1 hj2

variable {ϖ} in
/-- tex 4726-4727 in `𝒪_∞`: every nonzero element of `𝒪_∞` is (associated to) a power of the image
of `ϖ`, i.e. a power of two times a unit. Kind: PROVED. -/
theorem exists_associated_pow (hϖ : Irreducible ϖ) (y : OInf U ϖ) (hy : y ≠ 0) :
    ∃ m : ℕ, Associated (algebraMap R (OInf U ϖ) ϖ ^ m) y := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hx : x ∉ infinitesimals U ϖ := fun h => hy ((toOInf_eq_zero_iff U ϖ).mpr h)
  obtain ⟨m, u, hu, hxu⟩ := exists_eventually_eq_pow_mul_unit U hϖ hx
  have hU : IsUnit (toOInf U ϖ u) := (Pi.isUnit_iff.mpr hu).map _
  refine ⟨m, hU.unit, ?_⟩
  have e : (fun j => ϖ ^ m * u j) = (fun _ : ι => ϖ) ^ m * u := by
    funext j
    rw [Pi.mul_apply, Pi.pow_apply]
  rw [IsUnit.unit_spec, toOInf_eq_of_eventuallyEq U ϖ hxu, e, map_mul, map_pow]
  rfl

variable {ϖ} in
/-- `𝒪_∞` is an integral domain. Kind: PROVED. -/
theorem isDomain (hϖ : Irreducible ϖ) : IsDomain (OInf U ϖ) := by
  have : Nontrivial (OInf U ϖ) :=
    ⟨⟨1, 0, by simpa only [pow_zero] using algebraMap_pow_ne_zero U hϖ 0⟩⟩
  have : NoZeroDivisors (OInf U ϖ) := ⟨fun {a b} hab => by
    by_contra h
    obtain ⟨ha, hb⟩ := not_or.mp h
    obtain ⟨k, hk⟩ := exists_associated_pow U hϖ a ha
    obtain ⟨l, hl⟩ := exists_associated_pow U hϖ b hb
    have hkl := hk.mul_mul hl
    rw [hab, ← pow_add] at hkl
    exact algebraMap_pow_ne_zero U hϖ (k + l) ((associated_zero_iff_eq_zero _).mp hkl)⟩
  exact NoZeroDivisors.to_isDomain _

variable {ϖ} in
/-- The ideal of infinitesimals is prime. Kind: PROVED. -/
theorem isPrime_infinitesimals (hϖ : Irreducible ϖ) : (infinitesimals U ϖ).IsPrime :=
  (Ideal.Quotient.isDomain_iff_prime _).mp (isDomain U hϖ)

/-- `𝒪_∞` is a domain (instance form; the uniformizer hypothesis is passed as a `Fact`).
Kind: PROVED. -/
instance instIsDomain [Fact (Irreducible ϖ)] : IsDomain (OInf U ϖ) :=
  isDomain U Fact.out

/-- tex 4729 "uniformizer two": the image of `ϖ` in `𝒪_∞` is irreducible. Kind: PROVED. -/
theorem irreducible_algebraMap [Fact (Irreducible ϖ)] :
    Irreducible (algebraMap R (OInf U ϖ) ϖ) :=
  irreducible_of_forall_associated_pow
    (by simpa only [pow_one] using algebraMap_pow_ne_zero U (Fact.out : Irreducible ϖ) 1)
    (not_isUnit_algebraMap U (Fact.out : Irreducible ϖ).not_isUnit)
    (exists_associated_pow U Fact.out)

/-- tex 4666 and 4729: "(5.3) is a DVR". No completeness and no nonprincipality of `U` is assumed.
DEPARTURE: principality via Mathlib's `ofHasUnitMulPowIrreducibleFactorization` (see the module
docstring). Kind: PROVED. -/
instance instIsDiscreteValuationRing [Fact (Irreducible ϖ)] :
    IsDiscreteValuationRing (OInf U ϖ) :=
  isDiscreteValuationRing_of_forall_associated_pow
    (by simpa only [pow_one] using algebraMap_pow_ne_zero U (Fact.out : Irreducible ϖ) 1)
    (not_isUnit_algebraMap U (Fact.out : Irreducible ϖ).not_isUnit)
    (exists_associated_pow U Fact.out)

/-- tex 4729 "with uniformizer two": the image of `ϖ` generates the maximal ideal of `𝒪_∞`.
Kind: PROVED. -/
theorem maximalIdeal_eq_span_algebraMap [Fact (Irreducible ϖ)] :
    IsLocalRing.maximalIdeal (OInf U ϖ) = Ideal.span {algebraMap R (OInf U ϖ) ϖ} :=
  (irreducible_algebraMap U ϖ).maximalIdeal_eq

/-- tex 4728-4729: "Every nonzero ideal ... is principal", generated by a power of the uniformizer
(its element of least valuation). Kind: PROVED. -/
theorem ideal_eq_span_pow [Fact (Irreducible ϖ)] {I : Ideal (OInf U ϖ)} (hI : I ≠ ⊥) :
    ∃ n : ℕ, I = Ideal.span {algebraMap R (OInf U ϖ) ϖ ^ n} :=
  IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI (irreducible_algebraMap U ϖ)

variable {ϖ} in
/-- In a DVR, an element divisible by every power of the uniformizer is zero. Kind: PROVED. -/
theorem eq_zero_of_forall_pow_dvd (hϖ : Irreducible ϖ) {r : R} (h : ∀ n : ℕ, ϖ ^ n ∣ r) :
    r = 0 := by
  rw [← IsDiscreteValuationRing.addVal_eq_top_iff, ENat.eq_top_iff_forall_ge]
  intro n
  rw [← hϖ.addVal_pow n]
  exact IsDiscreteValuationRing.addVal_le_iff_dvd.mpr (h n)

variable {ϖ} in
/-- The diagonal `𝒪 → 𝒪_∞` is injective. Kind: PROVED. -/
theorem algebraMap_injective (hϖ : Irreducible ϖ) :
    Function.Injective (algebraMap R (OInf U ϖ)) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  rw [algebraMap_eq_toOInf, toOInf_eq_zero_iff] at hr
  exact eq_zero_of_forall_pow_dvd hϖ fun n => Filter.eventually_const.mp (hr n)

/-- tex 4729-4730 "characteristic-zero fraction field": if `𝒪` has characteristic zero, so does
`𝒪_∞`. Kind: PROVED. -/
instance instCharZero [Fact (Irreducible ϖ)] [CharZero R] : CharZero (OInf U ϖ) :=
  charZero_of_injective_algebraMap (algebraMap_injective U Fact.out)

/-- tex 4729-4730: the fraction field of `𝒪_∞` has characteristic zero. Kind: PROVED. -/
theorem charZero_fractionRing [Fact (Irreducible ϖ)] [CharZero R] :
    CharZero (FractionRing (OInf U ϖ)) :=
  inferInstance

variable {U ϖ} in
/-- The definition of `infinitesimals` is literally `v_ϖ(x_j) →_𝒰 ∞` (tex 4724), with `v_ϖ` the
`ℕ∞`-valued valuation `IsDiscreteValuationRing.addVal` of the DVR. Kind: PROVED. -/
theorem mem_infinitesimals_iff_tendsto_addVal (hϖ : Irreducible ϖ) {x : ι → R} :
    x ∈ infinitesimals U ϖ ↔
      Tendsto (fun j => IsDiscreteValuationRing.addVal R (x j)) (U : Filter ι) (𝓝 ⊤) := by
  rw [ENat.tendsto_nhds_top_iff_natCast_lt, mem_infinitesimals]
  have key : ∀ (n : ℕ) (y : R), ϖ ^ n ∣ y ↔ (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal R y :=
    fun n y => by rw [← hϖ.addVal_pow n, IsDiscreteValuationRing.addVal_le_iff_dvd]
  constructor
  · intro h n
    filter_upwards [h (n + 1)] with j hj
    rw [key] at hj
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hj
  · intro h n
    filter_upwards [h n] with j hj
    rw [key]
    exact hj.le

variable {ϖ} in
/-- tex 4726-4727 in valuation form: a non-infinitesimal sequence has one fixed valuation `m` at
`𝒰`-almost every `j`. Kind: PROVED. -/
theorem exists_eventually_addVal_eq (hϖ : Irreducible ϖ) {x : ι → R}
    (hx : x ∉ infinitesimals U ϖ) :
    ∃ m : ℕ, ∀ᶠ j in (U : Filter ι), IsDiscreteValuationRing.addVal R (x j) = m := by
  obtain ⟨m, u, hu, hxu⟩ := exists_eventually_eq_pow_mul_unit U hϖ hx
  refine ⟨m, ?_⟩
  filter_upwards [hxu] with j hj
  exact IsDiscreteValuationRing.addVal_def (x j) (hu j).unit hϖ m
    (by rw [IsUnit.unit_spec, mul_comm]; exact hj)

end DVR

/-! ### Passing integral matrices to (5.3) (tex 4732-4739) -/

section Matrices

variable {l m n : Type*}

/-- The image in `𝒪_∞` of a sequence `(w_j)` of integral vectors (tex 4732). Kind: definition. -/
def outerVec (w : ι → n → R) : n → OInf U ϖ := fun a => toOInf U ϖ (fun j => w j a)

/-- The image in `𝒪_∞` of a sequence `(M_j)` of integral matrices, entrywise (tex 4732-4738:
"Integral minimal-model matrices ... pass to (5.3)"). Kind: definition. -/
def outerMatrix (M : ι → Matrix m n R) : Matrix m n (OInf U ϖ) :=
  Matrix.of fun a b => toOInf U ϖ (fun j => M j a b)

/-- A sequence of matrices viewed as a matrix of sequences. Kind: definition. -/
def seqMatrix (M : ι → Matrix m n R) : Matrix m n (ι → R) :=
  Matrix.of fun a b j => M j a b

/-- `outerMatrix` is `Matrix.map` of the quotient map. Kind: PROVED. -/
theorem outerMatrix_eq_map (M : ι → Matrix m n R) :
    outerMatrix U ϖ M = (seqMatrix M).map (toOInf U ϖ) :=
  rfl

/-- For square matrices, `outerMatrix` is `RingHom.mapMatrix` of the quotient map (tex 4732).
Kind: PROVED. -/
theorem outerMatrix_eq_mapMatrix [Fintype n] [DecidableEq n] (M : ι → Matrix n n R) :
    outerMatrix U ϖ M = (toOInf U ϖ).mapMatrix (seqMatrix M) :=
  rfl

/-- A matrix identity holding modulo infinitesimals entrywise holds after passing to `𝒪_∞`
(tex 4732-4738). Kind: PROVED. -/
theorem map_toOInf_eq_of_sub_mem (A B : Matrix m n (ι → R))
    (h : ∀ a b, A a b - B a b ∈ infinitesimals U ϖ) :
    A.map (toOInf U ϖ) = B.map (toOInf U ϖ) := by
  ext a b
  exact (toOInf_eq_toOInf_iff U ϖ).mpr (h a b)

/-- A matrix identity holding entrywise at `𝒰`-almost every `j` holds after passing to `𝒪_∞`.
Kind: PROVED. -/
theorem map_toOInf_eq_of_eventually (A B : Matrix m n (ι → R))
    (h : ∀ a b, ∀ᶠ j in (U : Filter ι), A a b j = B a b j) :
    A.map (toOInf U ϖ) = B.map (toOInf U ϖ) := by
  ext a b
  exact toOInf_eq_of_eventuallyEq U ϖ (h a b)

/-- Sequences of matrices agreeing modulo infinitesimals have the same image. Kind: PROVED. -/
theorem outerMatrix_eq_of_sub_mem {M N : ι → Matrix m n R}
    (h : ∀ a b, (fun j => M j a b - N j a b) ∈ infinitesimals U ϖ) :
    outerMatrix U ϖ M = outerMatrix U ϖ N := by
  ext a b
  exact (toOInf_eq_toOInf_iff U ϖ).mpr (h a b)

/-- Sequences of matrices agreeing at `𝒰`-almost every `j` have the same image. Kind: PROVED. -/
theorem outerMatrix_eq_of_eventually {M N : ι → Matrix m n R}
    (h : ∀ᶠ j in (U : Filter ι), M j = N j) :
    outerMatrix U ϖ M = outerMatrix U ϖ N := by
  ext a b
  apply toOInf_eq_of_eventuallyEq
  filter_upwards [h] with j hj
  rw [hj]

/-- Kind: PROVED. -/
theorem outerMatrix_add (M N : ι → Matrix m n R) :
    outerMatrix U ϖ (fun j => M j + N j) = outerMatrix U ϖ M + outerMatrix U ϖ N := by
  ext a b
  exact map_add (toOInf U ϖ) (fun j => M j a b) (fun j => N j a b)

/-- Kind: PROVED. -/
theorem outerMatrix_sub (M N : ι → Matrix m n R) :
    outerMatrix U ϖ (fun j => M j - N j) = outerMatrix U ϖ M - outerMatrix U ϖ N := by
  ext a b
  exact map_sub (toOInf U ϖ) (fun j => M j a b) (fun j => N j a b)

/-- Kind: PROVED. -/
theorem outerMatrix_zero : outerMatrix U ϖ (fun _ => (0 : Matrix m n R)) = 0 := by
  ext a b
  exact map_zero (toOInf U ϖ)

/-- Kind: PROVED. -/
theorem outerMatrix_one [DecidableEq n] : outerMatrix U ϖ (fun _ => (1 : Matrix n n R)) = 1 := by
  ext a b
  by_cases hab : a = b
  · subst hab
    rw [Matrix.one_apply_eq]
    change toOInf U ϖ (fun _ => (1 : Matrix n n R) a a) = 1
    simp only [Matrix.one_apply_eq]
    exact map_one (toOInf U ϖ)
  · rw [Matrix.one_apply_ne hab]
    change toOInf U ϖ (fun _ => (1 : Matrix n n R) a b) = 0
    simp only [Matrix.one_apply_ne hab]
    exact map_zero (toOInf U ϖ)

/-- Passing to `𝒪_∞` is multiplicative for (rectangular) matrices. Kind: PROVED. -/
theorem outerMatrix_mul [Fintype n] (M : ι → Matrix l n R) (N : ι → Matrix n m R) :
    outerMatrix U ϖ (fun j => M j * N j) = outerMatrix U ϖ M * outerMatrix U ϖ N := by
  ext a b
  have e : (fun j => (M j * N j) a b) =
      ∑ c, (fun j => M j a c) * (fun j => N j c b) := by
    funext j
    rw [Finset.sum_apply, Matrix.mul_apply]
    rfl
  rw [Matrix.mul_apply]
  change toOInf U ϖ (fun j => (M j * N j) a b) =
    ∑ c, toOInf U ϖ (fun j => M j a c) * toOInf U ϖ (fun j => N j c b)
  rw [e, map_sum]
  simp only [map_mul]

/-- Passing to `𝒪_∞` commutes with matrix-vector products. Kind: PROVED. -/
theorem outerMatrix_mulVec [Fintype n] (M : ι → Matrix m n R) (w : ι → n → R) :
    outerMatrix U ϖ M *ᵥ outerVec U ϖ w = outerVec U ϖ (fun j => M j *ᵥ w j) := by
  funext a
  have e : (fun j => (M j *ᵥ w j) a) = ∑ c, (fun j => M j a c) * (fun j => w j c) := by
    funext j
    rw [Finset.sum_apply]
    rfl
  change ∑ c, toOInf U ϖ (fun j => M j a c) * toOInf U ϖ (fun j => w j c) =
    toOInf U ϖ (fun j => (M j *ᵥ w j) a)
  rw [e, map_sum]
  simp only [map_mul]

/-- Kind: PROVED. -/
theorem outerVec_add (v w : ι → n → R) :
    outerVec U ϖ (fun j => v j + w j) = outerVec U ϖ v + outerVec U ϖ w := by
  funext a
  exact map_add (toOInf U ϖ) (fun j => v j a) (fun j => w j a)

/-- Kind: PROVED. -/
theorem outerVec_sub (v w : ι → n → R) :
    outerVec U ϖ (fun j => v j - w j) = outerVec U ϖ v - outerVec U ϖ w := by
  funext a
  exact map_sub (toOInf U ϖ) (fun j => v j a) (fun j => w j a)

/-- Kind: PROVED. -/
theorem outerVec_eq_zero_iff (v : ι → n → R) :
    outerVec U ϖ v = 0 ↔ ∀ a, (fun j => v j a) ∈ infinitesimals U ϖ := by
  constructor
  · intro h a
    exact (toOInf_eq_zero_iff U ϖ).mp (congrFun h a)
  · intro h
    funext a
    exact (toOInf_eq_zero_iff U ϖ).mpr (h a)

/-- For square matrices, passing a sequence of integral matrices to `𝒪_∞` is a ring homomorphism
`(ι → Matrix n n 𝒪) →+* Matrix n n 𝒪_∞`, so every ring identity between sequences of matrices that
holds at `𝒰`-almost every `j` holds in `𝒪_∞` (tex 4732-4738). Kind: definition (+ PROVED laws). -/
def outerMatrixHom [Fintype n] [DecidableEq n] : (ι → Matrix n n R) →+* Matrix n n (OInf U ϖ) where
  toFun := outerMatrix U ϖ
  map_one' := outerMatrix_one U ϖ
  map_mul' M N := outerMatrix_mul U ϖ M N
  map_zero' := outerMatrix_zero U ϖ
  map_add' M N := outerMatrix_add U ϖ M N

/-- Kind: PROVED. -/
theorem outerMatrixHom_apply [Fintype n] [DecidableEq n] (M : ι → Matrix n n R) :
    outerMatrixHom U ϖ M = outerMatrix U ϖ M :=
  rfl

/-- "These inverse matrices ... pass to the same outer quotient" (tex 4737-4738): stagewise
two-sided inverses (at `𝒰`-almost every `j`) give two-sided inverses in `𝒪_∞`. Kind: PROVED. -/
theorem outerMatrix_inverse [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (f : ι → Matrix n m R) (f' : ι → Matrix m n R)
    (h₁ : ∀ᶠ j in (U : Filter ι), f j * f' j = 1) (h₂ : ∀ᶠ j in (U : Filter ι), f' j * f j = 1) :
    outerMatrix U ϖ f * outerMatrix U ϖ f' = 1 ∧ outerMatrix U ϖ f' * outerMatrix U ϖ f = 1 := by
  constructor
  · rw [← outerMatrix_mul, ← outerMatrix_one U ϖ]
    exact outerMatrix_eq_of_eventually U ϖ h₁
  · rw [← outerMatrix_mul, ← outerMatrix_one U ϖ]
    exact outerMatrix_eq_of_eventually U ϖ h₂

end Matrices

end Outer

/-! ### Nakayama and minimal homotopy equivalences (tex 4734-4737) -/

section Nakayama

variable {S : Type*} [CommRing S] [IsLocalRing S]

/-- tex 4736 "Nakayama applies": over a local ring, a square matrix whose residual matrix is invertible
is invertible. Kind: PROVED. -/
theorem matrix_isUnit_of_isUnit_map_residue {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n S) (h : IsUnit (M.map (IsLocalRing.residue S))) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det] at h ⊢
  have h' : IsUnit (IsLocalRing.residue S M.det) := by
    rw [RingHom.map_det]
    exact h
  exact isUnit_of_map_unit (IsLocalRing.residue S) _ h'

/-- The differential of a minimal complex: every entry lies in the maximal ideal ("after minimal
cancellation", tex 4734-4735). Kind: definition. -/
def EntriesInMaximalIdeal {m n : Type*} (d : Matrix m n S) : Prop :=
  ∀ a b, d a b ∈ IsLocalRing.maximalIdeal S

/-- A minimal differential vanishes residually. Kind: PROVED. -/
theorem map_residue_eq_zero {m n : Type*} {d : Matrix m n S} (hd : EntriesInMaximalIdeal d) :
    d.map (IsLocalRing.residue S) = 0 := by
  ext a b
  exact (IsLocalRing.residue_eq_zero_iff _).mpr (hd a b)

/-- tex 4736 "its residual matrices are invertible": if `f g - 1 = d s + s' d'` with minimal `d`,
`d'` (a chain homotopy `f g ≃ 1` in one degree), then residually `f g = 1`. Kind: PROVED. -/
theorem map_residue_mul_eq_one_of_minimal_homotopy {n m k k' : Type*}
    [Fintype n] [DecidableEq n] [Fintype m] [Fintype k] [Fintype k']
    {f : Matrix n m S} {g : Matrix m n S} {d : Matrix n k S} {s : Matrix k n S}
    {s' : Matrix n k' S} {d' : Matrix k' n S}
    (hd : EntriesInMaximalIdeal d) (hd' : EntriesInMaximalIdeal d')
    (h : f * g - 1 = d * s + s' * d') :
    f.map (IsLocalRing.residue S) * g.map (IsLocalRing.residue S) = 1 := by
  have h2 : (f * g - 1).map (IsLocalRing.residue S) =
      (d * s + s' * d').map (IsLocalRing.residue S) := by rw [h]
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
    map_residue_eq_zero hd, map_residue_eq_zero hd', Matrix.zero_mul, Matrix.mul_zero,
    add_zero, sub_eq_zero] at h2
  exact h2

/-- tex 4734-4736: if `f g - 1 = d s + s' d'` with minimal `d`, `d'`, then `f g` is invertible.
Kind: PROVED. -/
theorem isUnit_mul_of_minimal_homotopy {n m k k' : Type*}
    [Fintype n] [DecidableEq n] [Fintype m] [Fintype k] [Fintype k']
    {f : Matrix n m S} {g : Matrix m n S} {d : Matrix n k S} {s : Matrix k n S}
    {s' : Matrix n k' S} {d' : Matrix k' n S}
    (hd : EntriesInMaximalIdeal d) (hd' : EntriesInMaximalIdeal d')
    (h : f * g - 1 = d * s + s' * d') : IsUnit (f * g) := by
  apply matrix_isUnit_of_isUnit_map_residue
  rw [Matrix.map_mul, map_residue_mul_eq_one_of_minimal_homotopy hd hd' h]
  exact isUnit_one

/-- tex 4734-4736, square case: if `f g - 1 = d s + s' d'` with minimal `d`, `d'` and `f`, `g` square,
then `f` and `g` are invertible (over a commutative ring one homotopy suffices). Kind: PROVED. -/
theorem isUnit_of_minimal_homotopy_square {n k k' : Type*}
    [Fintype n] [DecidableEq n] [Fintype k] [Fintype k']
    {f g : Matrix n n S} {d : Matrix n k S} {s : Matrix k n S}
    {s' : Matrix n k' S} {d' : Matrix k' n S}
    (hd : EntriesInMaximalIdeal d) (hd' : EntriesInMaximalIdeal d')
    (h : f * g - 1 = d * s + s' * d') : IsUnit f ∧ IsUnit g := by
  have hfg := isUnit_mul_of_minimal_homotopy hd hd' h
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at hfg
  exact ⟨(Matrix.isUnit_iff_isUnit_det f).mpr (isUnit_of_mul_isUnit_left hfg),
    (Matrix.isUnit_iff_isUnit_det g).mpr (isUnit_of_mul_isUnit_right hfg)⟩

/-- tex 4734-4736 "After minimal cancellation an integral homotopy equivalence is degreewise
invertible": if `f : Matrix n m S` and `g : Matrix m n S` (one degree of chain maps between minimal
complexes) satisfy `f g - 1 = d₁ s₁ + s₁' d₁'` and `g f - 1 = d₂ s₂ + s₂' d₂'` with all `dᵢ`, `dᵢ'`
minimal, then `f` is invertible with explicit two-sided inverse `g (f g)⁻¹`. Kind: PROVED. -/
theorem inverse_of_minimal_homotopy_equivalence {n m k₁ k₁' k₂ k₂' : Type*}
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    [Fintype k₁] [Fintype k₁'] [Fintype k₂] [Fintype k₂']
    {f : Matrix n m S} {g : Matrix m n S}
    {d₁ : Matrix n k₁ S} {s₁ : Matrix k₁ n S} {s₁' : Matrix n k₁' S} {d₁' : Matrix k₁' n S}
    {d₂ : Matrix m k₂ S} {s₂ : Matrix k₂ m S} {s₂' : Matrix m k₂' S} {d₂' : Matrix k₂' m S}
    (hd₁ : EntriesInMaximalIdeal d₁) (hd₁' : EntriesInMaximalIdeal d₁')
    (hd₂ : EntriesInMaximalIdeal d₂) (hd₂' : EntriesInMaximalIdeal d₂')
    (hfg : f * g - 1 = d₁ * s₁ + s₁' * d₁') (hgf : g * f - 1 = d₂ * s₂ + s₂' * d₂') :
    f * (g * (f * g)⁻¹) = 1 ∧ g * (f * g)⁻¹ * f = 1 := by
  have hu : f * g * (f * g)⁻¹ = 1 := Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_mul_of_minimal_homotopy hd₁ hd₁' hfg))
  have hv : (g * f)⁻¹ * (g * f) = 1 := Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_mul_of_minimal_homotopy hd₂ hd₂' hgf))
  refine ⟨by rw [← Matrix.mul_assoc, hu], ?_⟩
  calc g * (f * g)⁻¹ * f = (g * f)⁻¹ * (g * f) * (g * (f * g)⁻¹ * f) := by
        rw [hv, Matrix.one_mul]
    _ = (g * f)⁻¹ * g * (f * g * (f * g)⁻¹) * f := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hu, Matrix.mul_one, Matrix.mul_assoc, hv]

end Nakayama

section OuterInverse

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {ι : Type*} (U : Ultrafilter ι) (ϖ : R)

/-- tex 4734-4738: stagewise minimal homotopy equivalences `f_j`, `g_j` over `𝒪` are degreewise
invertible with integral inverses `g_j (f_j g_j)⁻¹`, and these inverses pass to `𝒪_∞` as two-sided
inverses of the image of `(f_j)`. Kind: PROVED. -/
theorem outer_inverse_of_minimal_homotopy_equivalence {n m k₁ k₁' k₂ k₂' : Type*}
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    [Fintype k₁] [Fintype k₁'] [Fintype k₂] [Fintype k₂']
    (f : ι → Matrix n m R) (g : ι → Matrix m n R)
    (d₁ : ι → Matrix n k₁ R) (s₁ : ι → Matrix k₁ n R) (s₁' : ι → Matrix n k₁' R)
    (d₁' : ι → Matrix k₁' n R)
    (d₂ : ι → Matrix m k₂ R) (s₂ : ι → Matrix k₂ m R) (s₂' : ι → Matrix m k₂' R)
    (d₂' : ι → Matrix k₂' m R)
    (hd₁ : ∀ j, EntriesInMaximalIdeal (d₁ j)) (hd₁' : ∀ j, EntriesInMaximalIdeal (d₁' j))
    (hd₂ : ∀ j, EntriesInMaximalIdeal (d₂ j)) (hd₂' : ∀ j, EntriesInMaximalIdeal (d₂' j))
    (hfg : ∀ j, f j * g j - 1 = d₁ j * s₁ j + s₁' j * d₁' j)
    (hgf : ∀ j, g j * f j - 1 = d₂ j * s₂ j + s₂' j * d₂' j) :
    outerMatrix U ϖ f * outerMatrix U ϖ (fun j => g j * (f j * g j)⁻¹) = 1 ∧
      outerMatrix U ϖ (fun j => g j * (f j * g j)⁻¹) * outerMatrix U ϖ f = 1 :=
  outerMatrix_inverse U ϖ f _
    (Eventually.of_forall fun j => (inverse_of_minimal_homotopy_equivalence (hd₁ j) (hd₁' j)
      (hd₂ j) (hd₂' j) (hfg j) (hgf j)).1)
    (Eventually.of_forall fun j => (inverse_of_minimal_homotopy_equivalence (hd₁ j) (hd₁' j)
      (hd₂ j) (hd₂' j) (hfg j) (hgf j)).2)

end OuterInverse

/-! ### Approximate cycles (tex 4674-4682, 4740-4742) -/

section Cycles

variable {R : Type*} [CommRing R] {ι : Type*} (U : Ultrafilter ι) (ϖ : R)
  {G : ι → Type*} [∀ j, Group (G j)] {n : Type*} [Fintype n] [DecidableEq n]

/-- `ρ_∞` on the product group `Γ = ∏_j G_j` (tex 4674, 4681-4682): `ρ_∞(g)_{ab} = [ρ_j(g_j)_{ab}]`.
It is a monoid homomorphism. Kind: definition (the homomorphism laws are PROVED). -/
def outerRep (ρ : ∀ j, G j →* Matrix n n R) : (∀ j, G j) →* Matrix n n (OInf U ϖ) :=
  (outerMatrixHom U ϖ).toMonoidHom.comp (MonoidHom.pi fun j => (ρ j).comp (Pi.evalMonoidHom G j))

/-- Kind: PROVED. -/
theorem outerRep_apply (ρ : ∀ j, G j →* Matrix n n R) (g : ∀ j, G j) :
    outerRep U ϖ ρ g = outerMatrix U ϖ (fun j => ρ j (g j)) :=
  rfl

/-- Entrywise: `ρ_∞(g)_{ab} = π(j ↦ ρ_j(g_j)_{ab})`. Kind: PROVED. -/
theorem outerRep_apply_apply (ρ : ∀ j, G j →* Matrix n n R) (g : ∀ j, G j) (a b : n) :
    outerRep U ϖ ρ g a b = toOInf U ϖ (fun j => ρ j (g j) a b) :=
  rfl

/-- `ρ_∞` is multiplicative on the product group. Kind: PROVED. -/
theorem outerRep_mul (ρ : ∀ j, G j →* Matrix n n R) (g h : ∀ j, G j) :
    outerRep U ϖ ρ (g * h) = outerRep U ϖ ρ g * outerRep U ϖ ρ h :=
  map_mul _ g h

/-- `w_∞` (tex 4741): the image in `𝒪_∞` of a sequence of cochains `w_j : G_j → 𝒪^n`, evaluated at a
sequence `g = (g_j)`. Kind: definition. -/
def outerCochain (w : ∀ j, G j → n → R) (g : ∀ j, G j) : n → OInf U ϖ :=
  outerVec U ϖ (fun j => w j (g j))

omit [∀ j, Group (G j)] [Fintype n] [DecidableEq n] in
/-- Coordinatewise: `w_∞(g)_a = π(j ↦ w_j(g_j)_a)`. Kind: PROVED. -/
theorem outerCochain_apply (w : ∀ j, G j → n → R) (g : ∀ j, G j) (a : n) :
    outerCochain U ϖ w g a = toOInf U ϖ (fun j => w j (g j) a) :=
  rfl

/-- The degree-two term of (5.2) (tex 4679) at stage `j`:
`ρ_j(x) w_j(y) - w_j(x y) + w_j(x)`. Kind: definition. -/
def cocycleDefect (ρ : ∀ j, G j →* Matrix n n R) (w : ∀ j, G j → n → R) (j : ι) (x y : G j) :
    n → R :=
  ρ j x *ᵥ w j y - w j (x * y) + w j x

/-- The crossed-homomorphism expression of `w_∞` is the image of the stagewise defects.
Kind: PROVED. -/
theorem outer_defect_eq (ρ : ∀ j, G j →* Matrix n n R) (w : ∀ j, G j → n → R)
    (g h : ∀ j, G j) :
    outerRep U ϖ ρ g *ᵥ outerCochain U ϖ w h - outerCochain U ϖ w (g * h) +
        outerCochain U ϖ w g =
      outerVec U ϖ (fun j => cocycleDefect ρ w j (g j) (h j)) := by
  simp only [outerRep_apply, outerCochain]
  rw [outerMatrix_mulVec, ← outerVec_sub, ← outerVec_add]
  rfl

/-- tex 4681-4682 and 4740-4742: if, for the sequences `g`, `h`, every coordinate of the defect
sequence `j ↦ ρ_j(g_j) w_j(h_j) - w_j(g_j h_j) + w_j(g_j)` is infinitesimal (`v₂ → ∞` along `𝒰`), then
`ρ_∞(g) w_∞(h) - w_∞(g h) + w_∞(g) = 0` in `𝒪_∞`. Applied to all pairs, `w_∞` is an exact crossed
homomorphism of the product group. Kind: PROVED. -/
theorem outer_isCrossedHom (ρ : ∀ j, G j →* Matrix n n R) (w : ∀ j, G j → n → R)
    (g h : ∀ j, G j)
    (hw : ∀ a, (fun j => cocycleDefect ρ w j (g j) (h j) a) ∈ infinitesimals U ϖ) :
    outerRep U ϖ ρ g *ᵥ outerCochain U ϖ w h - outerCochain U ϖ w (g * h) +
        outerCochain U ϖ w g = 0 := by
  rw [outer_defect_eq, outerVec_eq_zero_iff]
  exact hw

/-- tex 4740-4741 "if `v₂(dw_j) → ∞`, the degree-two term in (5.2) tends to zero": if each stagewise
defect is the integral evaluation `e_j(x, y) (dw_j)` of a coboundary vector `dw_j` (integral matrices
`e_j(x, y)`), and every coordinate of `dw_j` has valuation tending to `∞` along `𝒰`, then every
coordinate of the defect sequence is infinitesimal. Kind: PROVED. -/
theorem cocycleDefect_mem_infinitesimals [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) {k : Type*} [Fintype k]
    (ρ : ∀ j, G j →* Matrix n n R) (w : ∀ j, G j → n → R)
    (e : ∀ j, G j → G j → Matrix n k R) (dw : ι → k → R)
    (he : ∀ j (x y : G j), cocycleDefect ρ w j x y = e j x y *ᵥ dw j)
    (hdw : ∀ c, Tendsto (fun j => IsDiscreteValuationRing.addVal R (dw j c)) (U : Filter ι) (𝓝 ⊤))
    (g h : ∀ j, G j) (a : n) :
    (fun j => cocycleDefect ρ w j (g j) (h j) a) ∈ infinitesimals U ϖ := by
  have hdw' : ∀ c, (fun j => dw j c) ∈ infinitesimals U ϖ := fun c =>
    (mem_infinitesimals_iff_tendsto_addVal hϖ).mpr (hdw c)
  have e2 : (fun j => cocycleDefect ρ w j (g j) (h j) a) =
      ∑ c, (fun j => e j (g j) (h j) a c) * (fun j => dw j c) := by
    funext j
    rw [he, Finset.sum_apply]
    rfl
  rw [e2]
  exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_left _ _ (hdw' c)

/-- tex 4740-4742 "Approximate cycles suffice ... so `w_∞` is an actual crossed homomorphism":
combination of `cocycleDefect_mem_infinitesimals` and `outer_isCrossedHom`. Kind: PROVED. -/
theorem outer_isCrossedHom_of_approximate_cycle [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) {k : Type*} [Fintype k]
    (ρ : ∀ j, G j →* Matrix n n R) (w : ∀ j, G j → n → R)
    (e : ∀ j, G j → G j → Matrix n k R) (dw : ι → k → R)
    (he : ∀ j (x y : G j), cocycleDefect ρ w j x y = e j x y *ᵥ dw j)
    (hdw : ∀ c, Tendsto (fun j => IsDiscreteValuationRing.addVal R (dw j c)) (U : Filter ι) (𝓝 ⊤))
    (g h : ∀ j, G j) :
    outerRep U ϖ ρ g *ᵥ outerCochain U ϖ w h - outerCochain U ϖ w (g * h) +
        outerCochain U ϖ w g = 0 :=
  outer_isCrossedHom U ϖ ρ w g h (cocycleDefect_mem_infinitesimals U hϖ ρ w e dw he hdw g h)

/-- tex 4677-4679 and 4732: the identities (5.2)
`e¹_g d = (ρ(g) - 1) e⁰` and `e²_{g,h} d = ρ(g) e¹_h - e¹_{gh} + e¹_g`, holding at every stage between
integral evaluation matrices `e⁰_j`, `e¹_j(x)`, `e²_j(x, y)` and minimal-model differentials `d⁰_j`,
`d¹_j`, pass to `𝒪_∞` for arbitrary sequences `g`, `h`. Kind: PROVED. -/
theorem formula_5_2_outer {p₀ p₁ p₂ : Type*} [Fintype p₁] [Fintype p₂]
    (ρ : ∀ j, G j →* Matrix n n R) (e₀ : ι → Matrix n p₀ R) (e₁ : ∀ j, G j → Matrix n p₁ R)
    (e₂ : ∀ j, G j → G j → Matrix n p₂ R) (d₀ : ι → Matrix p₁ p₀ R) (d₁ : ι → Matrix p₂ p₁ R)
    (h₁ : ∀ j (x : G j), e₁ j x * d₀ j = (ρ j x - 1) * e₀ j)
    (h₂ : ∀ j (x y : G j), e₂ j x y * d₁ j = ρ j x * e₁ j y - e₁ j (x * y) + e₁ j x)
    (g h : ∀ j, G j) :
    outerMatrix U ϖ (fun j => e₁ j (g j)) * outerMatrix U ϖ d₀ =
        (outerRep U ϖ ρ g - 1) * outerMatrix U ϖ e₀ ∧
      outerMatrix U ϖ (fun j => e₂ j (g j) (h j)) * outerMatrix U ϖ d₁ =
        outerRep U ϖ ρ g * outerMatrix U ϖ (fun j => e₁ j (h j)) -
          outerMatrix U ϖ (fun j => e₁ j ((g * h) j)) + outerMatrix U ϖ (fun j => e₁ j (g j)) := by
  constructor
  · rw [← outerMatrix_mul, outerRep_apply, ← outerMatrix_one U ϖ, ← outerMatrix_sub,
      ← outerMatrix_mul]
    exact congrArg (outerMatrix U ϖ) (funext fun j => h₁ j (g j))
  · rw [← outerMatrix_mul, outerRep_apply, ← outerMatrix_mul, ← outerMatrix_sub,
      ← outerMatrix_add]
    exact congrArg (outerMatrix U ϖ) (funext fun j => h₂ j (g j) (h j))

/-- tex 4740-4742 with the evaluations of (5.2): let `c_j` be degree-one cochains of the minimal model
and `w_j(x) = e¹_j(x) c_j` their evaluations. If (5.2) holds at every stage and every coordinate of
`dc_j = d¹_j c_j` has valuation tending to `∞` along `𝒰` (an approximate cycle), then `w_∞` is an exact
crossed homomorphism of the product group. Kind: PROVED. -/
theorem outer_isCrossedHom_of_formula_5_2 [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) {p₁ p₂ : Type*} [Fintype p₁] [Fintype p₂]
    (ρ : ∀ j, G j →* Matrix n n R) (e₁ : ∀ j, G j → Matrix n p₁ R)
    (e₂ : ∀ j, G j → G j → Matrix n p₂ R) (d₁ : ι → Matrix p₂ p₁ R)
    (h₂ : ∀ j (x y : G j), e₂ j x y * d₁ j = ρ j x * e₁ j y - e₁ j (x * y) + e₁ j x)
    (c : ι → p₁ → R)
    (hdc : ∀ b, Tendsto (fun j => IsDiscreteValuationRing.addVal R ((d₁ j *ᵥ c j) b))
      (U : Filter ι) (𝓝 ⊤))
    (g h : ∀ j, G j) :
    outerRep U ϖ ρ g *ᵥ outerCochain U ϖ (fun j x => e₁ j x *ᵥ c j) h -
        outerCochain U ϖ (fun j x => e₁ j x *ᵥ c j) (g * h) +
        outerCochain U ϖ (fun j x => e₁ j x *ᵥ c j) g = 0 := by
  refine outer_isCrossedHom_of_approximate_cycle U hϖ ρ (fun j x => e₁ j x *ᵥ c j) e₂
    (fun j => d₁ j *ᵥ c j) (fun j x y => ?_) hdc g h
  simp only [cocycleDefect]
  rw [Matrix.mulVec_mulVec (c j) (e₂ j x y) (d₁ j), h₂, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.mulVec_mulVec (c j) (ρ j x) (e₁ j y)]

end Cycles

/-! ### Non-vacuity: Elliot's case `𝒪 → ℤ₂`, `ϖ = 2` -/

section Examples

/-- `2` is a uniformizer of `ℤ₂`. Kind: PROVED. -/
instance fact_irreducible_two : Fact (Irreducible (2 : ℤ_[2])) :=
  ⟨by simpa using (PadicInt.irreducible_p : Irreducible ((2 : ℕ) : ℤ_[2]))⟩

/-- A nonprincipal ultrafilter on `ℕ` (any ultrafilter finer than the cofinite filter).
Kind: definition. -/
noncomputable def cofiniteUltrafilter : Ultrafilter ℕ :=
  Ultrafilter.of Filter.cofinite

theorem eventually_cofiniteUltrafilter {p : ℕ → Prop} (h : ∀ᶠ j in Filter.cofinite, p j) :
    ∀ᶠ j in (cofiniteUltrafilter : Filter ℕ), p j :=
  h.filter_mono (Ultrafilter.of_le _)

/-- Non-vacuity of (1) with `𝒪` replaced by `ℤ₂` (a DVR in Mathlib), `ϖ = 2`: `𝒪_∞` is a DVR with
uniformizer `2` and characteristic zero. Kind: PROVED. -/
example : IsDiscreteValuationRing (OInf cofiniteUltrafilter (2 : ℤ_[2])) := inferInstance

example : Irreducible (2 : OInf cofiniteUltrafilter (2 : ℤ_[2])) := by
  have h := irreducible_algebraMap cofiniteUltrafilter (2 : ℤ_[2])
  rwa [map_ofNat] at h

example : CharZero (OInf cofiniteUltrafilter (2 : ℤ_[2])) := inferInstance

/-- Nonprincipality is not needed: the construction also works for a principal ultrafilter.
Kind: PROVED. -/
example : IsDiscreteValuationRing (OInf (pure 0 : Ultrafilter ℕ) (2 : ℤ_[2])) := inferInstance

/-- Non-vacuity of the minimal-homotopy hypotheses (tex 4734-4736): over `ℤ₂`, with `f = 1`,
`g = 1 + d` for the minimal matrix `d` with all entries `2`, `s = 1` and `s' = d' = 0`, one has
`f g - 1 = d s + s' d'` although `f g ≠ 1`; the theorem then gives that `f g` is invertible.
Kind: PROVED. -/
example : (1 : Matrix (Fin 2) (Fin 2) ℤ_[2]) * (1 + Matrix.of fun _ _ => (2 : ℤ_[2])) ≠ 1 ∧
    IsUnit ((1 : Matrix (Fin 2) (Fin 2) ℤ_[2]) * (1 + Matrix.of fun _ _ => (2 : ℤ_[2]))) := by
  refine ⟨fun h => ?_, ?_⟩
  · have h01 := congrFun (congrFun h 0) 1
    rw [Matrix.one_mul, Matrix.add_apply, Matrix.one_apply_ne (by decide), Matrix.of_apply,
      zero_add] at h01
    exact two_ne_zero h01
  refine isUnit_mul_of_minimal_homotopy (d := Matrix.of fun _ _ => (2 : ℤ_[2]))
    (s := (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])) (s' := (0 : Matrix (Fin 2) (Fin 1) ℤ_[2]))
    (d' := (0 : Matrix (Fin 1) (Fin 2) ℤ_[2])) (fun _ _ => ?_) (fun _ _ => ?_) ?_
  · rw [Matrix.of_apply, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact (Fact.out : Irreducible (2 : ℤ_[2])).not_isUnit
  · rw [Matrix.zero_apply]
    exact Ideal.zero_mem _
  · rw [Matrix.one_mul, add_sub_cancel_left, Matrix.mul_one, Matrix.zero_mul, add_zero]

/-- Non-vacuity of (3): with the trivial representation, the cochains `w_j = 2 ^ j` are not cocycles at
any finite stage (their defect is `2 ^ j ≠ 0`), yet they satisfy the hypotheses of
`outer_isCrossedHom_of_approximate_cycle` (with `e_j = 1`, `dw_j = 2 ^ j`) along a nonprincipal
ultrafilter, so `w_∞` is an exact crossed homomorphism. Kind: PROVED. -/
example :
    let ρ0 : ∀ _ : ℕ, Unit →* Matrix (Fin 1) (Fin 1) ℤ_[2] := fun _ => 1
    let w0 : ∀ _ : ℕ, Unit → Fin 1 → ℤ_[2] := fun j _ _ => (2 : ℤ_[2]) ^ j
    (∀ j (x y : Unit), cocycleDefect ρ0 w0 j x y ≠ 0) ∧
    ∀ g h : ℕ → Unit,
      outerRep cofiniteUltrafilter (2 : ℤ_[2]) ρ0 g *ᵥ outerCochain cofiniteUltrafilter 2 w0 h -
          outerCochain cofiniteUltrafilter 2 w0 (g * h) +
          outerCochain cofiniteUltrafilter 2 w0 g = 0 := by
  intro ρ0 w0
  have hdef : ∀ j (x y : Unit), cocycleDefect ρ0 w0 j x y = fun _ => (2 : ℤ_[2]) ^ j := by
    intro j x y
    simp only [cocycleDefect, ρ0, w0, MonoidHom.one_apply, Matrix.one_mulVec, sub_self, zero_add]
  have hdw : ∀ b : Fin 1, Tendsto (fun j => IsDiscreteValuationRing.addVal ℤ_[2]
      ((fun _ : Fin 1 => (2 : ℤ_[2]) ^ j) b)) (cofiniteUltrafilter : Filter ℕ) (𝓝 ⊤) := by
    intro b
    have hmem : (fun j : ℕ => (2 : ℤ_[2]) ^ j) ∈ infinitesimals cofiniteUltrafilter (2 : ℤ_[2]) := by
      intro n
      apply eventually_cofiniteUltrafilter
      rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
      exact ⟨n, fun j hj => pow_dvd_pow 2 hj⟩
    exact (mem_infinitesimals_iff_tendsto_addVal Fact.out).mp hmem
  refine ⟨fun j x y => ?_, fun g h => ?_⟩
  · rw [hdef]
    intro h0
    exact pow_ne_zero j (two_ne_zero : (2 : ℤ_[2]) ≠ 0) (congrFun h0 0)
  · exact outer_isCrossedHom_of_approximate_cycle cofiniteUltrafilter Fact.out ρ0 w0
      (fun _ _ _ => 1) (fun j _ => (2 : ℤ_[2]) ^ j)
      (fun j x y => by rw [hdef, Matrix.one_mulVec]) hdw g h

end Examples

/-! ### A concrete scalar ring: `Λ_(2)` for `Λ = ℤ₂[[t]]` (tex 2747-2748)

Definition `ex:arith-data` (tex 2747-2748): "Put `Λ = ℤ₂[[t]]` and `𝒪 = \widehat{Λ_{(2)}}`."
For any DVR `R` with uniformizer `ϖ`, the ideal `(ϖ)` of `R[[X]]` is prime and the localization
`R[[X]]_(ϖ)` is a DVR with uniformizer (the image of) `ϖ`; for `R = ℤ₂`, `ϖ = 2` this is `Λ_(2)`,
a DVR with uniformizer `2` and characteristic zero. It is a concrete instance of the hypotheses on
`R` above (see the examples after this section).

DEPARTURE (this section): the Lean object is `Λ_(2)` itself, not its `2`-adic completion `𝒪`.
The completion step (the completion of a DVR is a DVR with the same uniformizer, of characteristic
zero when the DVR is) is GLUE: a textbook fact, not formalized here.
-/

namespace ScalarRing

section Coeff

variable {R : Type*} [CommSemiring R] {ϖ : R}

/-- A constant `C ϖ` divides a power series iff `ϖ` divides every coefficient.

Used for tex 2747-2748 (`Λ = ℤ₂[[t]]`, the prime `(2)` of `Λ`). Kind: PROVED.
DEPARTURE: stated for any commutative semiring (no irreducibility, no DVR hypothesis). -/
theorem C_dvd_iff_forall_dvd_coeff (f : PowerSeries R) :
    PowerSeries.C ϖ ∣ f ↔ ∀ i, ϖ ∣ PowerSeries.coeff i f := by
  constructor
  · rintro ⟨g, rfl⟩ i
    rw [PowerSeries.coeff_C_mul]
    exact dvd_mul_right _ _
  · intro h
    choose c hc using h
    refine ⟨PowerSeries.mk c, PowerSeries.ext fun i => ?_⟩
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc]

/-- A power series with a unit coefficient is not divisible by `C ϖ`.

Used for tex 2747-2748. Kind: PROVED.
DEPARTURE: stated for any commutative semiring. -/
theorem not_C_dvd_of_isUnit_coeff (hϖ : Irreducible ϖ) {g : PowerSeries R} {i : ℕ}
    (hg : IsUnit (PowerSeries.coeff i g)) : ¬PowerSeries.C ϖ ∣ g := fun h =>
  hϖ.not_isUnit (isUnit_of_dvd_unit ((C_dvd_iff_forall_dvd_coeff g).mp h i) hg)

end Coeff

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}

/-- In a DVR with uniformizer `ϖ`, a nonzero element is not divisible by every power of `ϖ`.

Used for tex 2747-2748. Kind: PROVED. -/
theorem exists_not_pow_dvd (hϖ : Irreducible ϖ) {a : R} (ha : a ≠ 0) :
    ∃ m : ℕ, ¬ϖ ^ m ∣ a := by
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  refine ⟨n + 1, fun h => ?_⟩
  have h' : ϖ ^ (n + 1) ∣ ϖ ^ n := h.trans hn.dvd
  rw [pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit] at h'
  exact Nat.not_succ_le_self n h'

/-- Key lemma. Over a DVR with uniformizer `ϖ`, every nonzero power series is
`C ϖ ^ n * g` with some coefficient of `g` a unit.

Used for tex 2747-2748 (every nonzero element of `Λ` is `2 ^ n` times an element outside the
prime `(2)`). Kind: PROVED. -/
theorem exists_eq_C_pow_mul_isUnit_coeff (hϖ : Irreducible ϖ) {f : PowerSeries R} (hf : f ≠ 0) :
    ∃ (n : ℕ) (g : PowerSeries R), f = PowerSeries.C ϖ ^ n * g ∧
      ∃ i, IsUnit (PowerSeries.coeff i g) := by
  classical
  obtain ⟨i₀, hi₀⟩ := not_forall.mp fun h : ∀ i, PowerSeries.coeff i f = 0 =>
    hf (PowerSeries.ext fun i => by rw [h i, map_zero])
  obtain ⟨m, hm⟩ := exists_not_pow_dvd hϖ hi₀
  have hP : ∃ n, ∃ i, ¬ϖ ^ (n + 1) ∣ PowerSeries.coeff i f :=
    ⟨m, i₀, fun h => hm ((pow_dvd_pow ϖ (Nat.le_succ m)).trans h)⟩
  obtain ⟨n, ⟨i, hi⟩, hmin⟩ : ∃ n, (∃ i, ¬ϖ ^ (n + 1) ∣ PowerSeries.coeff i f) ∧
      ∀ k < n, ∀ i, ϖ ^ (k + 1) ∣ PowerSeries.coeff i f := by
    exact ⟨Nat.find hP, Nat.find_spec hP, fun k hk j =>
      not_not.mp (not_exists.mp (Nat.find_min hP hk) j)⟩
  have hdiv : ∀ j, ϖ ^ n ∣ PowerSeries.coeff j f := by
    intro j
    rcases n with _ | k
    · rw [pow_zero]
      exact one_dvd _
    · exact hmin k (Nat.lt_add_one k) j
  obtain ⟨g, hg⟩ := (C_dvd_iff_forall_dvd_coeff (ϖ := ϖ ^ n) f).mpr hdiv
  refine ⟨n, g, by rw [hg, map_pow], i, isUnit_of_not_dvd hϖ fun hdvd => hi ?_⟩
  rw [hg, PowerSeries.coeff_C_mul, pow_succ]
  exact mul_dvd_mul_left _ hdvd

/-- For a uniformizer `ϖ` of a DVR `R`, the ideal `(ϖ)` of `R[[X]]` is prime: it is the kernel
of the reduction map `R[[X]] → (R/ϖ)[[X]]` into a domain.

tex 2747-2748 (the prime `(2)` of `Λ` at which `Λ_(2)` is formed). Kind: PROVED. -/
theorem isPrime_span_C (hϖ : Irreducible ϖ) :
    (Ideal.span {PowerSeries.C ϖ} : Ideal (PowerSeries R)).IsPrime := by
  have : (Ideal.span {ϖ} : Ideal R).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  have hker : (Ideal.span {PowerSeries.C ϖ} : Ideal (PowerSeries R)) =
      RingHom.ker (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ}))) := by
    ext f
    rw [Ideal.mem_span_singleton, RingHom.mem_ker, C_dvd_iff_forall_dvd_coeff,
      PowerSeries.ext_iff]
    refine forall_congr' fun i => ?_
    rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [hker]
  exact RingHom.ker_isPrime _

/-- The prime `(ϖ)` of `R[[X]]` as an instance, for a uniformizer `ϖ` recorded by `Fact`.

tex 2747-2748. Kind: PROVED. -/
instance isPrime_span_C_of_fact [Fact (Irreducible ϖ)] :
    (Ideal.span {PowerSeries.C ϖ} : Ideal (PowerSeries R)).IsPrime :=
  isPrime_span_C Fact.out

section IsLocalization

variable [Fact (Irreducible ϖ)] (L : Type*) [CommRing L] [Algebra (PowerSeries R) L]
  [IsLocalization.AtPrime L (Ideal.span {PowerSeries.C ϖ} : Ideal (PowerSeries R))]

/-- In any localization `L` of `R[[X]]` at `(ϖ)`, the image of `ϖ` is nonzero.

tex 2747-2748 and 4719-4730 (uniformizer two). Kind: PROVED. -/
theorem algebraMap_C_ne_zero : algebraMap (PowerSeries R) L (PowerSeries.C ϖ) ≠ 0 := by
  rw [Ne, IsLocalization.to_map_eq_zero_iff L
    (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {PowerSeries.C ϖ}))]
  intro h
  apply (Fact.out : Irreducible ϖ).ne_zero
  rw [← PowerSeries.coeff_zero_C ϖ, h, map_zero]

/-- In any localization `L` of `R[[X]]` at `(ϖ)`, the image of `ϖ` is not a unit.

tex 2747-2748 and 4719-4730 (uniformizer two). Kind: PROVED. -/
theorem not_isUnit_algebraMap_C : ¬IsUnit (algebraMap (PowerSeries R) L (PowerSeries.C ϖ)) := by
  rw [IsLocalization.AtPrime.isUnit_to_map_iff L (Ideal.span {PowerSeries.C ϖ}), Ideal.mem_primeCompl_iff, not_not]
  exact Ideal.mem_span_singleton_self _

/-- In any localization `L` of `R[[X]]` at `(ϖ)`, every nonzero element is associated to a power
of the image of `ϖ`.

tex 4719-4730 ("A nonzero element ... is that power of two times a unit"), for `Λ_(2)`.
Kind: PROVED. -/
theorem forall_associated_pow_algebraMap_C :
    ∀ x : L, x ≠ 0 →
      ∃ n : ℕ, Associated (algebraMap (PowerSeries R) L (PowerSeries.C ϖ) ^ n) x := by
  intro x hx
  have hϖ : Irreducible ϖ := Fact.out
  obtain ⟨⟨f, s⟩, hfs⟩ :=
    IsLocalization.surj (Ideal.span {PowerSeries.C ϖ} : Ideal (PowerSeries R)).primeCompl x
  dsimp only at hfs
  have hs : IsUnit (algebraMap (PowerSeries R) L s) := IsLocalization.map_units L s
  have hf : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hfs
    exact hx (hs.mul_left_eq_zero.mp hfs)
  obtain ⟨n, g, hfg, i, hgi⟩ := exists_eq_C_pow_mul_isUnit_coeff hϖ hf
  have hgP : g ∈ (Ideal.span {PowerSeries.C ϖ} : Ideal (PowerSeries R)).primeCompl := by
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton]
    exact not_C_dvd_of_isUnit_coeff hϖ hgi
  have hg : IsUnit (algebraMap (PowerSeries R) L g) :=
    IsLocalization.map_units L (⟨g, hgP⟩ :
      (Ideal.span {PowerSeries.C ϖ} : Ideal (PowerSeries R)).primeCompl)
  have key : algebraMap (PowerSeries R) L (PowerSeries.C ϖ) ^ n * algebraMap (PowerSeries R) L g =
      x * algebraMap (PowerSeries R) L s := by
    rw [hfs, hfg, map_mul, map_pow]
  refine ⟨n, (associated_mul_unit_right _ _ hg).trans ?_⟩
  rw [key]
  exact associated_mul_unit_left _ _ hs

/-- In any localization `L` of `R[[X]]` at `(ϖ)`, the image of `ϖ` is irreducible.

tex 4719-4730 ("uniformizer two"), for `Λ_(2)`. Kind: PROVED. -/
theorem irreducible_algebraMap_C_of_isLocalization [IsDomain L] :
    Irreducible (algebraMap (PowerSeries R) L (PowerSeries.C ϖ)) :=
  irreducible_of_forall_associated_pow (algebraMap_C_ne_zero (ϖ := ϖ) L)
    (not_isUnit_algebraMap_C (ϖ := ϖ) L) (forall_associated_pow_algebraMap_C (ϖ := ϖ) L)

end IsLocalization

/-- Any localization `L` of `R[[X]]` at `(ϖ)` is a DVR.

tex 4719-4730 ("a DVR with uniformizer two"), for `Λ_(2)`. Kind: PROVED.
The hypothesis `[IsDomain L]` always holds here (see the instance for `Localization.AtPrime`). -/
theorem isDiscreteValuationRing_of_isLocalization (ϖ : R) [Fact (Irreducible ϖ)] (L : Type*)
    [CommRing L] [IsDomain L] [Algebra (PowerSeries R) L]
    [IsLocalization.AtPrime L (Ideal.span {PowerSeries.C ϖ} : Ideal (PowerSeries R))] :
    IsDiscreteValuationRing L :=
  isDiscreteValuationRing_of_forall_associated_pow (algebraMap_C_ne_zero (ϖ := ϖ) L)
    (not_isUnit_algebraMap_C (ϖ := ϖ) L) (forall_associated_pow_algebraMap_C (ϖ := ϖ) L)

/-- The localization `R[[X]]_(ϖ)` is a DVR.

tex 2747-2748 (`Λ_(2)`) and 4719-4730 ("a DVR"). Kind: PROVED. -/
instance isDiscreteValuationRing_atPrime_span_C [Fact (Irreducible ϖ)] : IsDiscreteValuationRing
    (Localization.AtPrime (Ideal.span {PowerSeries.C ϖ} : Ideal (PowerSeries R))) :=
  isDiscreteValuationRing_of_isLocalization ϖ _

/-- The image of `ϖ` is a uniformizer of `R[[X]]_(ϖ)`.

tex 4719-4730 ("uniformizer two"). Kind: PROVED. -/
theorem irreducible_algebraMap_C [Fact (Irreducible ϖ)] :
    Irreducible (algebraMap (PowerSeries R)
      (Localization.AtPrime (Ideal.span {PowerSeries.C ϖ} : Ideal (PowerSeries R)))
      (PowerSeries.C ϖ)) :=
  irreducible_algebraMap_C_of_isLocalization _

/-- The maximal ideal of `R[[X]]_(ϖ)` is generated by the image of `ϖ`.

tex 4719-4730 ("uniformizer two"). Kind: PROVED. -/
theorem maximalIdeal_eq_span_algebraMap_C [Fact (Irreducible ϖ)] :
    IsLocalRing.maximalIdeal
        (Localization.AtPrime (Ideal.span {PowerSeries.C ϖ} : Ideal (PowerSeries R))) =
      Ideal.span {(algebraMap (PowerSeries R)
        (Localization.AtPrime (Ideal.span {PowerSeries.C ϖ} : Ideal (PowerSeries R)))
        (PowerSeries.C ϖ))} :=
  irreducible_algebraMap_C.maximalIdeal_eq

end DVR

/-! ### The specialization `Λ = ℤ₂[[t]]`, `ϖ = 2` -/

/-- `Λ = ℤ₂[[t]]` (tex 2747: "Put `Λ = ℤ₂[[t]]`"). Kind: definition (Mathlib power series over
the `2`-adic integers). -/
abbrev Λ := PowerSeries ℤ_[2]

/-- The constant power series `2` is the element `2` of `Λ`.

tex 2747-2748. Kind: PROVED. -/
theorem C_two : (PowerSeries.C (2 : ℤ_[2]) : Λ) = 2 :=
  map_ofNat _ 2

/-- The ideal `(2)` of `Λ` is prime (so `Λ_(2)` is defined).

tex 2747-2748 ("`Λ_{(2)}`"). Kind: PROVED. -/
instance isPrime_span_two : (Ideal.span {(2 : Λ)}).IsPrime := by
  rw [← C_two]
  exact isPrime_span_C_of_fact

/-- The two descriptions `(2)` and `(C 2)` of the prime of `Λ` have the same complement.

tex 2747-2748. Kind: PROVED. -/
theorem primeCompl_span_two :
    (Ideal.span {(2 : Λ)}).primeCompl = (Ideal.span {PowerSeries.C (2 : ℤ_[2])}).primeCompl := by
  ext x
  rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, C_two]

/-- `Λ_(2)` is a localization of `Λ` at the prime `(C 2)`.

tex 2747-2748. Kind: PROVED. -/
instance isLocalization_atPrime_span_C_two :
    IsLocalization.AtPrime (Localization.AtPrime (Ideal.span {(2 : Λ)}))
      (Ideal.span {PowerSeries.C (2 : ℤ_[2])}) := by
  show IsLocalization (Ideal.span {PowerSeries.C (2 : ℤ_[2])}).primeCompl
    (Localization.AtPrime (Ideal.span {(2 : Λ)}))
  rw [← primeCompl_span_two]
  exact Localization.isLocalization

/-- `Λ_(2)` is a DVR.

tex 2747-2748 (`𝒪 = \widehat{Λ_{(2)}}`) and 4719-4730 ("a DVR"). Kind: PROVED.
DEPARTURE: this is `Λ_(2)`; Elliot's `𝒪` is its `2`-adic completion, and the completion step
(a completion of a DVR is a DVR with the same uniformizer) is GLUE, not formalized here. -/
instance isDiscreteValuationRing_Λ_two :
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {(2 : Λ)})) :=
  isDiscreteValuationRing_of_isLocalization (2 : ℤ_[2]) _

/-- The image of `2` in `Λ_(2)` is the element `2`.

tex 2747-2748. Kind: PROVED. -/
theorem algebraMap_C_two :
    algebraMap Λ (Localization.AtPrime (Ideal.span {(2 : Λ)})) (PowerSeries.C (2 : ℤ_[2])) = 2 := by
  rw [C_two, map_ofNat]

/-- `2` is a uniformizer of `Λ_(2)`.

tex 4719-4730 ("uniformizer two"). Kind: PROVED.
DEPARTURE: stated for `Λ_(2)`; passing to the completion `𝒪` is GLUE, not formalized here. -/
theorem irreducible_two : Irreducible (2 : Localization.AtPrime (Ideal.span {(2 : Λ)})) := by
  rw [← algebraMap_C_two]
  exact irreducible_algebraMap_C_of_isLocalization _

/-- The maximal ideal of `Λ_(2)` is `(2)`.

tex 4719-4730 ("uniformizer two"). Kind: PROVED.
DEPARTURE: stated for `Λ_(2)`; passing to the completion `𝒪` is GLUE, not formalized here. -/
theorem maximalIdeal_eq_span_two :
    IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {(2 : Λ)})) = Ideal.span {2} :=
  irreducible_two.maximalIdeal_eq

/-- `Λ_(2)` has characteristic zero (hence so does its fraction field).

tex 4719-4730 ("characteristic-zero fraction field"). Kind: PROVED.
DEPARTURE: stated for `Λ_(2)`; passing to the completion `𝒪` is GLUE, not formalized here. -/
instance charZero_Λ_two : CharZero (Localization.AtPrime (Ideal.span {(2 : Λ)})) := by
  have : CharZero Λ := RingHom.charZero (PowerSeries.constantCoeff (R := ℤ_[2]))
  exact charZero_of_injective_algebraMap
    (IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {(2 : Λ)})))

end ScalarRing

section ScalarRingExamples

open ScalarRing

/-- `2` is a uniformizer of `Λ_(2)` (from `ScalarRing.irreducible_two`). Kind: PROVED. -/
instance fact_irreducible_two_scalarRing :
    Fact (Irreducible (2 : Localization.AtPrime (Ideal.span {(2 : Λ)}))) :=
  ⟨irreducible_two⟩

/-- The construction (5.3) applied to `R = Λ_(2)`, `ϖ = 2` (Elliot's `𝒪` up to the GLUE completion
step): a DVR with uniformizer `2` and characteristic zero. Kind: PROVED. -/
example : IsDiscreteValuationRing
    (OInf cofiniteUltrafilter (2 : Localization.AtPrime (Ideal.span {(2 : Λ)}))) :=
  inferInstance

example : Irreducible
    (2 : OInf cofiniteUltrafilter (2 : Localization.AtPrime (Ideal.span {(2 : Λ)}))) := by
  have h := irreducible_algebraMap cofiniteUltrafilter
    (2 : Localization.AtPrime (Ideal.span {(2 : Λ)}))
  rwa [map_ofNat] at h

example : CharZero
    (OInf cofiniteUltrafilter (2 : Localization.AtPrime (Ideal.span {(2 : Λ)}))) :=
  inferInstance

end ScalarRingExamples

end ZInQ.Manuscript.RC.Limits
