import ZInQKernel.Contrib.CloudB3E1RingClass.MovingGenuine
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.CurveAtPlace

/-!
# The power-residue formula for Frobenius on the Kummer radicals (the interface's `frob_kummer`)

Manuscript `diophantine_zq.tex`, tex 3676–3677 ("Choose a place realizing this representative ...
The Frobenius formula on `α_a^{1/2^n}` gives (4.4b)"). Lane RC27 states it as the GLUE field
`frob_kummer`: for a good prime `r ≡ 1 (mod 2^n)` and an arithmetic Frobenius `h` at `r` fixing `K`,
some place `v` over `r` satisfies `h(α_a^{1/2^n}) = ζ_{2^n}^{κ_r(res α_a)} α_a^{1/2^n}` for every
radicand. Its docstring names the content: the identification of `Pl r`, `x`, `κ` with the places
over `r`, the residues of `α_a`, and the `2^n`-th power-residue characters normalized by `ζ`. With
that identification the formula is a one-line computation.

This file makes the identification and proves the formula.

* `kummerPlaces r`: the places over `r` attached to Frobenius elements, i.e. pairs `(g, v)` with `v`
  a prime of `ℤ̄` over `r` at which `g` is a Frobenius (the tree's `FrobeniusPlace`).
* `kummerRes v y`: the residue of `y ∈ ℚ̄` at `v`, in `𝐅_r` when it lies there (it does for
  elements fixed by the Frobenius, e.g. the elements of `K`, and for `ζ`).
* `kummerX r v a`: the residue of `α_a` in `𝐅_r^×`. `kummerKappa r v`: the `2^n`-th power-residue
  character of `𝐅_r^×`, normalized by the residue of `ζ` (`exists_powerResidueChar`).
* **`frob_kummer_genuine`** (PROVED): the field `frob_kummer` for these data. The radicands must be
  units at the places over good primes (`α_unit`, true for `α_a = β_a/β̄_a` supported on the chosen
  primes, which good primes avoid).

Proof: `h` fixes `K ∋ α_a`, so `h(γ_a) = ζ^k γ_a` for some `k`. Reducing at the Frobenius place
gives `ζ̄^k = γ̄_a^{r−1} = ᾱ_a^{(r−1)/2^n} = ζ̄^{κ(ᾱ_a)}`. The residue `ζ̄` has order exactly `2^n`
(`ζ^{2^{n−1}} = −1` and `r` is odd), so `ζ^k = ζ^{κ(ᾱ_a)}`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open IsLocalRing
open ZInQ.Contrib.ChebFD.C10 (Zbar Qbar GQ IsFrobAt)
open ZInQ.Manuscript.RC.WitnessSpec
open ZInQ.Manuscript.RC.TateWiring

/-! ### Elements of a field of characteristic `r` fixed by the `r`-th power -/

/-- In a field of characteristic `r`, the solutions of `y^r = y` are the elements of `𝐅_r`.
Kind: PROVED. -/
theorem exists_zmod_of_pow_eq_self {F : Type*} [Field F] {r : ℕ} [Fact r.Prime] [CharP F r]
    (y : F) (hy : y ^ r = y) : ∃ z : ZMod r, ZMod.castHom (dvd_refl r) F z = y := by
  classical
  by_contra hne
  simp only [not_exists] at hne
  let f := ZMod.castHom (dvd_refl r) F
  let S : Finset F := Finset.univ.image f
  have hf : Function.Injective f := f.injective
  have hS : S.card = r := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, ZMod.card]
  let P : Polynomial F := Polynomial.X ^ r - Polynomial.X
  have hr1 : 1 < r := (Fact.out : r.Prime).one_lt
  have hdeg : P.natDegree = r := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hr1]
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  have hsub : insert y S ⊆ P.roots.toFinset := by
    intro w hw
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def]
    simp only [P, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rcases Finset.mem_insert.mp hw with rfl | hw
    · rw [hy, sub_self]
    · obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hw
      rw [← map_pow, ZMod.pow_card, sub_self]
  have hyS : y ∉ S := by
    intro h
    obtain ⟨z, -, hz⟩ := Finset.mem_image.mp h
    exact hne z hz
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hyS, hS] at h1
  have h2 := (Multiset.toFinset_card_le P.roots).trans (Polynomial.card_roots' P)
  rw [hdeg] at h2
  omega

/-! ### The places, residues and power-residue characters -/

/-- **The places over `r`** attached to Frobenius elements: pairs of `g ∈ G_ℚ` and a prime of `ℤ̄`
over `r` at which `g` is a Frobenius. Kind: definition. -/
def kummerPlaces (r : ℕ) : Type := Σ g : GQ, FrobeniusPlace g r

/-- **The residue in `𝐅_r`** of `y ∈ ℚ̄` at the place `v` (`0` if `y` is not integral at `v` or its
residue is not in `𝐅_r`). Kind: definition. -/
def kummerRes {r : ℕ} (v : kummerPlaces r) (y : Qbar) : ZMod r := by
  classical
  exact if hr : r.Prime then
    haveI : Fact r.Prime := ⟨hr⟩
    if h : ∃ (z : ZMod r) (hy : v.2.valuationRing.valuation y ≤ 1),
        ZMod.castHom (dvd_refl r) (ResidueField v.2.valuationRing.valuation.valuationSubring) z =
          residue v.2.valuationRing.valuation.valuationSubring ⟨y, hy⟩
      then h.choose else 0
    else 0

theorem kummerRes_spec {r : ℕ} [hr : Fact r.Prime] (v : kummerPlaces r) {y : Qbar}
    (hy : v.2.valuationRing.valuation y ≤ 1) {z : ZMod r}
    (hz : ZMod.castHom (dvd_refl r) (ResidueField v.2.valuationRing.valuation.valuationSubring) z =
      residue v.2.valuationRing.valuation.valuationSubring ⟨y, hy⟩) :
    kummerRes v y = z := by
  classical
  have hex : ∃ (z : ZMod r) (hy : v.2.valuationRing.valuation y ≤ 1),
      ZMod.castHom (dvd_refl r) (ResidueField v.2.valuationRing.valuation.valuationSubring) z =
        residue v.2.valuationRing.valuation.valuationSubring ⟨y, hy⟩ := ⟨z, hy, hz⟩
  have h1 : kummerRes v y = hex.choose := by
    rw [kummerRes, dite_eq_left_of_eq_true (eq_true hr.out), dite_eq_left_of_eq_true (eq_true hex)]
  rw [h1]
  apply (ZMod.castHom (dvd_refl r) (ResidueField v.2.valuationRing.valuation.valuationSubring)).injective
  rw [hex.choose_spec.2, hz]

/-- **The residue of `α_a` in `𝐅_r^×`** at the place `v` (`1` if it is not a unit). Kind: definition. -/
def kummerX {r : ℕ} (α : Qbar) (v : kummerPlaces r) : Additive (ZMod r)ˣ := by
  classical
  exact if h : IsUnit (kummerRes v α) then Additive.ofMul h.unit else 0

/-- **The `2^n`-th power-residue character** at `v`, normalized by the residue `ζ̄` of `ζ`:
`x^{(r−1)/2^n} = ζ̄^{κ(x)}` (trivial if `ζ̄` is not a primitive `2^n`-th root in `𝐅_r` or
`2^n ∤ r − 1`). Kind: definition. -/
def kummerKappa {r : ℕ} (n : ℕ) (ζ : Qbar) (v : kummerPlaces r) :
    Additive (ZMod r)ˣ →+ ZMod (2 ^ n) := by
  classical
  exact if h : ∃ (hr : r.Prime) (u : (ZMod r)ˣ), (u : ZMod r) = kummerRes v ζ ∧
      IsPrimitiveRoot u (2 ^ n) ∧ 2 ^ n ∣ r - 1 then
    haveI : Fact r.Prime := ⟨h.choose⟩
    (exists_powerResidueChar h.choose_spec.choose_spec.2.2
      h.choose_spec.choose_spec.2.1).choose
  else 0

theorem kummerKappa_spec {r n : ℕ} [hr : Fact r.Prime] {ζ : Qbar} (v : kummerPlaces r)
    (u : (ZMod r)ˣ) (hu : (u : ZMod r) = kummerRes v ζ) (hprim : IsPrimitiveRoot u (2 ^ n))
    (hdvd : 2 ^ n ∣ r - 1) (x : (ZMod r)ˣ) :
    x ^ ((r - 1) / 2 ^ n) = u ^ (kummerKappa n ζ v (Additive.ofMul x)).val := by
  classical
  have hex : ∃ (hr : r.Prime) (u : (ZMod r)ˣ), (u : ZMod r) = kummerRes v ζ ∧
      IsPrimitiveRoot u (2 ^ n) ∧ 2 ^ n ∣ r - 1 := ⟨hr.out, u, hu, hprim, hdvd⟩
  have hu' : hex.choose_spec.choose = u := Units.ext (hex.choose_spec.choose_spec.1.trans hu.symm)
  have hk : kummerKappa n ζ v = (exists_powerResidueChar (r := r) hex.choose_spec.choose_spec.2.2
      hex.choose_spec.choose_spec.2.1).choose := by
    rw [kummerKappa, dite_eq_left_of_eq_true (eq_true hex)]
  rw [hk, ← hu']
  exact (exists_powerResidueChar (r := r) hex.choose_spec.choose_spec.2.2
      hex.choose_spec.choose_spec.2.1).choose_spec.2 x

/-! ### The power-residue formula -/

theorem fix_of_mem_quadField {h : GQ} {s : Qbar} (hs : h s = s) {y : Qbar} (hy : y ∈ quadField s) :
    h y = y := by
  have hle : quadField s ≤ IntermediateField.fixedField (MulAction.stabilizer GQ s) := by
    rw [quadField, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      IntermediateField.mem_fixedField_iff]
    intro f hf
    exact hf
  exact (IntermediateField.mem_fixedField_iff _ _).mp (hle hy) h hs

variable {r : ℕ} [hr : Fact r.Prime] (v : kummerPlaces r)

theorem val_eq_one_of_pow {x : Qbar} {m : ℕ} (hm : m ≠ 0)
    (h : v.2.valuationRing.valuation (x ^ m) = 1) : v.2.valuationRing.valuation x = 1 := by
  rw [map_pow, pow_eq_one_iff] at h
  exact h.resolve_right hm

/-- The residue of an element of valuation one is nonzero. -/
theorem residue_ne_zero_of_val {x : Qbar} (hx : v.2.valuationRing.valuation x = 1) :
    residue v.2.valuationRing.valuation.valuationSubring ⟨x, hx.le⟩ ≠ 0 := by
  rw [IsLocalRing.residue_ne_zero_iff_isUnit, ValuationSubring.valuation_eq_one_iff]
  change v.2.valuationRing.valuation.valuationSubring.valuation x = 1
  rw [ValuationSubring.valuationSubring_valuation]
  exact hx

/-- **The power-residue formula at one Frobenius place** (tex 3676–3677). Let `h` be a Frobenius at
the place `w` over an odd prime `r ≡ 1 (mod 2^n)`, let `ζ` be a primitive `2^n`-th root of unity, and
let `γ^{2^n} = α`, with `α` fixed by `h` and a unit at `w`. Then
`h(γ) = ζ^{κ_w(res α)} γ`. Kind: PROVED. -/
theorem frob_kummer_at {h : GQ} (w : FrobeniusPlace h r) (hr2 : r ≠ 2) {n : ℕ} {ζ : Qbar}
    (hζ : IsPrimitiveRoot ζ (2 ^ n)) (hdvd : 2 ^ n ∣ r - 1) {α γ : Qbar} (hγ : γ ^ 2 ^ n = α)
    (hγ0 : γ ≠ 0) (hfix : h α = α) (hα : w.valuationRing.valuation α = 1) :
    h γ = ζ ^ (kummerKappa n ζ (⟨h, w⟩ : kummerPlaces r)
      (kummerX α (⟨h, w⟩ : kummerPlaces r))).val * γ := by
  classical
  set v : kummerPlaces r := ⟨h, w⟩
  set V := w.valuationRing.valuation
  have : NeZero (2 ^ n) := ⟨pow_ne_zero _ two_ne_zero⟩
  -- `h γ = ζ^k γ`
  have hα0 : α ≠ 0 := by rw [← hγ]; exact pow_ne_zero _ hγ0
  obtain ⟨k, hk, hkζ⟩ := hζ.eq_pow_of_pow_eq_one (ξ := h γ * γ⁻¹) (by
    rw [mul_pow, ← map_pow, hγ, hfix, inv_pow, hγ, mul_inv_cancel₀ hα0])
  have hhγ : h γ = ζ ^ k * γ := by rw [hkζ, mul_assoc, inv_mul_cancel₀ hγ0, mul_one]
  by_cases hn : n = 0
  · subst hn
    have hζ1 : ζ = 1 := by simpa using hζ
    rw [hhγ, hζ1, one_pow, one_pow]
  -- valuations
  have Vγ : V γ = 1 := val_eq_one_of_pow v (m := 2 ^ n) (pow_ne_zero _ two_ne_zero) (hγ ▸ hα)
  have Vζ : V ζ = 1 := val_eq_one_of_pow v (m := 2 ^ n) (pow_ne_zero _ two_ne_zero)
    (by rw [hζ.pow_eq_one, map_one])
  let 𝒪 := V.valuationSubring
  let res : 𝒪 →+* ResidueField 𝒪 := residue 𝒪
  let γ' : 𝒪 := ⟨γ, Vγ.le⟩
  let ζ' : 𝒪 := ⟨ζ, Vζ.le⟩
  let α' : 𝒪 := ⟨α, hα.le⟩
  have hγα : γ' ^ 2 ^ n = α' := Subtype.ext (by simpa using hγ)
  -- the Frobenius congruence
  have F1 : res ⟨h γ, (w.valuation_frob_le_one_iff γ).mpr Vγ.le⟩ = res γ' ^ r :=
    w.valuation_frob_residue γ Vγ.le
  have F2 : (⟨h γ, (w.valuation_frob_le_one_iff γ).mpr Vγ.le⟩ : 𝒪) = ζ' ^ k * γ' :=
    Subtype.ext (by simpa using hhγ)
  rw [F2, map_mul, map_pow] at F1
  have hγ'0 : res γ' ≠ 0 := residue_ne_zero_of_val v Vγ
  have hr1 : r = (r - 1) + 1 := (Nat.succ_pred_eq_of_pos (Fact.out : r.Prime).pos).symm
  have F3 : res ζ' ^ k = res γ' ^ (r - 1) := by
    rw [hr1, pow_succ] at F1
    exact mul_right_cancel₀ hγ'0 F1
  obtain ⟨m, hm⟩ := hdvd
  have F4 : res γ' ^ (r - 1) = res α' ^ m := by rw [hm, pow_mul, ← map_pow, hγα]
  -- `res α ∈ 𝐅_r`
  have F5 : res α' ^ r = res α' := by
    have := w.valuation_frob_residue α hα.le
    have he : (⟨h α, (w.valuation_frob_le_one_iff α).mpr hα.le⟩ : 𝒪) = α' := Subtype.ext hfix
    rw [he] at this
    exact this.symm
  obtain ⟨zα, hzα⟩ := exists_zmod_of_pow_eq_self (res α') F5
  have hxα : kummerRes v α = zα := kummerRes_spec v hα.le hzα
  have hα'0 : res α' ≠ 0 := residue_ne_zero_of_val v hα
  have hzα0 : zα ≠ 0 := by rintro rfl; rw [map_zero] at hzα; exact hα'0 hzα.symm
  have hU : IsUnit (kummerRes v α) := by rw [hxα]; exact isUnit_iff_ne_zero.mpr hzα0
  have hX : kummerX α v = Additive.ofMul hU.unit := by
    rw [kummerX, dite_eq_left_of_eq_true (eq_true hU)]
  -- `res ζ ∈ 𝐅_r`
  have hζr : ζ ^ r = ζ := by
    rw [hr1, hm, pow_succ, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  have F6 : res ζ' ^ r = res ζ' := by
    rw [← map_pow]
    exact congrArg res (Subtype.ext (by simpa using hζr))
  obtain ⟨zζ, hzζ⟩ := exists_zmod_of_pow_eq_self (res ζ') F6
  have hxζ : kummerRes v ζ = zζ := kummerRes_spec v Vζ.le hzζ
  -- `res ζ` is a primitive `2^n`-th root
  have hpr : IsPrimitiveRoot (res ζ') (2 ^ n) := by
    obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    refine IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime_pow ?_ ?_)
    · have hpow : ζ ^ 2 ^ n' = -1 :=
        (hζ.pow (pow_pos two_pos _) (by rw [pow_succ])).eq_neg_one_of_two_right
      have hres : res ζ' ^ 2 ^ n' = -1 := by
        rw [← map_pow, ← map_one res, ← map_neg res 1]
        exact congrArg res (Subtype.ext (by simpa using hpow))
      rw [hres]
      intro h1
      have h2 : ((2 : ℕ) : ResidueField 𝒪) = 0 := by
        have : (1 : ResidueField 𝒪) + 1 = 0 := by
          calc (1 : ResidueField 𝒪) + 1 = -1 + 1 := by rw [h1]
            _ = 0 := neg_add_cancel 1
        exact_mod_cast this
      rw [CharP.cast_eq_zero_iff (ResidueField 𝒪) r] at h2
      exact hr2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) Nat.prime_two).mp h2)
    · rw [← map_pow, ← map_one res]
      exact congrArg res (Subtype.ext (by simpa using hζ.pow_eq_one))
  have hzζ0 : zζ ≠ 0 := by
    rintro rfl; rw [map_zero] at hzζ; exact residue_ne_zero_of_val v Vζ hzζ.symm
  have hUζ : IsUnit zζ := isUnit_iff_ne_zero.mpr hzζ0
  have hprimz : IsPrimitiveRoot hUζ.unit (2 ^ n) := by
    rw [← IsPrimitiveRoot.coe_units_iff, IsUnit.unit_spec,
      ← IsPrimitiveRoot.map_iff_of_injective (f := ZMod.castHom (dvd_refl r) (ResidueField 𝒪))
        (ZMod.castHom (dvd_refl r) (ResidueField 𝒪)).injective, hzζ]
    exact hpr
  have hspec := kummerKappa_spec v hUζ.unit (by rw [IsUnit.unit_spec, hxζ]) hprimz
    ⟨m, hm⟩ hU.unit
  rw [← hX] at hspec
  set κv := (kummerKappa n ζ v (kummerX α v)).val
  have hdiv : (r - 1) / 2 ^ n = m := by
    rw [hm, Nat.mul_div_cancel_left _ (pow_pos two_pos n)]
  rw [hdiv] at hspec
  -- cast to the residue field
  have F7 : res α' ^ m = res ζ' ^ κv := by
    have := congrArg (fun z : (ZMod r)ˣ =>
      ZMod.castHom (dvd_refl r) (ResidueField 𝒪) (z : ZMod r)) hspec
    simp only [Units.val_pow_eq_pow_val, map_pow, IsUnit.unit_spec, hxα, hzα, hzζ] at this
    exact this
  have F8 : res ζ' ^ k = res ζ' ^ κv := by rw [F3, F4, F7]
  have hkκ : k = κv := hpr.pow_inj hk (ZMod.val_lt _) F8
  rw [hhγ, hkκ]

omit hr in
/-- **The interface's `frob_kummer` for the genuine places, residues and power-residue
characters** (tex 3676–3677; the GLUE field `frob_kummer` of `MovingDataK` and
`GenuineMovingInputs`), with `Pl := kummerPlaces`, `x r v a := kummerX (kd.α a) v` and
`κ r v := kummerKappa n kd.ζ v`. The input `hαunit` asks that the radicands be units at the places
over good primes. Kind: PROVED. -/
theorem frob_kummer_genuine {E : WeierstrassCurve ℚ} {s : Qbar} {n t : ℕ} (kd : KummerData s n t)
    (Sexc : Finset ℕ)
    (hαunit : ∀ (r : ℕ) [Fact r.Prime] (v : kummerPlaces r), GoodPrime E s Sexc r →
      ∀ a, v.2.valuationRing.valuation (kd.α a) = 1) :
    ∀ (r : ℕ) (h : ZInQ.Manuscript.RC.PrintsArith.GalQ), GoodPrime E s Sexc r →
      IsFrobAt h r → h s = s → (2 : ℤ) ^ n ∣ (r : ℤ) - 1 →
        ∃ v : kummerPlaces r, ∀ a,
          h (kd.γ a) = kd.ζ ^ (kummerKappa n kd.ζ v (kummerX (kd.α a) v)).val * kd.γ a := by
  intro r h hgood hfrob hs hdvd
  have : Fact r.Prime := ⟨hgood.1⟩
  let w := FrobeniusPlace.ofIsFrobAt hfrob
  refine ⟨⟨h, w⟩, fun a => ?_⟩
  have hdvd' : 2 ^ n ∣ r - 1 := by
    have h1 : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by
      rw [Nat.cast_sub hgood.1.one_lt.le, Nat.cast_one]
    exact_mod_cast (h1 ▸ hdvd)
  exact frob_kummer_at w hgood.2.1 kd.hζ hdvd' (kd.γ_pow a) (kd.γ_ne a)
    (fix_of_mem_quadField hs (kd.α_mem a)) (hαunit r ⟨h, w⟩ hgood a)

/-- **The residue of `ζ` is a primitive `2^n`-th root of unity in `𝐅_r`** at every place over an
odd prime `r ≡ 1 (mod 2^n)`. Kind: PROVED. -/
theorem exists_unit_kummerRes_zeta (v : kummerPlaces r) (hr2 : r ≠ 2) {n : ℕ} {ζ : Qbar}
    (hζ : IsPrimitiveRoot ζ (2 ^ n)) (hdvd : 2 ^ n ∣ r - 1) :
    ∃ u : (ZMod r)ˣ, (u : ZMod r) = kummerRes v ζ ∧ IsPrimitiveRoot u (2 ^ n) := by
  classical
  set V := v.2.valuationRing.valuation
  have Vζ : V ζ = 1 := val_eq_one_of_pow v (m := 2 ^ n) (pow_ne_zero _ two_ne_zero)
    (by rw [hζ.pow_eq_one, map_one])
  let 𝒪 := V.valuationSubring
  let res : 𝒪 →+* ResidueField 𝒪 := residue 𝒪
  let ζ' : 𝒪 := ⟨ζ, Vζ.le⟩
  obtain ⟨m, hm⟩ := hdvd
  have hr1 : r = (r - 1) + 1 := (Nat.succ_pred_eq_of_pos (Fact.out : r.Prime).pos).symm
  have hζr : ζ ^ r = ζ := by
    rw [hr1, hm, pow_succ, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  have F6 : res ζ' ^ r = res ζ' := by
    rw [← map_pow]
    exact congrArg res (Subtype.ext (by simpa using hζr))
  obtain ⟨zζ, hzζ⟩ := exists_zmod_of_pow_eq_self (res ζ') F6
  have hxζ : kummerRes v ζ = zζ := kummerRes_spec v Vζ.le hzζ
  have hpr : IsPrimitiveRoot (res ζ') (2 ^ n) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hζ1 : ζ = 1 := by simpa using hζ
      have : res ζ' = 1 := by
        rw [← map_one res]; exact congrArg res (Subtype.ext hζ1)
      rw [this, pow_zero]; exact IsPrimitiveRoot.one
    obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    refine IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime_pow ?_ ?_)
    · have hpow : ζ ^ 2 ^ n' = -1 :=
        (hζ.pow (pow_pos two_pos _) (by rw [pow_succ])).eq_neg_one_of_two_right
      have hres : res ζ' ^ 2 ^ n' = -1 := by
        rw [← map_pow, ← map_one res, ← map_neg res 1]
        exact congrArg res (Subtype.ext (by simpa using hpow))
      rw [hres]
      intro h1
      have h2 : ((2 : ℕ) : ResidueField 𝒪) = 0 := by
        have : (1 : ResidueField 𝒪) + 1 = 0 := by
          calc (1 : ResidueField 𝒪) + 1 = -1 + 1 := by rw [h1]
            _ = 0 := neg_add_cancel 1
        exact_mod_cast this
      rw [CharP.cast_eq_zero_iff (ResidueField 𝒪) r] at h2
      exact hr2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) Nat.prime_two).mp h2)
    · rw [← map_pow, ← map_one res]
      exact congrArg res (Subtype.ext (by simpa using hζ.pow_eq_one))
  have hzζ0 : zζ ≠ 0 := by
    rintro rfl; rw [map_zero] at hzζ; exact residue_ne_zero_of_val v Vζ hzζ.symm
  have hUζ : IsUnit zζ := isUnit_iff_ne_zero.mpr hzζ0
  refine ⟨hUζ.unit, by rw [IsUnit.unit_spec, hxζ], ?_⟩
  rw [← IsPrimitiveRoot.coe_units_iff, IsUnit.unit_spec,
    ← IsPrimitiveRoot.map_iff_of_injective (f := ZMod.castHom (dvd_refl r) (ResidueField 𝒪))
      (ZMod.castHom (dvd_refl r) (ResidueField 𝒪)).injective, hzζ]
  exact hpr

/-- **The power-residue character is onto** at every place over an odd prime `r ≡ 1 (mod 2^n)`
(tex 3585–3586). Kind: PROVED. -/
theorem kummerKappa_surjective (v : kummerPlaces r) (hr2 : r ≠ 2) {n : ℕ} {ζ : Qbar}
    (hζ : IsPrimitiveRoot ζ (2 ^ n)) (hdvd : 2 ^ n ∣ r - 1) :
    Function.Surjective (kummerKappa n ζ v) := by
  classical
  obtain ⟨u, hu, hprim⟩ := exists_unit_kummerRes_zeta v hr2 hζ hdvd
  have hex : ∃ (hr : r.Prime) (u : (ZMod r)ˣ), (u : ZMod r) = kummerRes v ζ ∧
      IsPrimitiveRoot u (2 ^ n) ∧ 2 ^ n ∣ r - 1 := ⟨hr.out, u, hu, hprim, hdvd⟩
  have hk : kummerKappa n ζ v = (exists_powerResidueChar (r := r) hex.choose_spec.choose_spec.2.2
      hex.choose_spec.choose_spec.2.1).choose := by
    rw [kummerKappa, dite_eq_left_of_eq_true (eq_true hex)]
  rw [hk]
  exact (exists_powerResidueChar (r := r) hex.choose_spec.choose_spec.2.2
      hex.choose_spec.choose_spec.2.1).choose_spec.1

omit hr in
/-- **The interface's `κ_surj` for the genuine power-residue characters** (tex 3585–3586).
Kind: PROVED. -/
theorem kappa_surj_genuine {E : WeierstrassCurve ℚ} {s : Qbar} {n t : ℕ} (kd : KummerData s n t)
    (Sexc : Finset ℕ) :
    ∀ r, GoodPrime E s Sexc r → ∀ v : kummerPlaces r, (2 : ℤ) ^ n ∣ (r : ℤ) - 1 →
      Function.Surjective (kummerKappa n kd.ζ v) := by
  intro r hgood v hdvd
  have : Fact r.Prime := ⟨hgood.1⟩
  have hdvd' : 2 ^ n ∣ r - 1 := by
    have h1 : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by
      rw [Nat.cast_sub hgood.1.one_lt.le, Nat.cast_one]
    exact_mod_cast (h1 ▸ hdvd)
  exact kummerKappa_surjective v hgood.2.1 kd.hζ hdvd'

end ZInQ.Contrib.CloudB3E1RingClass
