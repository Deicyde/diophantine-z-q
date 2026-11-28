import ZInQKernel.Contrib.OneProof.RC.ModelGeneric6.CharFreeSeamTwo

/-! **Formula-carrying composite seams** (rc-model-generic7, item 3, R0).

`ModelGeneric6.exists_quotientSeam` returns only `∃ ι hι, FiniteAlong ∧ finrankAlong = n ∧ ∃ g,
g.ker = H ∧ IsSeam`: its steps choose their own generators and drop the Vélu formulas. This file
builds the variant that takes one generator `c` of `H` as input and records, step by step along
the `minFac` recursion of the vendored composite `cyclicQuotientCurve`, the step maps with their
kernels and their Vélu formulas.

* `OddStepFormula E c' p f`: off `⟨c'⟩`, `f (x, y)` is the affine point with coordinates
  `(E.veluX S x, E.veluY S x y)`, `S = E.oddOrderSummingSet c' (p / 2)` (the formula of the
  vendored `exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed`), read with `coordsOrZero`
  so that it survives the Sigma equation of the bridge `stepCurve_stepSubgroup_eq_of_prime_ne_two`.
* `TwoStepFormula E c' f`: `c' = (x₀, y₀)` and `f` agrees with the vendored `veluPointMap2` at
  `(x₀, y₀)` (zero locus and `coordsOrZero`), surviving `stepCurve_stepSubgroup_two_eq`.
* `FormulaSeam E H c n g` (inductive): for `n = 1`, `g` is the identity transported along
  `cyclicQuotientCurve_one`; for `n ≥ 2`, `p = n.minFac`, `g = transport ∘ g' ∘ f` with `f` a step
  map to `E.stepCurve H p` with kernel `⟨(n/p) • c⟩`, its formula, `H.map f = E.stepSubgroup H p`,
  and `g'` satisfying the predicate at `(E.stepCurve H p, H.map f, f c, n/p)`; the transport is
  along `stepEq` (`cyclicQuotientCurve_eq_of_two_le` and `H.map f = stepSubgroup`).
* `exists_oddStep_formula`, `exists_twoStep_formula`: the prime steps at a given generator.
* `exists_formulaSeam`: everything `exists_quotientSeam` gives, for a `g` satisfying
  `FormulaSeam`. `exists_quotientSeam_of_formulaSeam` recovers `ModelGeneric6.exists_quotientSeam`
  from it.

Provenance: the step and composite proofs adapt the proofs of `ModelGeneric6.exists_oddStep`,
`ModelGeneric6.stepSeam_two` and `ModelGeneric6.exists_quotientSeam_of_steps` (the lead's copy
leave for the CharFreeSeam family); each adapted block carries a provenance line. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Manuscript.RC.ModelGeneric7

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine Polynomial
open ZInQ.Manuscript.RC.ModelGeneric6 (gate gate_isCentred gate_abel pointPlace IsSeam isSeam_comp
  finrankAlong_comp' finrankAlong_ne_one_of_seam twoFFHom_seam finrankAlong_twoFFHom_le)

section Cast

variable {K : Type*} [Field K] [DecidableEq K]

/-- Transport of points along an equality of Weierstrass curves, as an additive map. -/
def pointCast {V V' : WeierstrassCurve K} (h : V = V') :
    V.toAffine.Point →+ V'.toAffine.Point := by
  subst h
  exact AddMonoidHom.id _

theorem pointCast_apply {V V' : WeierstrassCurve K} (h : V = V') (P : V.toAffine.Point) :
    pointCast h P = cast (congrArg (fun V : WeierstrassCurve K => V.toAffine.Point) h) P := by
  subst h
  rfl

theorem pointCast_injective {V V' : WeierstrassCurve K} (h : V = V') :
    Function.Injective (pointCast h) := by
  subst h
  exact fun _ _ e => e

theorem ker_pointCast_comp {E V V' : WeierstrassCurve K} (h : V = V')
    (g : E.toAffine.Point →+ V.toAffine.Point) : ((pointCast h).comp g).ker = g.ker := by
  subst h
  rfl

end Cast

variable {k : Type} [Field k] [DecidableEq k] [IsAlgClosed k]

/-- Seam data transport along an equality of target curves. -/
theorem seam_transport {E V V' : WeierstrassCurve k} [E.IsElliptic] (h : V = V') (n : ℕ)
    (g : E.toAffine.Point →+ V.toAffine.Point)
    (hs : ∃ _ : V.IsElliptic, ∃ (ι : V.toAffine.FunctionField →ₐ[k] E.toAffine.FunctionField)
      (hι : ι.toRingHom.IsIntegral), FiniteAlong k ι ∧ finrankAlong k ι = n ∧ IsSeam ι hι g) :
    ∃ _ : V'.IsElliptic, ∃ (ι : V'.toAffine.FunctionField →ₐ[k] E.toAffine.FunctionField)
      (hι : ι.toRingHom.IsIntegral), FiniteAlong k ι ∧ finrankAlong k ι = n ∧
        IsSeam ι hι ((pointCast h).comp g) := by
  subst h
  exact hs

/-- The Vélu formula of an odd prime step at `c'` (the formula of the vendored
`exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed`), read on coordinates. -/
def OddStepFormula (E : WeierstrassCurve k) (c' : E.toAffine.Point) (p : ℕ) {V : WeierstrassCurve k}
    (f : E.toAffine.Point →+ V.toAffine.Point) : Prop :=
  ∀ (x y : k) (h : E.toAffine.Nonsingular x y),
    (Point.some x y h : E.toAffine.Point) ∉ AddSubgroup.zmultiples c' →
      f (Point.some x y h) ≠ 0 ∧
        (f (Point.some x y h)).coordsOrZero =
          (E.veluX (E.oddOrderSummingSet c' (p / 2)) x,
            E.veluY (E.oddOrderSummingSet c' (p / 2)) x y)

/-- The Vélu formula of the order-two step at `c' = (x₀, y₀)`: agreement with the vendored
`veluPointMap2` on the zero locus and on coordinates. -/
def TwoStepFormula (E : WeierstrassCurve k) (c' : E.toAffine.Point) {V : WeierstrassCurve k}
    (f : E.toAffine.Point →+ V.toAffine.Point) : Prop :=
  ∃ (x₀ y₀ : k) (hns : E.toAffine.Nonsingular x₀ y₀) (h2 : (2 : k) ≠ 0)
    (hgy : E.veluGy x₀ y₀ = 0) (hΔ : (E.veluQuotient2 x₀ y₀).Δ ≠ 0),
    c' = Point.some x₀ y₀ hns ∧
      ∀ P : E.toAffine.Point, (f P = 0 ↔ veluPointMap2 h2 hns.1 hgy hΔ P = 0) ∧
        (f P).coordsOrZero = (veluPointMap2 h2 hns.1 hgy hΔ P).coordsOrZero

/-- The formula of a prime step: odd or order two. -/
def StepFormula (E : WeierstrassCurve k) (c' : E.toAffine.Point) (p : ℕ) {V : WeierstrassCurve k}
    (f : E.toAffine.Point →+ V.toAffine.Point) : Prop :=
  (p ≠ 2 → OddStepFormula E c' p f) ∧ (p = 2 → TwoStepFormula E c' f)

/-- The target of one step of the composite, rewritten to the composite's target. -/
theorem stepEq (E : WeierstrassCurve k) (H : AddSubgroup E.toAffine.Point) {n : ℕ} (hn : 2 ≤ n)
    (f : E.toAffine.Point →+ (E.stepCurve H n.minFac).toAffine.Point)
    (hmap : H.map f = E.stepSubgroup H n.minFac) :
    (E.stepCurve H n.minFac).cyclicQuotientCurve (H.map f) (n / n.minFac) =
      E.cyclicQuotientCurve H n := by
  rw [hmap, cyclicQuotientCurve_eq_of_two_le E H hn]

/-- **The step-indexed predicate of formula-carrying composite seams** (R0). `FormulaSeam E H c n g`
says that `g : E → E.cyclicQuotientCurve H n` is the composite of the vendored Vélu steps along the
`minFac` recursion, each at the generator `(n/p) • c` of its kernel, with its formula. -/
inductive FormulaSeam : (E : WeierstrassCurve k) → (H : AddSubgroup E.toAffine.Point) →
    E.toAffine.Point → (n : ℕ) →
    (E.toAffine.Point →+ (E.cyclicQuotientCurve H n).toAffine.Point) → Prop where
  /-- Level one: the identity, transported along `cyclicQuotientCurve_one`. -/
  | one (E : WeierstrassCurve k) (H : AddSubgroup E.toAffine.Point) (c : E.toAffine.Point)
      (hcH : H = AddSubgroup.zmultiples c) (hc : addOrderOf c = 1) :
      FormulaSeam E H c 1 (pointCast (E.cyclicQuotientCurve_one H).symm)
  /-- Level `n ≥ 2`: a prime step at `(n / n.minFac) • c`, then the predicate one level down. -/
  | step (E : WeierstrassCurve k) (H : AddSubgroup E.toAffine.Point) (c : E.toAffine.Point)
      (n : ℕ) (hcH : H = AddSubgroup.zmultiples c) (hc : addOrderOf c = n) (hn : 2 ≤ n)
      (hE : (E.stepCurve H n.minFac).IsElliptic)
      (f : E.toAffine.Point →+ (E.stepCurve H n.minFac).toAffine.Point)
      (hker : f.ker = AddSubgroup.zmultiples ((n / n.minFac) • c))
      (hform : StepFormula E ((n / n.minFac) • c) n.minFac f)
      (hmap : H.map f = E.stepSubgroup H n.minFac)
      (g' : (E.stepCurve H n.minFac).toAffine.Point →+
        ((E.stepCurve H n.minFac).cyclicQuotientCurve (H.map f) (n / n.minFac)).toAffine.Point)
      (hg' : FormulaSeam (E.stepCurve H n.minFac) (H.map f) (f c) (n / n.minFac) g') :
      FormulaSeam E H c n ((pointCast (stepEq E H hn f hmap)).comp (g'.comp f))

-- Adapted from the proof of `exists_oddStep`,
-- ZInQKernel/Contrib/OneProof/RC/ModelGeneric6/CharFreeSeam.lean:143-201, base SHA
-- aba99b7b2e3eea8804ebeffd1834ba5f31fa9c7e (generator given; formula and kernel recorded).
/-- **The odd prime step at a given generator, with its formula.** Refines
`ModelGeneric6.exists_oddStep`: the generator `c'` is an input, the kernel is `⟨c'⟩`, and the
formula off the kernel is recorded. -/
theorem exists_oddStep_formula (E : WeierstrassCurve k) [E.IsElliptic]
    (H : AddSubgroup E.toAffine.Point) [IsAddCyclic H] [Finite H]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓk : (ℓ : k) ≠ 0)
    (Q : E.toAffine.Point) (hQH : Q ∈ H) (hQ : addOrderOf Q = ℓ) :
    ∃ _ : (E.stepCurve H ℓ).IsElliptic,
      ∃ (ι : (E.stepCurve H ℓ).toAffine.FunctionField →ₐ[k] E.toAffine.FunctionField)
        (hι : ι.toRingHom.IsIntegral), FiniteAlong k ι ∧ finrankAlong k ι = ℓ ∧
        ∃ f : E.toAffine.Point →+ (E.stepCurve H ℓ).toAffine.Point,
          f.ker = AddSubgroup.zmultiples Q ∧ StepFormula E Q ℓ f ∧
            H.map f = E.stepSubgroup H ℓ ∧ IsSeam ι hι f := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hodd : ℓ = 2 * (ℓ / 2) + 1 := by
    rcases Nat.even_or_odd ℓ with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact absurd (hℓ.eq_one_or_self_of_dvd 2 ⟨m, by omega⟩) (by omega)
    · omega
  have hQ' : addOrderOf Q = 2 * (ℓ / 2) + 1 := hQ.trans hodd
  have hΔ := E.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq (ℓ / 2) Q hQ'
  haveI hV : (E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2))).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  letI := gate E
  haveI := gate_isCentred E
  haveI := gate_abel E
  letI := gate (E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2)))
  haveI := gate_isCentred (E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2)))
  haveI := gate_abel (E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2)))
  obtain ⟨ι, hι, hfin, hdeg, -, hzero, hsome⟩ :=
    exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed (W := E) hQ' hΔ
  obtain ⟨φ, hφker, hφ⟩ := E.exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed hℓ hℓ2 hℓk Q hQ
  have hseam : IsSeam ι hι φ := by
    unfold IsSeam
    intro P
    by_cases hP : P ∈ AddSubgroup.zmultiples Q
    · have h0 : φ P = 0 := by rw [← AddMonoidHom.mem_ker, hφker]; exact hP
      change Place.restrictAlong ι hι (placeOfPoint P) = placeOfPoint (φ P)
      rw [h0]
      exact hzero P hP
    · rcases P with _ | ⟨x, y, h⟩
      · exact absurd (AddSubgroup.zero_mem _) hP
      · obtain ⟨h', hφP⟩ := hφ x y h hP
        obtain ⟨h'', hpl⟩ := hsome x y h hP
        change Place.restrictAlong ι hι (placeOfPoint _) = placeOfPoint (φ _)
        rw [hφP, hpl]
  have hform : StepFormula E Q ℓ φ := by
    refine ⟨fun _ x y h hP => ?_, fun h2 => absurd h2 hℓ2⟩
    obtain ⟨h', hφP⟩ := hφ x y h hP
    rw [hφP]
    exact ⟨Point.some_ne_zero h', rfl⟩
  have hbridge := E.stepCurve_stepSubgroup_eq_of_prime_ne_two hℓ hℓ2 H Q hQH hQ φ hφker hφ
  have result (s : Σ V : WeierstrassCurve k, AddSubgroup V.toAffine.Point)
      (hs : s = ⟨E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2)), H.map φ⟩) :
      ∃ _ : s.1.IsElliptic,
        ∃ (ι : s.1.toAffine.FunctionField →ₐ[k] E.toAffine.FunctionField)
          (hι : ι.toRingHom.IsIntegral), FiniteAlong k ι ∧ finrankAlong k ι = ℓ ∧
          ∃ f : E.toAffine.Point →+ s.1.toAffine.Point,
            f.ker = AddSubgroup.zmultiples Q ∧ StepFormula E Q ℓ f ∧ H.map f = s.2 ∧
              IsSeam ι hι f := by
    subst hs
    exact ⟨hV, ι, hι, hfin, hdeg.trans hodd.symm, φ, hφker, hform, rfl, hseam⟩
  exact result _ hbridge

open P2MW.S_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j.P2MKcKI
  in
-- Adapted from the proof of `stepSeam_two`,
-- ZInQKernel/Contrib/OneProof/RC/ModelGeneric6/CharFreeSeamTwo.lean:162-234, base SHA
-- aba99b7b2e3eea8804ebeffd1834ba5f31fa9c7e (generator given; formula and kernel recorded).
/-- **The order-two step at a given point of order two, with its formula.** Refines
`ModelGeneric6.stepSeam_two`: the point `Q` of order two is an input, the kernel is `⟨Q⟩`, and the
step map is recorded as the vendored `veluPointMap2` at `Q`. -/
theorem exists_twoStep_formula (h2 : (2 : k) ≠ 0) (E : WeierstrassCurve k) [E.IsElliptic]
    (H : AddSubgroup E.toAffine.Point) [IsAddCyclic H] [Finite H]
    (Q : E.toAffine.Point) (hQH' : Q ∈ H) (hQ2 : addOrderOf Q = 2) :
    ∃ _ : (E.stepCurve H 2).IsElliptic,
      ∃ (ι : (E.stepCurve H 2).toAffine.FunctionField →ₐ[k] E.toAffine.FunctionField)
        (hι : ι.toRingHom.IsIntegral), FiniteAlong k ι ∧ finrankAlong k ι = 2 ∧
        ∃ f : E.toAffine.Point →+ (E.stepCurve H 2).toAffine.Point,
          f.ker = AddSubgroup.zmultiples Q ∧ StepFormula E Q 2 f ∧
            H.map f = E.stepSubgroup H 2 ∧ IsSeam ι hι f := by
  have hQ0 : Q ≠ 0 := by
    intro h0; rw [h0, addOrderOf_zero] at hQ2; omega
  obtain ⟨x₀, y₀, hns, hqe⟩ : ∃ x₀ y₀ h, Q = .some x₀ y₀ h := by
    rcases hqP : Q with _ | ⟨x₀, y₀, h⟩
    · exact absurd hqP hQ0
    · exact ⟨x₀, y₀, h, rfl⟩
  have hgy : E.veluGy x₀ y₀ = 0 := by
    have h2Q : (2 : ℕ) • Q = 0 := hQ2 ▸ addOrderOf_nsmul_eq_zero _
    rw [two_nsmul, hqe, ← eq_neg_iff_add_eq_zero, WeierstrassCurve.Affine.Point.neg_some] at h2Q
    have hy := (WeierstrassCurve.Affine.Point.some.inj h2Q).2
    rw [WeierstrassCurve.Affine.negY] at hy
    rw [veluGy]
    linear_combination -hy
  have hΔ := veluQuotient2_Delta_ne_zero E.isUnit_Δ.ne_zero hns.1 hgy
  haveI hV : (E.veluQuotient2 x₀ y₀).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  obtain ⟨φ, hφ⟩ := E.exists_addMonoidHom_coe_eq_veluPointMap2 h2 hns.1 hgy hΔ
  have hQH : (WeierstrassCurve.Affine.Point.some x₀ y₀ hns : E.toAffine.Point) ∈ H :=
    hqe ▸ hQH'
  have hbridge := E.stepCurve_stepSubgroup_two_eq h2 H hns hQH hgy hΔ φ hφ
  have hker : φ.ker = AddSubgroup.zmultiples Q := by
    ext P
    rw [mem_ker_veluPointMap2 E h2 hns.1 hgy hΔ φ hφ]
    constructor
    · rintro (rfl | hP)
      · exact AddSubgroup.zero_mem _
      · rw [hP, ← hqe]; exact AddSubgroup.mem_zmultiples _
    · intro hP
      obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hP
      have hk : (m % 2) • Q = m • Q := by
        have := mod_addOrderOf_zsmul Q m
        rwa [hQ2, Nat.cast_ofNat] at this
      rcases Int.emod_two_eq_zero_or_one m with h | h
      · left; rw [← hk, h, zero_smul]
      · right; rw [← hk, h, one_smul, hqe]
  have hseam : IsSeam (ModelLevels.ModelGeneric4.twoFFHom h2 hns.1 hgy)
      (ModelLevels.ModelGeneric4.twoFFHom_isIntegral h2 hns.1 hgy) φ := by
    intro P
    rw [show φ P = veluPointMap2 h2 hns.1 hgy hΔ P from congrFun hφ P]
    exact twoFFHom_seam E h2 hns.1 hgy hΔ P
  have hdeg : finrankAlong k (ModelLevels.ModelGeneric4.twoFFHom h2 hns.1 hgy) = 2 := by
    have hle := finrankAlong_twoFFHom_le E h2 hns.1 hgy
    have hne := finrankAlong_ne_one_of_seam _ _ φ hseam
      (P := WeierstrassCurve.Affine.Point.some x₀ y₀ hns) (by simp)
      (by rw [← AddMonoidHom.mem_ker, hker, hqe]; exact AddSubgroup.mem_zmultiples _)
    have hpos : 0 < finrankAlong k (ModelLevels.ModelGeneric4.twoFFHom h2 hns.1 hgy) := by
      letI := algebraAlong (ModelLevels.ModelGeneric4.twoFFHom h2 hns.1 hgy)
      haveI : Module.Finite (E.veluQuotient2 x₀ y₀).toAffine.FunctionField E.toAffine.FunctionField :=
        ModelLevels.ModelGeneric4.twoFFHom_finiteAlong h2 hns.1 hgy
      exact Module.finrank_pos
    omega
  have hform : StepFormula E Q 2 φ := by
    refine ⟨fun h => absurd rfl h, fun _ => ⟨x₀, y₀, hns, h2, hgy, hΔ, hqe, fun P => ?_⟩⟩
    rw [show φ P = veluPointMap2 h2 hns.1 hgy hΔ P from congrFun hφ P]
    exact ⟨Iff.rfl, rfl⟩
  have result (s : Σ V : WeierstrassCurve k, AddSubgroup V.toAffine.Point)
      (hs : s = ⟨E.veluQuotient2 x₀ y₀, H.map φ⟩) :
      ∃ _ : s.1.IsElliptic,
        ∃ (ι : s.1.toAffine.FunctionField →ₐ[k] E.toAffine.FunctionField)
          (hι : ι.toRingHom.IsIntegral), FiniteAlong k ι ∧ finrankAlong k ι = 2 ∧
          ∃ f : E.toAffine.Point →+ s.1.toAffine.Point,
            f.ker = AddSubgroup.zmultiples Q ∧ StepFormula E Q 2 f ∧ H.map f = s.2 ∧
              IsSeam ι hι f := by
    subst hs
    exact ⟨hV, ModelLevels.ModelGeneric4.twoFFHom h2 hns.1 hgy,
      ModelLevels.ModelGeneric4.twoFFHom_isIntegral h2 hns.1 hgy,
      ModelLevels.ModelGeneric4.twoFFHom_finiteAlong h2 hns.1 hgy, hdeg, φ, hker, hform, rfl,
      hseam⟩
  exact result _ hbridge

open P2MW.S_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j.P2MKcKI
  in
-- Adapted from the proof of `exists_quotientSeam_of_steps`,
-- ZInQKernel/Contrib/OneProof/RC/ModelGeneric6/CharFreeSeam.lean:210-265, base SHA
-- aba99b7b2e3eea8804ebeffd1834ba5f31fa9c7e (generator given; steps recorded in `FormulaSeam`;
-- the composite target reached by `seam_transport` along `stepEq` instead of a goal rewrite).
/-- **Formula-carrying separable seams for the vendored Vélu composite** (R0). For a generator
`c` of order `n` of `H` (`H = ⟨c⟩`), with `(ℓ : k) ≠ 0` for each prime `ℓ ∣ n`, there is a seam
`g : E → E.cyclicQuotientCurve H n` with `g.ker = H`, `FiniteAlong k ι`, `finrankAlong k ι = n`,
and `FormulaSeam E H c n g`. Refines `ModelGeneric6.exists_quotientSeam`
(`exists_quotientSeam_of_formulaSeam`). -/
theorem exists_formulaSeam (n : ℕ) (hn : n ≠ 0)
    (hchar : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → (ℓ : k) ≠ 0)
    (E : WeierstrassCurve k) [E.IsElliptic] (H : AddSubgroup E.toAffine.Point)
    (c : E.toAffine.Point) (hcH : H = AddSubgroup.zmultiples c) (hc : addOrderOf c = n) :
    ∃ _ : (E.cyclicQuotientCurve H n).IsElliptic,
      ∃ (ι : (E.cyclicQuotientCurve H n).toAffine.FunctionField →ₐ[k] E.toAffine.FunctionField)
        (hι : ι.toRingHom.IsIntegral), FiniteAlong k ι ∧ finrankAlong k ι = n ∧
        ∃ g : E.toAffine.Point →+ (E.cyclicQuotientCurve H n).toAffine.Point,
          g.ker = H ∧ IsSeam ι hι g ∧ FormulaSeam E H c n g := by
  induction n using Nat.strong_induction_on generalizing E with
  | h n ih =>
    by_cases h₁ : n = 1
    · subst h₁
      have hc0 : c = 0 := AddMonoid.addOrderOf_eq_one_iff.mp hc
      have hH1 : H = ⊥ := by rw [hcH, hc0, AddSubgroup.zmultiples_zero_eq_bot]
      have hid : ∃ _ : E.IsElliptic,
          ∃ (ι : E.toAffine.FunctionField →ₐ[k] E.toAffine.FunctionField)
            (hι : ι.toRingHom.IsIntegral), FiniteAlong k ι ∧ finrankAlong k ι = 1 ∧
              IsSeam ι hι (AddMonoidHom.id _) := by
        refine ⟨inferInstance, AlgHom.id k _,
          P2MW.S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.WeierstrassCurve.Affine.IsogenyEndDatum.isIntegral_algHomId _,
          P2MW.S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.WeierstrassCurve.Affine.IsogenyEndDatum.finiteAlong_algHomId _,
          ?_, fun P => ?_⟩
        · change @Module.finrank E.toAffine.FunctionField E.toAffine.FunctionField _ _
            (algebraAlong (AlgHom.id k E.toAffine.FunctionField)).toModule = 1
          convert Module.finrank_self E.toAffine.FunctionField
        · exact P2MW.S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.WeierstrassCurve.Affine.IsogenyEndDatum.restrictAlong_algHomId _ _
      obtain ⟨hV, ι, hι, hfin, hdeg, hseam⟩ :=
        seam_transport (E.cyclicQuotientCurve_one H).symm 1 (AddMonoidHom.id _) hid
      refine ⟨hV, ι, hι, hfin, hdeg, pointCast (E.cyclicQuotientCurve_one H).symm, ?_, ?_,
        FormulaSeam.one E H c hcH hc⟩
      · have := ker_pointCast_comp (E.cyclicQuotientCurve_one H).symm (AddMonoidHom.id _)
        rw [AddMonoidHom.comp_id] at this
        rw [this, AddMonoidHom.ker_id, hH1]
      · rwa [AddMonoidHom.comp_id] at hseam
    have h₂ : 2 ≤ n := by omega
    have hp : n.minFac.Prime := Nat.minFac_prime h₁
    have hd : n.minFac ∣ n := Nat.minFac_dvd n
    have hmul : n.minFac * (n / n.minFac) = n := Nat.mul_div_cancel' hd
    have hm : n / n.minFac ≠ 0 := by
      intro h
      rw [h, mul_zero] at hmul
      exact hn hmul.symm
    have hlt : n / n.minFac < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hp.one_lt
    subst hcH
    have hHcard : AddSubgroup.zmultiples c ∈ CycSub E.toAffine.Point (n.minFac * (n / n.minFac)) :=
      ⟨inferInstance, by rw [Nat.card_zmultiples, hc, hmul]⟩
    haveI : Finite (AddSubgroup.zmultiples c) := finite_of_mem_cycSub (by rwa [hmul]) hHcard
    have hc'H : (n / n.minFac) • c ∈ AddSubgroup.zmultiples c :=
      AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples c) _
    have hc' : addOrderOf ((n / n.minFac) • c) = n.minFac := by
      rw [addOrderOf_nsmul' (x := c) hm, hc, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hd),
        Nat.div_div_self hd hn]
    have hstep : ∃ _ : (E.stepCurve (AddSubgroup.zmultiples c) n.minFac).IsElliptic,
        ∃ (ι : (E.stepCurve (AddSubgroup.zmultiples c) n.minFac).toAffine.FunctionField →ₐ[k]
            E.toAffine.FunctionField)
          (hι : ι.toRingHom.IsIntegral), FiniteAlong k ι ∧ finrankAlong k ι = n.minFac ∧
          ∃ f : E.toAffine.Point →+ (E.stepCurve (AddSubgroup.zmultiples c) n.minFac).toAffine.Point,
            f.ker = AddSubgroup.zmultiples ((n / n.minFac) • c) ∧
              StepFormula E ((n / n.minFac) • c) n.minFac f ∧
              (AddSubgroup.zmultiples c).map f =
                E.stepSubgroup (AddSubgroup.zmultiples c) n.minFac ∧ IsSeam ι hι f := by
      by_cases h2 : n.minFac = 2
      · have h2k : (2 : k) ≠ 0 := by exact_mod_cast hchar 2 Nat.prime_two (h2 ▸ hd)
        revert hc'H hc'
        rw [h2]
        intro hc'H hc'
        exact exists_twoStep_formula h2k E _ _ hc'H hc'
      · exact exists_oddStep_formula E _ hp h2 (hchar _ hp hd) _ hc'H hc'
    obtain ⟨he, ι₁, hι₁, hfin₁, hdeg₁, f, hf, hform, hsub, hseam₁⟩ := hstep
    haveI := he
    have hmap : (AddSubgroup.zmultiples c).map f ∈ CycSub _ (n / n.minFac) :=
      map_mem_cycSub f hp.ne_zero hHcard (by rw [hf]; exact AddSubgroup.zmultiples_le.mpr hc'H)
        (by rw [hf, Nat.card_zmultiples, hc'])
    have hfcH : (AddSubgroup.zmultiples c).map f = AddSubgroup.zmultiples (f c) :=
      AddMonoidHom.map_zmultiples f c
    have hfc : addOrderOf (f c) = n / n.minFac := by
      rw [← Nat.card_zmultiples, ← hfcH, hmap.2]
    have hchar' : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n / n.minFac → (ℓ : k) ≠ 0 :=
      fun ℓ hℓ hdvd => hchar ℓ hℓ (hdvd.trans (Nat.div_dvd_of_dvd hd))
    obtain ⟨hW, ι₂, hι₂, hfin₂, hdeg₂, g', hg', hseam₂, hpred⟩ :=
      ih (n / n.minFac) hlt hm hchar' (E.stepCurve (AddSubgroup.zmultiples c) n.minFac)
        ((AddSubgroup.zmultiples c).map f) (f c) hfcH hfc
    have hι : (ι₁.comp ι₂).toRingHom.IsIntegral :=
      RingHom.IsIntegral.trans ι₂.toRingHom ι₁.toRingHom hι₂ hι₁
    have hcomp : ∃ _ : ((E.stepCurve (AddSubgroup.zmultiples c) n.minFac).cyclicQuotientCurve
          ((AddSubgroup.zmultiples c).map f) (n / n.minFac)).IsElliptic,
        ∃ (ι : ((E.stepCurve (AddSubgroup.zmultiples c) n.minFac).cyclicQuotientCurve
            ((AddSubgroup.zmultiples c).map f) (n / n.minFac)).toAffine.FunctionField →ₐ[k]
              E.toAffine.FunctionField)
          (hι : ι.toRingHom.IsIntegral), FiniteAlong k ι ∧ finrankAlong k ι = n ∧
            IsSeam ι hι (g'.comp f) := by
      refine ⟨hW, ι₁.comp ι₂, hι, ?_, ?_, isSeam_comp ι₁ hι₁ f ι₂ hι₂ g' hseam₁ hseam₂ hι⟩
      · have h1 : RingHom.Finite ι₁.toRingHom := hfin₁
        have h2 : RingHom.Finite ι₂.toRingHom := hfin₂
        exact RingHom.Finite.comp (g := ι₁.toRingHom) h1 h2
      · rw [finrankAlong_comp', hdeg₁, hdeg₂]
        first | exact hmul | exact Nat.div_mul_cancel hd
    obtain ⟨hV, ι, hιV, hfin, hdeg, hseam⟩ :=
      seam_transport (stepEq E (AddSubgroup.zmultiples c) h₂ f hsub) n (g'.comp f) hcomp
    refine ⟨hV, ι, hιV, hfin, hdeg, _, ?_, hseam,
      FormulaSeam.step E _ c n rfl hc h₂ he f hf hform hsub g' hpred⟩
    rw [ker_pointCast_comp, ← AddMonoidHom.comap_ker, hg']
    exact comap_map_eq_of_ker_le f (by rw [hf]; exact AddSubgroup.zmultiples_le.mpr hc'H)

/-- `exists_formulaSeam` implies `ModelGeneric6.exists_quotientSeam` (same statement): the
variant is at least as strong. -/
theorem exists_quotientSeam_of_formulaSeam (n : ℕ) (hn : n ≠ 0)
    (hchar : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → (ℓ : k) ≠ 0)
    (E : WeierstrassCurve k) [E.IsElliptic] (H : AddSubgroup E.toAffine.Point)
    (hH : IsAddCyclic H ∧ Nat.card H = n) :
    ∃ _ : (E.cyclicQuotientCurve H n).IsElliptic,
      ∃ (ι : (E.cyclicQuotientCurve H n).toAffine.FunctionField →ₐ[k] E.toAffine.FunctionField)
        (hι : ι.toRingHom.IsIntegral), FiniteAlong k ι ∧ finrankAlong k ι = n ∧
        ∃ g : E.toAffine.Point →+ (E.cyclicQuotientCurve H n).toAffine.Point,
          g.ker = H ∧ IsSeam ι hι g := by
  haveI := hH.1
  obtain ⟨⟨c, hcH⟩, hgen⟩ := IsAddCyclic.exists_generator (α := H)
  have hHc : H = AddSubgroup.zmultiples c := by
    ext y
    constructor
    · intro hy
      obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgen ⟨y, hy⟩)
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨m, congrArg Subtype.val hm⟩
    · intro hy
      obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
      exact H.zsmul_mem hcH m
  have hc : addOrderOf c = n := by rw [← hH.2, hHc, Nat.card_zmultiples]
  obtain ⟨hV, ι, hι, hfin, hdeg, g, hg, hseam, -⟩ := exists_formulaSeam n hn hchar E H c hHc hc
  exact ⟨hV, ι, hι, hfin, hdeg, g, hg, hseam⟩

end ZInQ.Manuscript.RC.ModelGeneric7

#print axioms ZInQ.Manuscript.RC.ModelGeneric7.pointCast
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.seam_transport
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.stepEq
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.FormulaSeam
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.exists_oddStep_formula
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.exists_twoStep_formula
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.exists_formulaSeam
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.exists_quotientSeam_of_formulaSeam
