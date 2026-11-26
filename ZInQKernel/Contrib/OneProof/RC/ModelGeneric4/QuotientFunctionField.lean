import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_stepCurve_stepSubgroup_eq_of_prime_ne_two
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_restrictAlong_restrictAlong
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j

/-! # Function-field maps of the odd prime Vélu steps

Each odd prime step of the vendored iterated Vélu quotient is induced by a map of function
fields whose restriction of places is the actual Vélu point map. The places are read through
a fixed centred gate on each curve. -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric4

open AlgebraicCurve WeierstrassCurve.Affine

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.style.haveILetI false

variable {k : Type} [Field k] [DecidableEq k] [IsAlgClosed k] [CharZero k]

/-- The centred gate with Abel's theorem, fixed once for every elliptic equation. -/
@[instance_reducible] noncomputable def gate (W : WeierstrassCurve k) [W.IsElliptic] : GenusOnePlaceGate W.toAffine :=
  haveI := CoordinateRing.isDedekindDomain W
  haveI := hasPrincipalDivisors_functionField W.toAffine
  (exists_genusOnePlaceGate_isCentred_and_abelTheorem (W := W.toAffine)).choose

theorem gate_isCentred (W : WeierstrassCurve k) [W.IsElliptic] :
    @GenusOnePlaceGate.IsCentred k _ W.toAffine (gate W) :=
  haveI := CoordinateRing.isDedekindDomain W
  haveI := hasPrincipalDivisors_functionField W.toAffine
  (exists_genusOnePlaceGate_isCentred_and_abelTheorem (W := W.toAffine)).choose_spec.1

theorem gate_abel (W : WeierstrassCurve k) [W.IsElliptic] :
    @AbelTheorem k _ _ W.toAffine (gate W) :=
  haveI := CoordinateRing.isDedekindDomain W
  haveI := hasPrincipalDivisors_functionField W.toAffine
  (exists_genusOnePlaceGate_isCentred_and_abelTheorem (W := W.toAffine)).choose_spec.2

/-- The place of a point, read through the fixed gate. -/
noncomputable def pointPlace (W : WeierstrassCurve k) [W.IsElliptic] (P : W.toAffine.Point) :
    Place k W.toAffine.FunctionField :=
  letI := gate W
  placeOfPoint P

/-- A map of function fields inducing a point homomorphism on places. -/
def IsSeam {V W : WeierstrassCurve k} [V.IsElliptic] [W.IsElliptic]
    (ι : V.toAffine.FunctionField →ₐ[k] W.toAffine.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (f : W.toAffine.Point →+ V.toAffine.Point) : Prop :=
  ∀ P, (pointPlace W P).restrictAlong ι hι = pointPlace V (f P)

/-- The odd prime step of the vendored quotient is induced by a function-field map whose
restriction of places is the actual Vélu map, with kernel of order ℓ inside the subgroup and
image of the subgroup equal to the vendored transported subgroup. -/
theorem exists_oddStep (E : WeierstrassCurve k) [E.IsElliptic]
    (H : AddSubgroup E.toAffine.Point) [IsAddCyclic H] [Finite H]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hdvd : ℓ ∣ Nat.card H) :
    ∃ _ : (E.stepCurve H ℓ).IsElliptic,
      ∃ (ι : (E.stepCurve H ℓ).toAffine.FunctionField →ₐ[k] E.toAffine.FunctionField)
        (hι : ι.toRingHom.IsIntegral), FiniteAlong k ι ∧
        ∃ f : E.toAffine.Point →+ (E.stepCurve H ℓ).toAffine.Point,
          f.ker ≤ H ∧ Nat.card f.ker = ℓ ∧ H.map f = E.stepSubgroup H ℓ ∧ IsSeam ι hι f := by
  have hℓk : (ℓ : k) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  have : Fact ℓ.Prime := ⟨hℓ⟩
  let := Fintype.ofFinite H
  obtain ⟨q, hq⟩ := exists_prime_addOrderOf_dvd_card ℓ (by rwa [Fintype.card_eq_nat_card])
  let Q : E.toAffine.Point := q
  have hQ : addOrderOf Q = ℓ :=
    (addOrderOf_injective H.subtype Subtype.coe_injective q).trans hq
  have hodd : ℓ = 2 * (ℓ / 2) + 1 := by
    have := hℓ.eq_one_or_self_of_dvd 2
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
  obtain ⟨ι, hι, hfin, -, -, hzero, hsome⟩ :=
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
  have hQH : Q ∈ H := q.property
  have hbridge := E.stepCurve_stepSubgroup_eq_of_prime_ne_two hℓ hℓ2 H Q hQH hQ φ hφker hφ
  have result (s : Σ V : WeierstrassCurve k, AddSubgroup V.toAffine.Point)
      (hs : s = ⟨E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2)), H.map φ⟩) :
      ∃ _ : s.1.IsElliptic,
        ∃ (ι : s.1.toAffine.FunctionField →ₐ[k] E.toAffine.FunctionField)
          (hι : ι.toRingHom.IsIntegral), FiniteAlong k ι ∧
          ∃ f : E.toAffine.Point →+ s.1.toAffine.Point,
            f.ker ≤ H ∧ Nat.card f.ker = ℓ ∧ H.map f = s.2 ∧ IsSeam ι hι f := by
    subst hs
    refine ⟨hV, ι, hι, hfin, φ, ?_, ?_, rfl, hseam⟩
    · rw [hφker]; exact AddSubgroup.zmultiples_le.mpr hQH
    · rw [hφker, Nat.card_zmultiples, hQ]
  exact result _ hbridge

#print axioms exists_oddStep


open P2MW.S_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j.P2MKcKI
  in
/-- The prime steps available for the composite: for the prime ℓ, every cyclic subgroup of order
divisible by ℓ has a step map induced by a map of function fields. -/
def StepSeam (ℓ : ℕ) : Prop :=
  ∀ (E : WeierstrassCurve k) [E.IsElliptic] (H : AddSubgroup E.toAffine.Point) [IsAddCyclic H]
    [Finite H], ℓ ∣ Nat.card H →
    ∃ _ : (E.stepCurve H ℓ).IsElliptic,
      ∃ (ι : (E.stepCurve H ℓ).toAffine.FunctionField →ₐ[k] E.toAffine.FunctionField)
        (hι : ι.toRingHom.IsIntegral), FiniteAlong k ι ∧
        ∃ f : E.toAffine.Point →+ (E.stepCurve H ℓ).toAffine.Point,
          f.ker ≤ H ∧ Nat.card f.ker = ℓ ∧ H.map f = E.stepSubgroup H ℓ ∧ IsSeam ι hι f

theorem stepSeam_of_odd {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) : StepSeam (k := k) ℓ :=
  fun E _ H _ _ hdvd => exists_oddStep E H hℓ hℓ2 hdvd

private theorem isSeam_comp {U V W : WeierstrassCurve k} [U.IsElliptic] [V.IsElliptic]
    [W.IsElliptic] (ι₁ : V.toAffine.FunctionField →ₐ[k] U.toAffine.FunctionField)
    (hι₁ : ι₁.toRingHom.IsIntegral) (f₁ : U.toAffine.Point →+ V.toAffine.Point)
    (ι₂ : W.toAffine.FunctionField →ₐ[k] V.toAffine.FunctionField)
    (hι₂ : ι₂.toRingHom.IsIntegral) (f₂ : V.toAffine.Point →+ W.toAffine.Point)
    (h₁ : IsSeam ι₁ hι₁ f₁) (h₂ : IsSeam ι₂ hι₂ f₂) (hι : (ι₁.comp ι₂).toRingHom.IsIntegral) :
    IsSeam (ι₁.comp ι₂) hι (f₂.comp f₁) := by
  intro P
  rw [← Place.restrictAlong_restrictAlong ι₂ ι₁ hι₂ hι₁ hι, h₁ P, h₂ (f₁ P)]
  rfl

open P2MW.S_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j.P2MKcKI
  in
/-- The vendored iterated Vélu quotient is induced by a map of function fields whose restriction
of places is a point homomorphism with kernel exactly the given cyclic subgroup, provided each
prime step is so induced. -/
theorem exists_quotientSeam_of_steps (n : ℕ) (hn : n ≠ 0)
    (hsteps : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → StepSeam (k := k) ℓ)
    (E : WeierstrassCurve k) [E.IsElliptic] (H : AddSubgroup E.toAffine.Point)
    (hH : IsAddCyclic H ∧ Nat.card H = n) :
    ∃ _ : (E.cyclicQuotientCurve H n).IsElliptic,
      ∃ (ι : (E.cyclicQuotientCurve H n).toAffine.FunctionField →ₐ[k] E.toAffine.FunctionField)
        (hι : ι.toRingHom.IsIntegral), FiniteAlong k ι ∧
        ∃ g : E.toAffine.Point →+ (E.cyclicQuotientCurve H n).toAffine.Point,
          g.ker = H ∧ IsSeam ι hι g := by
  induction n using Nat.strong_induction_on generalizing E with
  | h n ih =>
    by_cases h₁ : n = 1
    · subst n
      have hH1 : H = ⊥ := AddSubgroup.card_eq_one.mp hH.2
      generalize hV : E.cyclicQuotientCurve H 1 = V
      rw [cyclicQuotientCurve_one] at hV
      subst hV
      refine ⟨inferInstance, AlgHom.id k _,
        P2MW.S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.WeierstrassCurve.Affine.IsogenyEndDatum.isIntegral_algHomId _,
        P2MW.S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.WeierstrassCurve.Affine.IsogenyEndDatum.finiteAlong_algHomId _,
        AddMonoidHom.id _, by rw [AddMonoidHom.ker_id, hH1], fun P => ?_⟩
      exact P2MW.S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.WeierstrassCurve.Affine.IsogenyEndDatum.restrictAlong_algHomId _ _
    have h₂ : 2 ≤ n := by omega
    let p := n.minFac
    have hp : p.Prime := Nat.minFac_prime h₁
    have hd : p ∣ n := Nat.minFac_dvd n
    have hmul : p * (n / p) = n := Nat.mul_div_cancel' hd
    haveI : IsAddCyclic H := hH.1
    haveI : Finite H := finite_of_mem_cycSub hn hH
    obtain ⟨he, ι₁, hι₁, hfin₁, f, hf, hcard, hsub, hseam₁⟩ :=
      hsteps p hp hd E H (by rw [hH.2]; exact hd)
    have hmap : H.map f ∈ CycSub _ (n / p) :=
      map_mem_cycSub f hp.ne_zero (hmul.symm ▸ hH) hf hcard
    have hm : n / p ≠ 0 := by
      intro h
      rw [h, mul_zero] at hmul
      exact hn hmul.symm
    have hlt : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hp.one_lt
    have hsteps' : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n / p → StepSeam (k := k) ℓ :=
      fun ℓ hℓ hdvd => hsteps ℓ hℓ (hdvd.trans (Nat.div_dvd_of_dvd hd))
    obtain ⟨hW, ι₂, hι₂, hfin₂, g, hg, hseam₂⟩ :=
      ih (n / p) hlt hm hsteps' (E.stepCurve H p) (H.map f) hmap
    rw [cyclicQuotientCurve_eq_of_two_le E H h₂, ← hsub]
    have hι : (ι₁.comp ι₂).toRingHom.IsIntegral :=
      RingHom.IsIntegral.trans ι₂.toRingHom ι₁.toRingHom hι₂ hι₁
    refine ⟨hW, ι₁.comp ι₂, hι, ?_, g.comp f, ?_, isSeam_comp ι₁ hι₁ f ι₂ hι₂ g hseam₁ hseam₂ hι⟩
    · have h1 : RingHom.Finite ι₁.toRingHom := hfin₁
      have h2 : RingHom.Finite ι₂.toRingHom := hfin₂
      exact RingHom.Finite.comp (g := ι₁.toRingHom) h1 h2
    · rw [← AddMonoidHom.comap_ker, hg]
      exact comap_map_eq_of_ker_le f hf

/-- For odd order the composite is unconditional. -/
theorem exists_quotientSeam_odd (n : ℕ) (hn : n ≠ 0) (hodd : ¬ 2 ∣ n)
    (E : WeierstrassCurve k) [E.IsElliptic] (H : AddSubgroup E.toAffine.Point)
    (hH : IsAddCyclic H ∧ Nat.card H = n) :
    ∃ _ : (E.cyclicQuotientCurve H n).IsElliptic,
      ∃ (ι : (E.cyclicQuotientCurve H n).toAffine.FunctionField →ₐ[k] E.toAffine.FunctionField)
        (hι : ι.toRingHom.IsIntegral), FiniteAlong k ι ∧
        ∃ g : E.toAffine.Point →+ (E.cyclicQuotientCurve H n).toAffine.Point,
          g.ker = H ∧ IsSeam ι hι g :=
  exists_quotientSeam_of_steps n hn (fun ℓ hℓ hdvd => stepSeam_of_odd hℓ (by
    rintro rfl
    exact hodd hdvd)) E H hH

#print axioms exists_quotientSeam_of_steps
#print axioms exists_quotientSeam_odd

end WeierstrassCurve.ModelLevels.ModelGeneric4
