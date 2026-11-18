import ZInQKernel.Contrib.OneProof.HeckeSqrtAction

/-! ON THE SPOT (provenance (c)): the sign character produces an eigenvector
whose square is a squarefree polynomial. A prime dividing that polynomial
ramifies in the fixed field of the sign kernel. -/

set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial

namespace SGRDirect.HeckeSqrt

variable {E : Type} [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
  [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
  [IsGalois (RatFunc ℚ) E]

local notation "B₀" => integralClosure ℚ[X] E
local notation "G₀" => Gal(E / RatFunc ℚ)

theorem mem_inertia_iff (Q : Ideal B₀) (τ : G₀) : τ ∈ Q.inertia G₀ ↔ τ ∈ InertiaQ E Q := by
  constructor
  · intro h b
    exact ⟨τ • b, rfl, h b⟩
  · intro h b
    obtain ⟨c, hc, hcb⟩ := h b
    have he : c = τ • b := Subtype.ext hc
    rwa [← he]

private theorem commutes_poly (τ : G₀) (f : ℚ[X]) :
    τ (algebraMap ℚ[X] E f) = algebraMap ℚ[X] E f := by
  rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E, AlgEquiv.commutes]

/-- Extract a nonzero eigenvector with square in `ℚ[X]`, removing all square factors. -/
theorem squarefree_eigenvector (χ : G₀ →* ℚˣ)
    (hχ : ∀ g, (χ g : ℚ) = 1 ∨ (χ g : ℚ) = -1)
    (t : G₀) (ht : (χ t : ℚ) = -1) :
    ∃ (s : E) (f : ℚ[X]), s ≠ 0 ∧ Squarefree f ∧ s ^ 2 = algebraMap ℚ[X] E f ∧
      ∀ g : G₀, g s = algebraMap ℚ[X] E (C (χ g : ℚ)) * s := by
  let K := IntermediateField.fixedField χ.ker
  have ht' : t ∉ χ.ker := by
    intro h
    have e : (χ t : ℚ) = 1 := congrArg Units.val (MonoidHom.mem_ker.mp h)
    rw [ht] at e
    norm_num at e
  have hm : ∃ z : E, z ∈ K ∧ t z ≠ z := by
    by_contra! h
    apply ht'
    rw [← IntermediateField.fixingSubgroup_fixedField χ.ker]
    exact (mem_fixingSubgroup_iff Gal(E/RatFunc ℚ)).2 h
  obtain ⟨z, hz, htz⟩ := hm
  have hfix : ∀ g : G₀, (χ g : ℚ) = 1 → g z = z := fun g hg =>
    (IntermediateField.mem_fixedField_iff _ _).1 hz g (MonoidHom.mem_ker.mpr (Units.ext hg))
  have hmove : ∀ g : G₀, (χ g : ℚ) = -1 → g z = t z := by
    intro g hg
    have he : (χ (t⁻¹ * g) : ℚ) = 1 := by
      rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, ht, hg]
      norm_num
    have := congrArg t (hfix (t⁻¹ * g) he)
    rwa [← AlgEquiv.mul_apply, mul_inv_cancel_left] at this
  let u := z - t z
  have hu : u ≠ 0 := sub_ne_zero.mpr htz.symm
  have huact (g : G₀) : g u = algebraMap ℚ[X] E (C (χ g : ℚ)) * u := by
    have hm : (χ (g * t) : ℚ) = (χ g : ℚ) * (-1) := by rw [map_mul, Units.val_mul, ht]
    change g (z - t z) = _
    rw [map_sub, ← AlgEquiv.mul_apply]
    rcases hχ g with hg | hg
    · rw [hg, one_mul] at hm
      rw [hfix g hg, hmove (g * t) (by simpa only [hg, one_mul] using hm), hg, C_1, map_one, one_mul]
    · have hm' : (χ (g * t) : ℚ) = 1 := hm.trans (by rw [hg]; norm_num)
      rw [hmove g hg, hfix (g * t) hm', hg, C_neg, C_1, map_neg, map_one, neg_one_mul, neg_sub]
  have hum := (IsGalois.mem_bot_iff_fixed (F := RatFunc ℚ) (u ^ 2)).2 (fun g => by
    rw [map_pow, huact, mul_pow]
    rcases hχ g with hg | hg <;> simp [hg])
  obtain ⟨d, hd⟩ := hum
  obtain ⟨a, b, hb, hd'⟩ := IsFractionRing.div_surjective ℚ[X] d
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  change algebraMap (RatFunc ℚ) E d = u ^ 2 at hd
  rw [← hd', map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at hd
  let v := u * algebraMap ℚ[X] E b
  have hv : v ≠ 0 := mul_ne_zero hu (fun e => hb0 (poly_injective (e.trans (map_zero _).symm)))
  have hv' : v ^ 2 = algebraMap ℚ[X] E (a * b) := by
    change (u * algebraMap ℚ[X] E b) ^ 2 = _
    rw [mul_pow, ← hd, map_mul]
    field_simp [show algebraMap ℚ[X] E b ≠ 0 from fun e =>
      hb0 (poly_injective (e.trans (map_zero _).symm))]
  obtain ⟨c, f, hcf, hf⟩ := exists_sq_mul_squarefree (a * b)
  rw [← hcf, map_mul, map_pow] at hv'
  have hc : algebraMap ℚ[X] E c ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide), zero_mul] at hv'
    exact (pow_ne_zero 2 hv) hv'
  refine ⟨v / algebraMap ℚ[X] E c, f, div_ne_zero hv hc, hf, ?_, ?_⟩
  · rw [div_pow, hv']
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ hc)
  · intro g
    rw [map_div₀, commutes_poly]
    change g (u * algebraMap ℚ[X] E b) / _ = _
    rw [map_mul, commutes_poly, huact, mul_assoc, ← mul_div_assoc]

/-- A squarefree numerator can only be divisible by primes where the
quadratic character is nontrivial on inertia. -/
theorem prime_support (χ : G₀ →* ℚˣ) (s : E) (f : ℚ[X])
    (hf : Squarefree f) (hs : s ^ 2 = algebraMap ℚ[X] E f)
    (hact : ∀ g : G₀, g s = algebraMap ℚ[X] E (C (χ g : ℚ)) * s)
    (p : ℚ[X]) (hp : Irreducible p) (hpf : p ∣ f)
    (Q : Ideal B₀) [Q.IsPrime] (hQ : Q.under ℚ[X] = Ideal.span {p}) :
    ¬ Q.inertia G₀ ≤ χ.ker := by
  intro hI
  let H := χ.ker
  let K := IntermediateField.fixedField H
  let A := integralClosure ℚ[X] K
  letI : Algebra A B₀ := (SGRDirect.incl K).toAlgebra
  haveI : IsScalarTower ℚ[X] A B₀ := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  haveI : IsDedekindDomain B₀ := integralClosure.isDedekindDomain ℚ[X] (RatFunc ℚ) E
  haveI : IsDedekindDomain A := integralClosure.isDedekindDomain ℚ[X] (RatFunc ℚ) K
  haveI : Module.IsTorsionFree ℚ[X] A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr fun a b h =>
      poly_injective (congrArg (fun x : A => ((x : K) : E)) h)
  haveI : Module.IsTorsionFree ℚ[X] B₀ :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr fun a b h =>
      poly_injective (congrArg (fun x : B₀ => (x : E)) h)
  set q := Q.under A
  haveI : q.IsPrime := Ideal.IsPrime.under A Q
  have hqu : q.under ℚ[X] = Ideal.span {p} := by
    change (Q.under A).under ℚ[X] = _
    rw [Ideal.under_under, hQ]
  have hP0 : (Ideal.span {p} : Ideal ℚ[X]) ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hp.ne_zero
  haveI : Q.LiesOver (Ideal.span {p} : Ideal ℚ[X]) := ⟨hQ.symm⟩
  haveI : q.LiesOver (Ideal.span {p} : Ideal ℚ[X]) := ⟨hqu.symm⟩
  have hepos : Q.ramificationIdx ℚ[X] ≠ 0 :=
    (Ideal.ramificationIdx_pos_of_isDedekindDomain' Q hP0).ne'
  -- Compare the inertia groups in the full extension and over the fixed field.
  have he : q.ramificationIdx ℚ[X] = 1 := by
    haveI : IsFractionRing B₀ E :=
      IsIntegralClosure.isFractionRing_of_finite_extension ℚ[X] (RatFunc ℚ) E _
    haveI : IsFractionRing A K :=
      IsIntegralClosure.isFractionRing_of_finite_extension ℚ[X] (RatFunc ℚ) K _
    haveI : IsScalarTower A B₀ E := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : Module.IsTorsionFree ℚ[X] E :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr poly_injective
    haveI : Module.IsTorsionFree A B₀ :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr fun a b h =>
        Subtype.ext (Subtype.ext (congrArg (fun x : B₀ => (x : E)) h))
    haveI : Module.Finite ℚ[X] B₀ := IsIntegralClosure.finite ℚ[X] (RatFunc ℚ) E B₀
    haveI : Module.Finite A B₀ := Module.Finite.of_restrictScalars_finite ℚ[X] A B₀
    haveI : Algebra.IsIntegral A B₀ := Algebra.IsIntegral.tower_top (R := ℚ[X])
    haveI : IsGaloisGroup G₀ ℚ[X] B₀ :=
      IsGaloisGroup.of_isFractionRing G₀ ℚ[X] B₀ (RatFunc ℚ) E
    haveI : IsGaloisGroup H A B₀ := IsGaloisGroup.of_isFractionRing H A B₀ K E
    let P := Q.under ℚ[X]
    haveI : P.IsPrime := Ideal.IsPrime.under ℚ[X] Q
    haveI : Q.LiesOver P := ⟨rfl⟩
    haveI : Q.LiesOver q := ⟨rfl⟩
    haveI : CharZero P.ResidueField := by
      let f := (algebraMap ℚ[X] P.ResidueField).comp Polynomial.C
      exact charZero_of_injective_ringHom f.injective
    haveI : CharZero q.ResidueField := by
      let f := ((algebraMap A q.ResidueField).comp (algebraMap ℚ[X] A)).comp Polynomial.C
      exact charZero_of_injective_ringHom f.injective
    have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := G₀) P Q
    have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := H) q Q
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx P Q G₀] at h1
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx q Q H] at h2
    let e : Q.inertia H ≃ Q.inertia G₀ :=
      { toFun := fun g => ⟨g.1.1, g.2⟩
        invFun := fun g => ⟨⟨g.1, hI g.2⟩, g.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have he : Q.ramificationIdx ℚ[X] = Q.ramificationIdx A := by
      rw [← h1, ← h2]
      exact (Nat.card_congr e).symm
    have ht := Ideal.ramificationIdx_tower (R := ℚ[X]) q Q
    rw [← he] at ht
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hepos) (ht.symm.trans (one_mul _).symm)
  obtain ⟨g, hg⟩ := hpf
  have hpg : ¬ p ∣ g := fun ⟨d, hd⟩ =>
    hp.not_isUnit (hf p ⟨d, by rw [hg, hd, mul_assoc]⟩)
  have hint : IsIntegral ℚ[X] s := by
    refine ⟨X ^ 2 - C f, monic_X_pow_sub_C _ (by decide), ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hs, sub_self]
  have hsK : s ∈ K := (IntermediateField.mem_fixedField_iff _ _).2 fun τ hτ => by
    rw [hact, MonoidHom.mem_ker.mp hτ, Units.val_one, C_1, map_one, one_mul]
  let a : A := ⟨⟨s, hsK⟩, isIntegral_algebraMap_iff.mp hint⟩
  have hasq : a ^ 2 = algebraMap ℚ[X] A f := Subtype.ext (Subtype.ext hs)
  have ha : a ∈ q := by
    apply (inferInstance : q.IsPrime).mem_of_pow_mem 2
    rw [hasq, ← Ideal.mem_comap, ← Ideal.under_def, hqu, Ideal.mem_span_singleton]
    exact ⟨g, hg⟩
  have hgq : algebraMap ℚ[X] A g ∉ q := by
    change g ∉ q.under ℚ[X]
    rw [hqu, Ideal.mem_span_singleton]
    exact hpg
  have hpq : algebraMap ℚ[X] A p ∈ q ^ 2 :=
    (Ideal.IsPrime.mem_pow_mul q (by
      rw [← map_mul, ← hg, ← hasq]
      exact Ideal.pow_mem_pow ha 2)).resolve_right hgq
  have hle : Ideal.map (algebraMap ℚ[X] A) (Ideal.span {p}) ≤ q ^ 2 := by
    rwa [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
  have he' := Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {p}) q hP0
  rw [he, Ideal.ramificationIdx'] at he'
  by_cases hb : BddAbove {n | Ideal.map (algebraMap ℚ[X] A) (Ideal.span {p}) ≤ q ^ n}
  · have := le_csSup hb hle
    omega
  · rw [Nat.sSup_of_not_bddAbove hb] at he'
    exact zero_ne_one he'

/-- An inertia element with sign `−1` forces the radicand to vanish in the residue field. -/
theorem radicand_mem_of_neg (χ : G₀ →* ℚˣ) (s : E) (f : ℚ[X])
    (hs : s ^ 2 = algebraMap ℚ[X] E f)
    (hact : ∀ g : G₀, g s = algebraMap ℚ[X] E (C (χ g : ℚ)) * s)
    (Q : Ideal B₀) (τ : G₀) (hi : τ ∈ Q.inertia G₀) (hn : (χ τ : ℚ) = -1) :
    f ∈ Q.under ℚ[X] := by
  have hint : IsIntegral ℚ[X] s := by
    refine ⟨X ^ 2 - C f, monic_X_pow_sub_C _ (by decide), ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hs, sub_self]
  let b : B₀ := ⟨s, hint⟩
  have hb : τ • b = -b := Subtype.ext (by simpa [hn] using hact τ)
  have h := hi b
  rw [hb, ← neg_add', ← two_mul] at h
  have hbQ : b ∈ Q := by
    have h2 : 2 * b ∈ Q := Q.neg_mem_iff.mp h
    have hC2 : algebraMap ℚ[X] B₀ (C 2) = 2 := by
      rw [map_ofNat, map_ofNat]
    have e : algebraMap ℚ[X] B₀ (C (1 / 2)) * (2 * b) = b := by
      rw [← hC2, ← mul_assoc, ← map_mul, ← C_mul]
      norm_num
    rw [← e]
    exact Q.mul_mem_left _ h2
  change algebraMap ℚ[X] B₀ f ∈ Q
  rw [← show b ^ 2 = algebraMap ℚ[X] B₀ f from Subtype.ext hs]
  exact Q.pow_mem_of_mem hbQ 2 (by decide)

end SGRDirect.HeckeSqrt

#print axioms SGRDirect.HeckeSqrt.squarefree_eigenvector
#print axioms SGRDirect.HeckeSqrt.prime_support
