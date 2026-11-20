import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Schwartz

/-! Factor the existing finite norm character place by place. The
truncation of the restricted product is on-the-spot (c). -/

noncomputable section

open ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.O7Assemble

open Eichler Adelic ThetaJoin ThetaClose LocalWeights

def singleR (p : Prime) : ℚ_[p.val]ˣ →* rationalIdeles where
  toFun u := ⟨Pi.mulSingle p u, (Set.finite_singleton p).subset fun q hq => by
    by_contra h
    exact hq (by rw [Pi.mulSingle_eq_of_ne h, map_one])⟩
  map_one' := Subtype.ext (map_one (MonoidHom.mulSingle (fun q : Prime => ℚ_[q.val]ˣ) p))
  map_mul' u v := Subtype.ext (map_mul (MonoidHom.mulSingle (fun q : Prime => ℚ_[q.val]ˣ) p) u v)

theorem singleR_same (p : Prime) (v : ℚ_[p.val]ˣ) : (singleR p v).val p = v :=
  by
  change Pi.mulSingle (M := fun q : Prime => ℚ_[q.val]ˣ) p v p = v
  exact Pi.mulSingle_eq_same (M := fun q : Prime => ℚ_[q.val]ˣ) p v

theorem singleR_away {p q : Prime} (h : q ≠ p) (v : ℚ_[p.val]ˣ) :
    (singleR p v).val q = 1 := by
  change Pi.mulSingle (M := fun q : Prime => ℚ_[q.val]ˣ) p v q = 1
  exact Pi.mulSingle_eq_of_ne (M := fun q : Prime => ℚ_[q.val]ˣ) h v

theorem discCharacter_units (S : Finset Prime) (z : rationalIdeles)
    (hz : ∀ q : Prime, valHom q (z.val q) = 1) :
    discriminantCharacter (O := ℤ) S z =
      ∏ q ∈ S, legendreUnit q.val (integralUnit q (z.val q) (hz q)) := by
  change (∏ q ∈ S, legendreUnit q.val (localUnitPart q z)) = _
  apply Finset.prod_congr rfl
  intro q _
  congr 1
  apply Units.ext
  apply Subtype.val_injective
  rw [localUnitPart_val, rationalPart_of_units z hz, map_one, div_one]
  rfl

theorem discCharacter_trivial (S : Finset Prime) (z : rationalIdeles)
    (hz : ∀ q : Prime, valHom q (z.val q) = 1)
    (hS : ∀ q ∈ S, z.val q = 1) :
    discriminantCharacter (O := ℤ) S z = 1 := by
  rw [discCharacter_units S z hz]
  apply Finset.prod_eq_one
  intro q hq
  have he : integralUnit q (z.val q) (hz q) = 1 := by
    apply Units.ext
    apply Subtype.val_injective
    exact congrArg Units.val (hS q hq)
  rw [he, map_one]

theorem singleR_integral (S : Finset Prime) (p : Prime) (v : ℚ_[p.val]ˣ)
    (hv : valHom p v = 1) :
    discriminantCharacter (O := ℤ) S (singleR p v) =
      if p ∈ S then legendreUnit p.val (integralUnit p v hv) else 1 := by
  classical
  have hh (q : Prime) : valHom q ((singleR p v).val q) = 1 := by
    by_cases h : q = p
    · subst q
      rw [singleR_same, hv]
    · rw [singleR_away h, map_one]
  rw [discCharacter_units S _ hh]
  by_cases hp : p ∈ S
  · rw [ite_eq_left hp, Finset.prod_eq_single_of_mem p hp]
    · congr 1
      apply Units.ext
      apply Subtype.val_injective
      exact congrArg Units.val (singleR_same p v)
    · intro q _ hq
      have he : integralUnit q ((singleR p v).val q) (hh q) = 1 := by
        apply Units.ext
        apply Subtype.val_injective
        exact congrArg Units.val (singleR_away hq v)
      rw [he, map_one]
  · rw [ite_eq_right hp]
    exact Finset.prod_eq_one fun q hq => by
      have he : integralUnit q ((singleR p v).val q) (hh q) = 1 := by
        apply Units.ext
        apply Subtype.val_injective
        exact congrArg Units.val (singleR_away (fun (h : q = p) => hp (show p ∈ S from h ▸ hq)) v)
      rw [he, map_one]

theorem discCharacter_product (S : Finset Prime) (z : rationalIdeles) :
    discriminantCharacter (O := ℤ) S z =
      ∏ᶠ p : ℕ, if hp : p.Prime then
        discriminantCharacter (O := ℤ) S (singleR ⟨p, hp⟩ (z.val ⟨p, hp⟩)) else 1 := by
  classical
  let T := S ∪ z.prop.toFinset
  let f (p : Prime) := singleR p (z.val p)
  let z₀ := ∏ p ∈ T, f p
  have h₀ (p : Prime) : z₀.val p = if p ∈ T then z.val p else 1 := by
    have hprod : z₀.val p = ∏ q ∈ T, (f q).val p :=
      map_prod ((Pi.evalMonoidHom _ p).comp rationalIdeles.subtype) _ _
    rw [hprod]
    by_cases hp : p ∈ T
    · rw [ite_eq_left hp, Finset.prod_eq_single_of_mem p hp]
      · exact singleR_same p _
      · exact fun q _ hq => singleR_away hq.symm _
    · rw [ite_eq_right hp]
      exact Finset.prod_eq_one fun q hq => singleR_away (fun (h : p = q) => hp (show p ∈ T from h.symm ▸ hq)) _
  have hval (p : Prime) : valHom p ((z / z₀).val p) = 1 := by
    change valHom p (z.val p / z₀.val p) = 1
    rw [h₀]
    by_cases hp : p ∈ T
    · rw [ite_eq_left hp, div_self', map_one]
    · rw [ite_eq_right hp, div_one]
      by_contra hn
      exact hp (Finset.mem_union_right _ ((z.prop.mem_toFinset).mpr hn))
  have hS (p : Prime) (hp : p ∈ S) : (z / z₀).val p = 1 := by
    change z.val p / z₀.val p = 1
    rw [h₀, ite_eq_left (Finset.mem_union_left _ hp), div_self']
  have hc : discriminantCharacter (O := ℤ) S z =
      discriminantCharacter (O := ℤ) S z₀ := by
    have hh := discCharacter_trivial S (z / z₀) hval hS
    rwa [map_div, div_eq_one] at hh
  let g (n : ℕ) := if hp : n.Prime then discriminantCharacter (O := ℤ) S (f ⟨n, hp⟩) else 1
  change _ = ∏ᶠ n, g n
  have hT : Function.mulSupport g ⊆ ↑(T.image Subtype.val) := by
    intro n hn
    by_contra h
    apply hn
    by_cases hp : n.Prime
    · let p : Prime := ⟨n, hp⟩
      have hnt : p ∉ T := fun ht => h (Finset.mem_image.mpr ⟨p, ht, rfl⟩)
      have hnp : p ∉ S := fun hs => hnt (Finset.mem_union_left _ hs)
      have hv : valHom p (z.val p) = 1 := by
        by_contra hv
        exact hnt (Finset.mem_union_right _ ((z.prop.mem_toFinset).mpr hv))
      simpa only [g, dite_eq_left hp, f, ite_eq_right hnp] using singleR_integral S p (z.val p) hv
    · simp [g, hp]
  rw [hc, map_prod, finprod_eq_prod_of_mulSupport_subset g hT,
    Finset.prod_image (fun _ _ _ _ hh => Subtype.ext hh)]
  exact Finset.prod_congr rfl fun p _ => by simp only [g, dite_eq_left p.prop]

variable {ell N m : ℕ} [Fact ell.Prime]
variable (h : ell % 4 = 3) (hN : 0 < N) (H : DiscriminantData m N ell)

private abbrev bad := (primes hN H).filter (fun q => q.val ∣ m)

theorem mem_bad (p : Prime) : p ∈ bad hN H ↔ p.val ∣ m := by
  simp only [bad, Finset.mem_filter, mem_exceptionalPlaces]
  exact ⟨And.right, fun hp => ⟨dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_right hp 2) N) ell, hp⟩⟩

theorem singleR_unramified (p : Prime) (hp : ¬ p.val ∣ m)
    (u : ℚ_[p.val]ˣ) (hu : 0 ≤ u.val.valuation) :
    (discriminantCharacter (O := ℤ) (bad hN H) (singleR p u) : ℤ) =
      chiD (-(m : ℤ)) p.val ^ u.val.valuation.toNat := by
  classical
  let z := singleR p u
  let e := u.val.valuation.toNat
  have he : (e : ℤ) = u.val.valuation := Int.toNat_of_nonneg hu
  have hz : rationalPart z = rationalPrime p ^ e := by
    apply div_eq_one.mp
    apply positive_rational_unit
    · rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
      refine div_pos (rationalPart_pos z) (pow_pos ?_ _)
      change (0 : ℚ) < p.val
      exact_mod_cast p.prop.pos
    · intro q
      rw [map_div, map_div, rationalPart_valuation, div_eq_one, map_pow, map_pow]
      apply Multiplicative.toAdd.injective
      rw [Int.toAdd_pow, val_rationalPrime]
      by_cases hq : q = p
      · subst q
        rw [show z.val p = u from singleR_same p u, ite_eq_left rfl, one_mul, he]
        rfl
      · rw [show z.val q = 1 from singleR_away hq _, map_one, ite_eq_right (Ne.symm hq)]
        simp
  let emb : Prime ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hS : (bad hN H).map emb = m.primeFactors := by
    ext n
    simp only [Finset.mem_map, Nat.mem_primeFactors]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.prop, (mem_bad hN H p).mp hp, by have := H.odd; omega⟩
    · rintro ⟨hn, hd, _⟩
      exact ⟨⟨n, hn⟩, (mem_bad hN H _).mpr hd, rfl⟩
  have hχ : chiD (-(m : ℤ)) p.val = ∏ q ∈ (bad hN H), jacobiSym p.val q.val := by
    simp only [chiD, Int.natAbs_neg, Int.natAbs_natCast]
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree H.squarefree]
    rw [← hS, Finset.prod_map]
    have hf (S : Finset Prime) : jacobiSym (p.val : ℤ) (∏ q ∈ S, q.val) =
        ∏ q ∈ S, jacobiSym p.val q.val := by
      induction S using Finset.induction_on with
      | empty => simp
      | insert q T hq ih =>
        rw [Finset.prod_insert hq, Finset.prod_insert hq, jacobiSym.mul_right', ih]
        · exact q.prop.ne_zero
        · exact Finset.prod_ne_zero_iff.mpr fun r _ => r.prop.ne_zero
    exact hf _
  rw [hχ, ← Finset.prod_pow]
  change ((∏ q ∈ bad hN H, legendreUnit q.val (localUnitPart q z) : ℤˣ) : ℤ) = _
  rw [Units.coe_prod]
  apply Finset.prod_congr rfl
  intro q hq
  have hqp : q ≠ p := fun hh => hp (hh ▸ (mem_bad hN H q).mp hq)
  have hqnd : ¬ q.val ∣ p.val := fun hdv =>
    hqp (Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.prop p.prop).mp hdv))
  let v := PhaseData.natUnit q p.val hqnd
  let f := Units.map (algebraMap ℤ_[q.val] ℚ_[q.val]).toMonoidHom
  have hv₀ : f v = rationalToLocal q (rationalPrime p) := by
    apply Units.ext
    change (↑(v.val) : ℚ_[q.val]) = _
    rw [PhaseData.natUnit_val]
    change (algebraMap ℤ_[q.val] ℚ_[q.val]) (p.val : ℤ_[q.val]) = _
    rw [map_natCast]
    simp [rationalToLocal, rationalPrime]
  have hv : localUnitPart q z = (v ^ e)⁻¹ := by
    apply Units.ext
    apply Subtype.val_injective
    rw [localUnitPart_val, hz, show z.val q = 1 from singleR_away hqp _, map_pow,
      one_div, ← hv₀, ← map_pow, ← map_inv]
    rfl
  rw [hv, map_inv, legendreUnit_inv, map_pow, Units.val_pow_eq_pow_val,
    legendreUnit_apply, PhaseData.natUnit_val, map_natCast]
  congr 1
  simpa only [legendreSym, Int.cast_natCast, Int.cast_id] using
    (jacobiSym.legendreSym.to_jacobiSym q.val (p.val : ℤ))

/-- The actual norm character in integer signs, with its local factors
computed by inserting one local reduced norm coordinate. -/
def normFactors : TorusWeights.NormFactors (levelRing h hN) (-(m : ℤ)) where
  character := normCharacter h hN (bad hN H)
  atPrime p := (discriminantCharacter (O := ℤ) (bad hN H)).comp (singleR p)
  rational := normCharacter_diagonal h hN (bad hN H)
  unramified p hp v hv := singleR_unramified hN H p (by simpa using hp) v hv
  unitValuation p u := by
    rw [localNrd_eq]
    exact congrArg Multiplicative.toAdd (val_localNorm_of_orderUnit h hN p u)
  product z := by
    rw [normCharacter, MonoidHom.comp_apply, discCharacter_product]
    apply finprod_congr
    intro p
    by_cases hp : p.Prime
    · simp only [dite_eq_left hp]
      rfl
    · simp only [dite_eq_right hp]

/-- On a local order unit only the ramified norm character survives. -/
theorem normFactors_unit (p : Prime) (u : localUnits (levelRing h hN) p) :
    (normFactors h hN H).atPrime p (TorusWeights.localNrd p u.val) =
      if p.val ∣ m then legendreUnit p.val (ThetaJoin.normUnit h hN p u) else 1 := by
  rw [localNrd_eq]
  simpa only [normFactors, MonoidHom.comp_apply, mem_bad, ThetaJoin.normUnit] using
    singleR_integral (bad hN H) p (localNormHom p u.val) (val_localNorm_of_orderUnit h hN p u)

variable (hcop : N.Coprime ell) (w : ℕ → ℤˣ) {M : ℕ}

/-- The norm reading at the actual chosen representative, via the same
integer character cast into the ring of the fixed level characters. -/
theorem stageNormRead (z : ClassSet (levelRing h hN)) :
    (actualPmLocal (M := M) h hN hcop H w).χN z =
      (((normFactors h hN H).character (classRepresentative z) : ℤ) : Coefficients hN H w) := by
  change ((levelNormCharacter h hN (levelRoots hN H w)
    (exceptionalProduct_ne_zero hN H) (classRepresentative z) : (Coefficients hN H w)ˣ) :
      Coefficients hN H w) = _
  change ((∏ q ∈ bad hN H, legendreUnit q.val
    (localUnitPart q (normIdeles h hN (classRepresentative z))) : (Coefficients hN H w)ˣ) :
      Coefficients hN H w) = _
  change _ = (((∏ q ∈ bad hN H, legendreUnit q.val
    (localUnitPart q (normIdeles h hN (classRepresentative z))) : ℤˣ) : ℤ) : Coefficients hN H w)
  simp only [Units.coe_prod, Int.cast_prod, legendreUnit_apply, Int.cast_id]

end ZInQ.Manuscript.RC.O7Assemble
