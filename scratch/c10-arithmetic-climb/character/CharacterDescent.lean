import ZInQKernel.HDecomp.C10.C10
import ZInQKernel.HDecomp.Descent.Chi
import CharacterDescentExpected

/-!
# Fixed-place descent of the existing complex character `GlueDescent.chi` into `Qbar`

PRIVATE CANDIDATE (climb/cyclotomic-coefficients). Not a public claim, not a provider,
not an adoption. This file proves the three independently stated targets of
`ClimbCharacterExpected` (`CharacterDescentExpected.lean`, sha256
54c7a9ca22c327aaafce799a0e16f6372be188c3deec90eb7422062602ef65cb) and nothing else.

What is proved: along a FIXED, caller-supplied complex place `ρ : GlueC10.Qbar →ₐ[ℚ] ℂ`,
the existing complex Dirichlet character of `ZInQKernel/HDecomp/Descent/Chi.lean` is the
`ρ`-image of a genuine `Qbar`-valued Dirichlet character of the SAME level, with the same
order (hence the same original prime-supported order bound), the same vanishing on
non-units, and the same oddness. `ρ` is never replaced by a convenient embedding: every
statement is universally quantified over `ρ`.

What is NOT proved and NOT assumed: no reproof of the complex `chi`, of its order bound,
of `oddChar`, of B2/ε local class-field splitting, of any cochain/isogeny/scalar datum,
of continuity, of C10 or of Hilbert 10. No `Fact`-assumed preimage and no new axiom.

Positivity guard: the generic lemmas take `[NeZero n]`; at the actual consumer the
instance is DERIVED from the existing primality hypotheses of `GlueDescent.exists_chi`
(`two_lt_lev`), not added as a new input.
-/

noncomputable section

open Polynomial

namespace ClimbCharacterDescent

/-! ## 1. A root of unity of `ℂ` lies in the image of any ring map from an
algebraically closed field.

The image of an algebraically closed field under a field map is algebraically closed, so
it already contains every root of `X ^ k - 1`. Formally: `X ^ k - C 1` splits over `K`,
so the roots of its image are the images of its roots (`roots_map_of_injective_of_card_eq_natDegree`). -/

theorem exists_preimage_of_pow_eq_one {K : Type*} [Field K] [IsAlgClosed K] (f : K →+* ℂ)
    {z : ℂ} {k : ℕ} (hk : 0 < k) (hz : z ^ k = 1) : ∃ w : K, f w = z := by
  classical
  have hcard : Multiset.card ((X : K[X]) ^ k - C (1 : K)).roots =
      ((X : K[X]) ^ k - C (1 : K)).natDegree :=
    splits_iff_card_roots.mp (IsAlgClosed.splits _)
  have hmap : ((X : K[X]) ^ k - C (1 : K)).roots.map f =
      (((X : K[X]) ^ k - C (1 : K)).map f).roots :=
    roots_map_of_injective_of_card_eq_natDegree f.injective hcard
  have hpf : ((X : K[X]) ^ k - C (1 : K)).map f = (X : ℂ[X]) ^ k - C (1 : ℂ) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, map_one]
  have hz0 : ((X : ℂ[X]) ^ k - C (1 : ℂ)) ≠ 0 := X_pow_sub_C_ne_zero hk 1
  have hzmem : z ∈ (((X : K[X]) ^ k - C (1 : K)).map f).roots := by
    rw [hpf, mem_roots hz0]
    simp [IsRoot.def, hz]
  rw [← hmap] at hzmem
  obtain ⟨w, -, hw⟩ := Multiset.mem_map.mp hzmem
  exact ⟨w, hw⟩

/-! ## 2. Every value of a complex Dirichlet character of nonzero level has a preimage.

Non-units go to `0`; a unit `u` satisfies `u ^ φ n = 1` (`ZMod.pow_totient`, the same step
`Chi.lean` uses for `orderOf_dvd_totient`), so its value is a `φ n`-th root of unity and
`φ n > 0` exactly because `n ≠ 0`. -/

theorem exists_preimage_value {K : Type*} [Field K] [IsAlgClosed K] (f : K →+* ℂ)
    (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n) (a : ZMod n) : ∃ w : K, f w = χ a := by
  classical
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    refine exists_preimage_of_pow_eq_one f
      (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))) ?_
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one]
  · exact ⟨0, by rw [map_zero, χ.map_nonunit ha]⟩

/-! ## 3. Descent of a multiplicative character along an injective ring hom -/

section Descend

variable {R : Type*} [CommMonoid R] {K L : Type*} [CommRing K] [CommRing L]
  (f : K →+* L) (hf : Function.Injective f) (χ : MulChar R L)
  (h : ∀ a : R, ∃ w : K, f w = χ a)

/-- The `K`-valued character whose `f`-image is `χ`, value by value. Multiplicativity,
normalization and vanishing on non-units are transported back through injectivity of `f`;
nothing is assumed about `χ` beyond its values having preimages. -/
def descend : MulChar R K where
  toFun a := (h a).choose
  map_one' := hf (by rw [(h 1).choose_spec, map_one, map_one])
  map_mul' a b := hf (by
    rw [(h (a * b)).choose_spec, map_mul f, (h a).choose_spec, (h b).choose_spec, map_mul])
  map_nonunit' a ha := hf (by rw [(h a).choose_spec, map_zero, χ.map_nonunit ha])

@[simp] theorem descend_apply (a : R) : f (descend f hf χ h a) = χ a := (h a).choose_spec

theorem ringHomComp_descend : (descend f hf χ h).ringHomComp f = χ :=
  MulChar.ext fun a => by rw [MulChar.ringHomComp_apply, descend_apply]

theorem descend_nonunit {a : R} (ha : ¬ IsUnit a) : descend f hf χ h a = 0 :=
  (descend f hf χ h).map_nonunit ha

end Descend

section Order

variable {R : Type*} [CommMonoid R] {K L : Type*} [CommRing K] [CommRing L]

theorem ringHomCompHom_injective (f : K →+* L) (hf : Function.Injective f) :
    Function.Injective (MulChar.ringHomCompHom (R := R) f) := by
  intro χ₁ χ₂ hχ
  refine MulChar.ext fun a => hf ?_
  have := congrArg (fun ψ : MulChar R L => ψ a) hχ
  simpa [MulChar.ringHomCompHom, MulChar.ringHomComp_apply] using this

theorem orderOf_descend (f : K →+* L) (hf : Function.Injective f) (χ : MulChar R L)
    (h : ∀ a : R, ∃ w : K, f w = χ a) : orderOf (descend f hf χ h) = orderOf χ := by
  have hord := orderOf_injective (MulChar.ringHomCompHom (R := R) f)
    (ringHomCompHom_injective f hf) (descend f hf χ h)
  have hval : MulChar.ringHomCompHom (R := R) f (descend f hf χ h) = χ :=
    ringHomComp_descend f hf χ h
  rw [hval] at hord
  exact hord.symm

end Order

/-! ## 4. The three independently stated targets -/

/-- The fixed place and the level are those of the caller; only the coefficient field moves. -/
theorem fixedPlaceDescent : ClimbCharacterExpected.FixedPlaceDescent := by
  intro n _ ρ χ
  have hinj : Function.Injective (ρ : GlueC10.Qbar →+* ℂ) := RingHom.injective _
  refine ⟨descend (ρ : GlueC10.Qbar →+* ℂ) hinj χ
    (fun a => exists_preimage_value (ρ : GlueC10.Qbar →+* ℂ) n χ a), fun a => ?_, ?_⟩
  · exact descend_apply (ρ : GlueC10.Qbar →+* ℂ) hinj χ _ a
  · exact orderOf_descend (ρ : GlueC10.Qbar →+* ℂ) hinj χ _

theorem fixedPlaceOddness : ClimbCharacterExpected.FixedPlaceOddness := by
  intro n _ ρ χ hodd
  have hinj : Function.Injective (ρ : GlueC10.Qbar →+* ℂ) := RingHom.injective _
  refine ⟨descend (ρ : GlueC10.Qbar →+* ℂ) hinj χ
    (fun a => exists_preimage_value (ρ : GlueC10.Qbar →+* ℂ) n χ a), fun a => ?_, ?_, ?_⟩
  · exact descend_apply (ρ : GlueC10.Qbar →+* ℂ) hinj χ _ a
  · refine hinj ?_
    rw [descend_apply, hodd, map_neg, map_one]
  · exact orderOf_descend (ρ : GlueC10.Qbar →+* ℂ) hinj χ _

/-- `NeZero (chiLevel Tm)` is derived from the hypotheses `GlueDescent.exists_chi`
already carries (`∀ p ∈ T, p.Prime` and `Tm ⊆ T`), via `GlueDescent.two_lt_lev`. -/
theorem chiLevel_pos {T Tm : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) (hTm : Tm ⊆ T) :
    0 < GlueDescent.chiLevel Tm := by
  refine Finset.prod_pos ?_
  intro p hp
  have := GlueDescent.two_lt_lev (hT p (hTm hp))
  omega

theorem actualGlueCharacter : ClimbCharacterExpected.ActualGlueCharacter := by
  intro T Tm hT hTm ρ
  have : NeZero (GlueDescent.chiLevel Tm) := NeZero.of_pos (chiLevel_pos hT hTm)
  obtain ⟨χ₀, hval, hord⟩ :=
    fixedPlaceDescent (GlueDescent.chiLevel Tm) ρ (GlueDescent.chi Tm)
  refine ⟨χ₀, hval, hord, ?_⟩
  rw [hord]
  exact (GlueDescent.exists_chi T Tm hT hTm).2.2

end ClimbCharacterDescent

/-! ## 5. Reports -/

#print axioms ClimbCharacterDescent.exists_preimage_of_pow_eq_one
#print axioms ClimbCharacterDescent.exists_preimage_value
#print axioms ClimbCharacterDescent.descend
#print axioms ClimbCharacterDescent.orderOf_descend
#print axioms ClimbCharacterDescent.fixedPlaceDescent
#print axioms ClimbCharacterDescent.fixedPlaceOddness
#print axioms ClimbCharacterDescent.chiLevel_pos
#print axioms ClimbCharacterDescent.actualGlueCharacter
