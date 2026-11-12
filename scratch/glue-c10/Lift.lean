import Mathlib

/-! glue-c10: step (c) of `FrobLift` — the restriction of a Frobenius of `G_ℚ` to a finite Galois
layer `E` is the Frobenius at the unramified prime below. -/

open NumberField

namespace GlueC10

abbrev Qbar : Type := AlgebraicClosure ℚ
abbrev GQ : Type := Qbar ≃ₐ[ℚ] Qbar
abbrev Zbar : Type := integralClosure ℤ Qbar

/-- `𝓞_E → \bar ℤ`. -/
noncomputable def toZbar (E : IntermediateField ℚ Qbar) : 𝓞 E →+* Zbar :=
  RingHom.codRestrict ((algebraMap E Qbar).comp (algebraMap (𝓞 E) E)) (integralClosure ℤ Qbar)
    (fun x => (RingOfIntegers.isIntegral_coe x).map (IsScalarTower.toAlgHom ℤ E Qbar))

@[simp] lemma toZbar_coe (E : IntermediateField ℚ Qbar) (x : 𝓞 E) :
    ((toZbar E x : Zbar) : Qbar) = ((x : E) : Qbar) := rfl

lemma card_quot (p : ℕ) [Fact p.Prime] : Nat.card (ℤ ⧸ Ideal.span {(p : ℤ)}) = p := by
  rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

/-- **Step (c) of `FrobLift` (GLUE, proved).** -/
theorem restrictNormal_eq_of_frob (E : IntermediateField ℚ Qbar) [FiniteDimensional ℚ E]
    [IsGalois ℚ E] (τ : E ≃ₐ[ℚ] E) (p : ℕ) [Fact p.Prime] (Q : Ideal (𝓞 E)) [Q.IsPrime]
    (hQp : Q.under ℤ = Ideal.span {(p : ℤ)}) [Algebra.IsUnramifiedAt ℤ Q]
    (hτ : IsArithFrobAt ℤ τ Q) (h : GQ) (P : Ideal Zbar) (hPQ : P.comap (toZbar E) = Q)
    (hh : ∀ x y : Zbar, (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P) :
    AlgEquiv.restrictNormal h E = τ := by
  have : NumberField E := ⟨⟩
  set σ := AlgEquiv.restrictNormal h E
  have hσ : IsArithFrobAt ℤ σ Q := by
    intro x
    rw [hQp, card_quot, ← hPQ, Ideal.mem_comap]
    apply hh (toZbar E x)
    rw [map_sub, map_pow, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, toZbar_coe,
      toZbar_coe]
    congr 1
    exact AlgEquiv.restrictNormal_commutes h E (x : E)
  have hQ : Q.primeCompl ≤ nonZeroDivisors (𝓞 E) := by
    intro x hx
    apply mem_nonZeroDivisors_of_ne_zero
    rintro rfl
    exact hx Q.zero_mem
  have heq := hσ.eq_of_isUnramifiedAt hτ hQ
  ext y
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
  have ha := congrArg (fun f => ((f a : 𝓞 E) : E)) heq
  have hb := congrArg (fun f => ((f b : 𝓞 E) : E)) heq
  simp only [MulSemiringAction.toAlgHom_apply] at ha hb
  have key : ∀ (g : E ≃ₐ[ℚ] E) (c : 𝓞 E), g (algebraMap (𝓞 E) E c) = ((g • c : 𝓞 E) : E) :=
    fun g c => rfl
  have e1 := (key σ a).trans (ha.trans (key τ a).symm)
  have e2 := (key σ b).trans (hb.trans (key τ b).symm)
  rw [map_div₀, map_div₀, e1, e2]

/-- `g ∈ G_ℚ` is a Frobenius at `p` (as in `C10.lean`). -/
def IsFrobAt (g : GQ) (p : ℕ) : Prop :=
  ∃ P : Ideal Zbar, P.IsPrime ∧ P.under ℤ = Ideal.span {(p : ℤ)} ∧
    ∀ x y : Zbar, (y : Qbar) = g (x : Qbar) - (x : Qbar) ^ p → y ∈ P

/-- **Step (b) of `FrobLift` (GLUE, open).** Every prime `𝔓` of `\bar ℤ` over a rational prime
`p` has an arithmetic Frobenius in `G_ℚ`.  (Compactness of `G_ℚ` and Mathlib's
`exists_isArithFrobAt` in each finite Galois layer.) -/
def FrobExistsAt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Ideal Zbar) [P.IsPrime], P.under ℤ = Ideal.span {(p : ℤ)} →
    ∃ h : GQ, ∀ x y : Zbar, (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P

/-- `FrobLift` of `C10.lean`. -/
def FrobLift : Prop :=
  ∀ (E : IntermediateField ℚ Qbar) [FiniteDimensional ℚ E] [IsGalois ℚ E]
    (τ : E ≃ₐ[ℚ] E) (p : ℕ) (Q : Ideal (𝓞 E)) [Q.IsPrime], p.Prime →
    Q.under ℤ = Ideal.span {(p : ℤ)} → Algebra.IsUnramifiedAt ℤ Q → IsArithFrobAt ℤ τ Q →
      ∃ h : GQ, IsFrobAt h p ∧ AlgEquiv.restrictNormal h E = τ

lemma toZbar_injective (E : IntermediateField ℚ Qbar) : Function.Injective (toZbar E) := by
  intro x y hxy
  have := congrArg (fun z : Zbar => (z : Qbar)) hxy
  simp only [toZbar_coe] at this
  exact RingOfIntegers.ext (Subtype.ext this)

/-- **`FrobLift` from step (b) (GLUE, proved): lying-over plus step (c).** -/
theorem frobLift_of_frobExistsAt (hb : FrobExistsAt) : FrobLift := by
  intro E _ _ τ p Q _ hp hQp hQu hτ
  have : Fact p.Prime := ⟨hp⟩
  let _ : Algebra (𝓞 E) Zbar := (toZbar E).toAlgebra
  have : Algebra.IsIntegral (𝓞 E) Zbar := Algebra.IsIntegral.tower_top ℤ
  obtain ⟨P, -, hP, hPQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral Q (⊥ : Ideal Zbar)
    (by
      intro x hx
      have : toZbar E x = 0 := hx
      rw [toZbar_injective E (this.trans (map_zero _).symm)]
      exact Q.zero_mem)
  have hPQ' : P.comap (toZbar E) = Q := hPQ
  have hPp : P.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [← hQp, Ideal.under, Ideal.under, ← hPQ', Ideal.comap_comap]
    congr 1
  obtain ⟨h, hh⟩ := hb p P hPp
  exact ⟨h, ⟨P, hP, hPp, hh⟩, restrictNormal_eq_of_frob E τ p Q hQp hτ h P hPQ' hh⟩

end GlueC10

#print axioms GlueC10.restrictNormal_eq_of_frob
#print axioms GlueC10.frobLift_of_frobExistsAt
