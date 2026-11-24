import ZInQKernel.Contrib.OneProof.JDescent5Odd
import ZInQKernel.Contrib.OneProof.JDescent5Period

/-! The CM degree row after the genus comparison. -/

namespace HDec.CMBranch.CMjBridges

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open TauCeti
open scoped UpperHalfPlane _root_.PeriodPair
open _root_.ZInQ.LeafPush2 (CPts cEvalAt IsUniformization)

noncomputable section
attribute [local instance] abVar_isIntegral abVarFunctionFieldAlgebra
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

private theorem cEvalAt_inv_eq_of_fixed {L : Type} [Field L] {A : PkgI3.AbVar L}
    {σ : L →+* ℂ} (p : CPts A σ) (U : A.X.left.Opens) (s : Γ(A.X.left, U))
    (hu : U ≤ abVarInv A ⁻¹ᵁ U) (hf : (abVarInv A).appLE U U hu s = s)
    (hp : ⊤ ≤ p.left ⁻¹ᵁ U) :
    cEvalAt p⁻¹ U s = cEvalAt p U s := by
  have hinv : (p⁻¹ : CPts A σ).left = p.left ≫ abVarInv A := rfl
  have hn : ⊤ ≤ (p⁻¹ : CPts A σ).left ⁻¹ᵁ U := by
    rw [hinv]
    exact hp.trans (p.left.preimage_mono hu)
  simp only [cEvalAt, dite_eq_left hp, dite_eq_left hn]
  have he := Scheme.Hom.appLE_comp_appLE p.left (abVarInv A) U U ⊤ hu hp
  have he' : (abVarInv A).appLE U U hu ≫ p.left.appLE U ⊤ hp =
      (p⁻¹ : CPts A σ).left.appLE U ⊤ hn := by
    exact he
  have ha := congrArg (fun f : Γ(A.X.left, U) ⟶ Γ(Spec (CommRingCat.of ℂ), ⊤) => f s) he'
  rw [CommRingCat.comp_apply, hf] at ha
  exact congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ha.symm

/-- On the specified period the section with pole order two is even. -/
theorem abVar_period_abscissa_even {L : Type} [Field L] [NumberField L]
    (hg : AbVarFunctionFieldGenusOne) (A : PkgI3.AbVar L) (hdim : A.dim = 1)
    {σ : L →+* ℂ} {τ : ℍ} {Λ : Submodule ℤ (Fin 1 → ℂ)}
    {Φ : (Fin 1 → ℂ) → CPts A σ} {s : ℂ} (hΦ : IsUniformization σ Λ Φ) (hs : s ≠ 0)
    (hΛ : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = s * (m + n * (τ : ℂ)))
    (P : Place L (AbVarFunctionField A))
    (hp : (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A)) (AbVarFunctionField A)).range =
      P.integers.toSubring) (x y : Γ(A.X.left, abVarPunctured A)) (a b : L)
    (hx : letI := abVarPunctured_nonempty A P hp
          P.ord (A.X.left.germToFunctionField (abVarPunctured A) x) = -2)
    (hy : letI := abVarPunctured_nonempty A P hp
          P.ord (A.X.left.germToFunctionField (abVarPunctured A) y) = -3)
    (hreg : letI := abVarPunctured_nonempty A P hp
      ∀ Q, Q ≠ P → 0 ≤ Q.ord (A.X.left.germToFunctionField (abVarPunctured A) x) ∧
        0 ≤ Q.ord (A.X.left.germToFunctionField (abVarPunctured A) y))
    (heq : y ^ 2 = x ^ 3 + abVarSectionConst A _ a * x + abVarSectionConst A _ b) :
    ∀ z : ℂ, cEvalAt (Φ (fun _ => s * (-z))) (abVarPunctured A) x =
      cEvalAt (Φ (fun _ => s * z)) (abVarPunctured A) x := by
  let U := abVarPunctured A
  have hu := (abVarInv_sections_of_genusOne hg A hdim hΦ hs hΛ P hp x y a b hx hy hreg heq).1
  let v : ℂ → (Fin 1 → ℂ) := fun z _ => s * z
  have hinv (z : ℂ) : Φ (v (-z)) = (Φ (v z))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← hΦ.1]
    have h0 : v (-z) + v z = 0 := funext (fun i => by simp [v])
    rw [h0]
    exact (hΦ.2.1 0).mpr Λ.zero_mem
  intro z
  change cEvalAt (Φ (v (-z))) U x = cEvalAt (Φ (v z)) U x
  rw [hinv]
  by_cases hz : z ∈ (PeriodPair.ofTau τ).lattice
  · have hv : v z ∈ Λ := by
      obtain ⟨n, m, hm⟩ := PeriodPair.mem_lattice.mp hz
      apply (hΛ _).mpr
      refine ⟨m, n, ?_⟩
      change s * z = _
      rw [← hm]
      change s * ((n : ℂ) * (τ : ℂ) + (m : ℂ) * 1) = _
      ring
    rw [(hΦ.2.1 _).mpr hv, inv_one]
  · exact cEvalAt_inv_eq_of_fixed (Φ (v z)) U x _ hu (abVar_period_mem_punctured hΦ hs hΛ hz)

/-- Genus one supplies nonsingular short coordinates with an even abscissa and an analytic
double pole on the specified period. -/
theorem cmPeriodShortCoordinatesDoublePole_of_genusOne
    (hgenus : AbVarFunctionFieldGenusOne) : CMPeriodShortCoordinatesDoublePole := by
  intro L _ _ E hE k _ _ R _ _ σ τ hτ
  let A := LeafAdopt.abVarEquiv L E
  have hA : A.dim = 1 := by rw [LeafAdopt.abVarEquiv_dim]; exact hE
  obtain ⟨Λ, Φ, hΦ, s, hs, hΛ⟩ := hτ
  obtain ⟨P, hp, x, y, a, b, hx, hy, hreg, heq, hΔ⟩ := abVar_shortSections_of_genusOne hgenus A hA
  exact ⟨Λ, Φ, hΦ, s, hs, hΛ, abVarPunctured A, x, y, a, b, hΔ, heq,
    fun z hz => abVar_period_mem_punctured hΦ hs hΛ hz,
    abVar_period_abscissa_even hgenus A hA hΦ hs hΛ P hp x y a b hx hy hreg heq,
    abVar_evaluatedPole_of_order A hΦ hs hΛ P hp x hx⟩

/-- The live row follows from Fowler's degree statement and the genus comparison. -/
theorem cmjDegree_of_print_of_genusOne
    (hgenus : AbVarFunctionFieldGenusOne) : CMjDegreePrint → CMjDegree :=
  cmjDegree_of_print_of_doublePole (cmPeriodShortCoordinatesDoublePole_of_genusOne hgenus)

#print axioms cEvalAt_inv_eq_of_fixed
#print axioms abVar_period_abscissa_even
#print axioms cmPeriodShortCoordinatesDoublePole_of_genusOne
#print axioms cmjDegree_of_print_of_genusOne

end

end HDec.CMBranch.CMjBridges
