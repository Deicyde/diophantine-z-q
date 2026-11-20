import ZInQKernel.Contrib.OneProof.JDescent5Sections

/-! A uniformizer and the regular numerator for the double pole. -/

namespace HDec.CMBranch.CMjBridges

open CategoryTheory AlgebraicGeometry TopologicalSpace TauCeti

noncomputable section
attribute [local instance] abVar_isIntegral abVarFunctionFieldAlgebra
set_option maxHeartbeats 800000

/-- A parameter and a regular numerator representing the exact pole of order two.
The order-one parameter is represented on the same algebraic neighborhood as the numerator.
The identity of sections is on the intersection with the domain of the meromorphic section. -/
theorem abVar_orderTwo_localParameter {L : Type} [Field L] (A : PkgI3.AbVar L)
    (P : Place L (AbVarFunctionField A))
    (hP : (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A)) (AbVarFunctionField A)).range =
      P.integers.toSubring)
    (U : A.X.left.Opens) [Nonempty U] (x : Γ(A.X.left, U))
    (hx : P.ord (A.X.left.germToFunctionField U x) = -2) :
    ∃ (V : A.X.left.Opens) (hV : abVarIdentity A ∈ V) (t u : Γ(A.X.left, V)),
      (letI : Nonempty V := ⟨⟨abVarIdentity A, hV⟩⟩
       P.ord (A.X.left.germToFunctionField V t) = 1) ∧
      ¬ IsUnit (A.X.left.presheaf.germ V (abVarIdentity A) hV t) ∧
      IsUnit (A.X.left.presheaf.germ V (abVarIdentity A) hV u) ∧
      (A.X.left.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op t) ^ 2 *
        A.X.left.presheaf.map (homOfLE (inf_le_right : V ⊓ U ≤ U)).op x =
        A.X.left.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op u := by
  let X := A.X.left
  let O := abVarIdentity A
  let F := AbVarFunctionField A
  let R := X.presheaf.stalk O
  let φ : R →+* F := algebraMap R F
  let Xf : F := X.germToFunctionField U x
  have hx' : P.ord Xf = -2 := hx
  have hx0 : Xf ≠ 0 := fun h => by rw [h, P.ord_zero] at hx'; omega
  obtain ⟨T, ht0, ht⟩ := P.exists_ne_zero_ord_eq 1
  let N := T ^ 2 * Xf
  have hn0 : N ≠ 0 := mul_ne_zero (pow_ne_zero _ ht0) hx0
  have hn : P.ord N = 0 := by
    dsimp only [N]
    rw [P.ord_mul (pow_ne_zero _ ht0) hx0, P.ord_pow, ht, hx']
    decide
  have htmem : T ∈ P.integers.toSubring :=
    P.mem_integers_iff_ord_nonneg.mpr (by rw [ht]; decide)
  have hnmem : N ∈ P.integers.toSubring :=
    P.mem_integers_iff_ord_nonneg.mpr (by rw [hn])
  have hinvmem : N⁻¹ ∈ P.integers.toSubring :=
    P.mem_integers_iff_ord_nonneg.mpr (by rw [P.ord_inv, hn, neg_zero])
  obtain ⟨t₀, ht₀⟩ : T ∈ φ.range := hP.symm ▸ htmem
  obtain ⟨u₀, hu₀⟩ : N ∈ φ.range := hP.symm ▸ hnmem
  obtain ⟨v₀, hv₀⟩ : N⁻¹ ∈ φ.range := hP.symm ▸ hinvmem
  let φI : R →+* P.integers.toSubring :=
    φ.codRestrict P.integers.toSubring (fun a => hP ▸ ⟨a, rfl⟩)
  have hnt : ¬ IsUnit t₀ := by
    intro h
    have htI : (φI t₀ : F) = T := ht₀
    have := (P.isUnit_iff_ord_eq_zero (x := φI t₀) (by rw [htI]; exact ht0)).1 (h.map φI)
    rw [htI, ht] at this
    omega
  have hnu : IsUnit u₀ := by
    have h1 : u₀ * v₀ = 1 := (IsFractionRing.injective R F) (by
      change φ (u₀ * v₀) = φ 1
      rw [map_mul, hu₀, hv₀, map_one, mul_inv_cancel₀ hn0])
    exact IsUnit.of_mul_eq_one v₀ h1
  obtain ⟨W, hW, tW, htW⟩ := X.presheaf.exists_germ_eq t₀
  obtain ⟨V, hVW, hV, u, hu⟩ := X.presheaf.exists_le_germ_eq u₀ hW
  let t : Γ(X, V) := X.presheaf.map (homOfLE hVW).op tW
  have ht' : X.presheaf.germ V O hV t = t₀ := by
    dsimp [t]
    rw [X.presheaf.germ_res_apply, htW]
  have : Nonempty V := ⟨⟨O, hV⟩⟩
  have htF : X.germToFunctionField V t = T := by
    rw [← X.algebraMap_germ_eq_germToFunctionField hV t, ht']
    exact ht₀
  have huF : X.germToFunctionField V u = N := by
    rw [← X.algebraMap_germ_eq_germToFunctionField hV u, hu]
    exact hu₀
  refine ⟨V, hV, t, u, by rwa [htF], ht' ▸ hnt, hu ▸ hnu, ?_⟩
  have hη (W : X.Opens) (h : Nonempty W) : genericPoint X ∈ W :=
    (genericPoint_spec X).mem_open_set_iff W.isOpen |>.mpr (by simpa using h)
  have : Nonempty (V ⊓ U : X.Opens) := ⟨⟨genericPoint X, hη V ‹_›, hη U ‹_›⟩⟩
  apply X.germToFunctionField_injective (V ⊓ U)
  change (X.germToFunctionField (V ⊓ U)).hom _ = (X.germToFunctionField (V ⊓ U)).hom _
  rw [map_mul, map_pow]
  change (X.germToFunctionField (V ⊓ U) (X.presheaf.map _ t)) ^ 2 *
      X.germToFunctionField (V ⊓ U) (X.presheaf.map _ x) =
      X.germToFunctionField (V ⊓ U) (X.presheaf.map _ u)
  rw [germToFunctionField_restrict (homOfLE (inf_le_left : V ⊓ U ≤ V)) t,
    germToFunctionField_restrict (homOfLE (inf_le_right : V ⊓ U ≤ U)) x,
    germToFunctionField_restrict (homOfLE (inf_le_left : V ⊓ U ≤ V)) u, htF, huF]

#print axioms abVar_orderTwo_localParameter

end

end HDec.CMBranch.CMjBridges
