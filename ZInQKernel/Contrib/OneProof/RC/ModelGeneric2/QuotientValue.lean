import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.QuotientInvariant
import ZInQKernel.Contrib.OneProof.ModularEquationGeneric

/-! # The quotient j-invariant of a cyclic pair -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric2

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1500000

open LeafModCurves ModelGeneric ModularCurve
open ZInQ.RLeaf (galPt addOrderOf_galPt)
open ZInQ.Contrib.CloudB2X0Transitive (ejBarIsElliptic ejBar_j)

variable {N : ℕ} [NeZero N] (h₂ : 2 ≤ N)

private theorem ejBar_transcendental :
    Transcendental ℚ (letI := ejBarIsElliptic; EjBar.j) := by
  rw [ejBar_j, transcendental_algebraMap_iff (algebraMap Qj Kbar).injective]
  convert RatFunc.transcendental_X (K := ℚ)
  exact Subsingleton.elim _ _

/-- The geometric quotient values are in bijection with the roots of the modular
polynomial at the first coordinate of the actual generic elliptic curve. -/
theorem genericQuotientValue_bijOn (data : ModularPolynomialData N) :
    Set.BijOn (genericQuotientValue h₂) Set.univ
      {y | (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Kbar)
        (algebraMap Qj Kbar RatFunc.X))).IsRoot y} := by
  letI := ejBarIsElliptic
  letI : CharZero Kbar := ZInQ.Contrib.CloudB2X0Transitive.charZero_Kbar
  have hbij := FltCqj2.cyclicQuotientJBijOn_proof ℚ N data Kbar
    (Nat.cast_ne_zero.mpr (NeZero.ne N)) EjBar ejBar_transcendental
  rw [ejBar_j] at hbij
  refine ⟨fun x _ => hbij.mapsTo (genericJSubgroups h₂ x).property, ?_, ?_⟩
  · intro x _ y _ he
    exact (genericJSubgroups h₂).injective (Subtype.ext <|
      hbij.injOn (genericJSubgroups h₂ x).property (genericJSubgroups h₂ y).property he)
  · intro y hy
    obtain ⟨C, hC, hCy⟩ := hbij.surjOn hy
    let D : CyclicSubgroups EjBar.toAffine.Point N := ⟨C, hC⟩
    refine ⟨(genericJSubgroups h₂).symm D, Set.mem_univ _, ?_⟩
    change EjBar.cyclicQuotientJ ((genericJSubgroups h₂) ((genericJSubgroups h₂).symm D)).val N = y
    rw [Equiv.apply_symm_apply]
    exact hCy

/-- The Galois action on geometric points of the pinned rational j-fibre is transitive. -/
theorem genericJPoints_transitive (x y : Y0RationalGenericJ h₂ →ₐ[Qj] Kbar) :
    ∃ σ : Kbar ≃ₐ[Qj] Kbar, σ.toAlgHom.comp x = y := by
  obtain ⟨P, hP⟩ := subgroupOfGenerator_surjective (genericJSubgroups h₂ x)
  obtain ⟨T, hT⟩ := subgroupOfGenerator_surjective (genericJSubgroups h₂ y)
  obtain ⟨σ, hσ⟩ := FltCqj2.x0Transitive_proof N P.val T.val (by omega) P.property T.property
  refine ⟨σ, (genericJSubgroups h₂).injective ?_⟩
  rw [genericJSubgroups_galois, ← hP, ← hT]
  apply Subtype.ext
  change (AddSubgroup.zmultiples P.val).map (Affine.Point.mapEquiv Ej σ).toAddMonoidHom =
    AddSubgroup.zmultiples T.val
  rw [AddMonoidHom.map_zmultiples]
  have hle : AddSubgroup.zmultiples (galPt σ P.val) ≤ AddSubgroup.zmultiples T.val :=
    AddSubgroup.zmultiples_le.mpr hσ
  letI : Finite (AddSubgroup.zmultiples T.val) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zmultiples, T.property]; exact NeZero.ne N)
  apply AddSubgroup.eq_of_le_of_card_ge hle
  rw [Nat.card_zmultiples, Nat.card_zmultiples, addOrderOf_galPt, P.property, T.property]

/-- Any geometric evaluation of the pinned generic algebra is injective. Choose
a conjugate evaluation for each point, then use separation by geometric points. -/
theorem genericJPoint_injective (x : Y0RationalGenericJ h₂ →ₐ[Qj] Kbar) :
    Function.Injective x := by
  letI := Y0RationalGenericJ_finite h₂
  letI := Y0RationalGenericJ_reduced h₂
  intro a b eq
  apply geometricPoints_separate (K := Qj) (L := Kbar) a b
  intro y
  obtain ⟨σ, rfl⟩ := genericJPoints_transitive h₂ x y
  exact congrArg σ eq

/-- There are exactly `ψ(N)` geometric points of the pinned generic j-fibre. -/
theorem genericJPoints_card :
    Nat.card (Y0RationalGenericJ h₂ →ₐ[Qj] Kbar) = dedekindPsi N :=
  (Nat.card_congr (genericJSubgroups h₂)).trans (FltCqj.ncard_cyclic_ejBar N).1

/-- The pinned generic algebra is a field over the actual j-line. -/
@[instance_reducible] noncomputable def genericJField : Field (Y0RationalGenericJ h₂) := by
  letI := Y0RationalGenericJ_finite h₂
  have h : Nat.card (Y0RationalGenericJ h₂ →ₐ[Qj] Kbar) ≠ 0 := by
    rw [genericJPoints_card h₂]
    exact (FltCqj.dedekindPsi_pos N).ne'
  let x := (Nat.card_ne_zero.mp h).1.some
  letI := Function.Injective.isDomain x (genericJPoint_injective h₂ x)
  exact fieldOfFiniteDimensional Qj (Y0RationalGenericJ h₂)

/-- The generic field has degree `ψ(N)` over the j-line. -/
theorem genericJFinrank : Module.finrank Qj (Y0RationalGenericJ h₂) = dedekindPsi N := by
  letI := genericJField h₂
  letI := Y0RationalGenericJ_finite h₂
  letI : Algebra.IsSeparable Qj (Y0RationalGenericJ h₂) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  rw [← AlgHom.natCard_of_splits Qj (Y0RationalGenericJ h₂) Kbar (fun _ => IsAlgClosed.splits _)]
  exact genericJPoints_card h₂

/-- The modular polynomial with its coefficient variable evaluated at the first
coordinate of the rational j-line. -/
noncomputable def genericModularPolynomial (data : ModularPolynomialData N) : Polynomial Qj :=
  (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom ℚ))).map
    (algebraMap (Polynomial ℚ) Qj)

private theorem genericModularPolynomial_map (data : ModularPolynomialData N) :
    (genericModularPolynomial data).map (algebraMap Qj Kbar) =
      data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Kbar)
        (algebraMap Qj Kbar RatFunc.X)) := by
  rw [genericModularPolynomial, Polynomial.map_map, Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom,
    Polynomial.map_X, RatFunc.algebraMap_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

/-- The actual quotient invariant satisfies the modular polynomial in the pinned
generic algebra. -/
theorem genericQuotientJ_aeval (data : ModularPolynomialData N) :
    Polynomial.aeval (Y0RationalGenericQuotientJ h₂) (genericModularPolynomial data) = 0 := by
  letI := Y0RationalGenericJ_finite h₂
  letI := Y0RationalGenericJ_reduced h₂
  apply geometricPoints_separate (K := Qj) (L := Kbar)
  intro x
  rw [← Polynomial.aeval_algHom_apply, map_zero, Y0RationalGenericQuotientJ_eval,
    Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, genericModularPolynomial_map]
  exact (genericQuotientValue_bijOn h₂ data).mapsTo (Set.mem_univ x)

/-- The specialized modular polynomial is the minimal polynomial of the
actual quotient invariant in the pinned generic field. -/
theorem genericQuotientJ_minpoly (data : ModularPolynomialData N) :
    minpoly Qj (Y0RationalGenericQuotientJ h₂) = genericModularPolynomial data := by
  letI : Nontrivial (Y0RationalGenericJ h₂) :=
    (genericJField h₂).toDivisionRing.toNontrivial
  have hirr : Irreducible (genericModularPolynomial data) :=
    ModularPolynomialData.irreducible_map_ratFunc_of_natCast_ne_zero ℚ N data
      (Nat.cast_ne_zero.mpr (NeZero.ne N))
  have hmonic : (genericModularPolynomial data).Monic := (data.monic.map _).map _
  symm
  exact minpoly.eq_of_irreducible_of_monic
    (x := Y0RationalGenericQuotientJ h₂) hirr (genericQuotientJ_aeval h₂ data) hmonic

/-- The actual quotient invariant generates the pinned generic field over the
first j-coordinate. -/
theorem genericQuotientJ_adjoin (data : ModularPolynomialData N) :
    letI := genericJField h₂
    IntermediateField.adjoin Qj {Y0RationalGenericQuotientJ h₂} = ⊤ := by
  letI := genericJField h₂
  letI := Y0RationalGenericJ_finite h₂
  apply IntermediateField.eq_of_le_of_finrank_eq le_top
  rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite Qj _),
    IntermediateField.finrank_top', genericQuotientJ_minpoly h₂ data, genericJFinrank h₂]
  rw [genericModularPolynomial, (data.monic.map _).natDegree_map, data.monic.natDegree_map]
  exact data.natDegree_eq

#print axioms ejBar_transcendental
#print axioms genericQuotientValue_bijOn
#print axioms genericJPoints_transitive
#print axioms genericJPoint_injective
#print axioms genericJPoints_card
#print axioms genericJField
#print axioms genericJFinrank
#print axioms genericModularPolynomial
#print axioms genericModularPolynomial_map
#print axioms genericQuotientJ_aeval
#print axioms genericQuotientJ_minpoly
#print axioms genericQuotientJ_adjoin

end WeierstrassCurve.ModelLevels.ModelGeneric2
