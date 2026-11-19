import ZInQKernel.Contrib.OneProof.ShimuraPointDictField
import ZInQKernel.Contrib.OneProof.ShimuraPointDictGeometry
import ZInQKernel.Contrib.OneProof.ShimuraHeckeJ

/-! Existence and single valuedness for the exact `AtTau` test in the Shimura Hecke bridge. -/

noncomputable section

namespace ShimuraPointDict

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Filter
open LeafModCurves PkgI3 PkgI3.AbVar R16Thm1 AfTateLam AfTateLam.HeckePin
open ShimuraSteps

section Model

variable {N : ℕ} {X : Over SpecQ} [IsIntegral X.left] {jX tX : X.left.functionField}

local notation "KX" => X.left.functionField

private def tauValuation (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (τ : UpperHalfPlane) :
    ValuationSubring KX :=
  finiteValuationSubring (fieldGerm hN hG τ) (fieldGerm_meromorphic hN hG τ)

private def tauBaseMap (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (τ : UpperHalfPlane) :
    ℚ →+* tauValuation hN hG τ := by
  let i : ℚ →+* KX := (Spec.preimage
    (X.left.fromSpecStalk (genericPoint X.left) ≫ X.hom)).hom
  let k : ℚ →+* PuncturedGerm (τ : ℂ) := (Germ.coeRingHom _).comp
    ((RingHom.pi fun _ : ℂ => Rat.castHom ℂ))
  have h : (fieldGerm hN hG τ).comp i = k := RingHom.ext_rat _ _
  refine i.codRestrict (tauValuation hN hG τ).toSubring fun q => ?_
  refine ⟨(q : ℂ), ?_⟩
  change HasValue (((fieldGerm hN hG τ).comp i) q) (q : ℂ)
  rw [h]
  exact tendsto_const_nhds

private abbrev tauValue (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (τ : UpperHalfPlane) :
    tauValuation hN hG τ →+* ℂ :=
  finiteValue (fieldGerm hN hG τ)

/-- Every parameter gives a complex point for the exact `AtTau` predicate. -/
theorem exists_atTau (hN : 2 ≤ N) (hC : IsCurve X) (hG : IsX1Gen N X jX tX)
    (τ : UpperHalfPlane) : ∃ x : CPt X, AtTau N jX tX x τ := by
  obtain ⟨x, hx⟩ := exists_regAt_of_valuation (tauValuation hN hG τ) (tauBaseMap hN hG τ)
    hC (tauValue hN hG τ)
  use x
  intro P Q c hQ hc
  have hv := (hasValue_fraction_iff hN hG τ P Q hQ c).mpr hc
  let g : tauValuation hN hG τ := ⟨_, ⟨c, hv⟩⟩
  have he : tauValue hN hG τ g = c := hasValue_unique (finiteValue_spec _ g) hv
  exact he ▸ hx g

private theorem stalk_witness_of_hasValue (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX)
    {τ : UpperHalfPlane} {x : CPt X} (hx : AtTau N jX tX x τ) {g : KX} {c : ℂ}
    (hc : HasValue (fieldGerm hN hG τ g) c) :
    ∃ r : X.left.presheaf.stalk (complexMap x (IsLocalRing.closedPoint ℂ)),
      algebraMap _ KX r = g ∧ Scheme.stalkClosedPointTo (complexMap x) r = c := by
  obtain ⟨P, Q, hQ, rfl⟩ := exists_polynomial_fraction hG.1 g
  simp only [algEval_apply] at hQ hc ⊢
  exact regAt_iff_stalk.mp (hx P Q c hQ ((hasValue_fraction_iff hN hG τ P Q hQ c).mp hc))

private theorem stalk_mem_tauValuation (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX)
    {τ : UpperHalfPlane} {x : CPt X} (hx : AtTau N jX tX x τ)
    (r : X.left.presheaf.stalk (complexMap x (IsLocalRing.closedPoint ℂ))) :
    algebraMap _ KX r ∈ tauValuation hN hG τ := by
  let g := algebraMap _ KX r
  change g ∈ finiteSubring (fieldGerm hN hG τ)
  by_contra hg
  have hv := hasValue_inv_of_not_mem (fieldGerm hN hG τ) (fieldGerm_meromorphic hN hG τ) hg
  obtain ⟨s, hs, h₀⟩ := stalk_witness_of_hasValue hN hG hx hv
  have hne : g ≠ 0 := fun h => hg (h ▸ (finiteSubring _).zero_mem)
  have hrs : r * s = 1 := IsFractionRing.injective _ KX (by
    rw [map_mul, map_one, hs]
    exact mul_inv_cancel₀ hne)
  have := congrArg (Scheme.stalkClosedPointTo (complexMap x)).hom hrs
  simp [h₀] at this

private def stalkToTau (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) {τ : UpperHalfPlane}
    {x : CPt X} (hx : AtTau N jX tX x τ) :
    X.left.presheaf.stalk (complexMap x (IsLocalRing.closedPoint ℂ)) →+* tauValuation hN hG τ :=
  (algebraMap _ KX).codRestrict _ (stalk_mem_tauValuation hN hG hx)

private theorem tauValue_stalkToTau (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX)
    {τ : UpperHalfPlane} {x : CPt X} (hx : AtTau N jX tX x τ) :
    (tauValue hN hG τ).comp (stalkToTau hN hG hx) = (Scheme.stalkClosedPointTo (complexMap x)).hom := by
  ext r
  obtain ⟨s, hs, he⟩ := stalk_witness_of_hasValue hN hG hx
    (finiteValue_spec _ (stalkToTau hN hG hx r))
  have hr : s = r := IsFractionRing.injective _ KX hs
  exact hr ▸ he.symm

/-- Any two complex points satisfying the same `AtTau` test coincide. -/
theorem atTau_unique (hN : 2 ≤ N) (hC : IsCurve X) (hG : IsX1Gen N X jX tX) :
    ∀ (τ : UpperHalfPlane) (x y : CPt X), AtTau N jX tX x τ → AtTau N jX tX y τ → x = y := by
  intro τ x y hx hy
  exact point_eq_of_stalk_to_valuation (tauValuation hN hG τ) (tauBaseMap hN hG τ)
    hC (tauValue hN hG τ) (stalkToTau hN hG hx) (stalkToTau hN hG hy) rfl rfl
      (tauValue_stalkToTau hN hG hx) (tauValue_stalkToTau hN hG hy)

/-- Existence and uniqueness on each of the fixed models. -/
theorem existsUnique_atTau (hN : 2 ≤ N) (hC : IsCurve X) (hG : IsX1Gen N X jX tX)
    (τ : UpperHalfPlane) : ∃! x : CPt X, AtTau N jX tX x τ := by
  obtain ⟨x, hx⟩ := exists_atTau hN hC hG τ
  exact ⟨x, hx, fun y hy => atTau_unique hN hC hG τ y x hy hx⟩

end Model

/-- The exact global existence input to the composite action assembly. -/
theorem x1TauPoints : X1TauPoints := by
  intro N hN X inst jX tX hC hG τ
  exact exists_atTau hN hC hG τ

/-- The realized analytic points detect constancy on the fixed models. -/
theorem constOnTauPoints : ConstOnTauPoints :=
  ShimuraSteps.HeckeJ.constOnTauPoints_of_realization x1TauPoints

section Composite

variable {N : ℕ} {X : Over SpecQ} [IsIntegral X.left] {jX tX : X.left.functionField}
  {J : AbVar ℚ} {aj : X ⟶ J.X}

/-- The coprime composite action law for the fixed operators. -/
def CoprimeActionLaw (jX tX : X.left.functionField) (aj : X ⟶ J.X) (N : ℕ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → ∀ s t : AbVar.End J,
    IsXi (N := N) jX tX aj m s → IsXi (N := N) jX tX aj n t →
    IsXi (N := N) jX tX aj (m * n) (s * t)

/-- The good prime power action law for the fixed operators. -/
def GoodPrimeActionLaw (jX tX : X.left.functionField) (aj : X ⟶ J.X) (N : ℕ)
    (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J) : Prop :=
  ∀ (p : Nat.Primes) (hpN : ¬ (p : ℕ) ∣ N) (k : ℕ) (s t : AbVar.End J),
    IsXi (N := N) jX tX aj ((p : ℕ) ^ k) s →
    IsXi (N := N) jX tX aj ((p : ℕ) ^ (k + 1)) t →
    IsXi (N := N) jX tX aj ((p : ℕ) ^ (k + 2))
      (tp p * t - ((p : ℕ) : AbVar.End J) * δ (unitOf N p.2 hpN) * s)

/-- Per model, the only additional inputs to the composite action assembly are its two laws. -/
theorem exists_xi_of_compositeActions (hN : 2 ≤ N) (hC : IsCurve X)
    (hG : IsX1Gen N X jX tX) {P₀ : RatPt X} (hJ : IsJacobian X P₀ J aj)
    {tp : Nat.Primes → AbVar.End J} {δ : (ZMod N)ˣ → AbVar.End J}
    (htp : ∀ p : Nat.Primes, IsHeckeT N jX tX aj (p : ℕ) (tp p))
    (hmul : CoprimeActionLaw jX tX aj N) (hgood : GoodPrimeActionLaw jX tX aj N tp δ) :
    ∃ ξ : ℕ → AbVar.End J, XiAction (N := N) jX tX aj ξ ∧ HeckeRelations tp δ ξ :=
  ShimuraSteps.HeckeJ.exists_xi_of_compositeActions x1TauPoints hN hC hG hJ
    (atTau_unique hN hC hG) htp hmul hgood

end Composite

/-- With the geometry of the analytic points supplied, the composite action laws imply the
unchanged Hecke relations proposition. -/
theorem shimuraHeckeRelations_of_compositeActions
    (hlaws : ∀ (N : ℕ), 2 ≤ N →
      ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
      IsCurve X → IsX1Gen N X jX tX →
      ∀ (P₀ : RatPt X) (J : AbVar ℚ) (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
      ∀ (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J),
      (∀ p : Nat.Primes, IsHeckeT N jX tX aj (p : ℕ) (tp p)) →
      (∀ d : (ZMod N)ˣ, IsDiamond N jX tX aj d (δ d)) →
      CoprimeActionLaw jX tX aj N ∧ GoodPrimeActionLaw jX tX aj N tp δ) :
    ShimuraHeckeRelations := by
  intro N hN X inst jX tX hC hG P₀ J aj hJ tp δ htp hd
  obtain ⟨hmul, hgood⟩ := hlaws N hN X jX tX hC hG P₀ J aj hJ tp δ htp hd
  exact exists_xi_of_compositeActions hN hC hG hJ htp hmul hgood

#print axioms exists_atTau
#print axioms stalk_witness_of_hasValue
#print axioms stalk_mem_tauValuation
#print axioms tauValue_stalkToTau
#print axioms atTau_unique
#print axioms existsUnique_atTau
#print axioms x1TauPoints
#print axioms constOnTauPoints
#print axioms exists_xi_of_compositeActions
#print axioms shimuraHeckeRelations_of_compositeActions

end ShimuraPointDict
