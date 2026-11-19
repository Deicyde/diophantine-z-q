import ZInQKernel.Contrib.OneProof.R16Thm1
import ZInQKernel.Contrib.OneProof.BShStandardGeometry
import ZInQKernel.Contrib.OneProof.BShStandardField

/-! ON THE SPOT (c): the rational diamond action on the specified model and its Jacobian. -/

noncomputable section

namespace BShStandard

open scoped MatrixGroups
open AlgebraicGeometry CategoryTheory Filter UpperHalfPlane MonoidalCategory CartesianMonoidalCategory MonObj
open LeafModCurves PkgI3 PkgI3.AbVar AfTateLam ShimuraPointDict

set_option backward.isDefEq.respectTransparency false

variable {X : Over SpecQ} [IsIntegral X.left] {jX tX : X.left.functionField} {N : ℕ}
local notation "KX" => X.left.functionField

private abbrev valRing (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (τ : ℍ) :
    ValuationSubring KX :=
  finiteValuationSubring (fieldGerm hN hG τ) (fieldGerm_meromorphic hN hG τ)

private theorem atTau_eval (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) {τ : ℍ} {x : CPt X}
    (hx : AtTau N jX tX x τ) {a : KX} {c : ℂ} (ha : HasValue (fieldGerm hN hG τ a) c) :
    ∃ r : X.left.presheaf.stalk (complexMap x (IsLocalRing.closedPoint ℂ)),
      algebraMap _ KX r = a ∧ Scheme.stalkClosedPointTo (complexMap x) r = c := by
  obtain ⟨P, Q, hQ, rfl⟩ := exists_polynomial_fraction hG.1 a
  simp only [algEval_apply] at hQ ha ⊢
  exact regAt_iff_stalk.mp (hx P Q c hQ ((hasValue_fraction_iff hN hG τ P Q hQ c).mp ha))

private theorem stalk_hasValue (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) {τ : ℍ} {x : CPt X}
    (hx : AtTau N jX tX x τ)
    (r : X.left.presheaf.stalk (complexMap x (IsLocalRing.closedPoint ℂ))) :
    HasValue (fieldGerm hN hG τ (algebraMap _ KX r))
      (Scheme.stalkClosedPointTo (complexMap x) r) := by
  have hmem : algebraMap _ KX r ∈ finiteSubring (fieldGerm hN hG τ) := by
    by_contra h
    have hv := hasValue_inv_of_not_mem (fieldGerm hN hG τ) (fieldGerm_meromorphic hN hG τ) h
    obtain ⟨s, hs, h₀⟩ := atTau_eval hN hG hx hv
    have hn : algebraMap _ KX r ≠ 0 := fun hh => h (hh ▸ (finiteSubring _).zero_mem)
    have hrs : r * s = 1 := IsFractionRing.injective _ KX (by
      rw [map_mul, map_one, hs]
      exact mul_inv_cancel₀ hn)
    have := congrArg (Scheme.stalkClosedPointTo (complexMap x)).hom hrs
    simp [h₀] at this
  obtain ⟨c, hc⟩ := hmem
  obtain ⟨s, hs, hv⟩ := atTau_eval hN hG hx hc
  have hsr : s = r := IsFractionRing.injective _ KX hs
  rw [hsr] at hv
  rw [hv]
  exact hc

/-- Every model in the bridge has the correct diamond operators over ℚ. -/
theorem exists_diamonds (hN : 2 ≤ N) (hC : IsCurve X) (hG : IsX1Gen N X jX tX)
    {P₀ : RatPt X} {J : AbVar ℚ} {aj : X ⟶ J.X} (hJ : IsJacobian X P₀ J aj) :
    ∃ δ : (ZMod N)ˣ → AbVar.End J, ∀ d : (ZMod N)ˣ, IsDiamond N jX tX aj d (δ d) := by
  suffices ∀ d : (ZMod N)ˣ, ∃ δ : AbVar.End J, IsDiamond N jX tX aj d δ from
    ⟨fun d => (this d).choose, fun d => (this d).choose_spec⟩
  intro d
  obtain ⟨φ, hφ⟩ := exists_diamond_fieldMap hN hG d
  letI : IsProper X.hom := hC.proper
  obtain ⟨f, hf⟩ := exists_extension hC (Spec.map (CommRingCat.ofHom φ) ≫ X.left.fromSpecFunctionField)
  obtain ⟨δ, hδ⟩ := exists_end_of_morphism hJ (f ≫ aj)
  refine ⟨δ, fun g hg hd τ τ' x x' z z' hx hx' hz hz' => ?_⟩
  have hp (σ : ℍ) (x z : CPt X) (hx : AtTau N jX tX x σ) (hz : AtTau N jX tX z (g • σ)) :
      x ≫ f = z := by
    let A := valRing hN hG σ
    let u := fieldGerm hN hG σ
    let e : A →+* ℂ := finiteValue u
    let qi : ℚ →+* KX := (Spec.preimage (X.left.fromSpecFunctionField ≫ X.hom)).hom
    let qg : ℚ →+* PuncturedGerm (σ : ℂ) :=
      (Germ.coeRingHom _).comp (RingHom.pi fun _ : ℂ => Rat.castHom ℂ)
    have hq : u.comp qi = qg := RingHom.ext_rat _ _
    let q : ℚ →+* A := qi.codRestrict A.toSubring (fun r => by
      refine ⟨(r : ℂ), ?_⟩
      change HasValue ((u.comp qi) r) (r : ℂ)
      rw [hq]
      exact tendsto_const_nhds)
    let i := algebraMap (X.left.presheaf.stalk (complexMap x (IsLocalRing.closedPoint ℂ))) KX
    let j := algebraMap (X.left.presheaf.stalk (complexMap z (IsLocalRing.closedPoint ℂ))) KX
    let vx := i.codRestrict A.toSubring (fun r => ⟨_, stalk_hasValue hN hG hx r⟩)
    let vz := (φ.comp j).codRestrict A.toSubring (fun r =>
      ⟨_, (hφ g hg hd σ _ _).mpr (stalk_hasValue hN hG hz r)⟩)
    refine point_eq_of_specialization hC f φ hf A q e vx vz rfl rfl ?_ ?_
    · ext r
      exact hasValue_unique (finiteValue_spec u (vx r)) (stalk_hasValue hN hG hx r)
    · ext r
      exact hasValue_unique (finiteValue_spec u (vz r))
        ((hφ g hg hd σ _ _).mpr (stalk_hasValue hN hG hz r))
  rw [hδ, ← Category.assoc, ← Category.assoc, hp τ x z hx hz, hp τ' x' z' hx' hz']

variable {J : AbVar ℚ} {aj : X ⟶ J.X}

/-- The unpointed trace of the prime correspondence evaluated on the `AtTau` points.
This is a property of a morphism to the Jacobian, before applying the Albanese property. -/
def IsPrimeTrace (jX tX : KX) (aj : X ⟶ J.X) (N p : ℕ) (F : X ⟶ J.X) : Prop :=
  ∀ (τ : ℍ) (x : CPt X) (y : Fin p → CPt X),
    AtTau N jX tX x τ → (∀ i, AtTau N jX tX (y i) (shiftDiv p i τ)) →
    (p ∣ N → x ≫ F = ∏ i, ajC aj (y i)) ∧
    (¬ p ∣ N → ∀ g : SL(2, ℤ), (N : ℤ) ∣ g 1 0 → (g 1 1 : ZMod N) = (p : ZMod N) →
      ∀ z : CPt X, AtTau N jX tX z (g • mulNat p τ) →
        x ≫ F = (∏ i, ajC aj (y i)) * ajC aj z)

/-- A prime trace gives the precise prime double-coset formula on differences. -/
theorem exists_hecke_of_trace {P₀ : RatPt X} (hJ : IsJacobian X P₀ J aj)
    {p : ℕ} {F : X ⟶ J.X} (hF : IsPrimeTrace jX tX aj N p F) :
    ∃ t : AbVar.End J, IsHeckeT N jX tX aj p t := by
  obtain ⟨t, ht⟩ := exists_end_of_morphism hJ F
  refine ⟨t, fun τ τ' x x' y y' hx hx' hy hy' => ⟨?_, ?_⟩⟩
  · intro hp
    rw [ht, (hF τ x y hx hy).1 hp, (hF τ' x' y' hx' hy').1 hp, Finset.prod_div_distrib]
  · intro hp g hg hd z z' hz hz'
    rw [ht, (hF τ x y hx hy).2 hp g hg hd z hz, (hF τ' x' y' hx' hy').2 hp g hg hd z' hz',
      Finset.prod_div_distrib]
    exact mul_div_mul_comm (α := J.Pt ℂ) _ _ _ _

/-- The prime trace morphisms are the remaining model-specific inputs to the row. -/
theorem bShStandardModel_of_primeTraces
    (hTrace : ∀ (N : ℕ), 2 ≤ N → ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
      IsCurve X → IsX1Gen N X jX tX →
      ∀ (P₀ : RatPt X) (J : AbVar ℚ) (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
        ∀ p : Nat.Primes, ∃ F : X ⟶ J.X, IsPrimeTrace jX tX aj N (p : ℕ) F) :
    R16Thm1.BShStandardModel := by
  intro N hN X _ jX tX hC hG P₀ J aj hJ
  obtain ⟨δ, hδ⟩ := exists_diamonds hN hC hG hJ
  have h (p : Nat.Primes) : ∃ t : AbVar.End J, IsHeckeT N jX tX aj (p : ℕ) t := by
    obtain ⟨F, hF⟩ := hTrace N hN X jX tX hC hG P₀ J aj hJ p
    exact exists_hecke_of_trace hJ hF
  exact ⟨fun p => (h p).choose, δ, fun p => (h p).choose_spec, hδ⟩

/-- The fixed bridge is also the original Hecke existence statement. -/
theorem heckeJ1DS_of_bShStandardModel (h : R16Thm1.BShStandardModel) : HeckeJ1DS := h

#print axioms atTau_eval
#print axioms stalk_hasValue
#print axioms exists_diamonds
#print axioms exists_hecke_of_trace
#print axioms bShStandardModel_of_primeTraces
#print axioms heckeJ1DS_of_bShStandardModel

end BShStandard
