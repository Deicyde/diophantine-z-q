import ZInQKernel.Contrib.RC53Assist.CentralUniversal.CoefficientComplex
import ZInQKernel.Contrib.RC53Assist.CentralUniversal.GenuineObjects
import ZInQKernel.Contrib.RC53Assist.CentralUniversal.DiscreteSelmer
import ZInQKernel.Contrib.RC53Assist.CentralSelmer.QuadraticDescentPlug

/-!
# Universal coefficients for the genuine quadratic Selmer group

The remaining arithmetic inputs are finite generation of compact Kummer
cohomology in degrees one and two, and the coefficient/Kummer comparison of
complexes. The latter is a cochain comparison after canonical truncation; it
contains no divisible-group map, no corank assertion, and no defect bound.

The universal-coefficient map, its injectivity, its exact torsion cokernel,
the integral-basis coordinates, and the rational-basis identification are
constructed from those inputs. The same integral free-part basis supplies
both kinds of coordinates.
-/

noncomputable section

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Manuscript.RC53Assist.CentralUniversal

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ZInQ.Manuscript.RC53Assist.CentralKummer
open ZInQ.Manuscript.RC53Assist.CentralSelmer
open ZInQ.Manuscript.RC53Assist.QuadraticDescent
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.BaseZeroLimit
open scoped TensorProduct

/-- Forget only the integral coefficient scalars, keeping the actual complex. -/
def integerCoefficientComplex (C : CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ) :
    CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  ((ModuleCat.restrictScalars (Int.castRingHom ℤ_[2])).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj C

/-- Restriction of scalars commutes with cohomology. -/
def integerHomologyEquiv (C : CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ) (n : ℤ) :
    (integerCoefficientComplex C).homology n ≃+ C.homology n :=
  (ShortComplex.mapHomologyIso (C.sc n)
    (ModuleCat.restrictScalars (Int.castRingHom ℤ_[2]))).toLinearEquiv.toAddEquiv

variable (ℓ : ℕ) (k : ℤ) [(Ecurve ℓ).IsElliptic]
  (S : Set (HeightOneSpectrum (𝓞 (QuadraticField k))))
  (hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S
    ((Ecurve ℓ).baseChange (QuadraticField k)) (2 ^ n))

/-- The precise finite-generation input supplied by perfection of the compact Kummer complex. -/
structure KummerCohomologyFinite : Prop where
  finite_one : Module.Finite ℤ_[2] ((arithmeticCompactComplex ℓ k S hFull).homology 1)
  finite_two : Module.Finite ℤ_[2] ((arithmeticCompactComplex ℓ k S hFull).homology 2)

/-- The coefficient quotient of the specified genuine compact complex. -/
abbrev arithmeticCoefficientComplex : CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ :=
  coefficientQuotientComplex (arithmeticCompactComplex ℓ k S hFull)

/-- The standard coefficient and local-Kummer comparison, retaining degrees zero and one.
Its source and target are genuine, fixed complexes. No map from a divisible group and no
bounded-defect or dimension statement is an input. -/
structure KummerCoefficientComparison where
  finite_support : S.Finite
  comparison : (integerCoefficientComplex (arithmeticCoefficientComplex ℓ k S hFull)).truncLE 1 ⟶
    discreteSelmerComplex ℓ k
  quasiIso : QuasiIso comparison

variable {ℓ k S hFull} in
/-- The Selmer identification induced by the specified cochain comparison. -/
def KummerCoefficientComparison.selmerEquiv
    (I : KummerCoefficientComparison ℓ k S hFull) :
    (arithmeticCoefficientComplex ℓ k S hFull).homology 1 ≃+ SelK ℓ k := by
  haveI : QuasiIso I.comparison := I.quasiIso
  let C := integerCoefficientComplex (arithmeticCoefficientComplex ℓ k S hFull)
  exact (integerHomologyEquiv (arithmeticCoefficientComplex ℓ k S hFull) 1).symm.trans
    ((asIso (HomologicalComplex.homologyMap (C.ιTruncLE 1) 1)).toLinearEquiv.toAddEquiv.symm.trans
      ((asIso (HomologicalComplex.homologyMap I.comparison 1)).toLinearEquiv.toAddEquiv.trans
        (discreteSelmerHomologyEquiv ℓ k)))

/-- The manuscript's map, with the tensor factors in its stated order. -/
def arithmeticUniversalCoefficientMap (I : KummerCoefficientComparison ℓ k S hFull) :
    ((arithmeticCompactComplex ℓ k S hFull).homology 1 ⊗[ℤ_[2]] Q2Z2) →+ SelK ℓ k :=
  (I.selmerEquiv).toAddMonoidHom.comp
    ((universalCoefficientMap (arithmeticCompactComplex ℓ k S hFull)).toAddMonoidHom.comp
      (TensorProduct.comm ℤ_[2] ((arithmeticCompactComplex ℓ k S hFull).homology 1)
        Q2Z2).toAddMonoidHom)

/-- The Selmer connecting map with target the actual second-cohomology torsion. -/
def arithmeticSelmerConnecting (I : KummerCoefficientComparison ℓ k S hFull) :
    SelK ℓ k →+ Submodule.torsion ℤ_[2] ((arithmeticCompactComplex ℓ k S hFull).homology 2) :=
  (coefficientTorsionConnecting (arithmeticCompactComplex ℓ k S hFull)).toAddMonoidHom.comp
    I.selmerEquiv.symm.toAddMonoidHom

/-- The rank is fixed by the integral cohomology, independently of all comparison choices. -/
abbrev arithmeticRank : ℕ :=
  Module.finrank ℤ_[2] (FreePart ((arithmeticCompactComplex ℓ k S hFull).homology 1))

/-- A basis of the actual integral free quotient. -/
def arithmeticFreeBasis (F : KummerCohomologyFinite ℓ k S hFull) :
    Module.Basis (Fin (arithmeticRank ℓ k S hFull)) ℤ_[2]
      (FreePart ((arithmeticCompactComplex ℓ k S hFull).homology 1)) := by
  have := F.finite_one
  exact freePartBasis _

/-- Divisible coordinates induced by that integral basis. -/
def arithmeticDivisibleCoordinates (F : KummerCohomologyFinite ℓ k S hFull) :
    Q2Z2 ⊗[ℤ_[2]] (arithmeticCompactComplex ℓ k S hFull).homology 1 ≃ₗ[ℤ_[2]]
      (Fin (arithmeticRank ℓ k S hFull) → Q2Z2) := by
  have := F.finite_one
  exact divisibleCoordinates _

/-- The rational identification is induced by flat base change and that same integral basis. -/
def arithmeticRationalH1Equiv (F : KummerCohomologyFinite ℓ k S hFull) :
    (arithmeticRationalComplex ℓ k S hFull).homology 1 ≃ₗ[ℚ_[2]]
      (Fin (arithmeticRank ℓ k S hFull) → ℚ_[2]) := by
  have := F.finite_one
  exact (rationalKummerHomologyIso S ((Ecurve ℓ).baseChange (QuadraticField k)) hFull 1).toLinearEquiv.trans
    (rationalCoordinates ((arithmeticCompactComplex ℓ k S hFull).homology 1))

/-- The basis identifies the prescribed divisible domain with the genuine cohomology tensor. -/
def arithmeticBasisToTensor (F : KummerCohomologyFinite ℓ k S hFull) :
    (Fin (arithmeticRank ℓ k S hFull) → Q2Z2) ≃+
      ((arithmeticCompactComplex ℓ k S hFull).homology 1 ⊗[ℤ_[2]] Q2Z2) :=
  ((arithmeticDivisibleCoordinates ℓ k S hFull F).symm.trans
    (TensorProduct.comm ℤ_[2] Q2Z2 ((arithmeticCompactComplex ℓ k S hFull).homology 1))).toAddEquiv

/-- The required map is the universal-coefficient map in integral free-part coordinates. -/
def arithmetic_j (I : KummerCoefficientComparison ℓ k S hFull)
    (F : KummerCohomologyFinite ℓ k S hFull) :
    (Fin (arithmeticRank ℓ k S hFull) → Q2Z2) →+ SelK ℓ k :=
  (arithmeticUniversalCoefficientMap ℓ k S hFull I).comp
    (arithmeticBasisToTensor ℓ k S hFull F).toAddMonoidHom

/-- The universal map is the coefficient-quotient formula on every pure tensor. -/
theorem arithmeticUniversalCoefficientMap_formula (I : KummerCoefficientComparison ℓ k S hFull)
    (q : ℚ_[2]) (x : (arithmeticCompactComplex ℓ k S hFull).homology 1) :
    arithmeticUniversalCoefficientMap ℓ k S hFull I (x ⊗ₜ[ℤ_[2]] divisibleQuotient q) =
      I.selmerEquiv (rationalToDivisible (arithmeticCompactComplex ℓ k S hFull)
        (q ⊗ₜ[ℤ_[2]] x)) := by
  change I.selmerEquiv
    (universalCoefficientMap (arithmeticCompactComplex ℓ k S hFull)
      (divisibleQuotient q ⊗ₜ[ℤ_[2]] x)) = _
  exact congrArg I.selmerEquiv (universalTensorMap_tmul _ _ _ q x)

/-- Exactness of the universal-coefficient map and the actual torsion connecting map. -/
theorem arithmeticUniversalCoefficient_exact (I : KummerCoefficientComparison ℓ k S hFull) :
    Function.Exact (arithmeticUniversalCoefficientMap ℓ k S hFull I)
      (arithmeticSelmerConnecting ℓ k S hFull I) :=
  exact_transport_addEquiv
    (universalCoefficientMap (arithmeticCompactComplex ℓ k S hFull)).toAddMonoidHom
    (coefficientTorsionConnecting (arithmeticCompactComplex ℓ k S hFull)).toAddMonoidHom
    (TensorProduct.comm ℤ_[2] ((arithmeticCompactComplex ℓ k S hFull).homology 1) Q2Z2).toAddEquiv
    I.selmerEquiv (universalCoefficient_exact _)

/-- No kernel is lost in the genuine universal-coefficient map. -/
theorem arithmeticUniversalCoefficientMap_injective (I : KummerCoefficientComparison ℓ k S hFull) :
    Function.Injective (arithmeticUniversalCoefficientMap ℓ k S hFull I) :=
  I.selmerEquiv.injective.comp
    ((universalCoefficientMap_injective (arithmeticCompactComplex ℓ k S hFull)).comp
      (TensorProduct.comm ℤ_[2] ((arithmeticCompactComplex ℓ k S hFull).homology 1) Q2Z2).injective)

/-- Every degree-two torsion class is an actual Selmer connecting class. -/
theorem arithmeticSelmerConnecting_surjective (I : KummerCoefficientComparison ℓ k S hFull) :
    Function.Surjective (arithmeticSelmerConnecting ℓ k S hFull I) := by
  intro y
  obtain ⟨x, hx⟩ := coefficientTorsionConnecting_surjective (arithmeticCompactComplex ℓ k S hFull) y
  refine ⟨I.selmerEquiv x, ?_⟩
  change coefficientTorsionConnecting (arithmeticCompactComplex ℓ k S hFull)
    (I.selmerEquiv.symm (I.selmerEquiv x)) = y
  rw [AddEquiv.symm_apply_apply]
  exact hx

/-- In coordinates, the required map is the universal map through the actual integral basis. -/
theorem arithmetic_j_apply (I : KummerCoefficientComparison ℓ k S hFull)
    (F : KummerCohomologyFinite ℓ k S hFull)
    (x : Fin (arithmeticRank ℓ k S hFull) → Q2Z2) :
    arithmetic_j ℓ k S hFull I F x = I.selmerEquiv
      (universalCoefficientMap (arithmeticCompactComplex ℓ k S hFull)
        ((arithmeticDivisibleCoordinates ℓ k S hFull F).symm x)) := by
  change I.selmerEquiv
    (universalCoefficientMap (arithmeticCompactComplex ℓ k S hFull)
      ((TensorProduct.comm ℤ_[2] ((arithmeticCompactComplex ℓ k S hFull).homology 1) Q2Z2)
        ((TensorProduct.comm ℤ_[2] ((arithmeticCompactComplex ℓ k S hFull).homology 1) Q2Z2).symm
          ((arithmeticDivisibleCoordinates ℓ k S hFull F).symm x)))) = _
  rw [LinearEquiv.apply_symm_apply]

/-- The coordinate expression as transport by the two specified equivalences. -/
theorem arithmetic_j_as_transport (I : KummerCoefficientComparison ℓ k S hFull)
    (F : KummerCohomologyFinite ℓ k S hFull) :
    arithmetic_j ℓ k S hFull I F = I.selmerEquiv.toAddMonoidHom.comp
      ((universalCoefficientMap (arithmeticCompactComplex ℓ k S hFull)).toAddMonoidHom.comp
        (arithmeticDivisibleCoordinates ℓ k S hFull F).symm.toAddMonoidHom) := by
  apply AddMonoidHom.ext
  intro x
  exact arithmetic_j_apply ℓ k S hFull I F x

/-- The required coordinate map is injective. -/
theorem arithmetic_j_injective (I : KummerCoefficientComparison ℓ k S hFull)
    (F : KummerCohomologyFinite ℓ k S hFull) :
    Function.Injective (arithmetic_j ℓ k S hFull I F) :=
  (arithmeticUniversalCoefficientMap_injective ℓ k S hFull I).comp
    (arithmeticBasisToTensor ℓ k S hFull F).injective

/-- The coordinate map has the exact second-cohomology torsion cokernel. -/
theorem arithmetic_j_exact (I : KummerCoefficientComparison ℓ k S hFull)
    (F : KummerCohomologyFinite ℓ k S hFull) :
    Function.Exact (arithmetic_j ℓ k S hFull I F) (arithmeticSelmerConnecting ℓ k S hFull I) := by
  rw [arithmetic_j_as_transport]
  exact exact_transport_addEquiv
    (universalCoefficientMap (arithmeticCompactComplex ℓ k S hFull)).toAddMonoidHom
    (coefficientTorsionConnecting (arithmeticCompactComplex ℓ k S hFull)).toAddMonoidHom
    (arithmeticDivisibleCoordinates ℓ k S hFull F).symm.toAddEquiv I.selmerEquiv
    (universalCoefficient_exact _)

/-- Its actual cokernel, not a freely chosen finite group, is second integral cohomology torsion. -/
def arithmetic_j_cokernelEquiv (I : KummerCoefficientComparison ℓ k S hFull)
    (F : KummerCohomologyFinite ℓ k S hFull) :
    (SelK ℓ k ⧸ (arithmetic_j ℓ k S hFull I F).range) ≃+
      Submodule.torsion ℤ_[2] ((arithmeticCompactComplex ℓ k S hFull).homology 2) :=
  QuotientAddGroup.liftEquiv (arithmetic_j ℓ k S hFull I F).range
    (arithmeticSelmerConnecting_surjective ℓ k S hFull I) (by
      ext y
      change (∃ x, arithmetic_j ℓ k S hFull I F x = y) ↔
        arithmeticSelmerConnecting ℓ k S hFull I y = 0
      exact (arithmetic_j_exact ℓ k S hFull I F y).symm)

/-- A fixed power of two kills the cokernel of the required map. -/
theorem arithmetic_j_coker_two_power (I : KummerCoefficientComparison ℓ k S hFull)
    (F : KummerCohomologyFinite ℓ k S hFull) :
    ∃ n : ℕ, ∀ y : SelK ℓ k, ∃ x,
      arithmetic_j ℓ k S hFull I F x = (2 ^ n : ℕ) • y := by
  have := F.finite_two
  obtain ⟨n, hn⟩ := universalCoefficientMap_coker_two_power (arithmeticCompactComplex ℓ k S hFull)
  refine ⟨n, ?_⟩
  rw [arithmetic_j_as_transport]
  exact coker_transport_addEquiv
    (universalCoefficientMap (arithmeticCompactComplex ℓ k S hFull)).toAddMonoidHom
    (arithmeticDivisibleCoordinates ℓ k S hFull F).symm.toAddEquiv I.selmerEquiv (2 ^ n) hn

/-- The required bounded-defects proof: the kernel is zero and the cokernel has a fixed two-power bound. -/
theorem arithmetic_j_boundedDefects (I : KummerCoefficientComparison ℓ k S hFull)
    (F : KummerCohomologyFinite ℓ k S hFull) : BoundedDefects (arithmetic_j ℓ k S hFull I F) := by
  obtain ⟨n, hn⟩ := arithmetic_j_coker_two_power ℓ k S hFull I F
  refine ⟨1, 2 ^ n, one_ne_zero, pow_ne_zero n two_ne_zero, fun x hx => ?_, hn⟩
  have hx0 : x = 0 := arithmetic_j_injective ℓ k S hFull I F (hx.trans (map_zero _).symm)
  simpa only [one_nsmul] using hx0

/-- One and the same nonzero integer kills both defects. -/
theorem arithmetic_j_two_power_defects (I : KummerCoefficientComparison ℓ k S hFull)
    (F : KummerCohomologyFinite ℓ k S hFull) :
    ∃ n : ℕ, (2 ^ n : ℕ) ≠ 0 ∧
      (∀ x, arithmetic_j ℓ k S hFull I F x = 0 → (2 ^ n : ℕ) • x = 0) ∧
      (∀ y : SelK ℓ k, ∃ x, arithmetic_j ℓ k S hFull I F x = (2 ^ n : ℕ) • y) := by
  obtain ⟨n, hn⟩ := arithmetic_j_coker_two_power ℓ k S hFull I F
  refine ⟨n, pow_ne_zero n two_ne_zero, fun x hx => ?_, hn⟩
  have hx0 : x = 0 := arithmetic_j_injective ℓ k S hFull I F (hx.trans (map_zero _).symm)
  rw [hx0, nsmul_zero]

/-- The coordinate map on a genuine cohomology tensor uses exactly the integral free-part basis. -/
theorem arithmetic_j_on_tensor (I : KummerCoefficientComparison ℓ k S hFull)
    (F : KummerCohomologyFinite ℓ k S hFull)
    (x : (arithmeticCompactComplex ℓ k S hFull).homology 1) (d : Q2Z2) :
    arithmetic_j ℓ k S hFull I F
        (fun i => (arithmeticFreeBasis ℓ k S hFull F).equivFun
          ((Submodule.torsion ℤ_[2] ((arithmeticCompactComplex ℓ k S hFull).homology 1)).mkQ x) i • d) =
      arithmeticUniversalCoefficientMap ℓ k S hFull I (x ⊗ₜ[ℤ_[2]] d) := by
  have := F.finite_one
  have hc : arithmeticDivisibleCoordinates ℓ k S hFull F (d ⊗ₜ[ℤ_[2]] x) =
      (fun i => (arithmeticFreeBasis ℓ k S hFull F).equivFun
        ((Submodule.torsion ℤ_[2] ((arithmeticCompactComplex ℓ k S hFull).homology 1)).mkQ x) i • d) := by
    funext i
    exact divisibleCoordinates_tmul _ d x i
  rw [arithmetic_j_apply, ← hc, LinearEquiv.symm_apply_apply]
  rfl

/-- The rational identification is the flat-base-change identification in that very same basis. -/
theorem arithmeticRationalH1Equiv_on_tensor (F : KummerCohomologyFinite ℓ k S hFull)
    (q : ℚ_[2]) (x : (arithmeticCompactComplex ℓ k S hFull).homology 1)
    (i : Fin (arithmeticRank ℓ k S hFull)) :
    arithmeticRationalH1Equiv ℓ k S hFull F
        ((rationalKummerHomologyIso S ((Ecurve ℓ).baseChange (QuadraticField k)) hFull 1).inv.hom
          (q ⊗ₜ[ℤ_[2]] x)) i =
      ((arithmeticFreeBasis ℓ k S hFull F).equivFun
        ((Submodule.torsion ℤ_[2] ((arithmeticCompactComplex ℓ k S hFull).homology 1)).mkQ x) i : ℚ_[2]) * q := by
  have := F.finite_one
  let e := rationalKummerHomologyIso S ((Ecurve ℓ).baseChange (QuadraticField k)) hFull 1
  have h := congrArg (fun f => f.hom (q ⊗ₜ[ℤ_[2]] x)) e.inv_hom_id
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at h
  change rationalCoordinates ((arithmeticCompactComplex ℓ k S hFull).homology 1)
    (e.hom.hom (e.inv.hom (q ⊗ₜ[ℤ_[2]] x))) i = _
  rw [h]
  exact rationalCoordinates_tmul _ q x i

/-- The number of coordinates is the genuine rational first-cohomology dimension. -/
theorem arithmeticRank_eq_rational_finrank (F : KummerCohomologyFinite ℓ k S hFull) :
    arithmeticRank ℓ k S hFull =
      Module.finrank ℚ_[2] ((arithmeticRationalComplex ℓ k S hFull).homology 1) := by
  rw [(arithmeticRationalH1Equiv ℓ k S hFull F).finrank_eq, Module.finrank_fin_fun]

/-- The rational Tate comparison is induced by the actual universal-coefficient map. -/
def arithmeticRatTateEquiv (I : KummerCoefficientComparison ℓ k S hFull)
    (F : KummerCohomologyFinite ℓ k S hFull) :
    (arithmeticRationalComplex ℓ k S hFull).homology 1 ≃ₗ[ℚ_[2]] RatTate (SelK ℓ k) :=
  universalCoefficientsRatTateEquiv (arithmeticRationalH1Equiv ℓ k S hFull F)
    (arithmetic_j ℓ k S hFull I F) (arithmetic_j_boundedDefects ℓ k S hFull I F)

/-- Under the full corank-one hypothesis the actual compact Kummer free rank is one. -/
theorem arithmeticRank_eq_one (hk : ¬ IsSquare (k : ℚ))
    (I : KummerCoefficientComparison ℓ k S hFull) (F : KummerCohomologyFinite ℓ k S hFull)
    (hSel : SelmerCorankOneOverK ℓ k) : arithmeticRank ℓ k S hFull = 1 := by
  rw [arithmeticRank_eq_rational_finrank ℓ k S hFull F,
    (arithmeticRatTateEquiv ℓ k S hFull I F).finrank_eq,
    finrank_ratTate_selK_eq_one ℓ hk hSel]

end ZInQ.Manuscript.RC53Assist.CentralUniversal
