import ZInQKernel.Contrib.RC53Assist.DerivedKummerActual.Resolution
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.ActualConsumer
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.HomologyFiniteDetection
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.CentralTraceHomotopy
import ZInQKernel.Contrib.RC53Assist.CentralKummer.RationalKummer
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.DetPairing
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.IotaWeil
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.CompKummer

/-!
# Integral local Kummer coefficients in a fixed global orientation

The finite Weil values of a single global Tate basis determine the local
roots-of-unity generators.  The local coefficient maps are the fixed
localization maps, followed by the canonical comparison of closures.

References: `diophantine_zq.tex`, Lemma `ex:arith-local-kummer`, lines
3413–3456; Silverman, *The Arithmetic of Elliptic Curves*, III.7–8;
Milne, *Arithmetic Duality Theorems*, I.2.3 and I.3.4.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.DKLocalAdapter

open CategoryTheory NumberField IsDedekindDomain TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.LambdaCoef ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.KummerMaps ZInQ.Manuscript.RC53Assist.CentralKummer
open ZInQ.Contrib.RC53Assist.IntegralDuality
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing

section CoefficientDictionary

attribute [local instance] levTop

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)

/-- Kind: definition; the two descriptions of the same compatible torsion
family, with the same two-adic scalar action (Silverman III.7). -/
def tateFamilyEquiv : TateS K S W ≃ₗ[ℤ_[2]] TateModule 2 (Pt K S W) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    apply TateModule.ext
    intro a
    change resN a r • (TateModule.proj a (show TateModule 2 (Pt K S W) from x)) =
      PadicInt.toZModPow a r • TateModule.proj a (show TateModule 2 (Pt K S W) from x)
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod (2 ^ a)), resN, ZMod.natCast_zmod_val]

/-- Kind: proved theorem; the dictionary preserves the inverse-limit
topology (Silverman III.7). -/
theorem tateFamilyEquiv_continuous : Continuous (tateFamilyEquiv (S := S) W) := by
  apply TateModule.continuous_iff.mpr
  intro a
  letI : TopologicalSpace (Lev K S W a) := ⊥
  letI : DiscreteTopology (Lev K S W a) := ⟨rfl⟩
  apply (IsLocallyConstant.iff_continuous _).mpr
  exact (continuous_apply a).comp continuous_subtype_val

variable [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

/-- Kind: definition; localization of every Tate level through the fixed
embedding of algebraic closures (Nekovář 5.1; tex 3413–3438). -/
def localAlgTateMap : TateS K S W →ₗ[ℤ_[2]]
    IntegralTateCoeff (Gloc K w)
      (PtAlg (w.adicCompletion K) (W.baseChange (w.adicCompletion K))) :=
  (TateModule.mapLinearMap (compPt (S := S) W w)).comp (tateFamilyEquiv W).toLinearMap

/-- Kind: proved theorem; localization has the prescribed finite
coefficient projection (tex 3413–3438). -/
theorem localAlgTateMap_projection (a : ℕ) (x : TateS K S W) :
    actualLevelEquiv (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) a
      (coefficientProjection (Gloc K w)
        (PtAlg (w.adicCompletion K) (W.baseChange (w.adicCompletion K))) a
          (localAlgTateMap W w x)) = compTors W (2 ^ a) w (projLev a x) := rfl

/-- Kind: definition; the inverse Tate dictionary is the same inverse at
every finite level (tex 3413–3438; Silverman III.7). -/
def localAlgTateEquiv : TateS K S W ≃ₗ[ℤ_[2]]
    IntegralTateCoeff (Gloc K w)
      (PtAlg (w.adicCompletion K) (W.baseChange (w.adicCompletion K))) where
  toFun := localAlgTateMap W w
  invFun y := tateOfLocal W ((HasFullTwoTorsion.full (K := K) (S := S) (W := W))) w
    (fun a => actualLevelEquiv (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) a
      (coefficientProjection (Gloc K w)
        (PtAlg (w.adicCompletion K) (W.baseChange (w.adicCompletion K))) a y))
    (fun a => congrArg Subtype.val (TateModule.proj_succ y a))
  left_inv x := by
    apply TateS.ext'
    intro a
    apply (compPt_injective (S := S) W w)
    have h := compTors_tateOfLocal W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w
      (fun a => actualLevelEquiv (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) a
        (coefficientProjection (Gloc K w)
          (PtAlg (w.adicCompletion K) (W.baseChange (w.adicCompletion K))) a
            (localAlgTateMap W w x)))
      (fun a => congrArg Subtype.val (TateModule.proj_succ (localAlgTateMap W w x) a)) a
    exact congrArg Subtype.val h
  right_inv y := by
    apply TateModule.ext
    intro a
    apply (actualLevelEquiv (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) a).injective
    change compTors W (2 ^ a) w (projLev a _) = _
    exact compTors_tateOfLocal W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w _
      (fun n => congrArg Subtype.val (TateModule.proj_succ y n)) a
  map_add' := (localAlgTateMap W w).map_add
  map_smul' := (localAlgTateMap W w).map_smul

/-- Kind: proved theorem; localization is continuous in the actual Tate
topologies (Silverman III.7; Nekovář 5.1). -/
theorem localAlgTateMap_continuous : Continuous (localAlgTateMap (S := S) W w) := by
  apply TateModule.continuous_iff.mpr
  intro a
  exact ((TateModule.isLocallyConstant_proj a).comp
    (TateModule.levelMap (compPt (S := S) W w) a)).comp_continuous
      (tateFamilyEquiv_continuous W)

/-- Kind: proved theorem; the fixed decomposition map gives the genuine
local Galois action (Nekovář 5.1; tex 3455–3463). -/
theorem localAlgTateMap_smul (σ : Gloc K w) (x : TateS K S W) :
    localAlgTateMap W w (locMap K S w σ • x) = σ • localAlgTateMap W w x := by
  apply TateModule.ext
  intro a
  apply Subtype.ext
  exact congrArg Subtype.val (compTors_smul W (2 ^ a) w σ (projLev a x))

/-- Kind: definition; the canonical separable-closure coefficient
isomorphism, on the actual Tate modules (tex 3413–3438). -/
def localClosureTateEquiv :
    IntegralTateCoeff (Gloc K w)
        (PtAlg (w.adicCompletion K) (W.baseChange (w.adicCompletion K))) ≃ₗ[ℤ_[2]]
      pointTate (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) where
  toFun := IntegralTransport.toSepCoefficients (w.adicCompletion K) (W.baseChange (w.adicCompletion K))
  invFun := IntegralTransport.toAlgCoefficients (w.adicCompletion K) (W.baseChange (w.adicCompletion K))
  left_inv := IntegralTransport.toAlg_toSep_coefficients (w.adicCompletion K) (W.baseChange (w.adicCompletion K))
  right_inv := IntegralTransport.toSep_toAlg_coefficients (w.adicCompletion K) (W.baseChange (w.adicCompletion K))
  map_add' := (IntegralTransport.toSepCoefficients (w.adicCompletion K)
    (W.baseChange (w.adicCompletion K))).map_add
  map_smul' := (IntegralTransport.toSepCoefficients (w.adicCompletion K)
    (W.baseChange (w.adicCompletion K))).map_smul

/-- Kind: definition; the actual local Tate coefficient dictionary used by
the integral Weil cup product (tex 3413–3438; Silverman III.7–8). -/
def localTateEquiv : TateS K S W ≃ₗ[ℤ_[2]]
    pointTate (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) :=
  (localAlgTateEquiv W w).trans (localClosureTateEquiv W w)

/-- Kind: proved theorem; the older and newer closure dictionaries are
literally the canonical inclusion (tex 3413–3438). -/
theorem compSepPt_eq (F : Type) [Field F] [CharZero F] (B : WeierstrassCurve F) :
    compSepPt F B = FiniteTrace.pointCoeffToAlg F B := by
  ext p
  obtain ⟨p, rfl⟩ := B.pointCoeffEquiv.surjective p
  rfl

/-- Kind: proved theorem; the torsion dictionary preserves that same
canonical closure comparison (tex 3413–3438). -/
theorem compSepTors_eq (F : Type) [Field F] [CharZero F] (B : WeierstrassCurve F) (a : ℕ) :
    compSepTors F B a = FiniteTrace.torsionCoeffToAlg F B a := by
  rw [compSepTors, FiniteTrace.torsionCoeffToAlg, compSepPt_eq]

/-- Kind: definition; the exact finite projection of the local Tate
coefficient dictionary (tex 3413–3438). -/
def localLevelEquiv (a : ℕ) : Lev K S W a ≃+
    (W.baseChange (w.adicCompletion K)).TorsionCoeff (2 ^ a) :=
  (compTorsEquiv W (2 ^ a) ((HasFullTwoTorsion.full (K := K) (S := S) (W := W)) a) w).trans
    (FiniteTrace.torsionCoeffToAlg (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) (2 ^ a)).symm

/-- Kind: proved theorem; projection of the integral dictionary is the
fixed finite decomposition and closure map (tex 3413–3438). -/
theorem localTateEquiv_projection (a : ℕ) (x : TateS K S W) :
    pointLevelEquiv (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) a
      (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K))
        (W.baseChange (w.adicCompletion K)).PointCoeff a (localTateEquiv (S := S) W w x)) =
      localLevelEquiv W w a (projLev a x) := rfl

/-- Kind: proved theorem; the integral coefficient dictionary is
continuous (Silverman III.7; Nekovář 5.1). -/
theorem localTateEquiv_continuous : Continuous (localTateEquiv (S := S) W w) :=
  (IntegralTransport.toSepCoefficients_continuous (w.adicCompletion K)
    (W.baseChange (w.adicCompletion K))).comp (localAlgTateMap_continuous W w)

/-- Kind: proved theorem; the integral dictionary intertwines the actual
local Galois actions (Nekovář 5.1; tex 3455–3463). -/
theorem localTateEquiv_smul (σ : Gloc K w) (x : TateS K S W) :
    localTateEquiv (S := S) W w (locMap K S w σ • x) =
      absoluteGaloisGroupRestrictEquiv (w.adicCompletion K) σ • localTateEquiv (S := S) W w x := by
  change IntegralTransport.toSepCoefficients (w.adicCompletion K) (W.baseChange (w.adicCompletion K))
    (localAlgTateMap W w (locMap K S w σ • x)) = _
  rw [localAlgTateMap_smul]
  have h := IntegralTransport.toSepCoefficients_smul (w.adicCompletion K)
    (W.baseChange (w.adicCompletion K))
      (absoluteGaloisGroupRestrictEquiv (w.adicCompletion K) σ) (localAlgTateMap W w x)
  rw [(absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).symm_apply_apply] at h
  exact h

end CoefficientDictionary

section OrientedScalarLine

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

include W in
/-- Kind: proved theorem; the roots needed to read finite Weil values
come from the same global full-torsion data (Silverman III.8.1). -/
theorem globalRoots (a : ℕ) : HasRootsOfUnity K S (2 ^ a) :=
  hasRootsOfUnity_of_fullTorsion K S W (2 ^ a)
    (HasFullTwoTorsion.full (K := K) (S := S) (W := W) a)

variable (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

/-- Kind: definition; the finite local logarithm is the global logarithm
transported through the fixed decomposition embedding (Silverman III.8.1;
Nekovář 5.1). It is used only to prove that the global Weil orientation
is a generator, not to choose unrelated local roots. -/
def orientedLocalLog (a : ℕ) :
    FiniteTateCoeff (AbsoluteGaloisGroup (w.adicCompletion K))
      (UnitsCoeff (w.adicCompletion K)) a ≃+ ZMod (2 ^ a) :=
  (actualMuLevelEquiv (w.adicCompletion K) a).trans
    ((compMu (w.adicCompletion K) (2 ^ a)).trans (iotaWeilLog (globalRoots (S := S) W a) w))

/-- Kind: proved theorem; the finite Tate dictionary followed by the
canonical closure inclusion is the original decomposition map
(tex 3413–3438). -/
theorem localLevelEquiv_toAlg (a : ℕ) (x : Lev K S W a) :
    compSepTors (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) (2 ^ a)
      (localLevelEquiv W w a x) = compTors W (2 ^ a) w x := by
  rw [compSepTors_eq]
  change FiniteTrace.torsionCoeffToAlg (w.adicCompletion K)
    (W.baseChange (w.adicCompletion K)) (2 ^ a)
      ((FiniteTrace.torsionCoeffToAlg (w.adicCompletion K)
        (W.baseChange (w.adicCompletion K)) (2 ^ a)).symm
          (compTorsEquiv W (2 ^ a) (HasFullTwoTorsion.full (K := K) (S := S) (W := W) a) w x)) = _
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- Kind: proved theorem; the actual local integral Weil value, at every
finite level, is the restriction of the same global Weil value
(Silverman III.8.1; tex 2798–2805, 5037). -/
theorem orientedLocalLog_pairing (a : ℕ) (x y : TateS K S W) :
    orientedLocalLog (S := S) W w a
      (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K))
        (UnitsCoeff (w.adicCompletion K)) a
          (coefficientWeilPairing (w.adicCompletion K) (W.baseChange (w.adicCompletion K))
            (localTateEquiv (S := S) W w x) (localTateEquiv (S := S) W w y))) =
      weilS W (globalRoots (S := S) W a) (projLev a x) (projLev a y) := by
  change iotaWeilLog (globalRoots (S := S) W a) w
    (compMu (w.adicCompletion K) (2 ^ a)
      (actualMuLevelEquiv (w.adicCompletion K) a
        (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K))
          (UnitsCoeff (w.adicCompletion K)) a
            (coefficientWeilPairing (w.adicCompletion K) (W.baseChange (w.adicCompletion K))
              (localTateEquiv (S := S) W w x) (localTateEquiv (S := S) W w y))))) = _
  rw [coefficientWeilPairing_projection, localTateEquiv_projection, localTateEquiv_projection]
  rw [← compWeil_compTors (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) (2 ^ a)
    (twoPower_isUnit (w.adicCompletion K) a), localLevelEquiv_toAlg, localLevelEquiv_toAlg]
  exact (iotaWeil_weilS_eq W (globalRoots (S := S) W a) w (projLev a x) (projLev a y)).symm

/-- Kind: definition; the integral local roots-of-unity generator is the
actual Weil value of the images of one fixed global Tate basis
(Silverman III.7–8; tex 5037). -/
def localMuGenerator : muTate (w.adicCompletion K) :=
  coefficientWeilPairing (w.adicCompletion K) (W.baseChange (w.adicCompletion K))
    (localTateEquiv (S := S) W w (tateBasis 0)) (localTateEquiv (S := S) W w (tateBasis 1))

/-- Kind: proved theorem; every finite value of the chosen local generator
has the same global normalization unit (Silverman III.8.1; tex 5037). -/
theorem orientedLocalLog_generator (a : ℕ) :
    orientedLocalLog (S := S) W w a
      (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K))
        (UnitsCoeff (w.adicCompletion K)) a (localMuGenerator (S := S) W w)) =
      weilS W (globalRoots (S := S) W a) (projLev a (tateBasis 0))
        (projLev a (tateBasis 1 : TateS K S W)) :=
  orientedLocalLog_pairing W w a _ _

/-- Kind: proved theorem; the generator is primitive at every finite
level by the source determinant/Weil unit theorem (Silverman III.8.1;
tex 5037). -/
theorem localMuGenerator_unit (a : ℕ) :
    IsUnit (orientedLocalLog (S := S) W w a
      (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K))
        (UnitsCoeff (w.adicCompletion K)) a (localMuGenerator (S := S) W w))) := by
  rw [orientedLocalLog_generator]
  exact isUnit_weilS_basis a (globalRoots (S := S) W a)

/-- Kind: proved theorem; the actual finite roots at every place are the
images of the very same global finite Weil value. This equality rules out
independent placewise normalization units (Nekovář 5.1; Silverman III.8.1;
tex 2798–2805, 5037). -/
theorem localMuGenerator_restriction (a : ℕ) :
    compMu (w.adicCompletion K) (2 ^ a)
      (actualMuLevelEquiv (w.adicCompletion K) a
        (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K))
          (UnitsCoeff (w.adicCompletion K)) a (localMuGenerator (S := S) W w))) =
      Additive.ofMul (restrictRootsOfUnity (iotaWeilEmb w) (2 ^ a)
        (weilBar W (2 ^ a) (inclTors (S := S) W (2 ^ a) (projLev a (tateBasis 0)))
          (inclTors (S := S) W (2 ^ a) (projLev a (tateBasis 1 : TateS K S W)))).toMul) := by
  apply (iotaWeilLog (globalRoots (S := S) W a) w).injective
  exact (orientedLocalLog_generator W w a).trans
    (iotaWeilLog_restrict (globalRoots (S := S) W a) w _).symm

/-- Kind: definition; the global scalar coordinate acts on the single
coherent local Weil generator (tex 2798–2805, 5037). -/
def localScalarMap : ℤ_[2] →ₗ[ℤ_[2]] muTate (w.adicCompletion K) :=
  LinearMap.toSpanSingleton ℤ_[2] (muTate (w.adicCompletion K)) (localMuGenerator (S := S) W w)

/-- Kind: proved theorem; the scalar map reduces by the canonical residue
map with the genuine global Weil unit (tex 5037; Silverman III.8.1). -/
theorem orientedLocalLog_scalar (a : ℕ) (r : ℤ_[2]) :
    orientedLocalLog (S := S) W w a
      (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K))
        (UnitsCoeff (w.adicCompletion K)) a (localScalarMap (S := S) W w r)) =
      PadicInt.toZModPow a r * orientedLocalLog (S := S) W w a
        (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K))
          (UnitsCoeff (w.adicCompletion K)) a (localMuGenerator (S := S) W w)) := by
  change orientedLocalLog (S := S) W w a
    (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K))
      (UnitsCoeff (w.adicCompletion K)) a (r • localMuGenerator (S := S) W w)) = _
  rw [coefficientProjection_scalar, ZMod.map_smul]
  rfl

/-- Kind: proved theorem; the scalar-line map is injective by joint finite
projection separation and the global Weil unit (tex 5037). -/
theorem localScalarMap_injective : Function.Injective (localScalarMap (S := S) W w) := by
  intro r s hrs
  apply PadicInt.ext_of_toZModPow.mp
  intro a
  have h := congrArg (fun z => orientedLocalLog (S := S) W w a
    (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K))
      (UnitsCoeff (w.adicCompletion K)) a z)) hrs
  rw [orientedLocalLog_scalar, orientedLocalLog_scalar] at h
  exact (localMuGenerator_unit (S := S) W w a).mul_left_inj.mp h

/-- Kind: proved theorem; the actual generator is onto at each finite
level, with no extra local root choice (Silverman III.8.1; tex 5037). -/
theorem localScalarMap_level_surjective (a : ℕ) :
    Function.Surjective (fun r : ℤ_[2] => coefficientProjection
      (AbsoluteGaloisGroup (w.adicCompletion K)) (UnitsCoeff (w.adicCompletion K)) a
        (localScalarMap (S := S) W w r)) := by
  intro z
  obtain ⟨u, hu⟩ := localMuGenerator_unit (S := S) W w a
  obtain ⟨r, hr⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow a)
    (orientedLocalLog (S := S) W w a z * ((u⁻¹ : (ZMod (2 ^ a))ˣ) : ZMod (2 ^ a)))
  refine ⟨r, (orientedLocalLog (S := S) W w a).injective ?_⟩
  rw [orientedLocalLog_scalar, hr, ← hu, mul_assoc, Units.inv_mul, mul_one]

/-- Kind: proved theorem; the coherent scalar-line map is continuous for
the genuine two-adic topologies (Silverman III.7). -/
theorem localScalarMap_continuous : Continuous (localScalarMap (S := S) W w) :=
  continuous_id.smul continuous_const

/-- Kind: proved theorem; compactness lifts the finite onto statements to
the actual integral roots-of-unity Tate module (Silverman III.7–8). -/
theorem localScalarMap_surjective : Function.Surjective (localScalarMap (S := S) W w) :=
  TateModule.surjective_of_forall_surjective_proj (localScalarMap_continuous W w)
    (localScalarMap_level_surjective W w)

/-- Kind: definition; the local integral scalar line is identified using
the globally coherent genuine Weil generator (tex 2798–2805, 5037). -/
def localScalarEquiv : ℤ_[2] ≃ₗ[ℤ_[2]] muTate (w.adicCompletion K) :=
  LinearEquiv.ofBijective (localScalarMap (S := S) W w)
    ⟨localScalarMap_injective W w, localScalarMap_surjective W w⟩

/-- Kind: proved theorem; the actual local integral Weil form is exactly
the restriction of the global determinant form in this orientation,
at every finite level and therefore integrally (tex 5037;
Silverman III.8.1). -/
theorem localWeil_eq_global_det (x y : TateS K S W) :
    coefficientWeilPairing (w.adicCompletion K) (W.baseChange (w.adicCompletion K))
      (localTateEquiv (S := S) W w x) (localTateEquiv (S := S) W w y) = localScalarEquiv (S := S) W w (detT x y) := by
  apply TateModule.ext
  intro a
  apply (orientedLocalLog (S := S) W w a).injective
  change orientedLocalLog (S := S) W w a
    (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K))
      (UnitsCoeff (w.adicCompletion K)) a
        (coefficientWeilPairing (w.adicCompletion K) (W.baseChange (w.adicCompletion K))
          (localTateEquiv (S := S) W w x) (localTateEquiv (S := S) W w y))) =
    orientedLocalLog (S := S) W w a
      (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K))
        (UnitsCoeff (w.adicCompletion K)) a (localScalarMap (S := S) W w (detT x y)))
  rw [orientedLocalLog_pairing, orientedLocalLog_scalar, orientedLocalLog_generator]
  exact (detT_mod_eq_weil a (globalRoots (S := S) W a) x y).symm

end OrientedScalarLine

section ContinuousLocalTransport

attribute [local instance] levTop

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

/-- Kind: proved theorem; the inverse decomposition dictionary is
continuous level by level (Nekovář 5.1; Silverman III.7). -/
theorem localAlgTateEquiv_symm_continuous :
    Continuous (localAlgTateEquiv (S := S) W w).symm := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro a
  change Continuous (fun y => (compTorsEquiv W (2 ^ a)
    (HasFullTwoTorsion.full (K := K) (S := S) (W := W) a) w).symm
      (actualLevelEquiv (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) a
        (coefficientProjection (Gloc K w)
          (PtAlg (w.adicCompletion K) (W.baseChange (w.adicCompletion K))) a y)))
  exact continuous_of_discreteTopology.comp
    (continuous_of_discreteTopology.comp (coefficientProjection_continuous (Gloc K w)
      (PtAlg (w.adicCompletion K) (W.baseChange (w.adicCompletion K))) a))

/-- Kind: proved theorem; the inverse actual local Tate isomorphism
preserves the genuine inverse-limit topology (tex 3413–3438). -/
theorem localTateEquiv_symm_continuous : Continuous (localTateEquiv (S := S) W w).symm :=
  (localAlgTateEquiv_symm_continuous W w).comp
    (IntegralTransport.toAlgCoefficients_continuous (w.adicCompletion K)
      (W.baseChange (w.adicCompletion K)))

/-- Kind: proved theorem; the integral Weil generator transforms by the
restriction of the global cyclotomic character, not by an independently
chosen local character (tex 2798–2805, 5037). -/
theorem localMuGenerator_smul (σ : Gloc K w) :
    absoluteGaloisGroupRestrictEquiv (w.adicCompletion K) σ • localMuGenerator (S := S) W w =
      (cyc2 K S (locMap K S w σ) : ℤ_[2]) • localMuGenerator (S := S) W w := by
  have h := coefficientWeilPairing_smul (w.adicCompletion K) (W.baseChange (w.adicCompletion K))
    (absoluteGaloisGroupRestrictEquiv (w.adicCompletion K) σ)
      (localTateEquiv (S := S) W w (tateBasis 0))
      (localTateEquiv (S := S) W w (tateBasis 1))
  rw [← localTateEquiv_smul W w σ, ← localTateEquiv_smul W w σ,
    localWeil_eq_global_det, detT_smul, detT_basis, mul_one] at h
  exact h.symm

/-- Kind: proved theorem; the oriented integral scalar identification is
Galois-equivariant for the restricted global cyclotomic action
(tex 2798–2805; Nekovář 5.1). -/
theorem localScalarEquiv_smul (σ : Gloc K w) (r : ℤ_[2]) :
    localScalarEquiv (S := S) W w ((cyc2 K S (locMap K S w σ) : ℤ_[2]) * r) =
      absoluteGaloisGroupRestrictEquiv (w.adicCompletion K) σ • localScalarEquiv (S := S) W w r := by
  change ((cyc2 K S (locMap K S w σ) : ℤ_[2]) * r) • localMuGenerator (S := S) W w =
    absoluteGaloisGroupRestrictEquiv (w.adicCompletion K) σ • (r • localMuGenerator (S := S) W w)
  calc
    _ = r • ((cyc2 K S (locMap K S w σ) : ℤ_[2]) • localMuGenerator (S := S) W w) := by
      rw [smul_smul, mul_comm]
    _ = r • (absoluteGaloisGroupRestrictEquiv (w.adicCompletion K) σ • localMuGenerator (S := S) W w) :=
      congrArg (fun z => r • z) (localMuGenerator_smul W w σ).symm
    _ = _ := (smul_comm _ _ _).symm

/-- Kind: proved theorem; the forward scalar isomorphism is continuous in
the actual two-adic topology (Silverman III.7). -/
theorem localScalarEquiv_continuous : Continuous (localScalarEquiv (S := S) W w) :=
  localScalarMap_continuous W w

/-- Kind: proved theorem; the inverse scalar-line isomorphism is
continuous by compactness and the Hausdorff inverse-limit topology
(Silverman III.7). -/
theorem localScalarEquiv_symm_continuous : Continuous (localScalarEquiv (S := S) W w).symm := by
  letI : T2Space (muTate (w.adicCompletion K)) :=
    inferInstanceAs (T2Space (TateModule 2 (UnitsCoeff (w.adicCompletion K))))
  exact ((localScalarEquiv (S := S) W w).toEquiv.toHomeomorphOfContinuousClosed
    (localScalarEquiv_continuous W w) (localScalarEquiv_continuous W w).isClosedMap).symm.continuous

/-- Kind: definition; the genuine continuous cochains in the restricted
global Tate coefficients (Nekovář 5.1; tex 3455–3463). -/
abbrev restrictedPointComplex := contCochains ℤ_[2] (Gloc K w)
  (ResMod (locMap K S w) (TateS K S W))

/-- Kind: definition; the actual local coefficient isomorphism with its
restricted-global source module (tex 3413–3438). -/
def restrictedTateMap : ResMod (locMap K S w) (TateS K S W) →ₗ[ℤ_[2]]
    pointTate (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) where
  toFun := localTateEquiv (S := S) W w
  map_add' := (localTateEquiv (S := S) W w).map_add
  map_smul' := (localTateEquiv (S := S) W w).map_smul

/-- Kind: definition; the inverse of the same actual local coefficient
map (tex 3413–3438). -/
def restrictedTateInv : pointTate (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) →ₗ[ℤ_[2]]
    ResMod (locMap K S w) (TateS K S W) where
  toFun := (localTateEquiv (S := S) W w).symm
  map_add' := (localTateEquiv (S := S) W w).symm.map_add
  map_smul' := (localTateEquiv (S := S) W w).symm.map_smul

/-- Kind: proved theorem; the coefficient map is equivariant along the
canonical absolute Galois group isomorphism (Nekovář 5.1). -/
theorem restrictedTateMap_smul (σ : AbsoluteGaloisGroup (w.adicCompletion K))
    (x : ResMod (locMap K S w) (TateS K S W)) :
    restrictedTateMap W w ((absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).symm σ • x) =
      σ • restrictedTateMap W w x := by
  have h := localTateEquiv_smul W w
    ((absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).symm σ) x
  rw [(absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).apply_symm_apply] at h
  exact h

/-- Kind: proved theorem; the inverse coefficient map uses the inverse of
that same Galois comparison (Nekovář 5.1). -/
theorem restrictedTateInv_smul (σ : Gloc K w)
    (x : pointTate (w.adicCompletion K) (W.baseChange (w.adicCompletion K))) :
    restrictedTateInv (S := S) W w (absoluteGaloisGroupRestrictEquiv (w.adicCompletion K) σ • x) =
      σ • restrictedTateInv (S := S) W w x := by
  apply (localTateEquiv (S := S) W w).injective
  change localTateEquiv (S := S) W w
    ((localTateEquiv (S := S) W w).symm
      (absoluteGaloisGroupRestrictEquiv (w.adicCompletion K) σ • x)) =
    localTateEquiv (S := S) W w (locMap K S w σ • (localTateEquiv (S := S) W w).symm x)
  rw [LinearEquiv.apply_symm_apply, localTateEquiv_smul, LinearEquiv.apply_symm_apply]

/-- Kind: definition; transport of the actual continuous point cochains
along the fixed coefficient and Galois isomorphisms (tex 3413–3438). -/
def localPointCochainMap : restrictedPointComplex (S := S) W w ⟶
    pointComplex (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) :=
  contCochainsMap
    ⟨(absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).symm.toMulEquiv.toMonoidHom,
      (absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).symm.continuous⟩
    (restrictedTateMap W w) (localTateEquiv_continuous W w) (restrictedTateMap_smul W w)

/-- Kind: definition; inverse transport of the same actual continuous
cochains (tex 3413–3438). -/
def localPointCochainInv : pointComplex (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) ⟶
    restrictedPointComplex (S := S) W w :=
  contCochainsMap
    ⟨(absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).toMulEquiv.toMonoidHom,
      (absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).continuous⟩
    (restrictedTateInv (S := S) W w) (localTateEquiv_symm_continuous W w) (restrictedTateInv_smul W w)

/-- Kind: proved theorem; the two actual cochain maps compose to the
identity, in every degree (tex 3413–3438). -/
theorem localPointCochainMap_inv :
    localPointCochainMap (S := S) W w ≫ localPointCochainInv W w =
      𝟙 (restrictedPointComplex (S := S) W w) := by
  ext n c
  apply Subtype.ext
  funext s
  change (localTateEquiv (S := S) W w).symm
    (localTateEquiv (S := S) W w (c.val (fun i =>
      (absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).symm
        (absoluteGaloisGroupRestrictEquiv (w.adicCompletion K) (s i))))) = c.val s
  simp only [ContinuousMulEquiv.symm_apply_apply]
  exact (localTateEquiv (S := S) W w).symm_apply_apply (show TateS K S W from c.val s)

/-- Kind: proved theorem; the reverse actual cochain composition is also
the identity (tex 3413–3438). -/
theorem localPointCochainInv_map :
    localPointCochainInv (S := S) W w ≫ localPointCochainMap W w =
      𝟙 (pointComplex (w.adicCompletion K) (W.baseChange (w.adicCompletion K))) := by
  ext n c
  apply Subtype.ext
  funext s
  change localTateEquiv (S := S) W w
    ((localTateEquiv (S := S) W w).symm (cfun c (fun i =>
      absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)
        ((absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).symm (s i))))) = cfun c s
  simp only [ContinuousMulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Kind: definition; the genuine integral local point-cochain
isomorphism, rather than only a cohomology identification
(tex 3413–3438). -/
def localPointCochainIso : restrictedPointComplex (S := S) W w ≅
    pointComplex (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) where
  hom := localPointCochainMap W w
  inv := localPointCochainInv W w
  hom_inv_id := localPointCochainMap_inv W w
  inv_hom_id := localPointCochainInv_map W w

/-- Kind: definition; the actual coefficient transport restricted to
continuous one-cocycles (tex 3413–3438). -/
def localPointCycleMap : LinearMap.ker ((restrictedPointComplex (S := S) W w).d 1 2).hom →ₗ[ℤ_[2]]
    LinearMap.ker ((pointComplex (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).d 1 2).hom where
  toFun c := ⟨((localPointCochainMap W w).f 1).hom c.val, by
    change ((pointComplex (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).d 1 2).hom
      (((localPointCochainMap W w).f 1).hom c.val) = 0
    have hc : ((restrictedPointComplex (S := S) W w).d 1 2).hom c.val = 0 := c.property
    have h := congrArg (fun f => f.hom c.val) ((localPointCochainMap W w).comm 1 2)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hc, map_zero] using h⟩
  map_add' c d := Subtype.ext (map_add _ _ _)
  map_smul' r c := Subtype.ext (map_smul _ _ _)

/-- Kind: definition; the original integral Kummer cocycle, with its
actual cycle witness (tex 3413–3438). -/
def globalKummerCycle (P : (W.baseChange (w.adicCompletion K)).toAffine.Point) :
    LinearMap.ker ((restrictedPointComplex (S := S) W w).d 1 2).hom :=
  ⟨tateKummerCocycle W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w P,
    tateKummerCocycleOf_isCocycle W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w _⟩

/-- Kind: proved theorem; the transported integral Kummer cocycle has the
actual finite torsion cocycle of the original division tower
(tex 3413–3438; Silverman III.7). -/
theorem localKummerCycle_projection (a : ℕ)
    (P : (W.baseChange (w.adicCompletion K)).toAffine.Point)
    (σ : AbsoluteGaloisGroup (w.adicCompletion K)) :
    FiniteTrace.torsionCoeffToAlg (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) (2 ^ a)
      (pointLevelEquiv (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) a
        (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K))
          (W.baseChange (w.adicCompletion K)).PointCoeff a
            (cfun (localPointCycleMap (S := S) W w (globalKummerCycle (S := S) W w P)).val (fun _ => σ)))) =
      towerKummerOf (isDivTower_divTower (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) P) a
        ((absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).symm σ) := by
  change FiniteTrace.torsionCoeffToAlg (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) (2 ^ a)
    (localLevelEquiv W w a
      (projLev a (tateKummerFunOf W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w
        (isDivTower_divTower (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) P)
          ((absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).symm σ)))) = _
  rw [← compSepTors_eq, localLevelEquiv_toAlg]
  exact compTors_tateKummerFunOf W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w _ _ a

end ContinuousLocalTransport

section ActualKummerClasses

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

/-- Kind: proved theorem; reduction of the original integral Kummer
cocycle is the actual finite Kummer class of the same point. The equality
uses the same division tower and the fixed coefficient map at every
level (tex 3413–3438; Milne I.3.4). -/
theorem localKummerCycle_class (a : ℕ)
    (P : (W.baseChange (w.adicCompletion K)).toAffine.Point) :
    pointH1Reduction (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) a
      (localPointCycleMap (S := S) W w (globalKummerCycle (S := S) W w P)) =
      (W.baseChange (w.adicCompletion K)).kummerMap (2 ^ a) (twoPower_isUnit (w.adicCompletion K) a) P := by
  let q : (W.baseChange (w.adicCompletion K)).PointCoeff :=
    (FiniteTrace.pointCoeffToAlg (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).symm
      (divTower (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) P a)
  have hqval : FiniteTrace.pointCoeffToAlg (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) q =
      divTower (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) P a :=
    (FiniteTrace.pointCoeffToAlg (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).apply_symm_apply _
  have hq : (2 ^ a : ℕ) • q = (W.baseChange (w.adicCompletion K)).basePointCoeff P := by
    apply (FiniteTrace.pointCoeffToAlg (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).injective
    rw [map_nsmul, FiniteTrace.pointCoeffToAlg_base]
    change (2 ^ a : ℕ) • FiniteTrace.pointCoeffToAlg (w.adicCompletion K)
      (W.baseChange (w.adicCompletion K))
        ((FiniteTrace.pointCoeffToAlg (w.adicCompletion K)
          (W.baseChange (w.adicCompletion K))).symm
            (divTower (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) P a)) = _
    rw [AddEquiv.apply_symm_apply]
    exact (isDivTower_divTower (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) P).two_pow_smul a
  rw [pointH1Reduction_class,
    (W.baseChange (w.adicCompletion K)).kummerMap_eq_H1pi (twoPower_isUnit (w.adicCompletion K) a) hq]
  apply congrArg (H1pi (AbsoluteGaloisGroup (w.adicCompletion K))
    ((W.baseChange (w.adicCompletion K)).TorsionCoeff (2 ^ a)))
  apply Subtype.ext
  funext σ
  apply (FiniteTrace.torsionCoeffToAlg (w.adicCompletion K)
    (W.baseChange (w.adicCompletion K)) (2 ^ a)).injective
  apply Subtype.ext
  change FiniteTrace.pointCoeffToAlg (w.adicCompletion K) (W.baseChange (w.adicCompletion K))
    (pointLevelEquiv (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) a
      (coefficientProjection (AbsoluteGaloisGroup (w.adicCompletion K))
        (W.baseChange (w.adicCompletion K)).PointCoeff a
          (cfun (localPointCycleMap (S := S) W w (globalKummerCycle (S := S) W w P)).val
            (fun _ => σ)))) =
    FiniteTrace.pointCoeffToAlg (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) (σ • q - q)
  have hp := congrArg Subtype.val (localKummerCycle_projection (S := S) W w a P σ)
  refine hp.trans ?_
  have hsmul : FiniteTrace.pointCoeffToAlg (w.adicCompletion K) (W.baseChange (w.adicCompletion K))
      (σ • q) = ((absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).symm σ) •
        FiniteTrace.pointCoeffToAlg (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) q := by
    have h := FiniteTrace.pointCoeffToAlg_smul (w.adicCompletion K) (W.baseChange (w.adicCompletion K))
      ((absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).symm σ) q
    rw [(absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).apply_symm_apply] at h
    exact h
  rw [map_sub, hsmul, hqval]
  rfl

/-- Kind: proved theorem; the cup of two original integral Kummer
cocycles is an actual continuous coboundary. Finite cup zero is proved
at all levels, then the normalized integral trace separates classes
(tex 3442–3450; Milne I.3.4). -/
theorem localKummerCup_boundary (hM : MilneLocalDualityPrint)
    (P Q : (W.baseChange (w.adicCompletion K)).toAffine.Point) :
    ∃ b : (actualTraceComplex (w.adicCompletion K)).X 1,
      ((actualTraceComplex (w.adicCompletion K)).d 1 2).hom b =
        integralCupOne (w.adicCompletion K) (W.baseChange (w.adicCompletion K))
          (localPointCycleMap (S := S) W w (globalKummerCycle (S := S) W w P)).val
          (localPointCycleMap (S := S) W w (globalKummerCycle (S := S) W w Q)).val := by
  let c := localPointCycleMap (S := S) W w (globalKummerCycle (S := S) W w P)
  let d := localPointCycleMap (S := S) W w (globalKummerCycle (S := S) W w Q)
  apply (IntegralTrace.normalizedCycleTrace_eq_zero_iff_boundary (w.adicCompletion K)
    (integralCupCycle (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) c d)).mp
  apply PadicInt.ext_of_toZModPow.mp
  intro a
  rw [map_zero]
  apply ZMod.toRatAddCircle_injective (2 ^ a)
  rw [map_zero]
  change padicInvariant a (IntegralTrace.normalizedCycleTrace (w.adicCompletion K)
    (integralCupCycle (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) c d)) = 0
  rw [IntegralCompatibility.integralCup_invariant_compatibility]
  change ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing (W.baseChange (w.adicCompletion K))
    (2 ^ a) (twoPower_isUnit (w.adicCompletion K) a)
      (pointH1Reduction (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) a
        (localPointCycleMap (S := S) W w (globalKummerCycle (S := S) W w P)))
      (pointH1Reduction (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) a
        (localPointCycleMap (S := S) W w (globalKummerCycle (S := S) W w Q))) = 0
  rw [localKummerCycle_class, localKummerCycle_class]
  obtain ⟨M⟩ := hM (w.adicCompletion K) (W.baseChange (w.adicCompletion K))
  exact kummer_finite_isotropy
    (W.baseChange (w.adicCompletion K)) M (2 ^ a) (twoPower_isUnit (w.adicCompletion K) a) P Q

end ActualKummerClasses

section TracedSpanIsotropy

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

/-- Kind: definition; the genuine local trace-cup pairing, pulled back
through the fixed point-cochain dictionary (tex 3442–3450). -/
def kummerTracePair : (restrictedPointComplex (S := S) W w).X 1 →ₗ[ℤ_[2]]
    (restrictedPointComplex (S := S) W w).X 1 →ₗ[ℤ_[2]] ℤ_[2] :=
  ((integralCupOne (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).compl₁₂
    ((localPointCochainMap W w).f 1).hom ((localPointCochainMap W w).f 1).hom).compr₂
      (AllCochainTrace.trv (w.adicCompletion K))

/-- Kind: proved theorem; a boundary paired with a cycle has zero
normalized trace, by the cochain Leibniz rule (Brown V.3;
tex 3442–3450). -/
theorem actualCupTrace_boundary_left
    (b : (pointComplex (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).X 0)
    (c : LinearMap.ker ((pointComplex (w.adicCompletion K)
      (W.baseChange (w.adicCompletion K))).d 1 2).hom) :
    AllCochainTrace.trv (w.adicCompletion K)
      (integralCupOne (w.adicCompletion K) (W.baseChange (w.adicCompletion K))
        (((pointComplex (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).d 0 1).hom b) c.val) = 0 := by
  have hc : ((pointComplex (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).d 1 2).hom c.val = 0 := c.property
  have h := (integralCupPair (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).leib 0 1 1 rfl b c.val
  rw [hc, map_zero, smul_zero, add_zero] at h
  have ht := AllCochainTrace.htrv (w.adicCompletion K)
    ((integralCupPair (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).P 0 1 1 rfl b c.val)
  rw [h] at ht
  exact ht

/-- Kind: proved theorem; a cycle paired with a boundary has zero
normalized trace, with the degree-one Leibniz sign (Brown V.3;
tex 3442–3450). -/
theorem actualCupTrace_boundary_right
    (c : LinearMap.ker ((pointComplex (w.adicCompletion K)
      (W.baseChange (w.adicCompletion K))).d 1 2).hom)
    (b : (pointComplex (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).X 0) :
    AllCochainTrace.trv (w.adicCompletion K)
      (integralCupOne (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) c.val
        (((pointComplex (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).d 0 1).hom b)) = 0 := by
  have hc : ((pointComplex (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).d 1 2).hom c.val = 0 := c.property
  have h := (integralCupPair (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).leib 1 0 1 rfl c.val b
  rw [hc, LinearMap.map_zero₂, zero_add] at h
  simp only [pow_one, neg_one_smul] at h
  have ht := AllCochainTrace.htrv (w.adicCompletion K)
    ((integralCupPair (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).P 1 0 1 rfl c.val b)
  rw [h, map_neg] at ht
  exact neg_eq_zero.mp ht

/-- Kind: proved theorem; the original integral Kummer generators have
zero traced cup product, from all-level finite cup zero and integral
class separation (Milne I.3.4; tex 3442–3450). -/
theorem kummerTracePair_generators (hM : MilneLocalDualityPrint)
    (P Q : (W.baseChange (w.adicCompletion K)).toAffine.Point) :
    kummerTracePair (S := S) W w
      (tateKummerCocycle W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w P)
      (tateKummerCocycle W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w Q) = 0 := by
  obtain ⟨b, hb⟩ := localKummerCup_boundary (S := S) W w hM P Q
  change AllCochainTrace.trv (w.adicCompletion K)
    (integralCupOne (w.adicCompletion K) (W.baseChange (w.adicCompletion K))
      (localPointCycleMap (S := S) W w (globalKummerCycle (S := S) W w P)).val
      (localPointCycleMap (S := S) W w (globalKummerCycle (S := S) W w Q)).val) = 0
  rw [← hb]
  exact AllCochainTrace.htrv (w.adicCompletion K) b

/-- Kind: proved theorem; the pulled-back trace-cup pairing kills a
source boundary against a source cycle (Brown V.3; tex 3442–3450). -/
theorem kummerTracePair_boundary_left
    (b : (restrictedPointComplex (S := S) W w).X 0)
    (c : LinearMap.ker ((restrictedPointComplex (S := S) W w).d 1 2).hom) :
    kummerTracePair (S := S) W w (((restrictedPointComplex (S := S) W w).d 0 1).hom b) c.val = 0 := by
  have h := congrArg (fun f => f.hom b) ((localPointCochainMap W w).comm 0 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  change AllCochainTrace.trv (w.adicCompletion K)
    (integralCupOne (w.adicCompletion K) (W.baseChange (w.adicCompletion K))
      (((localPointCochainMap W w).f 1).hom (((restrictedPointComplex (S := S) W w).d 0 1).hom b))
      (localPointCycleMap W w c).val) = 0
  rw [← h]
  exact actualCupTrace_boundary_left W w (((localPointCochainMap W w).f 0).hom b)
    (localPointCycleMap W w c)

/-- Kind: proved theorem; the reverse boundary-cycle trace identity is
preserved by the same cochain map (Brown V.3; tex 3442–3450). -/
theorem kummerTracePair_boundary_right
    (c : LinearMap.ker ((restrictedPointComplex (S := S) W w).d 1 2).hom)
    (b : (restrictedPointComplex (S := S) W w).X 0) :
    kummerTracePair (S := S) W w c.val (((restrictedPointComplex (S := S) W w).d 0 1).hom b) = 0 := by
  have h := congrArg (fun f => f.hom b) ((localPointCochainMap W w).comm 0 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  change AllCochainTrace.trv (w.adicCompletion K)
    (integralCupOne (w.adicCompletion K) (W.baseChange (w.adicCompletion K))
      (localPointCycleMap W w c).val
      (((localPointCochainMap W w).f 1).hom (((restrictedPointComplex (S := S) W w).d 0 1).hom b))) = 0
  rw [← h]
  exact actualCupTrace_boundary_right W w (localPointCycleMap W w c)
    (((localPointCochainMap W w).f 0).hom b)

/-- Kind: proved theorem; bilinearity extends finite-generator trace
isotropy to both integral Kummer spans (tex 3442–3450). -/
theorem kummerTracePair_spans (hM : MilneLocalDualityPrint)
    (u v : (restrictedPointComplex (S := S) W w).X 1)
    (hu : u ∈ tateKummerZ W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w)
    (hv : v ∈ tateKummerZ W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w) :
    kummerTracePair (S := S) W w u v = 0 := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨P, rfl⟩ := hu
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨Q, rfl⟩ := hv
      exact kummerTracePair_generators W w hM P Q
    | zero => exact map_zero _
    | add v v' hv hv' h h' => rw [map_add, h, h', zero_add]
    | smul r v hv h => rw [map_smul, h, smul_zero]
  | zero => exact LinearMap.map_zero₂ _ _
  | add u u' hu hu' h h' => rw [map_add, LinearMap.add_apply, h, h', zero_add]
  | smul r u hu h => rw [map_smul, LinearMap.smul_apply, h, smul_zero]

/-- Kind: proved theorem; the entire literal integral cocycle condition
is trace-isotropic, including all continuous coboundaries
(tex 3413–3450; Milne I.3.4). -/
theorem kummerTracePair_condition (hM : MilneLocalDualityPrint)
    (u v : (tateKummerCondition W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w).X 1) :
    kummerTracePair (S := S) W w u.val v.val = 0 := by
  obtain ⟨uz, huz, ub, hub, hu⟩ := Submodule.mem_sup.mp u.property
  obtain ⟨vz, hvz, vb, hvb, hv⟩ := Submodule.mem_sup.mp v.property
  obtain ⟨b, hb⟩ := (mem_contB1_iff ub).mp hub
  obtain ⟨c, hc⟩ := (mem_contB1_iff vb).mp hvb
  let zu : LinearMap.ker ((restrictedPointComplex (S := S) W w).d 1 2).hom :=
    ⟨uz, tateKummerZ_cocycle W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w uz huz⟩
  let zv : LinearMap.ker ((restrictedPointComplex (S := S) W w).d 1 2).hom :=
    ⟨vz, tateKummerZ_cocycle W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w vz hvz⟩
  let bc : LinearMap.ker ((restrictedPointComplex (S := S) W w).d 1 2).hom :=
    ⟨contD ℤ_[2] (Gloc K w) (ResMod (locMap K S w) (TateS K S W)) 0 b, contD_contD 0 b⟩
  rw [← hu, ← hv, LinearMap.map_add₂, map_add, map_add]
  have hzz := kummerTracePair_spans W w hM uz vz huz hvz
  have hzb := kummerTracePair_boundary_right W w zu c
  have hbz := kummerTracePair_boundary_left W w b zv
  have hbb := kummerTracePair_boundary_right W w bc c
  change ((restrictedPointComplex (S := S) W w).d 0 1).hom b = ub at hb
  change ((restrictedPointComplex (S := S) W w).d 0 1).hom c = vb at hc
  change kummerTracePair (S := S) W w uz (((restrictedPointComplex (S := S) W w).d 0 1).hom c) = 0 at hzb
  change kummerTracePair (S := S) W w (((restrictedPointComplex (S := S) W w).d 0 1).hom b) vz = 0 at hbz
  change kummerTracePair (S := S) W w (((restrictedPointComplex (S := S) W w).d 0 1).hom b)
    (((restrictedPointComplex (S := S) W w).d 0 1).hom c) = 0 at hbb
  change kummerTracePair (S := S) W w uz vz + kummerTracePair (S := S) W w uz vb +
    (kummerTracePair (S := S) W w ub vz + kummerTracePair (S := S) W w ub vb) = 0
  rw [← hb, ← hc, hzz, hzb, hbz, hbb]
  simp

end TracedSpanIsotropy

section IntegralLineCochains

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

/-- Kind: definition; identification of the restricted global integral
cyclotomic line with the genuine local roots-of-unity Tate module,
using the finite Weil values of one global basis (tex 2798–2805, 5037;
Nekovář 5.1). -/
def localIntegralLineEquiv : ResMod (locMap K S w) (IntegralTate1 K S) ≃ₗ[ℤ_[2]]
    muTate (w.adicCompletion K) :=
  (ContinuousCharacterLine.equiv ℤ_[2] (cyc2 K S)).trans (localScalarEquiv (S := S) W w)

/-- Kind: proved theorem; the integral line identification is continuous
in the inherited two-adic and inverse-limit topologies
(Silverman III.7; tex 2798–2805). -/
theorem localIntegralLineEquiv_continuous : Continuous (localIntegralLineEquiv (S := S) W w) :=
  (localScalarEquiv_continuous W w).comp
    (ContinuousCharacterLine.homeomorph ℤ_[2] (cyc2 K S)).continuous

/-- Kind: proved theorem; the inverse integral line identification is
continuous in the same genuine topologies (Silverman III.7). -/
theorem localIntegralLineEquiv_symm_continuous :
    Continuous (localIntegralLineEquiv (S := S) W w).symm :=
  (ContinuousCharacterLine.homeomorph ℤ_[2] (cyc2 K S)).symm.continuous.comp
    (localScalarEquiv_symm_continuous W w)

/-- Kind: proved theorem; the line identification respects the actual
local action and the restriction of the global cyclotomic character
(tex 2798–2805; Nekovář 5.1). -/
theorem localIntegralLineEquiv_smul (σ : Gloc K w)
    (x : ResMod (locMap K S w) (IntegralTate1 K S)) :
    localIntegralLineEquiv (S := S) W w (σ • x) =
      absoluteGaloisGroupRestrictEquiv (w.adicCompletion K) σ • localIntegralLineEquiv (S := S) W w x :=
  localScalarEquiv_smul W w σ (ContinuousCharacterLine.equiv ℤ_[2] (cyc2 K S) x)

/-- Kind: proved theorem; the scalar identification takes the restriction
of the actual global determinant pairing to the actual local integral
Weil pairing, without an extra comparison assumption (tex 5037;
Silverman III.8.1). -/
theorem localIntegralLineEquiv_beta
    (x y : ResMod (locMap K S w) (TateS K S W)) :
    localIntegralLineEquiv (S := S) W w
      (resPairing ℤ_[2] (GKS K S) (integralBeta (K := K) (S := S) (W := W)) (locMap K S w) x y) =
      coefficientWeilPairing (w.adicCompletion K) (W.baseChange (w.adicCompletion K))
        (restrictedTateMap W w x) (restrictedTateMap W w y) :=
  (localWeil_eq_global_det W w x y).symm

/-- Kind: definition; continuous local cochains with values in the
restriction of the global integral cyclotomic line
(Nekovář 5.1; tex 3455–3463). -/
abbrev restrictedLineComplex := contCochains ℤ_[2] (Gloc K w)
  (ResMod (locMap K S w) (IntegralTate1 K S))

/-- Kind: proved theorem; equivariance of the inverse actual line map
along the inverse Galois comparison (Nekovář 5.1). -/
theorem localIntegralLineEquiv_inv_smul (σ : Gloc K w) (x : muTate (w.adicCompletion K)) :
    (localIntegralLineEquiv (S := S) W w).symm
      (absoluteGaloisGroupRestrictEquiv (w.adicCompletion K) σ • x) =
      σ • (localIntegralLineEquiv (S := S) W w).symm x := by
  apply (localIntegralLineEquiv (S := S) W w).injective
  rw [LinearEquiv.apply_symm_apply, localIntegralLineEquiv_smul, LinearEquiv.apply_symm_apply]

/-- Kind: proved theorem; equivariance of the forward line map in the
contravariant cochain direction (Nekovář 5.1). -/
theorem localIntegralLineEquiv_map_smul (σ : AbsoluteGaloisGroup (w.adicCompletion K))
    (x : ResMod (locMap K S w) (IntegralTate1 K S)) :
    localIntegralLineEquiv (S := S) W w
      ((absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).symm σ • x) =
      σ • localIntegralLineEquiv (S := S) W w x := by
  have h := localIntegralLineEquiv_smul (S := S) W w
    ((absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).symm σ) x
  rw [(absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).apply_symm_apply] at h
  exact h

/-- Kind: definition; the cochain-level identification of the integral
trace targets, induced by the globally coherent scalar-line map
(tex 2798–2805, 3442–3450). -/
def localLineCochainMap : restrictedLineComplex (S := S) w ⟶ actualTraceComplex (w.adicCompletion K) :=
  contCochainsMap
    ⟨(absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).symm.toMulEquiv.toMonoidHom,
      (absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).symm.continuous⟩
    (localIntegralLineEquiv (S := S) W w).toLinearMap
      (localIntegralLineEquiv_continuous W w) (localIntegralLineEquiv_map_smul W w)

/-- Kind: definition; inverse cochain transport of the same genuine
integral trace targets (tex 2798–2805, 3442–3450). -/
def localLineCochainInv : actualTraceComplex (w.adicCompletion K) ⟶ restrictedLineComplex (S := S) w :=
  contCochainsMap
    ⟨(absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).toMulEquiv.toMonoidHom,
      (absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).continuous⟩
    (localIntegralLineEquiv (S := S) W w).symm.toLinearMap
      (localIntegralLineEquiv_symm_continuous W w) (localIntegralLineEquiv_inv_smul W w)

/-- Kind: proved theorem; the trace-target cochain maps are inverse in
every degree (tex 3442–3450). -/
theorem localLineCochainMap_inv :
    localLineCochainMap (S := S) W w ≫ localLineCochainInv W w =
      𝟙 (restrictedLineComplex (S := S) w) := by
  ext n c
  apply Subtype.ext
  funext s
  change (localIntegralLineEquiv (S := S) W w).symm
    (localIntegralLineEquiv (S := S) W w (c.val (fun i =>
      (absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).symm
        (absoluteGaloisGroupRestrictEquiv (w.adicCompletion K) (s i))))) = c.val s
  simp only [ContinuousMulEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-- Kind: proved theorem; the reverse trace-target composition is the
identity (tex 3442–3450). -/
theorem localLineCochainInv_map :
    localLineCochainInv (S := S) W w ≫ localLineCochainMap W w =
      𝟙 (actualTraceComplex (w.adicCompletion K)) := by
  ext n c
  apply Subtype.ext
  funext s
  change localIntegralLineEquiv (S := S) W w
    ((localIntegralLineEquiv (S := S) W w).symm (c.val (fun i =>
      absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)
        ((absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).symm (s i))))) = c.val s
  simp only [ContinuousMulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Kind: definition; the genuine integral trace-target cochain
isomorphism in the fixed global orientation (tex 2798–2805, 3442–3450). -/
def localLineCochainIso : restrictedLineComplex (S := S) w ≅ actualTraceComplex (w.adicCompletion K) where
  hom := localLineCochainMap (S := S) W w
  inv := localLineCochainInv (S := S) W w
  hom_inv_id := localLineCochainMap_inv W w
  inv_hom_id := localLineCochainInv_map W w

/-- Kind: definition; the continuous cup pairing in the restricted
actual global determinant coefficients (tex 2798–2805, 5037). -/
def restrictedIntegralCup : NatPair (restrictedPointComplex (S := S) W w)
    (restrictedPointComplex (S := S) W w) (restrictedLineComplex (S := S) w) :=
  contNatPair (resPairing ℤ_[2] (GKS K S) (integralBeta (K := K) (S := S) (W := W)) (locMap K S w))
    (fun σ x y => integralBeta_galois (locMap K S w σ) x y)
    (resPairing_continuous ℤ_[2] (GKS K S) (integralBeta (K := K) (S := S) (W := W))
      integralBeta_continuous (locMap K S w))

/-- Kind: proved theorem; the integral cup-product dictionary is a
literal equality in every bidegree, for the same coefficient maps
(Brown V.3; tex 2798–2805, 3442–3450). -/
theorem localLineCochainMap_cup (p q n : ℕ) (hpq : p + q = n)
    (x : (restrictedPointComplex (S := S) W w).X p)
    (y : (restrictedPointComplex (S := S) W w).X q) :
    ((localLineCochainMap (S := S) W w).f n).hom
      ((restrictedIntegralCup W w).P p q n hpq x y) =
      (integralCupPair (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).P p q n hpq
        (((localPointCochainMap W w).f p).hom x) (((localPointCochainMap W w).f q).hom y) := by
  apply Subtype.ext
  funext g
  let φ := (absoluteGaloisGroupRestrictEquiv (w.adicCompletion K)).symm.toMulEquiv.toMonoidHom
  change localIntegralLineEquiv (S := S) W w
    (cupFun (resPairing ℤ_[2] (GKS K S) (integralBeta (K := K) (S := S) (W := W)) (locMap K S w))
      p q n hpq (cfun x) (cfun y) (φ ∘ g)) =
      cupFun (coefficientWeilPairing (w.adicCompletion K) (W.baseChange (w.adicCompletion K)))
        p q n hpq (cfun (((localPointCochainMap W w).f p).hom x))
          (cfun (((localPointCochainMap W w).f q).hom y)) g
  unfold cupFun
  rw [localIntegralLineEquiv_beta]
  rw [← map_headProd φ p n (by omega)]
  apply congrArg₂ (fun a b => coefficientWeilPairing (w.adicCompletion K)
    (W.baseChange (w.adicCompletion K)) a b)
  · rfl
  · exact restrictedTateMap_smul (S := S) W w (headProd p n (by omega) g)
      (show ResMod (locMap K S w) (TateS K S W) from y.val (fun j => φ (g ⟨p + j, by omega⟩)))

/-- Kind: definition; the normalized local integral trace, transported
along the same globally coherent line isomorphism (Milne I.2.3;
Nekovář 5.1; tex 3442–3450). -/
def orientedLocalTrace : (restrictedLineComplex (S := S) w).X 2 →ₗ[ℤ_[2]] ℤ_[2] :=
  (AllCochainTrace.trv (w.adicCompletion K)).comp ((localLineCochainMap (S := S) W w).f 2).hom

/-- Kind: proved theorem; the transported trace kills every genuine
continuous coboundary (tex 3442–3450). -/
theorem orientedLocalTrace_boundary (b : (restrictedLineComplex (S := S) w).X 1) :
    orientedLocalTrace (S := S) W w (((restrictedLineComplex (S := S) w).d 1 2).hom b) = 0 := by
  have h := congrArg (fun f => f.hom b) ((localLineCochainMap (S := S) W w).comm 1 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  change AllCochainTrace.trv (w.adicCompletion K)
    (((localLineCochainMap (S := S) W w).f 2).hom
      (((restrictedLineComplex (S := S) w).d 1 2).hom b)) = 0
  rw [← h]
  exact AllCochainTrace.htrv (w.adicCompletion K) _

/-- Kind: proved theorem; zero trace of a target two-cycle means an
actual continuous coboundary, not just zero residues
(Milne I.2.3; tex 3442–3450). -/
theorem orientedLocalTrace_kernel (z : (restrictedLineComplex (S := S) w).X 2)
    (hz : ((restrictedLineComplex (S := S) w).d 2 3).hom z = 0)
    (ht : orientedLocalTrace (S := S) W w z = 0) :
    ∃ b : (restrictedLineComplex (S := S) w).X 1,
      ((restrictedLineComplex (S := S) w).d 1 2).hom b = z := by
  have h := congrArg (fun f => f.hom z) ((localLineCochainMap (S := S) W w).comm 2 3)
  have hc : ((actualTraceComplex (w.adicCompletion K)).d 2 3).hom
      (((localLineCochainMap (S := S) W w).f 2).hom z) = 0 := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hz, map_zero] using h
  obtain ⟨b, hb⟩ := AllCochainTrace.hker (w.adicCompletion K)
    (((localLineCochainMap (S := S) W w).f 2).hom z) hc ht
  refine ⟨((localLineCochainInv (S := S) W w).f 1).hom b, ?_⟩
  have hi := congrArg (fun f => f.hom b) ((localLineCochainInv (S := S) W w).comm 1 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hi
  rw [hi, hb]
  have hback := congrArg (fun f => (f.f 2).hom z) (localLineCochainMap_inv (S := S) W w)
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using hback

/-- Kind: proved theorem; the trace of the restricted global determinant
cup is the actual normalized local Weil trace of the fixed source
cochains (tex 3442–3450, 5037). -/
theorem orientedLocalTrace_cup_one
    (x y : (restrictedPointComplex (S := S) W w).X 1) :
    orientedLocalTrace (S := S) W w ((restrictedIntegralCup W w).P 1 1 2 rfl x y) =
      kummerTracePair (S := S) W w x y := by
  change AllCochainTrace.trv (w.adicCompletion K)
    (((localLineCochainMap (S := S) W w).f 2).hom
      ((restrictedIntegralCup W w).P 1 1 2 rfl x y)) = _
  rw [localLineCochainMap_cup]
  rfl

end IntegralLineCochains

section TruncatedIntegralCondition

open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology (VanishesOutside)
open ZInQ.Contrib.CloudB3RC53.Duality (LocalTruncIsotropy kummerTruncIsotropy)

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

/-- Kind: proved theorem; the actual integral cocycle condition has
support in degrees zero and one (tex 3413–3438; Nekovář 6.1.2). -/
theorem integralKummerCondition_support :
    VanishesOutside (tateKummerCondition W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w)
      (fun n => n = 0 ∨ n = 1) := by
  intro n hn
  have h0 : n ≠ 0 := fun h => hn (Or.inl h)
  have h1 : n ≠ 1 := fun h => hn (Or.inr h)
  match n, h0, h1 with
  | .ofNat 0, h0, _ => exact (h0 rfl).elim
  | .ofNat 1, _, h1 => exact (h1 rfl).elim
  | .ofNat (n + 2), _, _ =>
    change Subsingleton (↥(⊥ : Submodule ℤ_[2]
      (contCochain ℤ_[2] (Gloc K w) (ResMod (locMap K S w) (TateS K S W)) (n + 2))))
    infer_instance
  | .negSucc _, _, _ => exact inferInstanceAs (Subsingleton PUnit)

/-- Kind: definition; truncated isotropy for the literal integral Kummer
condition is derived from all-level finite Kummer cup zero, the coherent
line transport, and actual integral class separation
(tex 3442–3450; Milne I.3.4; Nekovář 6.2.1.3). -/
def integralKummerLocalTrunc (hM : MilneLocalDualityPrint) :
    LocalTruncIsotropy
      (tateKummerConditionι W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w)
      (tateKummerConditionι W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w)
      (natPair (restrictedIntegralCup (S := S) W w)) :=
  kummerTruncIsotropy (integralKummerCondition_support W w) (integralKummerCondition_support W w)
    (orientedLocalTrace (S := S) W w) (orientedLocalTrace_kernel W w) (by
      intro x y
      change orientedLocalTrace (S := S) W w ((restrictedIntegralCup W w).P 1 1 2 rfl x.val y.val) = 0
      rw [orientedLocalTrace_cup_one]
      exact kummerTracePair_condition W w hM x y)

end TruncatedIntegralCondition

section CentralConsumer

open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SwitchInputs

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- Kind: definition with proved fields; the exact central consumer
isotropy witness is constructed on the original compact Kummer data.
No isotropy or local orthogonality witness is a premise
(tex 3442–3450; Milne I.3.4; Nekovář 6.2.1.3). -/
def centralIntegralTruncIsotropy_of_print (D : GenuineKummerData K E₀ hZ)
    (hM : MilneLocalDualityPrint) : CentralIntegralTruncIsotropy D := by
  classical
  exact TruncIsotropyData.ofLocal fun v => integralKummerLocalTrunc
    (S := D.S) (centralCurve D) v.1 hM

/-- Kind: definition with proved fields; the peer's unmodified pairing
constructor consumes the derived witness on the same central Selmer data
(tex 3455–3463; Nekovář 6.3.1). -/
def centralIntegralPairing_of_print (D : GenuineKummerData K E₀ hZ)
    (hM : MilneLocalDualityPrint) :
    SelPairDataTrunc (compactCentralSelData D) (compactCentralSelData D) :=
  centralIntegralPairDataTrunc D (centralIntegralTruncIsotropy_of_print D hM)

/-- Kind: proved theorem; the constructed central pairing retains the
literal global integral cyclotomic cochain target
(tex 2798–2805, 3455–3463; Nekovář 6.3.1). -/
theorem centralIntegralPairing_of_print_target (D : GenuineKummerData K E₀ hZ)
    (hM : MilneLocalDualityPrint) :
    (centralIntegralPairing_of_print D hM).E = globalCx ℤ_[2] (GKS K D.S) (IntegralTate1 K D.S) := rfl

end CentralConsumer

section LiteralConditionModules

open ZInQ.Contrib.RC53Assist.InnerLimitArith (MilneLocalFiniteness)

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

/-- Kind: definition; the original integral Kummer condition, with no
finite-model replacement (tex 3413–3438). -/
abbrev integralCondition :=
  tateKummerCondition W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w

/-- Kind: definition; the inclusion of that literal condition in the
restricted global Tate cochains (tex 3413–3438). -/
abbrev integralConditionMap :=
  tateKummerConditionι W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w

/-- Kind: definition; the degree-zero condition is the actual Tate
module by evaluation at the unique zero-cochain argument
(tex 3413–3438; Silverman III.7). -/
def integralConditionZeroEquiv : (integralCondition (S := S) W w).X 0 ≃ₗ[ℤ_[2]] TateS K S W where
  toFun x := x.val.val default
  invFun t := ofCondZero
    (tateKummerZ W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w)
    (tateKummerZ_cocycle W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w)
    (constCochain (k := ℤ_[2]) (G := Gloc K w) (show ResMod (locMap K S w) (TateS K S W) from t))
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext s
    exact congrArg x.val.val (Subsingleton.elim default s)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Kind: proved theorem; the actual degree-zero term is finite over the
two-adic integers, by the genuine Tate basis (Silverman III.7;
tex 3413–3438). -/
theorem integralCondition_zero_finite : Module.Finite ℤ_[2] ((integralCondition (S := S) W w).X 0) :=
  Module.Finite.of_surjective (integralConditionZeroEquiv (S := S) W w).symm.toLinearMap
    (integralConditionZeroEquiv (S := S) W w).symm.surjective

/-- Kind: proved theorem; the actual degree-one term is finitely
generated, because its boundaries are the image of the finite
zero-term and its cohomology is finite by Milne I.2.1. No finiteness of
all Galois cochain terms is claimed (tex 3413–3438). -/
theorem integralCondition_one_finite (hloc : MilneLocalFiniteness) :
    Module.Finite ℤ_[2] ((integralCondition (S := S) W w).X 1) := by
  let Z := tateKummerZ W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w
  let hZ := tateKummerZ_cocycle W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w
  let U := integralCondition (S := S) W w
  let d : U.X 0 →ₗ[ℤ_[2]] U.X 1 := U.d 0 1 rfl
  have h0 : Module.Finite ℤ_[2] (U.X 0) := integralCondition_zero_finite W w
  have hH : Module.Finite ℤ_[2] (U.toCC.homology 1) :=
    ZInQ.Contrib.RC53Assist.Finiteness.moduleFinite_tateKummerCondition_homology W
      (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) hloc w 1
  have hQ : Module.Finite ℤ_[2] (U.X 1 ⧸ condB1 Z hZ) :=
    Module.Finite.equiv (cocycleConditionH1Iso Z hZ).toLinearEquiv
  have hN : LinearMap.range d = condB1 Z hZ := by
    ext u
    constructor
    · rintro ⟨b, rfl⟩
      change (condOne Z hZ (U.d 0 1 rfl b) : contCochain ℤ_[2] (Gloc K w)
        (ResMod (locMap K S w) (TateS K S W)) 1) ∈ contB1 ℤ_[2] (Gloc K w)
          (ResMod (locMap K S w) (TateS K S W))
      exact (mem_contB1_iff _).mpr ⟨(condZero Z hZ b).val, (cocycleCondition_d₀ Z hZ b).symm⟩
    · intro hu
      change (condOne Z hZ u : contCochain ℤ_[2] (Gloc K w)
        (ResMod (locMap K S w) (TateS K S W)) 1) ∈ contB1 ℤ_[2] (Gloc K w)
          (ResMod (locMap K S w) (TateS K S W)) at hu
      obtain ⟨b, hb⟩ := (mem_contB1_iff _).mp hu
      refine ⟨ofCondZero Z hZ b, ?_⟩
      apply Subtype.ext
      exact (cocycleCondition_d₀ Z hZ _).trans hb
  have hQR : Module.Finite ℤ_[2] (U.X 1 ⧸ LinearMap.range d) := by
    rw [hN]
    exact hQ
  exact Module.Finite.of_exact (f := d) (g := (LinearMap.range d).mkQ)
    (fun u => by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
      rfl)
    (LinearMap.range d).mkQ_surjective

/-- Kind: proved theorem; all terms of the literal integral Kummer
condition are finitely generated, while the full continuous cochain
complex need not have finite terms (Milne I.2.1; tex 3413–3438). -/
theorem integralCondition_term_finite (hloc : MilneLocalFiniteness) (n : ℤ) :
    Module.Finite ℤ_[2] ((integralCondition (S := S) W w).X n) := by
  by_cases h0 : n = 0
  · subst n
    exact integralCondition_zero_finite W w
  by_cases h1 : n = 1
  · subst n
    exact integralCondition_one_finite W w hloc
  have : Subsingleton ((integralCondition (S := S) W w).X n) :=
    integralKummerCondition_support W w n (by omega)
  have : Finite ((integralCondition (S := S) W w).X n) := Finite.of_subsingleton
  exact Module.Finite.of_finite

/-- Kind: proved theorem; every literal condition term is torsion-free,
being a submodule of functions valued in the genuine free Tate module
(Silverman III.7; tex 3413–3438). -/
theorem integralCondition_term_torsionFree (n : ℤ) :
    Module.IsTorsionFree ℤ_[2] ((integralCondition (S := S) W w).X n) := by
  letI : Module.IsTorsionFree ℤ_[2] (ResMod (locMap K S w) (TateS K S W)) :=
    inferInstanceAs (Module.IsTorsionFree ℤ_[2] (TateS K S W))
  cases n with
  | ofNat n =>
    let Z := tateKummerZ W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w
    let f : (condP Z n) → (Fin n → Gloc K w) → TateS K S W :=
      fun u s => u.val.val s
    have hf : Function.Injective f := by
      intro u v huv
      apply Subtype.ext
      apply Subtype.ext
      funext s
      exact congrFun huv s
    haveI : Module.IsTorsionFree ℤ_[2] ((Fin n → Gloc K w) → TateS K S W) := inferInstance
    exact Function.Injective.moduleIsTorsionFree f hf (fun r u => rfl)
  | negSucc n => exact inferInstanceAs (Module.IsTorsionFree ℤ_[2] PUnit)

/-- Kind: proved theorem; the literal integral Kummer terms are finite
free over the scalar PID. This is derived from finiteness and
torsion-freeness, not assumed as a local derived comparison
(Milne I.2.1; tex 3413–3438). -/
theorem integralCondition_term_free (hloc : MilneLocalFiniteness) (n : ℤ) :
    Module.Free ℤ_[2] ((integralCondition (S := S) W w).X n) := by
  have := integralCondition_term_finite (S := S) W w hloc n
  have := integralCondition_term_torsionFree (S := S) W w n
  infer_instance

end LiteralConditionModules

section LocalInvariantIsomorphism

/-- Kind: proved theorem; the actual roots-of-unity Tate module is
compact because every genuine finite roots-of-unity level is finite
(Silverman III.7; Milne I.2.3). -/
theorem actualMuTate_compact (F : Type) [Field F] [CharZero F] : CompactSpace (muTate F) := by
  letI : ∀ a, Finite (TateModuleLevel 2 (UnitsCoeff F) a) := fun a =>
    Finite.of_equiv (KummerCoeff F (2 ^ a)) (actualMuLevelEquiv F a).symm.toEquiv
  exact inferInstanceAs (CompactSpace (TateModule 2 (UnitsCoeff F)))

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

include S W in
/-- Kind: proved theorem; some actual integral roots-of-unity two-cycle
has normalized trace one. A genuine finite invariant-one class is
lifted using the printed third-degree exactness and the same Tate
projection, then its unit trace is inverted. No local trace isomorphism
or local Kummer duality is assumed (Milne I.2.3; Nekovář 5.1.3). -/
theorem actualLocalTrace_cycle_one
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint) :
    ∃ z : LinearMap.ker ((actualTraceComplex (w.adicCompletion K)).d 2 3).hom,
      AllCochainTrace.trv (w.adicCompletion K) z.val = 1 := by
  let F := w.adicCompletion K
  let G := AbsoluteGaloisGroup F
  let A := UnitsCoeff F
  haveI : CompactSpace (IntegralTateCoeff G A) := actualMuTate_compact F
  have hcoeff : Function.Surjective (coefficientProjection G A 1) := by
    intro y
    obtain ⟨r, hr⟩ := localScalarMap_level_surjective (S := S) W w 1 y
    exact ⟨localScalarMap (S := S) W w r, hr⟩
  let cfin : H2 G (FiniteTateCoeff G A 1) :=
    (actualMuH2Equiv F 1).symm
      ((FiniteTrace.finiteInvariant F 2 (twoPower_isUnit F 1)).symm 1)
  obtain ⟨c, hc⟩ := kerToH2_surjective (k := ℤ_[2]) (G := G) (M := FiniteTateCoeff G A 1) cfin
  obtain ⟨t, ht⟩ := CoordinateReduction.first_cochain_surjective G A 2 hcoeff c.val
  have hpD : ((reduceCochains G A 1).f 3).hom (((actualTraceComplex F).d 2 3).hom t) = 0 := by
    rw [reduceCochains_d, ht]
    exact c.property
  obtain ⟨q, hq⟩ := (CoordinateReduction.first_cochain_kernel G A 3 _).mp hpD
  obtain ⟨z, b, hz⟩ := FiniteCycleLift.cycleLift_of_third_exact F
    (FiniteLocalDegreeBound.actualThirdDegreeExact_of_print hH F) 1 t q
      (by simpa only [pow_one] using hq.symm)
  have hb0 : ((reduceCochains G A 1).f 2).hom ((2 : ℤ_[2]) • b) = 0 :=
    (CoordinateReduction.first_cochain_kernel G A 2 _).mpr ⟨b, rfl⟩
  have hzproj : reduceTwoCycle G A 1 z = c := by
    apply Subtype.ext
    change ((reduceCochains G A 1).f 2).hom z.val = c.val
    rw [hz, map_add] at ht
    simpa only [pow_one, hb0, add_zero] using ht
  have hnorm : PadicInt.toZModPow 1 (AllCochainTrace.trv F z.val) = 1 := by
    rw [AllCochainTrace.trv_on_cycles, IntegralTrace.normalizedCycleTrace_projection]
    change FiniteTrace.finiteInvariant F 2 (twoPower_isUnit F 1)
      (actualMuH2Equiv F 1 (kerToH2 (reduceTwoCycle G A 1 z))) = 1
    rw [hzproj, hc]
    change FiniteTrace.finiteInvariant F 2 (twoPower_isUnit F 1)
      (actualMuH2Equiv F 1 ((actualMuH2Equiv F 1).symm
        ((FiniteTrace.finiteInvariant F 2 (twoPower_isUnit F 1)).symm 1))) = 1
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  haveI : IsLocalHom (PadicInt.toZModPow (p := 2) 1) :=
    IsLocalHom.of_surjective _ (ZMod.ringHom_surjective _)
  have hu : IsUnit (AllCochainTrace.trv F z.val) :=
    isUnit_of_map_unit (PadicInt.toZModPow 1) _ (by rw [hnorm]; exact isUnit_one)
  obtain ⟨u, huval⟩ := hu
  refine ⟨((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) • z, ?_⟩
  change AllCochainTrace.trv F (((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) • z.val) = 1
  rw [map_smul, smul_eq_mul, ← huval, Units.inv_mul]

/-- Kind: proved theorem; the globally oriented local line has an
actual continuous trace-one two-cycle. This is transported from the
same genuine local invariant, not supplied as an extra normalization
(Nekovář 5.1.3; Milne I.2.3). -/
theorem orientedLocalTrace_cycle_one
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint) :
    ∃ z : (restrictedLineComplex (S := S) w).X 2,
      ((restrictedLineComplex (S := S) w).d 2 3).hom z = 0 ∧ orientedLocalTrace (S := S) W w z = 1 := by
  obtain ⟨z, hz⟩ := actualLocalTrace_cycle_one (S := S) W w hH
  let y := ((localLineCochainInv (S := S) W w).f 2).hom z.val
  have hc : ((restrictedLineComplex (S := S) w).d 2 3).hom y = 0 := by
    have h := congrArg (fun f => f.hom z.val) ((localLineCochainInv (S := S) W w).comm 2 3)
    have hdz : ((actualTraceComplex (w.adicCompletion K)).d 2 3).hom z.val = 0 := z.property
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hdz, map_zero] using h
  refine ⟨y, hc, ?_⟩
  have hb := congrArg (fun f => (f.f 2).hom z.val) (localLineCochainInv_map (S := S) W w)
  have he : ((localLineCochainMap (S := S) W w).f 2).hom y = z.val := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using hb
  change AllCochainTrace.trv (w.adicCompletion K) (((localLineCochainMap (S := S) W w).f 2).hom y) = 1
  rw [he]
  exact hz

/-- Kind: proved theorem; the actual transported integral local trace
induces `H² ≃ ℤ₂`, by the proved boundary kernel and a proved trace-one
cycle. This is a coefficient invariant isomorphism, not a Kummer
orthogonality assumption (Nekovář 5.1.3, 5.2.1; Milne I.2.3). -/
theorem orientedLocalTrace_inducesIsoH2
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint) :
    InducesIsoH2 (C := natCx (restrictedLineComplex (S := S) w)) (orientedLocalTrace (S := S) W w) :=
  ⟨orientedLocalTrace_kernel W w, orientedLocalTrace_cycle_one W w hH⟩

end LocalInvariantIsomorphism

section LiteralFiniteClassDictionary

/-- Kind: definition; canonical transport of actual point one-cycles
from the separable closure to the algebraic closure
(tex 3413–3438; Silverman III.7). -/
def pointCycleToAlg (F : Type) [Field F] [CharZero F] [DecidableEq F]
    (B : WeierstrassCurve F) [B.IsElliptic] :
    LinearMap.ker ((pointComplex F B).d 1 2).hom →ₗ[ℤ_[2]]
      LinearMap.ker ((actualIntegralComplex F B).d 1 2).hom where
  toFun c := ⟨((IntegralTransport.toAlgComplex F B).f 1).hom c.val, by
    change ((actualIntegralComplex F B).d 1 2).hom
      (((IntegralTransport.toAlgComplex F B).f 1).hom c.val) = 0
    have hc : ((pointComplex F B).d 1 2).hom c.val = 0 := c.property
    have h := congrArg (fun f => f.hom c.val) ((IntegralTransport.toAlgComplex F B).comm 1 2)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hc, map_zero] using h⟩
  map_add' c d := Subtype.ext (map_add _ _ _)
  map_smul' r c := Subtype.ext (map_smul _ _ _)

/-- Kind: proved theorem; the same integral closure dictionaries are
inverse on genuine one-cycles (tex 3413–3438). -/
theorem pointCycleToAlg_sep (F : Type) [Field F] [CharZero F] [DecidableEq F]
    (B : WeierstrassCurve F) [B.IsElliptic]
    (c : LinearMap.ker ((pointComplex F B).d 1 2).hom) :
    IntegralTransport.toSepCycle F B (pointCycleToAlg F B c) = c := by
  apply Subtype.ext
  change ((IntegralTransport.toSepComplex F B).f 1).hom
    (((IntegralTransport.toAlgComplex F B).f 1).hom c.val) = c.val
  have h := congrArg (fun f => (f.f 1).hom c.val) (IntegralTransport.toAlgComplex_toSepComplex F B)
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h

/-- Kind: proved theorem; the canonical closure cycle map preserves the
actual finite class reduction (tex 3413–3438; Milne I.3.4). -/
theorem pointCycleToAlg_h1 (F : Type) [Field F] [CharZero F] [DecidableEq F]
    (B : WeierstrassCurve F) [B.IsElliptic] (a : ℕ)
    (c : LinearMap.ker ((pointComplex F B).d 1 2).hom) :
    actualH1Reduction F B a (pointCycleToAlg F B c) =
      FiniteTrace.hOneToAlg F B (2 ^ a) (pointH1Reduction F B a c) := by
  have h := IntegralTransport.integralReduction_square F B a (pointCycleToAlg F B c)
  rw [pointCycleToAlg_sep] at h
  exact (FiniteTrace.hOneToAlg F B (2 ^ a)).symm_apply_eq.mp h.symm

/-- Kind: proved theorem; actual finite Kummer class reduction sees
integral scalars through their canonical finite residues
(tex 3413–3438; Milne I.3.4). -/
theorem pointH1Reduction_smul (F : Type) [Field F] [CharZero F] [DecidableEq F]
    (B : WeierstrassCurve F) [B.IsElliptic] (a : ℕ) (r : ℤ_[2])
    (c : LinearMap.ker ((pointComplex F B).d 1 2).hom) :
    pointH1Reduction F B a (r • c) = (PadicInt.toZModPow a r).val • pointH1Reduction F B a c := by
  apply (FiniteTrace.hOneToAlg F B (2 ^ a)).injective
  rw [map_nsmul, ← pointCycleToAlg_h1, ← pointCycleToAlg_h1, map_smul,
    IntegralKummer.actualH1Reduction_smul]

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

/-- Kind: definition; the inclusion of the literal Kummer one-term in
actual continuous cycles (tex 3413–3438). -/
def integralConditionCycleMap : (integralCondition (S := S) W w).X 1 →ₗ[ℤ_[2]]
    LinearMap.ker ((restrictedPointComplex (S := S) W w).d 1 2).hom where
  toFun u := ⟨u.val, by
    exact (Submodule.mem_bot ℤ_[2]).mp
      (condP_d_mem
        (tateKummerZ W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w)
        (tateKummerZ_cocycle W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w)
        1 u.val u.property)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Kind: definition; actual one-cycles whose specified finite class
lies in the genuine Kummer image. Scalar closure is proved by the
canonical finite residue action (tex 3413–3438; Milne I.3.4). -/
def finiteKummerCycles (a : ℕ) : Submodule ℤ_[2]
    (LinearMap.ker ((restrictedPointComplex (S := S) W w).d 1 2).hom) where
  carrier := {c | pointH1Reduction (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) a
    (localPointCycleMap (S := S) W w c) ∈
      ((W.baseChange (w.adicCompletion K)).kummerMap (2 ^ a) (twoPower_isUnit (w.adicCompletion K) a)).range}
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [map_zero, map_zero]
    exact AddSubgroup.zero_mem _
  add_mem' hU hV := by
    simp only [Set.mem_setOf_eq] at hU hV ⊢
    rw [map_add, map_add]
    exact AddSubgroup.add_mem _ hU hV
  smul_mem' r c hU := by
    simp only [Set.mem_setOf_eq] at hU ⊢
    rw [map_smul, pointH1Reduction_smul]
    exact AddSubgroup.nsmul_mem _ hU _

/-- Kind: definition; the same finite-Kummer cycle submodule read in
the full continuous one-cochains (tex 3413–3438; Milne I.3.4). -/
def finiteKummerCochains (a : ℕ) : Submodule ℤ_[2] ((restrictedPointComplex (S := S) W w).X 1) :=
  (finiteKummerCycles (S := S) W w a).map
    (LinearMap.ker ((restrictedPointComplex (S := S) W w).d 1 2).hom).subtype

/-- Kind: proved theorem; every literal integral Kummer one-term has
its genuine Kummer class at every fixed finite level, including the
entire scalar span and all continuous boundaries
(tex 3413–3438; Milne I.3.4). -/
theorem integralCondition_finite_Kummer (a : ℕ)
    (u : (integralCondition (S := S) W w).X 1) :
    pointH1Reduction (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) a
      (localPointCycleMap (S := S) W w (integralConditionCycleMap W w u)) ∈
        ((W.baseChange (w.adicCompletion K)).kummerMap (2 ^ a) (twoPower_isUnit (w.adicCompletion K) a)).range := by
  let V := finiteKummerCochains (S := S) W w a
  have hZ : tateKummerZ W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w ≤ V := by
    apply Submodule.span_le.mpr
    rintro _ ⟨P, rfl⟩
    refine ⟨globalKummerCycle (S := S) W w P, ?_, rfl⟩
    change pointH1Reduction (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) a
      (localPointCycleMap (S := S) W w (globalKummerCycle (S := S) W w P)) ∈
        ((W.baseChange (w.adicCompletion K)).kummerMap (2 ^ a) (twoPower_isUnit (w.adicCompletion K) a)).range
    rw [localKummerCycle_class]
    exact ⟨P, rfl⟩
  have hB : contB1 ℤ_[2] (Gloc K w) (ResMod (locMap K S w) (TateS K S W)) ≤ V := by
    intro v hv
    obtain ⟨b, rfl⟩ := (mem_contB1_iff v).mp hv
    let c : LinearMap.ker ((restrictedPointComplex (S := S) W w).d 1 2).hom :=
      ⟨contD ℤ_[2] (Gloc K w) (ResMod (locMap K S w) (TateS K S W)) 0 b, contD_contD 0 b⟩
    refine ⟨c, ?_, rfl⟩
    have hb : ((pointComplex (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).d 0 1).hom
        (((localPointCochainMap W w).f 0).hom b) = (localPointCycleMap W w c).val := by
      change ((pointComplex (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).d 0 1).hom
        (((localPointCochainMap W w).f 0).hom b) =
        ((localPointCochainMap W w).f 1).hom (((restrictedPointComplex (S := S) W w).d 0 1).hom b)
      have h := congrArg (fun f => f.hom b) ((localPointCochainMap W w).comm 0 1)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
    have hzero := ActualConeModels.point_reduction_boundary K w (W.baseChange (w.adicCompletion K)) a
      (localPointCycleMap W w c) (((localPointCochainMap W w).f 0).hom b) hb
    change pointH1Reduction (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) a
      (localPointCycleMap W w c) ∈
        ((W.baseChange (w.adicCompletion K)).kummerMap (2 ^ a) (twoPower_isUnit (w.adicCompletion K) a)).range
    rw [hzero]
    exact AddSubgroup.zero_mem _
  obtain ⟨c, hmem, hval⟩ := (show u.val ∈ V from (sup_le hZ hB) u.property)
  have he : c = integralConditionCycleMap (S := S) W w u := Subtype.ext hval
  change pointH1Reduction (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) a
    (localPointCycleMap (S := S) W w c) ∈
      ((W.baseChange (w.adicCompletion K)).kummerMap (2 ^ a) (twoPower_isUnit (w.adicCompletion K) a)).range at hmem
  rw [he] at hmem
  exact hmem

end LiteralFiniteClassDictionary

end ZInQ.Contrib.RC53Assist.DKLocalAdapter
