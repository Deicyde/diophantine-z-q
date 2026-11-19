import ZInQKernel.Contrib.RC53Assist.Boundary45Stage.Identification
import ZInQKernel.Contrib.OneProof.RC.BaseZeroLimit.NonVacuity

/-!
# Obstructions to interpreting the conditional packet as a retained model

The constructions and counterexamples below were found in an independent
review. They show that the unrestricted packet does not identify the finite
Heegner construction or its retained finite free model. They are not
counterexamples to the conditional coordinate-boundary theorem.

The model fields can be erased even with a fixed place partition and fixed
representatives. The global class premise is equivalent to the global
boundary obligation. With an empty Kummer partition every local condition
is full, and arbitrary finite model matrices and ranks remain admissible.

No arithmetic assertion is introduced or discharged here. In particular the
actual support-field division-point input is retained as a premise.
-/

set_option maxHeartbeats 600000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions

open CategoryTheory NumberField IsDedekindDomain Matrix
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps ZInQ.Manuscript.RC.BaseZeroAssembly
open ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage
open ZInQ.Manuscript.RC.BaseZeroLimit
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

section FixedPacket

variable {K : Type} [Field K] [NumberField K] [DecidableEq K]
  {S S0 : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K) [W.IsElliptic]
  (i : ℕ) (hS : S0 ⊆ S) (hFull : FullTorsion K S0 W (2 ^ i))
  (Pold : Set (HeightOneSpectrum (𝓞 K)))
  (hdiv : GlobalDivisionPointsInSupport (S0 := S0) W i)
  {P : W.toAffine.Point} (T : SplitNormStage P) (L : ℤ) (N M0 : ℕ)

/-- Found in an independent review: every model field can be erased while
retaining the supplied stage, place partition and arithmetic representatives. -/
def eraseModel (C : CentralRetainedInput W i hS hFull Pold hdiv T L N M0)
    (A : Matrix (Fin N) (Fin M0) ℤ_[2]) :
    CentralRetainedInput W i hS hFull Pold hdiv T L N M0 :=
  { C with
    p1 := 0
    p0 := 0
    dC := A
    hdC := by intro v w; simp
    zeta := 0
    jay := 0
    hzeta := by ext a; simp
    hjay := by ext a; simp }

/-- Erasure leaves the actual representatives untouched and accepts any matrix. -/
theorem eraseModel_spec (C : CentralRetainedInput W i hS hFull Pold hdiv T L N M0)
    (A : Matrix (Fin N) (Fin M0) ℤ_[2]) :
    (eraseModel W i hS hFull Pold hdiv T L N M0 C A).zG = C.zG ∧
      (eraseModel W i hS hFull Pold hdiv T L N M0 C A).zU = C.zU ∧
      (eraseModel W i hS hFull Pold hdiv T L N M0 C A).jU = C.jU ∧
      (eraseModel W i hS hFull Pold hdiv T L N M0 C A).p1 = 0 ∧
      (eraseModel W i hS hFull Pold hdiv T L N M0 C A).p0 = 0 ∧
      (eraseModel W i hS hFull Pold hdiv T L N M0 C A).dC = A ∧
      (eraseModel W i hS hFull Pold hdiv T L N M0 C A).zeta = 0 ∧
      (eraseModel W i hS hFull Pold hdiv T L N M0 C A).jay = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Found in an independent review: the class premise is exactly the global
boundary obligation, and does not derive it for a specified constructed class. -/
theorem class_premise_iff_global_boundary
    (zG : (centralSelData W i hS hFull Pold).G.X 1) :
    cochainClass (centralSelData W i hS hFull Pold) zG =
      globalKummerMap W i hdiv hS hFull Pold (L • T.W) ↔
    ∃ g : (centralSelData W i hS hFull Pold).G.X 0,
      (centralSelData W i hS hFull Pold).G.d 0 1 rfl g =
        zG - (L * (T.a - 2)) • globalKummerCocycle W i hdiv hS hFull Pold P := by
  let D := centralSelData W i hS hFull Pold
  have he : cochainClass D (zG - (L * (T.a - 2)) •
      globalKummerCocycle W i hdiv hS hFull Pold P) =
      cochainClass D zG - globalKummerMap W i hdiv hS hFull Pold (L • T.W) := by
    rw [map_sub, map_zsmul, T.weightedPoint_eq, smul_smul, map_zsmul, globalKummerMap_apply]
  rw [← sub_eq_zero, ← he, cochainClass_eq_zero_iff]

/-- Found in an independent review: a single Kummer Selmer lift manufactures
all representatives and zero projections, even with the old partition fixed. -/
def zeroProjectionInputFixed
    (jU : (centralSelData W i hS hFull Pold).U.X 1)
    (jL : (centralSelData W i hS hFull Pold).L.X 0)
    (hjU : (centralSelData W i hS hFull Pold).U.d 1 2 rfl jU = 0)
    (hj : (centralSelData W i hS hFull Pold).res.f 1 1 rfl
        (globalKummerCocycle W i hdiv hS hFull Pold P) -
      (centralSelData W i hS hFull Pold).ι.f 1 1 rfl jU =
        (centralSelData W i hS hFull Pold).L.d 0 1 rfl jL)
    (A : Matrix (Fin N) (Fin M0) ℤ_[2]) :
    CentralRetainedInput W i hS hFull Pold hdiv T L N M0 := by
  let c : ℤ := L * (T.a - 2)
  let jG := globalKummerCocycle W i hdiv hS hFull Pold P
  refine
    { zG := c • jG
      hzG := by rw [map_zsmul, globalKummerCocycle_closed, smul_zero]
      zU := c • jU
      jU := jU
      zL := c • jL
      jL := jL
      hzU := by rw [map_zsmul, hjU, smul_zero]
      hjU := hjU
      hz := by rw [map_zsmul, map_zsmul, ← smul_sub, hj, map_zsmul]
      hj := hj
      hzcls := ?_
      p1 := 0
      p0 := 0
      dC := A
      hdC := by intro v w; simp
      zeta := 0
      jay := 0
      hzeta := by ext a; simp
      hjay := by ext a; simp }
  rw [map_zsmul, ← globalKummerMap_apply, T.weightedPoint_eq, smul_smul, map_zsmul]

/-- The manufactured representative is exactly the multiplied Kummer cocycle. -/
theorem zeroProjectionInputFixed_spec
    (jU : (centralSelData W i hS hFull Pold).U.X 1)
    (jL : (centralSelData W i hS hFull Pold).L.X 0)
    (hjU : (centralSelData W i hS hFull Pold).U.d 1 2 rfl jU = 0)
    (hj : (centralSelData W i hS hFull Pold).res.f 1 1 rfl
        (globalKummerCocycle W i hdiv hS hFull Pold P) -
      (centralSelData W i hS hFull Pold).ι.f 1 1 rfl jU =
        (centralSelData W i hS hFull Pold).L.d 0 1 rfl jL)
    (A : Matrix (Fin N) (Fin M0) ℤ_[2]) :
    (zeroProjectionInputFixed W i hS hFull Pold hdiv T L N M0 jU jL hjU hj A).zG =
      (L * (T.a - 2)) • globalKummerCocycle W i hdiv hS hFull Pold P ∧
      (zeroProjectionInputFixed W i hS hFull Pold hdiv T L N M0 jU jL hjU hj A).p1 = 0 ∧
      (zeroProjectionInputFixed W i hS hFull Pold hdiv T L N M0 jU jL hjU hj A).dC = A :=
  ⟨rfl, rfl, rfl⟩

end FixedPacket

section EmptyPartition

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K) [W.IsElliptic]
  (i : ℕ) (hFull : FullTorsion K S W (2 ^ i))

/-- Found in an independent review: the allowed empty old partition gives a full condition. -/
theorem emptyPartition_at (v : Places K S) :
    urOutside (Set.Subset.refl S) (ZMod (2 ^ i)) (CentralCoeff (S0 := S) W i)
      (fun v _ => centralOldCondition W i (Set.Subset.refl S) hFull ∅ v) v =
    fullAt K S (ZMod (2 ^ i)) (InflMod (Set.Subset.refl S) (CentralCoeff (S0 := S) W i)) v := by
  unfold urOutside
  rw [dite_eq_left v.2]
  change centralOldCondition W i (Set.Subset.refl S) hFull ∅ v = _
  unfold centralOldCondition
  exact ite_eq_right (Set.notMem_empty v.1)

/-- The entire allowed empty-partition datum is relaxed, without a Kummer place. -/
theorem emptyPartition_conditions :
    centralConditions W i (Set.Subset.refl S) hFull ∅ =
      relaxedConditions (ZMod (2 ^ i)) (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) (InflMod (Set.Subset.refl S) (CentralCoeff (S0 := S) W i)) := by
  unfold centralConditions
  have he := funext (emptyPartition_at W i hFull)
  rw [he]
  rfl

/-- The central data with empty partition are exactly the full Galois data. -/
theorem emptyPartition_data :
    centralSelData W i (Set.Subset.refl S) hFull ∅ =
      galoisSelData K S (ZMod (2 ^ i)) (InflMod (Set.Subset.refl S) (CentralCoeff (S0 := S) W i))
        (relaxedConditions (ZMod (2 ^ i)) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (InflMod (Set.Subset.refl S) (CentralCoeff (S0 := S) W i))) := by
  unfold centralSelData
  rw [emptyPartition_conditions]

/-- A Selmer lift is automatic for the allowed all-full pattern. -/
theorem fullPattern_lift :
    ∀ (z : (centralSelData W i (Set.Subset.refl S) hFull ∅).G.X 1),
    (centralSelData W i (Set.Subset.refl S) hFull ∅).G.d 1 2 rfl z = 0 →
    ∃ (u : (centralSelData W i (Set.Subset.refl S) hFull ∅).U.X 1)
      (l : (centralSelData W i (Set.Subset.refl S) hFull ∅).L.X 0),
      (centralSelData W i (Set.Subset.refl S) hFull ∅).U.d 1 2 rfl u = 0 ∧
      (centralSelData W i (Set.Subset.refl S) hFull ∅).res.f 1 1 rfl z -
        (centralSelData W i (Set.Subset.refl S) hFull ∅).ι.f 1 1 rfl u =
          (centralSelData W i (Set.Subset.refl S) hFull ∅).L.d 0 1 rfl l := by
  rw [emptyPartition_data W i hFull]
  intro z hz
  let D := galoisSelData K S (ZMod (2 ^ i))
    (InflMod (Set.Subset.refl S) (CentralCoeff (S0 := S) W i))
    (relaxedConditions (ZMod (2 ^ i)) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod (Set.Subset.refl S) (CentralCoeff (S0 := S) W i)))
  refine ⟨D.res.f 1 1 rfl z, 0, ?_, ?_⟩
  · have h := D.res.comm 1 2 1 2 rfl rfl rfl rfl z
    have hzD : D.G.d 1 2 rfl z = 0 := hz
    change D.L.d 1 2 rfl (D.res.f 1 1 rfl z) = 0
    rw [← h, hzD, map_zero]
  · change D.res.f 1 1 rfl z - D.res.f 1 1 rfl z = D.L.d 0 1 rfl 0
    rw [sub_self, map_zero]

variable [DecidableEq K]
  (hdiv : GlobalDivisionPointsInSupport (S0 := S) W i)
  {P : W.toAffine.Point} (T : SplitNormStage P) (L : ℤ) (N M0 : ℕ)

/-- Found in an independent review: arbitrary matrices and ranks are admissible,
using only the retained torsion/division inputs and no arithmetic-stage identification. -/
theorem arbitrary_model_record (A : Matrix (Fin N) (Fin M0) ℤ_[2]) :
    ∃ C : CentralRetainedInput W i (Set.Subset.refl S) hFull ∅ hdiv T L N M0,
      C.p1 = 0 ∧ C.p0 = 0 ∧ C.dC = A ∧ C.zeta = 0 ∧ C.jay = 0 := by
  obtain ⟨u, l, hu, hl⟩ := fullPattern_lift W i hFull
    (globalKummerCocycle W i hdiv (Set.Subset.refl S) hFull ∅ P)
    (globalKummerCocycle_closed W i hdiv (Set.Subset.refl S) hFull ∅ P)
  exact ⟨zeroProjectionInputFixed W i (Set.Subset.refl S) hFull ∅ hdiv T L N M0 u l hu hl A,
    rfl, rfl, rfl, rfl, rfl⟩

/-- The degeneracy persists at precision one, multiplier one and positive ranks. -/
theorem positive_precision_trivial_stage
    (hF : FullTorsion K S W (2 ^ 1))
    (hD : GlobalDivisionPointsInSupport (S0 := S) W 1) (P : W.toAffine.Point) :
    ∃ R : RetainedStage45 P 1 1 1 1,
      R.S = selfStage P ∧ R.dC = 1 ∧ R.p1 = 0 ∧ R.p0 = 0 ∧ R.zeta = 0 ∧ R.jay = 0 := by
  obtain ⟨C, hp1, hp0, hd, hz, hj⟩ := arbitrary_model_record W 1 hF hD (selfStage P) 1 1 1 1
  exact ⟨centralRetainedStage W 1 (Set.Subset.refl S) hF ∅ hD (selfStage P) 1 1 1 C,
    rfl, hd, hp1, hp0, hz, hj⟩

end EmptyPartition

end ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions
