import ZInQKernel.Contrib.RC53Assist.Boundary45.LocalFacts
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.KummerImage
import ZInQKernel.Contrib.OneProof.RC.BaseZeroLimit.Boundary

/-!
# Genuine central data for the retained finite boundary

The local data are fixed by the elliptic curve, the coefficient character,
the decomposition embeddings, and the specified Kummer places. Their
coefficient maps are the actual twist and torsion comparisons. There is no
arbitrary cocycle span or existential choice of a Selmer datum.

Before specialization, the actual Kummer/full/unramified pattern equals the
mixed-stage datum as complexes with maps. At the base and at t = 0, the
coefficient comparison is the actual Galois-compatible quotient M/tM over
Z/2^i. The same coefficient projection carries each actual Kummer cocycle
and its span to the specified central Kummer cocycle and span.

The central datum supplies the two representative-level local hypotheses.
The conditional retained-stage constructor uses those proofs, the canonical
class map and the actual global division-point Kummer map. Its input packet
is unrestricted in the norm stage, place partition, representatives and
model projections: it does not identify the actual arithmetic stage or the
retained finite free model. In particular the model may be erased without
changing the representatives. The local proofs work at every precision,
including the genuine zero coefficient ring at precision zero.

The arithmetic division points over the support field, the actual constructed
class, its local Selmer-cone representatives, and a normalized finite-model
comparison are not supplied by that conditional packet. Ring-class fields
and CM points are not constructed here. Nor is a comparison from the integral
derived Kummer object to these explicit finite cochain conditions, or the
complete base-zero leaf, asserted. The obstructions to interpreting the
packet as an identification were found in an independent review.

The manuscript passages used are lines 2914-2936, 3254-3266, 3278-3295,
3372-3405, 3413-3438, 3458-3463, 3479-3498, and 3912-3921. The local and
coefficient proofs use existing continuous cochain definitions and algebra.
No printed arithmetic assertion is introduced.
-/

set_option maxHeartbeats 600000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

section Local

variable {K : Type} [Field K] [NumberField K]
  {S S0 : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)

/-- The two boundary hypotheses for the actual, non-inflated Kummer map. -/
theorem actualKummerAt_localFacts (s : KS K S) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)
    (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α]
    (hFull : FullTorsion K S W (2 ^ i)) (v : Places K S)
    (hα : IsLocallyQuadAt i α (quadChar s hs hs0) v.1) :
    Boundary45Local.LocalFacts (actualKummerAt W i s hs hs0 α hFull v hα).i := by
  classical
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  exact Boundary45Local.cocycleCondition_localFacts _ _

variable (hS : S0 ⊆ S) (s : KS K S0) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S0) h) (hs0 : s ≠ 0)
  (α : GKS K S0 →* (Acoef i)ˣ) [IsOpenKer α]
  (hFull : FullTorsion K S0 W (2 ^ i))

/-- The two boundary hypotheses for the actual inflated Kummer map. -/
theorem actualKummerAtS_localFacts (v : Places K S)
    (hα : IsLocallyQuadAt i α (quadChar s hs hs0) v.1) :
    Boundary45Local.LocalFacts (actualKummerAtS hS W i s hs hs0 α hFull v hα).i := by
  classical
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  exact Boundary45Local.cocycleCondition_localFacts _ _

omit [IsOpenKer α] in
/-- The genuine coefficient inclusion is nondegenerate at positive precision. -/
theorem kummerIotaS_injective (hi : i ≠ 0) (v : Places K S) :
    Function.Injective (kummerIotaS hS W i s hs hs0 α hFull v) := by
  intro t t' htt
  apply kummerIotaBase_injective (S := S0) W i s hs hs0 α hFull v.1 hi
  exact htt

omit [W.IsElliptic] in
/-- Equality of the spans gives equality of the local complexes together with their maps. -/
theorem cocycleCondAt_congr (v : Places K S)
    (Z Z' : Submodule (Acoef i)
      (contCochain (Acoef i) (Gloc K v.1)
        (ResMod (locMap K S v.1) (MinS hS W i α)) 1))
    (hZ : ∀ z ∈ Z, contD (Acoef i) (Gloc K v.1)
      (ResMod (locMap K S v.1) (MinS hS W i α)) 1 z = 0)
    (hZ' : ∀ z ∈ Z', contD (Acoef i) (Gloc K v.1)
      (ResMod (locMap K S v.1) (MinS hS W i α)) 1 z = 0)
    (he : Z = Z') :
    (⟨cocycleCondition Z hZ, cocycleConditionι Z hZ⟩ :
      CondAt K S (Acoef i) (MinS hS W i α) v) =
      ⟨cocycleCondition Z' hZ', cocycleConditionι Z' hZ'⟩ := by
  subst Z'
  rfl

open scoped Classical in
/-- The actual local Kummer class map for the inflated coefficient module. -/
def actualKummerMapS (v : Places K S)
    (hα : IsLocallyQuadAt i α (quadChar s hs hs0) v.1) :
    (localTwist W h v.1).toAffine.Point →+
      (locAt K S (Acoef i) (MinS hS W i α) v).toCC.homology 1 :=
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  kummerMapIn (Acoef i) (kummerIotaS hS W i s hs hs0 α hFull v)
    (kummerIotaS_smul hS W i s hs hs0 α hFull v hα)

open scoped Classical in
/-- The inflated condition has exactly the image of the genuine local Kummer map. -/
theorem actualKummerAtS_range_eq_span (v : Places K S)
    (hα : IsLocallyQuadAt i α (quadChar s hs hs0) v.1) :
    LinearMap.range (HomologicalComplex.homologyMap
      (GHom.toCC (actualKummerAtS hS W i s hs hs0 α hFull v hα).i) 1).hom =
      Submodule.span (Acoef i)
        (Set.range (actualKummerMapS W i hS s hs hs0 α hFull v hα)) := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  exact range_homologyMap_kummerConditionIn (Acoef i)
    (kummerIotaS hS W i s hs hs0 α hFull v)
    (kummerIotaS_smul hS W i s hs hs0 α hFull v hα)

variable (P : Set (HeightOneSpectrum (𝓞 K)))
  (hα : ∀ v ∈ P, IsLocallyQuadAt i α (quadChar s hs hs0) v)

/-- The full places are specified, not chosen through a local-condition existential.
Outside the coefficient support this set is ignored and the unramified condition is used. -/
def fixedFullPlaces : Set (Places K S) := {v | v.1 ∉ P}

open scoped Classical in
/-- The actual extended Kummer span at the Kummer places, zero at the unused places.
The zero branches do not replace any Kummer condition: those places are full or unramified. -/
def fixedKummerSpan (v : Places K S) :
    Submodule (Acoef i)
      (contCochain (Acoef i) (Gloc K v.1)
        (ResMod (locMap K S v.1) (MinS hS W i α)) 1) :=
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  if v.1 ∈ P then kummerZ' (Acoef i) (kummerIotaS hS W i s hs hs0 α hFull v) else ⊥

include hα in
/-- The actual spans satisfy the cocycle hypothesis; it is not an additional leaf. -/
theorem fixedKummerSpan_cocycle (v : Places K S) :
    ∀ z ∈ fixedKummerSpan W i hS s hs hs0 α hFull P v,
      contD (Acoef i) (Gloc K v.1)
        (ResMod (locMap K S v.1) (MinS hS W i α)) 1 z = 0 := by
  classical
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  unfold fixedKummerSpan
  split_ifs with hv
  · exact kummerZ'_cocycle (Acoef i) (kummerIotaS hS W i s hs hs0 α hFull v)
      (kummerIotaS_smul hS W i s hs hs0 α hFull v (hα v.1 hv))
  · intro z hz
    have hz0 : z = 0 := (Submodule.mem_bot _).1 hz
    rw [hz0, map_zero]

/-- The prescribed actual Selmer datum: Kummer at the specified old places,
full at the other old places, and unramified outside the coefficient support. -/
def kummerFullSelData : SelData (Acoef i) :=
  kummerSelData hS W i s hs hs0 α hFull P hα
    (fun v _ _ => fullAt K S (Acoef i) (MinS hS W i α) v)

/-- Equality of the actual Kummer datum with the mixed-stage datum, including every map. -/
theorem kummerFullSelData_eq_mixed :
    kummerFullSelData W i hS s hs hs0 α hFull P hα =
      Boundary45Local.mixedStageSelData hS W i α (fixedFullPlaces P)
        (fixedKummerSpan W i hS s hs hs0 α hFull P)
        (fixedKummerSpan_cocycle W i hS s hs hs0 α hFull P hα) := by
  classical
  unfold kummerFullSelData kummerSelData Boundary45Local.mixedStageSelData
  congr 1
  funext v hv
  by_cases hvP : v.1 ∈ P
  · rw [dite_eq_left hvP]
    unfold Boundary45Local.mixedStageCond fixedFullPlaces
    simp only [Set.mem_ofPred_eq]
    rw [ite_eq_right (not_not.mpr hvP)]
    have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    exact (cocycleCondAt_congr W i hS α v
      (fixedKummerSpan W i hS s hs hs0 α hFull P v)
      (kummerZ' (Acoef i) (kummerIotaS hS W i s hs hs0 α hFull v))
      (fixedKummerSpan_cocycle W i hS s hs hs0 α hFull P hα v)
      (kummerZ'_cocycle (Acoef i) (kummerIotaS hS W i s hs hs0 α hFull v)
        (kummerIotaS_smul hS W i s hs hs0 α hFull v (hα v.1 hvP)))
      (by unfold fixedKummerSpan; exact ite_eq_left hvP)).symm
  · rw [dite_eq_right hvP]
    unfold Boundary45Local.mixedStageCond fixedFullPlaces
    simp only [Set.mem_ofPred_eq]
    rw [ite_eq_left hvP]

/-- Both local hypotheses for the fixed actual datum, with no free span or local-fact input. -/
theorem kummerFullSelData_localFacts :
    Boundary45Local.LocalFacts (kummerFullSelData W i hS s hs hs0 α hFull P hα).ι := by
  rw [kummerFullSelData_eq_mixed W i hS s hs hs0 α hFull P hα]
  exact Boundary45Local.mixedStage_localFacts hS W i α (fixedFullPlaces P)
    (fixedKummerSpan W i hS s hs hs0 α hFull P)
    (fixedKummerSpan_cocycle W i hS s hs hs0 α hFull P hα)

open scoped Classical in
/-- The entire fixed datum is the genuine continuous Galois Selmer datum.
This equality fixes the global and local groups, differentials, restriction and inclusion. -/
theorem kummerFullSelData_eq_galois :
    letI := acoefTop i
    haveI := acoefTop_discrete i
    kummerFullSelData W i hS s hs hs0 α hFull P hα =
      galoisSelData K S (Acoef i) (MinS hS W i α)
        (actualConditions hS W i α (fun v _ =>
          if hP : v.1 ∈ P then actualKummerAtS hS W i s hs hs0 α hFull v (hα v.1 hP)
          else fullAt K S (Acoef i) (MinS hS W i α) v)) := rfl

/-- In every nonnegative degree the global group is the actual continuous cochain group. -/
theorem kummerFullSelData_global_X (n : ℕ) :
    (kummerFullSelData W i hS s hs hs0 α hFull P hα).G.X n =
      ModuleCat.of (Acoef i) (contCochain (Acoef i) (GKS K S) (MinS hS W i α) n) := rfl

/-- The local group is the product of the actual local continuous cochain groups. -/
theorem kummerFullSelData_local_X (n : ℕ) :
    (kummerFullSelData W i hS s hs hs0 α hFull P hα).L.X n =
      ModuleCat.of (Acoef i) (∀ v : Places K S,
        contCochain (Acoef i) (Gloc K v.1)
          (ResMod (locMap K S v.1) (MinS hS W i α)) n) := rfl

/-- Localization is restriction along the specified decomposition maps, not an arbitrary map. -/
theorem kummerFullSelData_res_apply (n : ℕ)
    (c : (kummerFullSelData W i hS s hs hs0 α hFull P hα).G.X n) (v : Places K S) :
    (kummerFullSelData W i hS s hs hs0 α hFull P hα).res.f n n rfl c v =
      ((resCochains (k := Acoef i) (M := MinS hS W i α) (locMap K S v.1)).f n).hom c := rfl

/-- Finite support gives the existing Galois-data predicate, for these fixed objects. -/
theorem kummerFullSelData_isGalois (hSfin : S.Finite) :
    ZInQ.Manuscript.RC.Wiring.IsGaloisSelData
      (kummerFullSelData W i hS s hs hs0 α hFull P hα) :=
  isGaloisSelData_kummerSelData hS W i s hs hs0 α hFull hSfin P hα _
    (fun v _ _ => fullAt_isInjective K S (Acoef i) (MinS hS W i α) v)

end Local

section Geometric

open scoped Classical
open Finset WeierstrassCurve

variable {K : Type} [Field K] [NumberField K] [DecidableEq K]
  {S0 : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) (H : IntermediateField K (KS K S0))

/-- The canonical inclusion of the points over the base field into the specified extension. -/
def geometricPointInclusion : W.toAffine.Point →+ (W.baseChange H).toAffine.Point :=
  (Affine.Point.map (W' := W) (Algebra.ofId K H)).comp
    (Affine.Point.equivBaseChangeSelf W.toAffine).toAddMonoidHom

omit [NumberField K] in
/-- The inclusion is injective because the field map is injective. -/
theorem geometricPointInclusion_injective : Function.Injective (geometricPointInclusion W H) :=
  (Affine.Point.map_injective _).comp (Affine.Point.equivBaseChangeSelf W.toAffine).injective

/-- The genuine finite Galois action on points, as integral linear endomorphisms. -/
def geometricPointAction : (H ≃ₐ[K] H) →* Module.End ℤ (W.baseChange H).toAffine.Point where
  toFun σ :=
    { toFun := Affine.Point.map (W' := W) σ.toAlgHom
      map_add' := map_add _
      map_smul' := fun z P => map_zsmul _ z P }
  map_one' := by
    ext P
    rcases P with _ | ⟨x, y, hxy⟩ <;> rfl
  map_mul' σ τ := by
    ext P
    exact (Affine.Point.map_map τ.toAlgHom σ.toAlgHom P).symm

/-- Abelianity of the specified finite Galois extension, with its canonical multiplication.
For a ring-class field this is class-field theory, not a freely chosen group structure. -/
def AbelianStageExtension : Prop :=
  ∀ σ τ : H ≃ₐ[K] H, σ * τ = τ * σ

variable [FiniteDimensional K H] (hAb : AbelianStageExtension H)
  (N : Subgroup (H ≃ₐ[K] H)) (Q : Finset (H ≃ₐ[K] H))
  (hQ : ∀ δ : H ≃ₐ[K] H, ∃! t, t ∈ Q ∧ t⁻¹ * δ ∈ N)
  (y1 yr : (W.baseChange H).toAffine.Point)
  (hy1 : ∀ n ∈ N, geometricPointAction W H n y1 = y1)
  (a : ℤ) (σ : H ≃ₐ[K] H)

/-- The split clause of (4.1), at the specified points and subgroup.
The arithmetic source is Cai-Chen-Liu, Theorem 2.15, through the elliptic quotient,
as used in manuscript lines 2914-2936. This definition does not assert the equality. -/
def GeometricSplitNormRelation : Prop :=
  ∑ n ∈ Finset.univ.filter (· ∈ N), geometricPointAction W H n yr =
    a • y1 - geometricPointAction W H σ y1 - geometricPointAction W H σ⁻¹ y1

variable (hnorm : GeometricSplitNormRelation W H N y1 yr a σ)
  (P : W.toAffine.Point)
  (hP : geometricPointInclusion W H P = ∑ t ∈ Q, geometricPointAction W H t y1)

/-- The finite norm stage on the actual points and automorphisms of the specified extension.
The weighted point is determined by (4.1), not supplied by an existential field.
Identifying the extension and points with the ring-class field and CM points is a separate
arithmetic task; it is not implied by the norm relation alone. -/
def geometricSplitNormStage : SplitNormStage P := by
  letI : CommGroup (H ≃ₐ[K] H) :=
    { (inferInstance : Group (H ≃ₐ[K] H)) with mul_comm := hAb }
  refine
    { Pt := (W.baseChange H).toAffine.Point
      Δ := H ≃ₐ[K] H
      act := geometricPointAction W H
      N := N
      T := Q
      hT := hQ
      y1 := y1
      hy1 := hy1
      yr := yr
      a := a
      σ := σ
      hnorm := hnorm
      incl := geometricPointInclusion W H
      hincl := geometricPointInclusion_injective W H
      hP := hP
      W := (a - 2) • P
      hW := ?_ }
  have he := ZInQ.Manuscript.RC.HeegnerAlgebra.B1b_twisted_split_norm (A := ℤ)
    (geometricPointAction W H) N Q hQ 1 (fun _ _ => rfl) yr y1 hy1 a σ hnorm
  simp only [MonoidHom.one_apply, Units.val_one, one_smul, inv_one, Int.cast_id] at he
  rw [map_zsmul, hP, he]
  congr 1
  ring

omit [NumberField K] in
/-- The stage keeps the genuine point group, Galois group, inclusion, action and trace multiplier.
In particular it is not an unrelated norm stage carried beside the local datum. -/
theorem geometricSplitNormStage_spec :
    (geometricSplitNormStage W H hAb N Q hQ y1 yr hy1 a σ hnorm P hP).Pt =
        (W.baseChange H).toAffine.Point ∧
      (geometricSplitNormStage W H hAb N Q hQ y1 yr hy1 a σ hnorm P hP).Δ = (H ≃ₐ[K] H) ∧
      (geometricSplitNormStage W H hAb N Q hQ y1 yr hy1 a σ hnorm P hP).incl =
        geometricPointInclusion W H ∧
      (geometricSplitNormStage W H hAb N Q hQ y1 yr hy1 a σ hnorm P hP).act =
        geometricPointAction W H ∧
      (geometricSplitNormStage W H hAb N Q hQ y1 yr hy1 a σ hnorm P hP).W = (a - 2) • P :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end Geometric

section FiniteCharacter

variable {K : Type} [Field K] [NumberField K]
  {S S0 : Set (HeightOneSpectrum (𝓞 K))}
  (i : ℕ) (s : KS K S0) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S0) h) (hs0 : s ≠ 0)
  (H : IntermediateField K (KS K S0)) [Normal K H] [FiniteDimensional K H]
  (ξ : (H ≃ₐ[K] H) →* Multiplicative (ZMod (2 ^ (2 * i))))

/-- The actual coefficient character is inflated from the specified finite Galois extension. -/
def finiteStageCharacter : GKS K S0 →* (Acoef i)ˣ :=
  alphaChar i (quadChar s hs hs0) (inflChar H ξ)

/-- Continuity of the finite-stage coefficient character is supplied by finite Galois inflation. -/
theorem finiteStageCharacter_isOpenKer : IsOpenKer (finiteStageCharacter i s hs hs0 H ξ) :=
  alphaChar_isOpenKer i (quadChar s hs hs0) (inflChar H ξ) (inflChar_isOpen_ker H ξ)

variable (P : Set (HeightOneSpectrum (𝓞 K)))

/-- The required old local type, stated on the same finite Galois character.
This is the locally trivial moving-character input of manuscript lines 2729 and 3500-3506. -/
def FiniteCharacterOldType : Prop :=
  ∀ v ∈ P, ∀ g : Gloc K v, inflChar H ξ (locMap K S0 v g) = 1

omit [FiniteDimensional K H] in
/-- The old local character hypothesis follows for the actual inflated character. -/
theorem finiteStageCharacter_localType (hξ : FiniteCharacterOldType i H ξ P) :
    ∀ v ∈ P, IsLocallyQuadAt i (finiteStageCharacter i s hs hs0 H ξ) (quadChar s hs hs0) v :=
  fun v hv => isLocallyQuadAt_alphaChar i (quadChar s hs hs0) (inflChar H ξ) v (hξ v hv)

variable (hS : S0 ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic]
  (hFull : FullTorsion K S0 W (2 ^ i)) (hξ : FiniteCharacterOldType i H ξ P)

/-- The genuine Kummer/full/unramified datum of the specified finite Galois stage. -/
def finiteStageSelData : SelData (Acoef i) :=
  letI := finiteStageCharacter_isOpenKer i s hs hs0 H ξ
  kummerFullSelData W i hS s hs hs0 (finiteStageCharacter i s hs hs0 H ξ) hFull P
    (finiteStageCharacter_localType i s hs hs0 H ξ P hξ)

/-- The two local boundary hypotheses hold on this fixed finite Galois stage.
No arbitrary character, cocycle span, coefficient map or Selmer datum is introduced. -/
theorem finiteStageSelData_localFacts :
    Boundary45Local.LocalFacts (finiteStageSelData i s hs hs0 H ξ P hS W hFull hξ).ι := by
  have := finiteStageCharacter_isOpenKer i s hs hs0 H ξ
  exact kummerFullSelData_localFacts W i hS s hs hs0
    (finiteStageCharacter i s hs hs0 H ξ) hFull P
    (finiteStageCharacter_localType i s hs hs0 H ξ P hξ)

end FiniteCharacter

section CentralCharacter

variable {K : Type} [Field K] [NumberField K]
  {S0 : Set (HeightOneSpectrum (𝓞 K))} (i : ℕ) (hi : i ≠ 0)

omit [NumberField K] in
/-- The square root at the base character is the specified element one. -/
theorem baseSqrt_sq : (1 : KS K S0) ^ 2 = algebraMap K (KS K S0) 1 := by
  rw [one_pow, map_one]

/-- The actual quadratic character at the base is trivial. -/
theorem baseQuadChar_eq_one :
    quadChar (1 : KS K S0) baseSqrt_sq one_ne_zero = 1 := by
  ext g
  simp [quadChar]

/-- Evaluation at the central parameter kills the actual moving variable. -/
theorem acoefConst_tA : acoefConst i hi (ZInQ.Manuscript.RC.HeegnerAlgebra.tA i) = 0 := by
  change Polynomial.constantCoeff (Polynomial.X : Polynomial (ZMod (2 ^ i))) = 0
  exact Polynomial.coeff_X_zero

omit [NumberField K] in
/-- The actual moving character specializes to one for every finite character. -/
theorem acoefConst_movingChar (ξ : GKS K S0 →* Multiplicative (ZMod (2 ^ (2 * i))))
    (g : GKS K S0) :
    acoefConst i hi ((movingCharS i ξ g : (Acoef i)ˣ) : Acoef i) = 1 := by
  have hunit : acoefConst i hi ((onePlusT i : (Acoef i)ˣ) : Acoef i) = 1 := by
    change acoefConst i hi (1 + ZInQ.Manuscript.RC.HeegnerAlgebra.tA i) = 1
    rw [map_add, map_one, acoefConst_tA i hi, add_zero]
  change acoefConst i hi (((onePlusT i : (Acoef i)ˣ) : Acoef i) ^
    (Multiplicative.toAdd (ξ g)).val) = 1
  rw [map_pow, hunit, one_pow]

/-- At the base and at the central parameter, the coefficient character is trivial.
The finite Galois extension and character are retained in the statement. -/
theorem finiteStageCharacter_at_base_const
    (H : IntermediateField K (KS K S0)) [Normal K H] [FiniteDimensional K H]
    (ξ : (H ≃ₐ[K] H) →* Multiplicative (ZMod (2 ^ (2 * i)))) (g : GKS K S0) :
    acoefConst i hi
      ((finiteStageCharacter i (1 : KS K S0) baseSqrt_sq one_ne_zero H ξ g : (Acoef i)ˣ) :
        Acoef i) = 1 := by
  unfold finiteStageCharacter
  rw [baseQuadChar_eq_one]
  change acoefConst i hi
    ((((intUnitsTo (Acoef i)) 1 : (Acoef i)ˣ) : Acoef i) *
      ((movingCharS i (inflChar H ξ) g : (Acoef i)ˣ) : Acoef i)) = 1
  rw [map_one, Units.val_one, one_mul]
  exact acoefConst_movingChar i hi (inflChar H ξ) g

end CentralCharacter

section CentralEvaluation

open scoped Classical

/-- The actual coefficient evaluation at every precision, including the zero ring at precision zero. -/
def centralEval (i : ℕ) : Acoef i →+* ZMod (2 ^ i) :=
  if hi : i ≠ 0 then acoefConst i hi else
    { toFun := fun _ => 0
      map_zero' := rfl
      map_one' := by
        have hi0 : i = 0 := not_not.mp hi
        subst i
        exact @Subsingleton.elim (ZMod 1) inferInstance _ _
      map_add' := fun _ _ => (zero_add 0).symm
      map_mul' := fun _ _ => (zero_mul 0).symm }

/-- At positive precision this is the existing constant-coefficient map. -/
theorem centralEval_pos (i : ℕ) (hi : i ≠ 0) : centralEval i = acoefConst i hi := by
  unfold centralEval
  exact dite_eq_left hi

/-- The actual finite-stage character has trivial central specialization at every precision. -/
theorem finiteStageCharacter_at_base_central {K : Type} [Field K] [NumberField K]
    {S0 : Set (HeightOneSpectrum (𝓞 K))} (i : ℕ)
    (H : IntermediateField K (KS K S0)) [Normal K H] [FiniteDimensional K H]
    (ξ : (H ≃ₐ[K] H) →* Multiplicative (ZMod (2 ^ (2 * i)))) (g : GKS K S0) :
    centralEval i
      ((finiteStageCharacter i (1 : KS K S0) baseSqrt_sq one_ne_zero H ξ g : (Acoef i)ˣ) :
        Acoef i) = 1 := by
  by_cases hi : i ≠ 0
  · rw [centralEval_pos i hi]
    exact finiteStageCharacter_at_base_const i hi H ξ g
  · have hi0 : i = 0 := not_not.mp hi
    subst i
    exact @Subsingleton.elim (ZMod 1) inferInstance _ _

/-- The central coefficient ring is included by constant polynomials. -/
def centralScalarSection (i : ℕ) : ZMod (2 ^ i) →+* Acoef i :=
  (Ideal.Quotient.mk _).comp Polynomial.C

/-- The total central evaluation is polynomial evaluation at zero. -/
theorem centralEval_mk (i : ℕ) (p : Polynomial (ZMod (2 ^ i))) :
    centralEval i (Ideal.Quotient.mk _ p) = p.coeff 0 := by
  by_cases hi : i ≠ 0
  · rw [centralEval_pos i hi]
    rfl
  · have hi0 : i = 0 := not_not.mp hi
    subst i
    exact @Subsingleton.elim (ZMod 1) inferInstance _ _

/-- The constant-polynomial inclusion is a section of the actual central evaluation. -/
theorem centralEval_scalarSection (i : ℕ) (a : ZMod (2 ^ i)) :
    centralEval i (centralScalarSection i a) = a := by
  change centralEval i (Ideal.Quotient.mk _ (Polynomial.C a)) = a
  rw [centralEval_mk]
  simp

/-- The moving variable is zero in the actual central coefficient ring. -/
theorem centralEval_tA (i : ℕ) : centralEval i (ZInQ.Manuscript.RC.HeegnerAlgebra.tA i) = 0 := by
  rw [ZInQ.Manuscript.RC.HeegnerAlgebra.tA, centralEval_mk]
  exact Polynomial.coeff_X_zero

/-- Every actual coefficient is its constant term plus a multiple of the moving variable. -/
theorem coefficient_central_decomposition (i : ℕ) (a : Acoef i) :
    ∃ b : Acoef i, a = ZInQ.Manuscript.RC.HeegnerAlgebra.tA i * b +
      centralScalarSection i (centralEval i a) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨Ideal.Quotient.mk _ p.divX, ?_⟩
  rw [centralEval_mk]
  change Ideal.Quotient.mk _ p =
    Ideal.Quotient.mk _ Polynomial.X * Ideal.Quotient.mk _ p.divX +
      Ideal.Quotient.mk _ (Polynomial.C (p.coeff 0))
  rw [← map_mul, ← map_add]
  exact congrArg (Ideal.Quotient.mk _) (Polynomial.X_mul_divX_add p).symm

end CentralEvaluation

section CentralCoefficients

open TensorProduct

variable {K : Type} [Field K]
  {S0 : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  (i : ℕ)

/-- The central coefficient module, over the actual ring Z/2^i and with trivial character. -/
abbrev CentralCoeff : Type :=
  CoefMod (ZMod (2 ^ i)) (1 : GKS K S0 →* (ZMod (2 ^ i))ˣ)
    (TorsS K S0 W ((2 ^ i : ℕ) : ℤ))

/-- The actual central coefficient projection, induced by evaluation at t = 0. -/
def centralCoeffProjection (α : GKS K S0 →* (Acoef i)ˣ) :
    Mcoef K S0 W i α →+ CentralCoeff (S0 := S0) W i :=
  (CoefMod.equiv (ZMod (2 ^ i)) 1 (TorsS K S0 W ((2 ^ i : ℕ) : ℤ))).toAddEquiv.toAddMonoidHom.comp
    ((TensorProduct.map (centralEval i).toAddMonoidHom.toIntLinearMap
      (LinearMap.id : TorsS K S0 W ((2 ^ i : ℕ) : ℤ) →ₗ[ℤ]
        TorsS K S0 W ((2 ^ i : ℕ) : ℤ))).toAddMonoidHom.comp
      (CoefMod.equiv (Acoef i) α (TorsS K S0 W ((2 ^ i : ℕ) : ℤ))).symm.toAddEquiv.toAddMonoidHom)

/-- The projection keeps the actual torsion point and evaluates only its coefficient. -/
theorem centralCoeffProjection_tmul (α : GKS K S0 →* (Acoef i)ˣ) (a : Acoef i)
    (t : TorsS K S0 W ((2 ^ i : ℕ) : ℤ)) :
    centralCoeffProjection W i α
      (CoefMod.equiv (Acoef i) α _ (a ⊗ₜ[ℤ] t)) =
      CoefMod.equiv (ZMod (2 ^ i)) 1 _ (centralEval i a ⊗ₜ[ℤ] t) := by
  change TensorProduct.map (centralEval i).toAddMonoidHom.toIntLinearMap
    (LinearMap.id : TorsS K S0 W ((2 ^ i : ℕ) : ℤ) →ₗ[ℤ] _) (a ⊗ₜ[ℤ] t) = _
  rw [TensorProduct.map_tmul]
  rfl

/-- The coefficient map t ↦ 1 ⊗ t is unchanged by central projection. -/
theorem centralCoeffProjection_oneTmul (α : GKS K S0 →* (Acoef i)ˣ)
    (t : TorsS K S0 W ((2 ^ i : ℕ) : ℤ)) :
    centralCoeffProjection W i α (oneTmul (Acoef i) α _ t) =
      oneTmul (ZMod (2 ^ i)) (1 : GKS K S0 →* (ZMod (2 ^ i))ˣ) _ t := by
  rw [oneTmul_apply, centralCoeffProjection_tmul, map_one]
  rfl

/-- Central projection intertwines the genuine Galois actions when the character specializes to one. -/
theorem centralCoeffProjection_galois (α : GKS K S0 →* (Acoef i)ˣ)
    (hα : ∀ g, centralEval i ((α g : (Acoef i)ˣ) : Acoef i) = 1)
    (g : GKS K S0) (m : Mcoef K S0 W i α) :
    centralCoeffProjection W i α (g • m) = g • centralCoeffProjection W i α m := by
  obtain ⟨x, rfl⟩ := (CoefMod.equiv (Acoef i) α (TorsS K S0 W ((2 ^ i : ℕ) : ℤ))).surjective m
  induction x using TensorProduct.inductionOn with
  | tmul a t =>
    rw [CoefMod.smul_tmul, centralCoeffProjection_tmul, centralCoeffProjection_tmul,
      CoefMod.smul_tmul]
    simp only [MonoidHom.one_apply, Units.val_one, one_mul]
    rw [map_mul, hα g, one_mul]
  | add x y hx hy =>
    simpa only [map_add, smul_add] using congrArg₂ (· + ·) hx hy

/-- The constant-coefficient section on the actual tensor coefficient module. -/
def centralCoeffSection (α : GKS K S0 →* (Acoef i)ˣ) :
    CentralCoeff (S0 := S0) W i →+ Mcoef K S0 W i α :=
  (CoefMod.equiv (Acoef i) α (TorsS K S0 W ((2 ^ i : ℕ) : ℤ))).toAddEquiv.toAddMonoidHom.comp
    ((TensorProduct.map (centralScalarSection i).toAddMonoidHom.toIntLinearMap
      (LinearMap.id : TorsS K S0 W ((2 ^ i : ℕ) : ℤ) →ₗ[ℤ]
        TorsS K S0 W ((2 ^ i : ℕ) : ℤ))).toAddMonoidHom.comp
      (CoefMod.equiv (ZMod (2 ^ i)) 1 (TorsS K S0 W ((2 ^ i : ℕ) : ℤ))).symm.toAddEquiv.toAddMonoidHom)

/-- The actual central projection has its canonical coefficient section as a right inverse. -/
theorem centralCoeffProjection_section (α : GKS K S0 →* (Acoef i)ˣ)
    (m : CentralCoeff (S0 := S0) W i) :
    centralCoeffProjection W i α (centralCoeffSection W i α m) = m := by
  obtain ⟨x, rfl⟩ := (CoefMod.equiv (ZMod (2 ^ i)) 1 (TorsS K S0 W ((2 ^ i : ℕ) : ℤ))).surjective m
  change TensorProduct.map (centralEval i).toAddMonoidHom.toIntLinearMap
      (LinearMap.id : TorsS K S0 W ((2 ^ i : ℕ) : ℤ) →ₗ[ℤ] _)
      (TensorProduct.map (centralScalarSection i).toAddMonoidHom.toIntLinearMap
        (LinearMap.id : TorsS K S0 W ((2 ^ i : ℕ) : ℤ) →ₗ[ℤ] _) x) = x
  induction x using TensorProduct.inductionOn with
  | tmul a t =>
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul]
    change centralEval i (centralScalarSection i a) ⊗ₜ[ℤ] t = a ⊗ₜ[ℤ] t
    rw [centralEval_scalarSection]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]

/-- Central projection is semilinear for the actual coefficient evaluation. -/
theorem centralCoeffProjection_smul (α : GKS K S0 →* (Acoef i)ˣ)
    (a : Acoef i) (m : Mcoef K S0 W i α) :
    centralCoeffProjection W i α (a • m) = centralEval i a • centralCoeffProjection W i α m := by
  obtain ⟨x, rfl⟩ := (CoefMod.equiv (Acoef i) α (TorsS K S0 W ((2 ^ i : ℕ) : ℤ))).surjective m
  change TensorProduct.map (centralEval i).toAddMonoidHom.toIntLinearMap
      (LinearMap.id : TorsS K S0 W ((2 ^ i : ℕ) : ℤ) →ₗ[ℤ] _) (a • x) =
    centralEval i a • TensorProduct.map (centralEval i).toAddMonoidHom.toIntLinearMap
      (LinearMap.id : TorsS K S0 W ((2 ^ i : ℕ) : ℤ) →ₗ[ℤ] _) x
  induction x using TensorProduct.inductionOn with
  | tmul b t =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul]
    change centralEval i (a * b) ⊗ₜ[ℤ] t = (centralEval i a * centralEval i b) ⊗ₜ[ℤ] t
    rw [map_mul]
  | add x y hx hy =>
    rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- The actual coefficient module decomposes into its central part and a multiple of t. -/
theorem centralCoeff_decomposition (α : GKS K S0 →* (Acoef i)ˣ) (m : Mcoef K S0 W i α) :
    ∃ b : Mcoef K S0 W i α,
      m = ZInQ.Manuscript.RC.HeegnerAlgebra.tA i • b +
        centralCoeffSection W i α (centralCoeffProjection W i α m) := by
  obtain ⟨x, rfl⟩ := (CoefMod.equiv (Acoef i) α (TorsS K S0 W ((2 ^ i : ℕ) : ℤ))).surjective m
  change ∃ b : (Acoef i) ⊗[ℤ] TorsS K S0 W ((2 ^ i : ℕ) : ℤ),
    x = ZInQ.Manuscript.RC.HeegnerAlgebra.tA i • b +
      TensorProduct.map (centralScalarSection i).toAddMonoidHom.toIntLinearMap
        (LinearMap.id : TorsS K S0 W ((2 ^ i : ℕ) : ℤ) →ₗ[ℤ] _)
        (TensorProduct.map (centralEval i).toAddMonoidHom.toIntLinearMap
          (LinearMap.id : TorsS K S0 W ((2 ^ i : ℕ) : ℤ) →ₗ[ℤ] _) x)
  induction x using TensorProduct.inductionOn with
  | tmul a t =>
    obtain ⟨b, hb⟩ := coefficient_central_decomposition i a
    refine ⟨b ⊗ₜ[ℤ] t, ?_⟩
    rw [TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.map_tmul, TensorProduct.map_tmul]
    change a ⊗ₜ[ℤ] t = (ZInQ.Manuscript.RC.HeegnerAlgebra.tA i * b) ⊗ₜ[ℤ] t +
      centralScalarSection i (centralEval i a) ⊗ₜ[ℤ] t
    rw [← TensorProduct.add_tmul, ← hb]
  | add x y hx hy =>
    obtain ⟨b, hb⟩ := hx
    obtain ⟨b', hb'⟩ := hy
    refine ⟨b + b', ?_⟩
    rw [smul_add, map_add, map_add]
    conv_lhs => rw [hb, hb']
    abel

/-- The kernel of the actual central projection is precisely t times the coefficient module. -/
theorem centralCoeffProjection_eq_zero_iff (α : GKS K S0 →* (Acoef i)ˣ)
    (m : Mcoef K S0 W i α) :
    centralCoeffProjection W i α m = 0 ↔
      ∃ b : Mcoef K S0 W i α, ZInQ.Manuscript.RC.HeegnerAlgebra.tA i • b = m := by
  constructor
  · intro hm
    obtain ⟨b, hb⟩ := centralCoeff_decomposition W i α m
    rw [hm, map_zero, add_zero] at hb
    exact ⟨b, hb.symm⟩
  · rintro ⟨b, rfl⟩
    rw [centralCoeffProjection_smul, centralEval_tA, zero_smul]

/-- The actual image tM as a submodule of the original coefficient module. -/
def centralMovingImage (α : GKS K S0 →* (Acoef i)ˣ) : Submodule (Acoef i) (Mcoef K S0 W i α) :=
  LinearMap.range (ZInQ.Manuscript.RC.HeegnerAlgebra.tA i •
    (LinearMap.id : Mcoef K S0 W i α →ₗ[Acoef i] Mcoef K S0 W i α))

/-- The group kernel is the same actual submodule tM. -/
theorem centralCoeffProjection_ker (α : GKS K S0 →* (Acoef i)ˣ) :
    (centralCoeffProjection W i α).ker = (centralMovingImage W i α).toAddSubgroup := by
  ext m
  change centralCoeffProjection W i α m = 0 ↔
    ∃ b : Mcoef K S0 W i α, ZInQ.Manuscript.RC.HeegnerAlgebra.tA i • b = m
  exact centralCoeffProjection_eq_zero_iff W i α m

/-- The genuine central coefficient fibre is the actual quotient M/tM. -/
def centralCoeffQuotientEquiv (α : GKS K S0 →* (Acoef i)ˣ) :
    (Mcoef K S0 W i α ⧸ (centralMovingImage W i α).toAddSubgroup) ≃+
      CentralCoeff (S0 := S0) W i :=
  (QuotientAddGroup.quotientAddEquivOfEq (centralCoeffProjection_ker W i α).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (centralCoeffProjection W i α)
      (fun m => ⟨centralCoeffSection W i α m, centralCoeffProjection_section W i α m⟩))

/-- This fibre identification is the actual coefficient projection on representatives. -/
theorem centralCoeffQuotientEquiv_mk (α : GKS K S0 →* (Acoef i)ˣ) (m : Mcoef K S0 W i α) :
    centralCoeffQuotientEquiv W i α (QuotientAddGroup.mk m) = centralCoeffProjection W i α m := rfl

variable [NumberField K]

/-- For the specified finite-stage character the actual quotient identification intertwines Galois. -/
theorem centralCoeffQuotientEquiv_galois
    (H : IntermediateField K (KS K S0)) [Normal K H] [FiniteDimensional K H]
    (ξ : (H ≃ₐ[K] H) →* Multiplicative (ZMod (2 ^ (2 * i)))) (g : GKS K S0)
    (m : Mcoef K S0 W i (finiteStageCharacter i (1 : KS K S0) baseSqrt_sq one_ne_zero H ξ)) :
    centralCoeffQuotientEquiv W i (finiteStageCharacter i (1 : KS K S0) baseSqrt_sq one_ne_zero H ξ)
        (QuotientAddGroup.mk (g • m)) =
      g • centralCoeffQuotientEquiv W i
        (finiteStageCharacter i (1 : KS K S0) baseSqrt_sq one_ne_zero H ξ) (QuotientAddGroup.mk m) := by
  rw [centralCoeffQuotientEquiv_mk, centralCoeffQuotientEquiv_mk]
  exact centralCoeffProjection_galois W i _ (finiteStageCharacter_at_base_central i H ξ) g m

omit [NumberField K] in
/-- Over Z/2^i, the actual map t ↦ 1 ⊗ t is bijective on the 2^i-torsion module. -/
theorem centralOneTmul_bijective :
    Function.Bijective (oneTmul (ZMod (2 ^ i)) (1 : GKS K S0 →* (ZMod (2 ^ i))ˣ)
      (TorsS K S0 W ((2 ^ i : ℕ) : ℤ))) := by
  have ht : ∀ t : TorsS K S0 W ((2 ^ i : ℕ) : ℤ), (2 ^ i : ℕ) • t = 0 := fun t =>
    Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.1 t.2)
  refine ⟨oneTmul_injective (ZMod (2 ^ i)) (RingHom.id _) 1 _ ht, ?_⟩
  intro m
  obtain ⟨x, rfl⟩ := (CoefMod.equiv (ZMod (2 ^ i)) 1 (TorsS K S0 W ((2 ^ i : ℕ) : ℤ))).surjective m
  induction x using TensorProduct.inductionOn with
  | tmul a t =>
    refine ⟨a.val • t, ?_⟩
    change (1 : ZMod (2 ^ i)) ⊗ₜ[ℤ] (a.val • t) = a ⊗ₜ[ℤ] t
    have hcoef : a.val • (1 : ZMod (2 ^ i)) = a := by
      rw [nsmul_eq_mul, mul_one]
      exact ZMod.natCast_zmod_val a
    exact (TensorProduct.smul_tmul a.val (1 : ZMod (2 ^ i)) t).symm.trans
      (congrArg (fun b : ZMod (2 ^ i) => b ⊗ₜ[ℤ] t) hcoef)
  | add x y hx hy =>
    obtain ⟨t, ht⟩ := hx
    obtain ⟨t', ht'⟩ := hy
    refine ⟨t + t', ?_⟩
    rw [map_add, ht, ht']
    rfl

variable [W.IsElliptic]

/-- The actual central coefficient module is finite; it is not an arbitrary finite module. -/
instance centralCoeff_finite : Finite (CentralCoeff (S0 := S0) W i) := by
  have : Finite (TorsS K S0 W ((2 ^ i : ℕ) : ℤ)) :=
    finite_torsS (by exact_mod_cast (pow_ne_zero i two_ne_zero : (2 : ℕ) ^ i ≠ 0))
  infer_instance

variable {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S0 ⊆ S)
  (hFull : FullTorsion K S0 W (2 ^ i))

/-- The actual central Kummer coefficient map, obtained by projecting the original map.
The local twist, its degree-zero torsion and the fixed decomposition embedding are retained. -/
def centralKummerIotaS (v : Places K S) :
    TorsAlg (v.1.adicCompletion K) (localTwist W 1 v.1) (2 ^ i) →+
      ResMod (locMap K S v.1) (InflMod hS (CentralCoeff (S0 := S0) W i)) :=
  (centralCoeffProjection W i (1 : GKS K S0 →* (Acoef i)ˣ)).comp
    (kummerIotaS hS W i (1 : KS K S0) baseSqrt_sq one_ne_zero 1 hFull v)

/-- Projecting the actual Kummer coefficient map for any finite character gives this same central map. -/
theorem centralKummerIotaS_from_actual (α : GKS K S0 →* (Acoef i)ˣ) (v : Places K S)
    (t : TorsAlg (v.1.adicCompletion K) (localTwist W 1 v.1) (2 ^ i)) :
    centralCoeffProjection W i α
      (kummerIotaS hS W i (1 : KS K S0) baseSqrt_sq one_ne_zero α hFull v t) =
      centralKummerIotaS W i hS hFull v t := rfl

/-- The central map is equivariant for the actual local action through localization and inflation. -/
theorem centralKummerIotaS_smul (v : Places K S) (g : Gloc K v.1)
    (t : TorsAlg (v.1.adicCompletion K) (localTwist W 1 v.1) (2 ^ i)) :
    centralKummerIotaS W i hS hFull v (g • t) =
      g • centralKummerIotaS W i hS hFull v t := by
  have hquad : IsLocallyQuadAt i (1 : GKS K S0 →* (Acoef i)ˣ)
      (quadChar (1 : KS K S0) baseSqrt_sq one_ne_zero) v.1 := by
    rw [baseQuadChar_eq_one]
    intro σ
    change 1 = intUnitsTo (Acoef i) 1
    exact (map_one _).symm
  change centralCoeffProjection W i 1
      (kummerIotaS hS W i (1 : KS K S0) baseSqrt_sq one_ne_zero 1 hFull v (g • t)) =
    (inflMap K hS (locMap K S v.1 g)) • centralCoeffProjection W i 1
      (kummerIotaS hS W i (1 : KS K S0) baseSqrt_sq one_ne_zero 1 hFull v t)
  rw [kummerIotaS_smul hS W i (1 : KS K S0) baseSqrt_sq one_ne_zero 1 hFull v hquad]
  change centralCoeffProjection (S0 := S0) W i 1
      ((inflMap K hS (locMap K S v.1 g)) •
        (show Mcoef K S0 W i 1 from
          kummerIotaS hS W i (1 : KS K S0) baseSqrt_sq one_ne_zero 1 hFull v t)) = _
  exact centralCoeffProjection_galois (S0 := S0) W i 1 (fun _ => by simp) _ _

open scoped Classical in
/-- The central coefficient map is the actual torsion identification followed by its scalar unit map. -/
theorem centralKummerIotaS_bijective (v : Places K S) :
    Function.Bijective (centralKummerIotaS W i hS hFull v) := by
  let β : TorsAlg (v.1.adicCompletion K) (localTwist W 1 v.1) (2 ^ i) ≃+
      TorsS K S0 W ((2 ^ i : ℕ) : ℤ) :=
    (twistTors (W.baseChange (v.1.adicCompletion K)) (algebraMap K (v.1.adicCompletion K) 1)
      two_ne_zero (localSqrt_ne_zero (1 : KS K S0) one_ne_zero v.1)
      (localSqrt_sq (1 : KS K S0) baseSqrt_sq v.1) (2 ^ i)).trans
        (compTorsEquiv (S := S0) W (2 ^ i) hFull v.1).symm
  have he : centralKummerIotaS W i hS hFull v =
      (oneTmul (ZMod (2 ^ i)) (1 : GKS K S0 →* (ZMod (2 ^ i))ˣ)
        (TorsS K S0 W ((2 ^ i : ℕ) : ℤ))).comp β.toAddMonoidHom := by
    ext t
    exact centralCoeffProjection_oneTmul W i 1 (β t)
  rw [he]
  exact (centralOneTmul_bijective (S0 := S0) W i).comp β.bijective

/-- The actual coefficient projection on continuous local cochains. -/
def localCochainProjection (α : GKS K S0 →* (Acoef i)ˣ) [IsOpenKer α]
    (v : Places K S) (n : ℕ) :
    contCochain (Acoef i) (Gloc K v.1) (ResMod (locMap K S v.1) (MinS hS W i α)) n →+
      contCochain (ZMod (2 ^ i)) (Gloc K v.1)
        (ResMod (locMap K S v.1) (InflMod hS (CentralCoeff (S0 := S0) W i))) n where
  toFun c := ⟨(fun g => centralCoeffProjection W i α (c.1 g)),
    (continuous_of_discreteTopology (f := centralCoeffProjection W i α)).comp c.2⟩
  map_zero' := by
    apply Subtype.ext
    funext g
    exact map_zero (centralCoeffProjection W i α)
  map_add' c c' := by
    apply Subtype.ext
    funext g
    exact map_add (centralCoeffProjection W i α) (c.1 g) (c'.1 g)

omit [W.IsElliptic] in
/-- The continuous cochain projection is semilinear for the same actual coefficient evaluation. -/
theorem localCochainProjection_smul (α : GKS K S0 →* (Acoef i)ˣ) [IsOpenKer α]
    (v : Places K S) (n : ℕ) (a : Acoef i)
    (c : contCochain (Acoef i) (Gloc K v.1) (ResMod (locMap K S v.1) (MinS hS W i α)) n) :
    localCochainProjection W i hS α v n (a • c) =
      centralEval i a • localCochainProjection W i hS α v n c := by
  apply Subtype.ext
  funext g
  exact centralCoeffProjection_smul W i α a (c.1 g)

open scoped Classical in
/-- Each actual extended Kummer cocycle projects to the same central Kummer cocycle. -/
theorem localCochainProjection_kummer (α : GKS K S0 →* (Acoef i)ˣ) [IsOpenKer α]
    (v : Places K S) (a : Acoef i) (p : (localTwist W 1 v.1).toAffine.Point) :
    haveI := isElliptic_localTwist W (one_ne_zero : (1 : K) ≠ 0) v.1
    localCochainProjection W i hS α v 1
        (kummerCocycleIn (kummerIotaS hS W i (1 : KS K S0) baseSqrt_sq one_ne_zero α hFull v) a p) =
      centralEval i a • kummerCocycleIn (centralKummerIotaS W i hS hFull v) 1 p := by
  have := isElliptic_localTwist W (one_ne_zero : (1 : K) ≠ 0) v.1
  apply Subtype.ext
  funext g
  let t := kummerFun (v.1.adicCompletion K) (localTwist W 1 v.1) (2 ^ i) p (g 0)
  let m : Mcoef K S0 W i α :=
    kummerIotaS hS W i (1 : KS K S0) baseSqrt_sq one_ne_zero α hFull v t
  change centralCoeffProjection W i α (a • m) =
    centralEval i a • ((1 : ZMod (2 ^ i)) • centralKummerIotaS W i hS hFull v t)
  have he : centralCoeffProjection W i α m = centralKummerIotaS W i hS hFull v t :=
    centralKummerIotaS_from_actual W i hS hFull α v t
  exact (centralCoeffProjection_smul W i α a m).trans
    ((congrArg (fun x : CentralCoeff (S0 := S0) W i => centralEval i a • x) he).trans
      (congrArg (fun x : CentralCoeff (S0 := S0) W i => centralEval i a • x)
        (one_smul (ZMod (2 ^ i)) (centralKummerIotaS W i hS hFull v t)).symm))

open scoped Classical in
/-- The image of the specified actual Kummer span is exactly the central Kummer span.
This is a comparison of the actual generators, with no free submodule parameter. -/
theorem localKummerSpan_projection (α : GKS K S0 →* (Acoef i)ˣ) [IsOpenKer α] (v : Places K S) :
    haveI := isElliptic_localTwist W (one_ne_zero : (1 : K) ≠ 0) v.1
    Set.range (fun z : kummerZ' (Acoef i)
        (kummerIotaS hS W i (1 : KS K S0) baseSqrt_sq one_ne_zero α hFull v) =>
      localCochainProjection W i hS α v 1 z) =
    (kummerZ' (ZMod (2 ^ i)) (centralKummerIotaS W i hS hFull v) :
      Set (contCochain (ZMod (2 ^ i)) (Gloc K v.1)
        (ResMod (locMap K S v.1) (InflMod hS (CentralCoeff (S0 := S0) W i))) 1)) := by
  have := isElliptic_localTwist W (one_ne_zero : (1 : K) ≠ 0) v.1
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    have key : ∀ c ∈ kummerZ' (Acoef i)
        (kummerIotaS hS W i (1 : KS K S0) baseSqrt_sq one_ne_zero α hFull v),
        localCochainProjection W i hS α v 1 c ∈
          kummerZ' (ZMod (2 ^ i)) (centralKummerIotaS W i hS hFull v) := by
      intro c hc
      induction hc using Submodule.span_induction with
      | mem c hc =>
        obtain ⟨⟨a, p⟩, rfl⟩ := hc
        rw [localCochainProjection_kummer]
        exact Submodule.smul_mem _ _ (kummerCocycleIn_mem (centralKummerIotaS W i hS hFull v) 1 p)
      | zero =>
        rw [map_zero]
        exact zero_mem _
      | add c c' hc hc' ih ih' =>
        rw [map_add]
        exact add_mem ih ih'
      | smul a c hc ih =>
        rw [localCochainProjection_smul]
        exact Submodule.smul_mem _ _ ih
    exact key z z.2
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨a, p⟩, rfl⟩ := hy
      refine ⟨⟨kummerCocycleIn
        (kummerIotaS hS W i (1 : KS K S0) baseSqrt_sq one_ne_zero α hFull v)
        (centralScalarSection i a) p, kummerCocycleIn_mem _ _ _⟩, ?_⟩
      change localCochainProjection W i hS α v 1
        (kummerCocycleIn (kummerIotaS hS W i (1 : KS K S0) baseSqrt_sq one_ne_zero α hFull v)
          (centralScalarSection i a) p) = kummerCocycleIn (centralKummerIotaS W i hS hFull v) a p
      rw [localCochainProjection_kummer, centralEval_scalarSection]
      exact (kummerCocycleIn_eq_smul (centralKummerIotaS W i hS hFull v) a p).symm
    | zero =>
      exact ⟨⟨0, zero_mem _⟩, map_zero (localCochainProjection W i hS α v 1)⟩
    | add y y' hy hy' ih ih' =>
      obtain ⟨z, hz⟩ := ih
      obtain ⟨z', hz'⟩ := ih'
      change localCochainProjection W i hS α v 1 z.val = y at hz
      change localCochainProjection W i hS α v 1 z'.val = y' at hz'
      refine ⟨z + z', ?_⟩
      change localCochainProjection W i hS α v 1 (z.val + z'.val) = y + y'
      exact (map_add (localCochainProjection W i hS α v 1) z.val z'.val).trans
        (congrArg₂ (· + ·) hz hz')
    | smul a y hy ih =>
      obtain ⟨z, hz⟩ := ih
      change localCochainProjection W i hS α v 1 z.val = y at hz
      refine ⟨centralScalarSection i a • z, ?_⟩
      change localCochainProjection W i hS α v 1 (centralScalarSection i a • z.val) = a • y
      rw [localCochainProjection_smul, centralEval_scalarSection, hz]

open scoped Classical in
/-- The actual Kummer local condition in the central Z/2^i coefficient fibre. -/
def centralKummerAt (v : Places K S) :
    CondAt K S (ZMod (2 ^ i)) (InflMod hS (CentralCoeff (S0 := S0) W i)) v :=
  haveI := isElliptic_localTwist W (one_ne_zero : (1 : K) ≠ 0) v.1
  kummerAt v (localTwist W 1 v.1) (2 ^ i) (centralKummerIotaS W i hS hFull v)
    (centralKummerIotaS_smul W i hS hFull v)

/-- The two boundary hypotheses for the actual central Kummer condition. -/
theorem centralKummerAt_localFacts (v : Places K S) :
    Boundary45Local.LocalFacts (centralKummerAt W i hS hFull v).i := by
  classical
  have := isElliptic_localTwist W (one_ne_zero : (1 : K) ≠ 0) v.1
  exact Boundary45Local.cocycleCondition_localFacts _ _

open scoped Classical in
/-- The actual local Kummer map in the central coefficient fibre. -/
def centralLocalKummerMap (v : Places K S) :
    (localTwist W 1 v.1).toAffine.Point →+
      (locAt K S (ZMod (2 ^ i)) (InflMod hS (CentralCoeff (S0 := S0) W i)) v).toCC.homology 1 :=
  haveI := isElliptic_localTwist W (one_ne_zero : (1 : K) ≠ 0) v.1
  kummerMapIn (ZMod (2 ^ i)) (centralKummerIotaS W i hS hFull v)
    (centralKummerIotaS_smul W i hS hFull v)

open scoped Classical in
/-- The central Kummer condition has exactly the actual local Kummer image. -/
theorem centralKummerAt_range_eq_span (v : Places K S) :
    LinearMap.range (HomologicalComplex.homologyMap
      (GHom.toCC (centralKummerAt W i hS hFull v).i) 1).hom =
      Submodule.span (ZMod (2 ^ i)) (Set.range (centralLocalKummerMap W i hS hFull v)) := by
  have := isElliptic_localTwist W (one_ne_zero : (1 : K) ≠ 0) v.1
  exact range_homologyMap_kummerConditionIn (ZMod (2 ^ i))
    (centralKummerIotaS W i hS hFull v) (centralKummerIotaS_smul W i hS hFull v)

variable (P : Set (HeightOneSpectrum (𝓞 K)))

open scoped Classical in
/-- The prescribed old local condition in the central fibre. -/
def centralOldCondition (v : Places K S) :
    CondAt K S (ZMod (2 ^ i)) (InflMod hS (CentralCoeff (S0 := S0) W i)) v :=
  if v.1 ∈ P then centralKummerAt W i hS hFull v
  else fullAt K S (ZMod (2 ^ i)) (InflMod hS (CentralCoeff (S0 := S0) W i)) v

/-- The genuine central local conditions, with unramified maps outside the coefficient support. -/
def centralConditions : GaloisLocalConditions K S (ZMod (2 ^ i)) (InflMod hS (CentralCoeff (S0 := S0) W i)) :=
  ofCondAt K S (ZMod (2 ^ i)) (InflMod hS (CentralCoeff (S0 := S0) W i))
    (urOutside hS (ZMod (2 ^ i)) (CentralCoeff (S0 := S0) W i)
      (fun v _ => centralOldCondition W i hS hFull P v))

/-- The actual continuous Selmer datum in the central coefficient fibre. -/
def centralSelData : SelData (ZMod (2 ^ i)) :=
  galoisSelData K S (ZMod (2 ^ i)) (InflMod hS (CentralCoeff (S0 := S0) W i))
    (centralConditions W i hS hFull P)

/-- The two local boundary hypotheses on the genuine Z/2^i datum consumed by retained stages. -/
theorem centralSelData_localFacts :
    Boundary45Local.LocalFacts (centralSelData W i hS hFull P).ι := by
  classical
  change Boundary45Local.LocalFacts (piMap (centralConditions W i hS hFull P).i)
  apply Boundary45Local.localFacts_pi
  intro v
  change Boundary45Local.LocalFacts
    (urOutside hS (ZMod (2 ^ i)) (CentralCoeff (S0 := S0) W i)
      (fun v _ => centralOldCondition W i hS hFull P v) v).i
  by_cases hv : v.1 ∈ S0
  · unfold urOutside
    rw [dite_eq_left hv]
    change Boundary45Local.LocalFacts (centralOldCondition W i hS hFull P v).i
    by_cases hvP : v.1 ∈ P
    · have he : centralOldCondition W i hS hFull P v = centralKummerAt W i hS hFull v := by
        unfold centralOldCondition
        exact ite_eq_left hvP
      rw [he]
      exact centralKummerAt_localFacts W i hS hFull v
    · have he : centralOldCondition W i hS hFull P v =
          fullAt K S (ZMod (2 ^ i)) (InflMod hS (CentralCoeff (S0 := S0) W i)) v := by
        unfold centralOldCondition
        exact ite_eq_right hvP
      rw [he]
      exact Boundary45Local.full_localFacts _
  · unfold urOutside
    rw [dite_eq_right hv]
    exact Boundary45Local.urAt_localFacts hS (ZMod (2 ^ i)) (CentralCoeff (S0 := S0) W i) v hv

/-- Every central global term is the actual continuous cochain group over Z/2^i. -/
theorem centralSelData_global_X (n : ℕ) :
    (centralSelData W i hS hFull P).G.X n =
      ModuleCat.of (ZMod (2 ^ i))
        (contCochain (ZMod (2 ^ i)) (GKS K S) (InflMod hS (CentralCoeff (S0 := S0) W i)) n) := rfl

/-- Every central local term is the product of the actual local continuous cochain groups. -/
theorem centralSelData_local_X (n : ℕ) :
    (centralSelData W i hS hFull P).L.X n =
      ModuleCat.of (ZMod (2 ^ i)) (∀ v : Places K S,
        contCochain (ZMod (2 ^ i)) (Gloc K v.1)
          (ResMod (locMap K S v.1) (InflMod hS (CentralCoeff (S0 := S0) W i))) n) := rfl

/-- These are literally the two representative-level statements required by RetainedStage45. -/
theorem centralSelData_localHypotheses :
    (∀ c : (centralSelData W i hS hFull P).L.X 0,
      (centralSelData W i hS hFull P).L.d 0 1 rfl c = 0 →
      ∃ w : (centralSelData W i hS hFull P).U.X 0,
        (centralSelData W i hS hFull P).U.d 0 1 rfl w = 0 ∧
          (centralSelData W i hS hFull P).ι.f 0 0 rfl w = c) ∧
    (∀ u : (centralSelData W i hS hFull P).U.X 1,
      (centralSelData W i hS hFull P).U.d 1 2 rfl u = 0 →
      (∃ c : (centralSelData W i hS hFull P).L.X 0,
        (centralSelData W i hS hFull P).ι.f 1 1 rfl u =
          (centralSelData W i hS hFull P).L.d 0 1 rfl c) →
      ∃ w : (centralSelData W i hS hFull P).U.X 0,
        (centralSelData W i hS hFull P).U.d 0 1 rfl w = u) :=
  centralSelData_localFacts W i hS hFull P

end CentralCoefficients

section Classes

variable {k : Type} [CommRing k]

/-- The canonical ambient group C^1/B^1. Its closed part is the first cohomology.
Using this ambient group avoids postulating a class map on nonclosed cochains. -/
abbrev cochainClasses (D : SelData k) : Type :=
  D.G.X 1 ⧸ LinearMap.range (D.G.d 0 1 rfl)

/-- The canonical class map on all global cochains. -/
def cochainClass (D : SelData k) : D.G.X 1 →+ cochainClasses D :=
  (LinearMap.range (D.G.d 0 1 rfl)).mkQ.toAddMonoidHom

/-- Its kernel is exactly the actual global coboundaries; no exactness leaf is needed. -/
theorem cochainClass_eq_zero_iff (D : SelData k) (c : D.G.X 1) :
    cochainClass D c = 0 ↔ ∃ g : D.G.X 0, D.G.d 0 1 rfl g = c :=
  (Submodule.Quotient.mk_eq_zero _).trans LinearMap.mem_range

/-- Actual first cohomology embeds in the canonical ambient cochain-class group. -/
def cohomologyToClasses (D : SelData k) : (D.G.toCC.homology 1) →ₗ[k] cochainClasses D :=
  (((D.G.toCC.homologyIsoSc' 0 1 2 (by simp) (by simp)).hom) ≫
    (D.G.toCC.sc' 0 1 2).homologyι ≫ (D.G.toCC.sc' 0 1 2).moduleCatOpcyclesIso.hom).hom

/-- The comparison retains the actual first cohomology, not merely its kernel criterion. -/
theorem cohomologyToClasses_injective (D : SelData k) : Function.Injective (cohomologyToClasses D) := by
  change Function.Injective
    ((((D.G.toCC.homologyIsoSc' 0 1 2 (by simp) (by simp)).hom) ≫
      (D.G.toCC.sc' 0 1 2).homologyι ≫ (D.G.toCC.sc' 0 1 2).moduleCatOpcyclesIso.hom).hom)
  exact (ModuleCat.mono_iff_injective _).1 inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- On actual closed representatives the ambient class is exactly the embedded homology class. -/
theorem cohomologyToClasses_π (D : SelData k) (c : D.G.toCC.cycles 1) :
    cohomologyToClasses D ((D.G.toCC.homologyπ 1).hom c) =
      cochainClass D ((D.G.toCC.iCycles 1).hom c) := by
  let S := D.G.toCC.sc' 0 1 2
  let f : D.G.toCC.homology 1 ⟶ ModuleCat.of k (cochainClasses D) :=
    (D.G.toCC.homologyIsoSc' 0 1 2 (by simp) (by simp)).hom ≫
      S.homologyι ≫ S.moduleCatOpcyclesIso.hom
  have hπ := D.G.toCC.π_homologyIsoSc'_hom 0 1 2 (by simp) (by simp)
  have hι := D.G.toCC.cyclesIsoSc'_hom_iCycles 0 1 2 (by simp) (by simp)
  have hf : D.G.toCC.homologyπ 1 ≫ f =
      D.G.toCC.iCycles 1 ≫ ModuleCat.ofHom (LinearMap.range (D.G.d 0 1 rfl)).mkQ := by
    calc
      D.G.toCC.homologyπ 1 ≫ f =
          (D.G.toCC.homologyπ 1 ≫ (D.G.toCC.homologyIsoSc' 0 1 2 (by simp) (by simp)).hom) ≫
            S.homologyι ≫ S.moduleCatOpcyclesIso.hom := by simp only [f, Category.assoc]
      _ = ((D.G.toCC.cyclesIsoSc' 0 1 2 (by simp) (by simp)).hom ≫ S.homologyπ) ≫
            S.homologyι ≫ S.moduleCatOpcyclesIso.hom :=
          congrArg (fun q => q ≫ S.homologyι ≫ S.moduleCatOpcyclesIso.hom) hπ
      _ = (D.G.toCC.cyclesIsoSc' 0 1 2 (by simp) (by simp)).hom ≫
            (S.homologyπ ≫ S.homologyι) ≫ S.moduleCatOpcyclesIso.hom := by simp only [Category.assoc]
      _ = (D.G.toCC.cyclesIsoSc' 0 1 2 (by simp) (by simp)).hom ≫
            (S.iCycles ≫ S.pOpcycles) ≫ S.moduleCatOpcyclesIso.hom :=
          congrArg (fun q => (D.G.toCC.cyclesIsoSc' 0 1 2 (by simp) (by simp)).hom ≫
            q ≫ S.moduleCatOpcyclesIso.hom) S.homology_π_ι
      _ = ((D.G.toCC.cyclesIsoSc' 0 1 2 (by simp) (by simp)).hom ≫ S.iCycles) ≫
            (S.pOpcycles ≫ S.moduleCatOpcyclesIso.hom) := by simp only [Category.assoc]
      _ = ((D.G.toCC.cyclesIsoSc' 0 1 2 (by simp) (by simp)).hom ≫ S.iCycles) ≫
            ModuleCat.ofHom (LinearMap.range (D.G.d 0 1 rfl)).mkQ :=
          congrArg (fun q => ((D.G.toCC.cyclesIsoSc' 0 1 2 (by simp) (by simp)).hom ≫ S.iCycles) ≫ q)
            S.pOpcycles_comp_moduleCatOpcyclesIso_hom
      _ = D.G.toCC.iCycles 1 ≫ ModuleCat.ofHom (LinearMap.range (D.G.d 0 1 rfl)).mkQ :=
          congrArg (fun q => q ≫ ModuleCat.ofHom (LinearMap.range (D.G.d 0 1 rfl)).mkQ) hι
  exact congrArg (fun g => g.hom c) hf

/-- Equality of classes in the canonical ambient group is exactly equality in actual H^1. -/
theorem cochainClasses_eq_iff_homology (D : SelData k) (c c' : D.G.toCC.cycles 1) :
    cochainClass D ((D.G.toCC.iCycles 1).hom c) =
        cochainClass D ((D.G.toCC.iCycles 1).hom c') ↔
      (D.G.toCC.homologyπ 1).hom c = (D.G.toCC.homologyπ 1).hom c' := by
  rw [← cohomologyToClasses_π, ← cohomologyToClasses_π]
  exact (cohomologyToClasses_injective D).eq_iff

end Classes

section GlobalKummer

open scoped Classical
open WeierstrassCurve

variable {K : Type} [Field K] [NumberField K] [DecidableEq K]
  {S0 : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)

/-- The actual points over the coefficient-support field, with their discrete topology. -/
def SupportPoints : Type := (W.baseChange (KS K S0)).toAffine.Point

instance supportPoints_addCommGroup : AddCommGroup (SupportPoints (S0 := S0) W) :=
  inferInstanceAs (AddCommGroup (W.baseChange (KS K S0)).toAffine.Point)

instance supportPoints_top : TopologicalSpace (SupportPoints (S0 := S0) W) := ⊥

instance supportPoints_discrete : DiscreteTopology (SupportPoints (S0 := S0) W) := ⟨rfl⟩

instance supportPoints_action : DistribMulAction (GKS K S0) (SupportPoints (S0 := S0) W) where
  smul g Q := Affine.Point.map (galS K S0 g).toAlgHom Q
  one_smul Q := pointMap_one Q
  mul_smul g h Q := (Affine.Point.map_map (galS K S0 h).toAlgHom (galS K S0 g).toAlgHom Q).symm
  smul_zero _ := map_zero _
  smul_add _ _ _ := map_add _ _ _

/-- This actual point action is continuous: its coordinate stabilizers are open. -/
instance supportPoints_continuousSMul : ContinuousSMul (GKS K S0) (SupportPoints (S0 := S0) W) := by
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro Q
  rcases Q with _ | ⟨x, y, hxy⟩
  · convert isOpen_univ
    ext g
    simp only [SetLike.mem_coe, Set.mem_univ, iff_true]
    change Affine.Point.map (galS K S0 g).toAlgHom 0 = 0
    exact map_zero _
  · refine Subgroup.isOpen_mono (H₁ := stabS K S0 x ⊓ stabS K S0 y) (fun g hg => ?_) ?_
    · rw [Subgroup.mem_inf, mem_stabS, mem_stabS] at hg
      change Affine.Point.map (galS K S0 g).toAlgHom (.some x y hxy) = .some x y hxy
      rw [Affine.Point.map_some, Affine.Point.some.injEq]
      exact ⟨hg.1, hg.2⟩
    · rw [Subgroup.coe_inf]
      exact (isOpen_stabS K S0 x).inter (isOpen_stabS K S0 y)

/-- The actual base-field point inclusion into the coefficient-support field. -/
def supportBasePoint : W.toAffine.Point →+ SupportPoints (S0 := S0) W :=
  (Affine.Point.map (W' := W) (Algebra.ofId K (KS K S0))).comp
    (Affine.Point.equivBaseChangeSelf W.toAffine).toAddMonoidHom

omit [NumberField K] in
/-- Base-field points are fixed by the actual Galois action. -/
theorem supportBasePoint_fixed (g : GKS K S0) (P : W.toAffine.Point) :
    g • supportBasePoint (S0 := S0) W P = supportBasePoint (S0 := S0) W P := by
  change Affine.Point.map (W' := W) (galS K S0 g).toAlgHom
      (Affine.Point.map (W' := W) (Algebra.ofId K (KS K S0))
        (Affine.Point.equivBaseChangeSelf W.toAffine P)) =
    Affine.Point.map (W' := W) (Algebra.ofId K (KS K S0))
      (Affine.Point.equivBaseChangeSelf W.toAffine P)
  rw [Affine.Point.map_map]
  rw [Subsingleton.elim ((galS K S0 g).toAlgHom.comp (Algebra.ofId K (KS K S0)))
    (Algebra.ofId K (KS K S0))]

variable (i : ℕ)

/-- The precise remaining global division-point input for the actual support field.
This is not a consequence of FullTorsion alone and is not asserted here as a printed theorem. -/
def GlobalDivisionPointsInSupport : Prop :=
  ∀ P : W.toAffine.Point, ∃ Q : SupportPoints (S0 := S0) W,
    (2 ^ i : ℕ) • Q = supportBasePoint (S0 := S0) W P

variable (hdiv : GlobalDivisionPointsInSupport (S0 := S0) W i)

/-- A genuine division point in the specified support field, when that arithmetic input is supplied. -/
def supportDivisionPoint (P : W.toAffine.Point) : SupportPoints (S0 := S0) W :=
  Classical.choose (hdiv P)

omit [NumberField K] in
/-- The chosen point is an actual division point of the specified base-field point. -/
theorem supportDivisionPoint_spec (P : W.toAffine.Point) :
    (2 ^ i : ℕ) • supportDivisionPoint W i hdiv P = supportBasePoint (S0 := S0) W P :=
  Classical.choose_spec (hdiv P)

/-- The support-field torsion, as a discrete submodule of the actual point group. -/
abbrev SupportTorsion : Type := AddSubgroup.torsionBy (SupportPoints (S0 := S0) W) ((2 ^ i : ℕ) : ℤ)

instance supportTorsion_action : DistribMulAction (GKS K S0) (SupportTorsion (S0 := S0) W i) where
  smul g t := ⟨g • t.1, by
    rw [AddSubgroup.torsionBy.nsmul_iff, smul_comm,
      AddSubgroup.torsionBy.nsmul_iff.1 t.2, smul_zero]⟩
  one_smul t := Subtype.ext (one_smul _ _)
  mul_smul g h t := Subtype.ext (mul_smul _ _ _)
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g t u := Subtype.ext (smul_add g t.1 u.1)

/-- The actual support torsion is carried to the central module by t ↦ 1 ⊗ t. -/
def supportTorsionCoefficient : SupportTorsion (S0 := S0) W i →+ CentralCoeff (S0 := S0) W i :=
  (oneTmul (ZMod (2 ^ i)) (1 : GKS K S0 →* (ZMod (2 ^ i))ˣ)
    (TorsS K S0 W ((2 ^ i : ℕ) : ℤ))).comp
      { toFun := fun t => ⟨t.1, t.2⟩
        map_zero' := rfl
        map_add' := fun _ _ => rfl }

omit [NumberField K] [DecidableEq K] in
/-- This is the actual Galois-equivariant coefficient inclusion, not a chosen map. -/
theorem supportTorsionCoefficient_smul (g : GKS K S0) (t : SupportTorsion (S0 := S0) W i) :
    supportTorsionCoefficient W i (g • t) = g • supportTorsionCoefficient W i t := by
  change oneTmul (ZMod (2 ^ i)) (1 : GKS K S0 →* (ZMod (2 ^ i))ˣ)
      (TorsS K S0 W ((2 ^ i : ℕ) : ℤ))
      (g • (show TorsS K S0 W ((2 ^ i : ℕ) : ℤ) from ⟨t.1, t.2⟩)) =
    g • oneTmul (ZMod (2 ^ i)) (1 : GKS K S0 →* (ZMod (2 ^ i))ˣ)
      (TorsS K S0 W ((2 ^ i : ℕ) : ℤ)) ⟨t.1, t.2⟩
  simpa using (smul_oneTmul (ZMod (2 ^ i)) (1 : GKS K S0 →* (ZMod (2 ^ i))ˣ)
    (TorsS K S0 W ((2 ^ i : ℕ) : ℤ)) g ⟨t.1, t.2⟩ 1 (by simp)).symm

/-- The Kummer difference in the actual support-field torsion. -/
def supportKummerDifference (P : W.toAffine.Point) (g : GKS K S0) : SupportTorsion (S0 := S0) W i :=
  ⟨g • supportDivisionPoint W i hdiv P - supportDivisionPoint W i hdiv P, by
    rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_sub, smul_comm,
      supportDivisionPoint_spec, supportBasePoint_fixed, sub_self]⟩

omit [NumberField K] in
/-- Its cocycle identity holds on the actual torsion group. -/
theorem supportKummerDifference_mul (P : W.toAffine.Point) (g g' : GKS K S0) :
    supportKummerDifference W i hdiv P (g * g') =
      g • supportKummerDifference W i hdiv P g' + supportKummerDifference W i hdiv P g := by
  apply Subtype.ext
  change (g * g') • supportDivisionPoint W i hdiv P - supportDivisionPoint W i hdiv P =
    g • (g' • supportDivisionPoint W i hdiv P - supportDivisionPoint W i hdiv P) +
      (g • supportDivisionPoint W i hdiv P - supportDivisionPoint W i hdiv P)
  rw [mul_smul, smul_sub]
  abel

/-- The actual division-point difference is continuous in the genuine Galois topology. -/
theorem supportKummerDifference_continuous (P : W.toAffine.Point) :
    Continuous (supportKummerDifference W i hdiv P) := by
  change Continuous (fun g : GKS K S0 =>
    (⟨g • supportDivisionPoint W i hdiv P - supportDivisionPoint W i hdiv P, _⟩ :
      SupportTorsion (S0 := S0) W i))
  exact Continuous.subtype_mk ((continuous_id.smul continuous_const).sub continuous_const) _

/-- The genuine continuous global Kummer cocycle over the coefficient support. -/
def supportKummerCocycle (P : W.toAffine.Point) :
    contCochain (ZMod (2 ^ i)) (GKS K S0) (CentralCoeff (S0 := S0) W i) 1 :=
  ⟨(fun g => supportTorsionCoefficient W i (supportKummerDifference W i hdiv P (g 0))),
    (continuous_of_discreteTopology (f := supportTorsionCoefficient W i)).comp
      ((supportKummerDifference_continuous W i hdiv P).comp (continuous_apply 0))⟩

/-- It is closed for the genuine continuous cochain differential. -/
theorem supportKummerCocycle_closed (P : W.toAffine.Point) :
    contD (ZMod (2 ^ i)) (GKS K S0) (CentralCoeff (S0 := S0) W i) 1
      (supportKummerCocycle W i hdiv P) = 0 := by
  apply Subtype.ext
  funext g
  have hd := contCochains_d_apply (k := ZMod (2 ^ i)) (G := GKS K S0)
    (M := CentralCoeff (S0 := S0) W i) 1 (supportKummerCocycle W i hdiv P) g
  refine hd.trans ?_
  rw [Fin.sum_univ_two]
  change g 0 • supportTorsionCoefficient W i (supportKummerDifference W i hdiv P (g 1)) +
    ((-1 : ZMod (2 ^ i)) ^ ((0 : ℕ) + 1)) •
      supportTorsionCoefficient W i (supportKummerDifference W i hdiv P (g 0 * g 1)) +
    ((-1 : ZMod (2 ^ i)) ^ ((1 : ℕ) + 1)) •
      supportTorsionCoefficient W i (supportKummerDifference W i hdiv P (g 0)) = 0
  rw [supportKummerDifference_mul, map_add, supportTorsionCoefficient_smul]
  simp only [zero_add, pow_one, neg_one_smul, Nat.reduceAdd, even_two, Even.neg_pow, one_pow,
    one_smul]
  abel

/-- The choices of actual division points give an additive class map: the defect is a coboundary. -/
theorem supportKummerCocycle_add (P P' : W.toAffine.Point) :
    supportKummerCocycle W i hdiv (P + P') - supportKummerCocycle W i hdiv P -
      supportKummerCocycle W i hdiv P' ∈
        contB1 (ZMod (2 ^ i)) (GKS K S0) (CentralCoeff (S0 := S0) W i) := by
  have hT : supportDivisionPoint W i hdiv (P + P') - supportDivisionPoint W i hdiv P -
      supportDivisionPoint W i hdiv P' ∈
      AddSubgroup.torsionBy (SupportPoints (S0 := S0) W) ((2 ^ i : ℕ) : ℤ) := by
    rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_sub, nsmul_sub,
      supportDivisionPoint_spec, supportDivisionPoint_spec, supportDivisionPoint_spec, map_add]
    abel
  refine (mem_contB1_iff _).2 ⟨constCochain (supportTorsionCoefficient W i ⟨_, hT⟩), ?_⟩
  apply Subtype.ext
  funext g
  refine (cfun_contD_constCochain (k := ZMod (2 ^ i)) (G := GKS K S0)
    (M := CentralCoeff (S0 := S0) W i) _ g).trans ?_
  change _ = supportTorsionCoefficient W i (supportKummerDifference W i hdiv (P + P') (g 0)) -
    supportTorsionCoefficient W i (supportKummerDifference W i hdiv P (g 0)) -
    supportTorsionCoefficient W i (supportKummerDifference W i hdiv P' (g 0))
  rw [← supportTorsionCoefficient_smul, ← map_sub, ← map_sub, ← map_sub]
  congr 1
  apply Subtype.ext
  change g 0 • (supportDivisionPoint W i hdiv (P + P') - supportDivisionPoint W i hdiv P -
    supportDivisionPoint W i hdiv P') -
    (supportDivisionPoint W i hdiv (P + P') - supportDivisionPoint W i hdiv P -
      supportDivisionPoint W i hdiv P') =
    (g 0 • supportDivisionPoint W i hdiv (P + P') - supportDivisionPoint W i hdiv (P + P')) -
    (g 0 • supportDivisionPoint W i hdiv P - supportDivisionPoint W i hdiv P) -
    (g 0 • supportDivisionPoint W i hdiv P' - supportDivisionPoint W i hdiv P')
  rw [smul_sub, smul_sub]
  abel

variable {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S0 ⊆ S) [W.IsElliptic]
  (hFull : FullTorsion K S0 W (2 ^ i)) (Pold : Set (HeightOneSpectrum (𝓞 K)))

/-- The same global Kummer cocycle, inflated to the actual Selmer support. -/
def globalKummerCocycle (P : W.toAffine.Point) : (centralSelData W i hS hFull Pold).G.X 1 :=
  ((resCochains (k := ZMod (2 ^ i)) (M := CentralCoeff (S0 := S0) W i) (inflMap K hS)).f 1).hom
    (supportKummerCocycle W i hdiv P)

/-- Inflation retains the actual closed global representative. -/
theorem globalKummerCocycle_closed (P : W.toAffine.Point) :
    (centralSelData W i hS hFull Pold).G.d 1 2 rfl
      (globalKummerCocycle W i hdiv hS hFull Pold P) = 0 := by
  let φ := resCochains (k := ZMod (2 ^ i)) (M := CentralCoeff (S0 := S0) W i) (inflMap K hS)
  have he : contD (ZMod (2 ^ i)) (GKS K S) (InflMod hS (CentralCoeff (S0 := S0) W i)) 1
      ((φ.f 1).hom (supportKummerCocycle W i hdiv P)) =
      (φ.f 2).hom (contD (ZMod (2 ^ i)) (GKS K S0) (CentralCoeff (S0 := S0) W i) 1
        (supportKummerCocycle W i hdiv P)) :=
    congrArg (fun f => f.hom (supportKummerCocycle W i hdiv P)) (φ.comm 1 2)
  exact he.trans (by
    rw [supportKummerCocycle_closed]
    exact map_zero ((φ.f 2).hom))

/-- Inflation carries the actual additive defect to an actual global coboundary. -/
theorem globalKummerCocycle_add (P P' : W.toAffine.Point) :
    globalKummerCocycle W i hdiv hS hFull Pold (P + P') -
      globalKummerCocycle W i hdiv hS hFull Pold P -
      globalKummerCocycle W i hdiv hS hFull Pold P' ∈
      LinearMap.range ((centralSelData W i hS hFull Pold).G.d 0 1 rfl) := by
  obtain ⟨c, hc⟩ := (mem_contB1_iff _).1 (supportKummerCocycle_add W i hdiv P P')
  let φ := resCochains (k := ZMod (2 ^ i)) (M := CentralCoeff (S0 := S0) W i) (inflMap K hS)
  refine ⟨(φ.f 0).hom c, ?_⟩
  have he : contD (ZMod (2 ^ i)) (GKS K S) (InflMod hS (CentralCoeff (S0 := S0) W i)) 0
      ((φ.f 0).hom c) =
      (φ.f 1).hom (contD (ZMod (2 ^ i)) (GKS K S0) (CentralCoeff (S0 := S0) W i) 0 c) :=
    congrArg (fun f => f.hom
      (show (contCochains (ZMod (2 ^ i)) (GKS K S0) (CentralCoeff (S0 := S0) W i)).X 0 from c))
      (φ.comm 0 1)
  refine he.trans ?_
  rw [hc]
  exact (map_sub ((φ.f 1).hom)
    (supportKummerCocycle W i hdiv (P + P') - supportKummerCocycle W i hdiv P)
    (supportKummerCocycle W i hdiv P')).trans
      (congrArg (fun x => x - (φ.f 1).hom (supportKummerCocycle W i hdiv P'))
        (map_sub ((φ.f 1).hom) (supportKummerCocycle W i hdiv (P + P'))
          (supportKummerCocycle W i hdiv P)))

/-- The actual global Kummer class map into the canonical cochain-class group. -/
def globalKummerMap : W.toAffine.Point →+ cochainClasses (centralSelData W i hS hFull Pold) :=
  AddMonoidHom.mk'
    (fun P => cochainClass (centralSelData W i hS hFull Pold)
      (globalKummerCocycle W i hdiv hS hFull Pold P)) fun P P' => by
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ + Submodule.Quotient.mk _
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    rw [← sub_sub]
    exact globalKummerCocycle_add W i hdiv hS hFull Pold P P'

/-- The class is that of the same inflated actual division-point cocycle. -/
theorem globalKummerMap_apply (P : W.toAffine.Point) :
    globalKummerMap W i hdiv hS hFull Pold P =
      cochainClass (centralSelData W i hS hFull Pold)
        (globalKummerCocycle W i hdiv hS hFull Pold P) := rfl

end GlobalKummer

section Retained

open Matrix ZInQ.Manuscript.RC.BaseZeroLimit

variable {K : Type} [Field K] [NumberField K] [DecidableEq K]
  {S S0 : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K) [W.IsElliptic]
  (i : ℕ) (hS : S0 ⊆ S) (hFull : FullTorsion K S0 W (2 ^ i))
  (Pold : Set (HeightOneSpectrum (𝓞 K)))
  (hdiv : GlobalDivisionPointsInSupport (S0 := S0) W i)
  {P : W.toAffine.Point} (T : SplitNormStage P) (L : ℤ) (N M0 : ℕ)

/-- An unrestricted conditional representative and model packet for a supplied norm stage.
The ambient cochain groups and their maps are fixed, and neither local boundary hypothesis
is a field. The stage, place partition, global representative, projections and coordinates
are not identified with the actual construction. The class field is equivalent to the
global-boundary obligation; zero projections are allowed even at positive precision.
Inhabitation of this packet is not evidence of an actual retained arithmetic model.
These limitations were found in an independent review. -/
structure CentralRetainedInput : Type where
  zG : (centralSelData W i hS hFull Pold).G.X 1
  hzG : (centralSelData W i hS hFull Pold).G.d 1 2 rfl zG = 0
  zU : (centralSelData W i hS hFull Pold).U.X 1
  jU : (centralSelData W i hS hFull Pold).U.X 1
  zL : (centralSelData W i hS hFull Pold).L.X 0
  jL : (centralSelData W i hS hFull Pold).L.X 0
  hzU : (centralSelData W i hS hFull Pold).U.d 1 2 rfl zU = 0
  hjU : (centralSelData W i hS hFull Pold).U.d 1 2 rfl jU = 0
  hz : (centralSelData W i hS hFull Pold).res.f 1 1 rfl zG -
    (centralSelData W i hS hFull Pold).ι.f 1 1 rfl zU =
      (centralSelData W i hS hFull Pold).L.d 0 1 rfl zL
  hj : (centralSelData W i hS hFull Pold).res.f 1 1 rfl
      (globalKummerCocycle W i hdiv hS hFull Pold P) -
    (centralSelData W i hS hFull Pold).ι.f 1 1 rfl jU =
      (centralSelData W i hS hFull Pold).L.d 0 1 rfl jL
  hzcls : cochainClass (centralSelData W i hS hFull Pold) zG =
    globalKummerMap W i hdiv hS hFull Pold (L • T.W)
  p1 : (centralSelData W i hS hFull Pold).G.X 1 ×
      (centralSelData W i hS hFull Pold).U.X 1 ×
      (centralSelData W i hS hFull Pold).L.X 0 →+
    (Fin N → ℤ_[2] ⧸ twoAdicStage i)
  p0 : (centralSelData W i hS hFull Pold).G.X 0 ×
      (centralSelData W i hS hFull Pold).U.X 0 →+
    (Fin M0 → ℤ_[2] ⧸ twoAdicStage i)
  dC : Matrix (Fin N) (Fin M0) ℤ_[2]
  hdC : ∀ (v : (centralSelData W i hS hFull Pold).G.X 0)
      (w : (centralSelData W i hS hFull Pold).U.X 0),
    p1 ((centralSelData W i hS hFull Pold).G.d 0 1 rfl v,
      (centralSelData W i hS hFull Pold).U.d 0 1 rfl w,
      (centralSelData W i hS hFull Pold).res.f 0 0 rfl v -
        (centralSelData W i hS hFull Pold).ι.f 0 0 rfl w) =
      dC.map (Ideal.Quotient.mk (twoAdicStage i)) *ᵥ p0 (v, w)
  zeta : Fin N → ℤ_[2]
  jay : Fin N → ℤ_[2]
  hzeta : p1 (zG, zU, zL) = fun a => Ideal.Quotient.mk (twoAdicStage i) (zeta a)
  hjay : p1 (globalKummerCocycle W i hdiv hS hFull Pold P, jU, jL) =
    fun a => Ideal.Quotient.mk (twoAdicStage i) (jay a)

variable (C : CentralRetainedInput W i hS hFull Pold hdiv T L N M0)

/-- A conditional constructor for the retained-stage interface on the supplied packet.
The two local fields and class-map kernel are proved on the genuine central datum.
Preserving the supplied stage and representatives does not identify them with the
finite Heegner construction, and the packet supplies no normalized model comparison. -/
def centralRetainedStage : RetainedStage45 P L i N M0 :=
  let D := centralSelData W i hS hFull Pold
  { S := T
    G0 := D.G.X 0
    G1 := D.G.X 1
    G2 := D.G.X 2
    U0 := D.U.X 0
    U1 := D.U.X 1
    U2 := D.U.X 2
    L0 := D.L.X 0
    L1 := D.L.X 1
    H1 := cochainClasses D
    dG0 := (D.G.d 0 1 rfl).toAddMonoidHom
    dG1 := (D.G.d 1 2 rfl).toAddMonoidHom
    dU0 := (D.U.d 0 1 rfl).toAddMonoidHom
    dU1 := (D.U.d 1 2 rfl).toAddMonoidHom
    dL0 := (D.L.d 0 1 rfl).toAddMonoidHom
    loc0 := (D.res.f 0 0 rfl).toAddMonoidHom
    loc1 := (D.res.f 1 1 rfl).toAddMonoidHom
    ι0 := (D.ι.f 0 0 rfl).toAddMonoidHom
    ι1 := (D.ι.f 1 1 rfl).toAddMonoidHom
    hloc := D.res.comm 0 1 0 1 rfl rfl rfl rfl
    hι := D.ι.comm 0 1 0 1 rfl rfl rfl rfl
    honto := (centralSelData_localFacts W i hS hFull Pold).1
    hinj := (centralSelData_localFacts W i hS hFull Pold).2
    cls := cochainClass D
    hexact := fun c _ hc => (cochainClass_eq_zero_iff D c).1 hc
    δ := globalKummerMap W i hdiv hS hFull Pold
    zG := C.zG
    jG := globalKummerCocycle W i hdiv hS hFull Pold P
    zU := C.zU
    jU := C.jU
    zL := C.zL
    jL := C.jL
    hzG := C.hzG
    hjG := globalKummerCocycle_closed W i hdiv hS hFull Pold P
    hzU := C.hzU
    hjU := C.hjU
    hz := C.hz
    hj := C.hj
    hzcls := C.hzcls
    hjcls := rfl
    p1 := C.p1
    p0 := C.p0
    dC := C.dC
    hdC := C.hdC
    zeta := C.zeta
    jay := C.jay
    hzeta := C.hzeta
    hjay := C.hjay }

/-- The conditional constructor preserves its supplied stage and the ambient cochain maps.
This is a preservation statement, not an identification of the arithmetic stage,
the prescribed place partition, the constructed class or the retained finite free model. -/
theorem centralRetainedStage_spec :
    (centralRetainedStage W i hS hFull Pold hdiv T L N M0 C).S = T ∧
      (centralRetainedStage W i hS hFull Pold hdiv T L N M0 C).G1 =
        (centralSelData W i hS hFull Pold).G.X 1 ∧
      (centralRetainedStage W i hS hFull Pold hdiv T L N M0 C).U1 =
        (centralSelData W i hS hFull Pold).U.X 1 ∧
      (centralRetainedStage W i hS hFull Pold hdiv T L N M0 C).L0 =
        (centralSelData W i hS hFull Pold).L.X 0 ∧
      (centralRetainedStage W i hS hFull Pold hdiv T L N M0 C).loc0 =
        ((centralSelData W i hS hFull Pold).res.f 0 0 rfl).toAddMonoidHom ∧
      (centralRetainedStage W i hS hFull Pold hdiv T L N M0 C).ι0 =
        ((centralSelData W i hS hFull Pold).ι.f 0 0 rfl).toAddMonoidHom ∧
      (centralRetainedStage W i hS hFull Pold hdiv T L N M0 C).δ =
        globalKummerMap W i hdiv hS hFull Pold ∧
      (centralRetainedStage W i hS hFull Pold hdiv T L N M0 C).cls =
        cochainClass (centralSelData W i hS hFull Pold) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The finite-coordinate boundary conditional on the unrestricted packet.
The local lifting hypotheses are proved, but the class and model obligations are inputs.
For an erased model this theorem proves only the zero coordinate identity. -/
theorem centralRetainedStage_exists_witness :
    ∃ v : Fin M0 → ℤ_[2], ∀ a : Fin N,
      C.zeta a - ((L * (T.a - 2) : ℤ) : ℤ_[2]) * C.jay a - (C.dC *ᵥ v) a ∈ twoAdicStage i :=
  (centralRetainedStage W i hS hFull Pold hdiv T L N M0 C).exists_witness

end Retained

end ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage
