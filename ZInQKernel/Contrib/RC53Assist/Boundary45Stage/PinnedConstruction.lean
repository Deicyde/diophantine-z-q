import ZInQKernel.Contrib.RC53Assist.Boundary45Stage.Identification

/-!
# A pinned construction and deformation-retract contract

This file gives a stronger conditional interface after the obstructions found
in an independent review. The finite Heegner representative is a specified
input object, not an existentially chosen representative packet. Its norm
stage is computed from the specified extension, point and Galois data. The
old Kummer partition contains the specified places above 2N.

The finite free model and all comparison maps are also specified inputs.
The projection and section form a deformation retract in every degree,
with an explicit degree-minus-one homotopy and normalization identities.
The projections and coordinates of the conditional retained-stage output
are determined by these maps. They cannot be erased while the same model
and retract contract are retained, when that model term is nonzero.

No ring-class field, CM point, finite Heegner class or model contraction
is constructed here. The arithmetic interpretation of the named input,
its class identity, and the actual normalized model comparison remain
open. The contract is not a new printed arithmetic assertion.

The manuscript passages are lines 2914-2936, 3372-3405, 3880-3892,
3912-3921 and 4391-4442.
-/

set_option maxHeartbeats 600000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned

open CategoryTheory NumberField IsDedekindDomain Matrix WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.BaseZeroAssembly
open ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage
open ZInQ.Manuscript.RC.BaseZeroLimit

section Additive

variable {R : Type} [CommRing R]

/-- The same complex and differentials with only the canonical integral scalar action retained. -/
def additiveCx (C : GCx R) : GCx ℤ where
  X n := ModuleCat.of ℤ (C.X n)
  d n m h := (C.d n m h).toAddMonoidHom.toIntLinearMap
  d_d n m l hnm hml x := C.d_d n m l hnm hml x

end Additive

section Retract

variable (C M : GCx ℤ)
  (p : GHom C M) (s : GHom M C)
  (h : ∀ n m : ℤ, n = m + 1 → C.X n →ₗ[ℤ] C.X m)

/-- A specified deformation retract, with both maps and the homotopy fixed before the contract.
The exact model composite and all homotopy identities are part of the contract. -/
def DeformationRetractContract : Prop :=
  (∀ n (x : M.X n), p.f n n rfl (s.f n n rfl x) = x) ∧
  (∀ n (x : C.X n),
    C.d (n - 1) n (by omega) (h n (n - 1) (by omega) x) +
      h (n + 1) n rfl (C.d n (n + 1) rfl x) = x - s.f n n rfl (p.f n n rfl x)) ∧
  (∀ n (x : M.X n), h n (n - 1) (by omega) (s.f n n rfl x) = 0) ∧
  (∀ n (x : C.X n), p.f (n - 1) (n - 1) rfl (h n (n - 1) (by omega) x) = 0) ∧
  (∀ n (x : C.X n), h (n - 1) (n - 2) (by omega) (h n (n - 1) (by omega) x) = 0)

/-- A retract projects onto every term of the specified model. -/
theorem retract_projection_surjective (H : DeformationRetractContract C M p s h) (n : ℤ) :
    Function.Surjective (p.f n n rfl) :=
  fun x => ⟨s.f n n rfl x, H.1 n x⟩

/-- The independent-review erasure is impossible for a fixed nonzero retract term. -/
theorem retract_projection_not_zero (H : DeformationRetractContract C M p s h)
    (n : ℤ) (x : M.X n) (hx : x ≠ 0) : p.f n n rfl ≠ 0 := by
  intro hp
  have he := H.1 n x
  rw [hp, LinearMap.zero_apply] at he
  exact hx he.symm

/-- The homotopy is explicitly the identity minus section followed by projection. -/
theorem retract_homotopy_identity (H : DeformationRetractContract C M p s h)
    (n : ℤ) (x : C.X n) :
    C.d (n - 1) n (by omega) (h n (n - 1) (by omega) x) +
      h (n + 1) n rfl (C.d n (n + 1) rfl x) =
      x - s.f n n rfl (p.f n n rfl x) := H.2.1 n x

end Retract

/-- A specified bounded finite free model over the actual finite coordinate ring.
All bases and the lifted degree-zero differential are retained with the model itself. -/
structure FiniteFreeModel (i : ℕ) : Type 1 where
  C : GCx (ℤ_[2] ⧸ twoAdicStage i)
  rank : ℤ → ℕ
  coords : ∀ n : ℤ, C.X n ≃ₗ[ℤ_[2] ⧸ twoAdicStage i]
    (Fin (rank n) → ℤ_[2] ⧸ twoAdicStage i)
  lower : ℤ
  upper : ℤ
  bounded : ∀ n, n < lower ∨ upper < n → rank n = 0
  d01 : Matrix (Fin (rank 1)) (Fin (rank 0)) ℤ_[2]
  hd01 : ∀ x : C.X 0, coords 1 (C.d 0 1 rfl x) =
    d01.map (Ideal.Quotient.mk (twoAdicStage i)) *ᵥ coords 0 x

/-- The finite coordinate ring is nonzero at every positive precision. -/
theorem coordinateRing_one_ne_zero (i : ℕ) (hi : 0 < i) :
    (1 : ℤ_[2] ⧸ twoAdicStage i) ≠ 0 := by
  intro hz
  have hm : (1 : ℤ_[2]) ∈ twoAdicStage i := (Ideal.Quotient.eq_zero_iff_mem).1 hz
  obtain ⟨b, hb⟩ := mem_twoAdicStage_iff.1 hm
  have hmod := congrArg (PadicInt.toZMod (p := 2)) hb
  rw [map_one, map_mul, map_pow, map_ofNat,
    show (2 : ZMod 2) = 0 by decide, zero_pow (Nat.ne_of_gt hi), zero_mul] at hmod
  exact one_ne_zero hmod

section ModelComparison

variable {R : Type} [CommRing R] (D : SelData R) {i : ℕ} (M : FiniteFreeModel i)

/-- A fixed comparison to the fixed finite model, with every map and normalization displayed.
The existence of this record for an arithmetic construction remains an open model obligation. -/
structure ModelComparison : Type 1 where
  projection : GHom (additiveCx (selCx D)) (additiveCx M.C)
  sectionMap : GHom (additiveCx M.C) (additiveCx (selCx D))
  homotopy : ∀ n m : ℤ, n = m + 1 →
    (additiveCx (selCx D)).X n →ₗ[ℤ] (additiveCx (selCx D)).X m
  retract : DeformationRetractContract (additiveCx (selCx D)) (additiveCx M.C)
    projection sectionMap homotopy

/-- The actual degree-zero Selmer cochain associated to a global/local-condition pair. -/
def selmerZeroPair : D.G.X 0 × D.U.X 0 →+ (selCx D).X 0 where
  toFun x := (x.1, x.2, 0)
  map_zero' := rfl
  map_add' _ _ := Prod.ext rfl (Prod.ext rfl (zero_add 0).symm)

/-- The actual degree-zero pair covers the whole cone term when the negative local term is zero. -/
theorem selmerZeroPair_surjective [Subsingleton (D.L.X (-1))] :
    Function.Surjective (selmerZeroPair D) := by
  rintro ⟨g, u, l⟩
  exact ⟨(g, u), Prod.ext rfl (Prod.ext rfl
    (@Subsingleton.elim (D.L.X (-1)) inferInstance 0 l))⟩

/-- Its differential is the genuine Selmer-cone boundary of that pair. -/
theorem selmerZeroPair_d (v : D.G.X 0) (w : D.U.X 0) :
    (selCx D).d 0 1 rfl (selmerZeroPair D (v, w)) =
      (D.G.d 0 1 rfl v, D.U.d 0 1 rfl w,
        D.res.f 0 0 rfl v - D.ι.f 0 0 rfl w) := by
  change (D.G.d 0 1 rfl v, D.U.d 0 1 rfl w,
    D.res.f 0 0 rfl v - D.ι.f 0 0 rfl w - D.L.d (-1) 0 rfl 0) = _
  rw [map_zero, sub_zero]

/-- The projection in degree zero is determined by the specified full comparison and basis. -/
def modelProjection0 (F : ModelComparison D M) :
    D.G.X 0 × D.U.X 0 →+ (Fin (M.rank 0) → ℤ_[2] ⧸ twoAdicStage i) :=
  (M.coords 0).toAddEquiv.toAddMonoidHom.comp
    ((F.projection.f 0 0 rfl).toAddMonoidHom.comp (selmerZeroPair D))

/-- The projection in degree one is determined by the same comparison and basis. -/
def modelProjection1 (F : ModelComparison D M) :
    D.G.X 1 × D.U.X 1 × D.L.X 0 →+ (Fin (M.rank 1) → ℤ_[2] ⧸ twoAdicStage i) :=
  (M.coords 1).toAddEquiv.toAddMonoidHom.comp (F.projection.f 1 1 rfl).toAddMonoidHom

/-- The conditional packet's degree-zero square follows from the specified full chain comparison. -/
theorem modelProjection_d (F : ModelComparison D M) (v : D.G.X 0) (w : D.U.X 0) :
    modelProjection1 D M F
      (D.G.d 0 1 rfl v, D.U.d 0 1 rfl w, D.res.f 0 0 rfl v - D.ι.f 0 0 rfl w) =
      M.d01.map (Ideal.Quotient.mk (twoAdicStage i)) *ᵥ modelProjection0 D M F (v, w) := by
  have he := F.projection.comm 0 1 0 1 rfl rfl rfl rfl (selmerZeroPair D (v, w))
  have hp := congrArg (M.coords 1) he
  have hd := M.hd01 (F.projection.f 0 0 rfl (selmerZeroPair D (v, w)))
  have hboundary := selmerZeroPair_d D v w
  change M.coords 1 (F.projection.f 1 1 rfl
    (D.G.d 0 1 rfl v, D.U.d 0 1 rfl w, D.res.f 0 0 rfl v - D.ι.f 0 0 rfl w)) = _
  exact (congrArg (fun x => M.coords 1 (F.projection.f 1 1 rfl x)) hboundary).symm.trans
    (hp.trans hd)

/-- The degree-one coordinate projection of a fixed retract is surjective, unlike an erased packet. -/
theorem modelProjection1_surjective (F : ModelComparison D M) :
    Function.Surjective (modelProjection1 D M F) := by
  intro x
  refine ⟨F.sectionMap.f 1 1 rfl ((M.coords 1).symm x), ?_⟩
  change M.coords 1 (F.projection.f 1 1 rfl
    (F.sectionMap.f 1 1 rfl ((M.coords 1).symm x))) = x
  exact (congrArg (M.coords 1) (F.retract.1 1 ((M.coords 1).symm x))).trans
    ((M.coords 1).apply_symm_apply x)

/-- The independent-review zero projection is excluded whenever one model coordinate is nonzero. -/
theorem modelProjection1_not_zero (F : ModelComparison D M)
    (a : Fin (M.rank 1)) (u : ℤ_[2] ⧸ twoAdicStage i) (hu : u ≠ 0) :
    modelProjection1 D M F ≠ 0 := by
  classical
  intro hp
  obtain ⟨x, hx⟩ := modelProjection1_surjective D M F (Pi.single a u)
  rw [hp, AddMonoidHom.zero_apply] at hx
  have he := congrFun hx a
  simp only [Pi.zero_apply, Pi.single_eq_same] at he
  exact hu he.symm

/-- The degree-zero projection is onto the fixed model when the negative local term is zero. -/
theorem modelProjection0_surjective [Subsingleton (D.L.X (-1))]
    (F : ModelComparison D M) : Function.Surjective (modelProjection0 D M F) := by
  intro y
  obtain ⟨x, hx⟩ := selmerZeroPair_surjective D
    (F.sectionMap.f 0 0 rfl ((M.coords 0).symm y))
  refine ⟨x, ?_⟩
  change M.coords 0 (F.projection.f 0 0 rfl (selmerZeroPair D x)) = y
  exact (congrArg (fun c => M.coords 0 (F.projection.f 0 0 rfl c)) hx).trans
    ((congrArg (M.coords 0) (F.retract.1 0 ((M.coords 0).symm y))).trans
      ((M.coords 0).apply_symm_apply y))

/-- Positive precision and a positive degree-zero rank exclude the zero projection as well. -/
theorem modelProjection0_not_zero_of_positive_precision [Subsingleton (D.L.X (-1))]
    (F : ModelComparison D M) (hi : 0 < i) (hrank : 0 < M.rank 0) :
    modelProjection0 D M F ≠ 0 := by
  classical
  intro hp
  let a : Fin (M.rank 0) := ⟨0, hrank⟩
  obtain ⟨x, hx⟩ := modelProjection0_surjective D M F (Pi.single a 1)
  rw [hp, AddMonoidHom.zero_apply] at hx
  have he := congrFun hx a
  simp only [Pi.zero_apply, Pi.single_eq_same] at he
  exact coordinateRing_one_ne_zero i hi he.symm

/-- Positive precision and a positive degree-one rank exclude the zero projection. -/
theorem modelProjection1_not_zero_of_positive_precision (F : ModelComparison D M)
    (hi : 0 < i) (hrank : 0 < M.rank 1) : modelProjection1 D M F ≠ 0 :=
  modelProjection1_not_zero D M F ⟨0, hrank⟩ 1 (coordinateRing_one_ne_zero i hi)

end ModelComparison

section Places

variable {K : Type} [Field K]

/-- The specified fixed places above the integer 2N. Its arithmetic conductor interpretation
must be supplied for the specified curve; it is not proved merely by naming N. -/
def fixedPlacesAboveTwoN (N : ℕ) : Set (HeightOneSpectrum (𝓞 K)) :=
  {v | (((2 * N : ℕ) : 𝓞 K)) ∈ v.asIdeal}

/-- The actual old Kummer partition must contain all the specified fixed places. -/
def FixedPlacesIncluded (N : ℕ) (Pold : Set (HeightOneSpectrum (𝓞 K))) : Prop :=
  fixedPlacesAboveTwoN (K := K) N ⊆ Pold

/-- A specified dyadic place lies in the fixed set for every conductor parameter. -/
theorem dyadic_mem_fixedPlaces (N : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (hv : (2 : 𝓞 K) ∈ v.asIdeal) : v ∈ fixedPlacesAboveTwoN (K := K) N := by
  change (((2 * N : ℕ) : 𝓞 K)) ∈ v.asIdeal
  rw [Nat.cast_mul, Nat.cast_ofNat]
  exact Ideal.mul_mem_right _ _ hv

/-- With a specified dyadic place, an empty old Kummer partition cannot satisfy the contract. -/
theorem fixedPlacesIncluded_not_empty (N : ℕ) (Pold : Set (HeightOneSpectrum (𝓞 K)))
    (H : FixedPlacesIncluded (K := K) N Pold)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (2 : 𝓞 K) ∈ v.asIdeal) : Pold ≠ ∅ := by
  intro he
  have hm := H (dyadic_mem_fixedPlaces N v hv)
  rw [he] at hm
  exact Set.notMem_empty v hm

end Places

section Geometry

open scoped Classical

variable {K : Type} [Field K] [NumberField K] [DecidableEq K]
  {S0 : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  (P : W.toAffine.Point)

/-- The specified extension, norm and CM-point candidates underlying one stage.
The fields pin mathematical objects; this record alone does not certify that the
extension is the ring-class field or that its points are the manuscript's CM points. -/
structure SpecifiedNormGeometry : Type 1 where
  H : IntermediateField K (KS K S0)
  [normal : Normal K H]
  [finite : FiniteDimensional K H]
  abelian : AbelianStageExtension H
  relative : Subgroup (H ≃ₐ[K] H)
  transversal : Finset (H ≃ₐ[K] H)
  htransversal : ∀ δ : H ≃ₐ[K] H,
    ∃! t, t ∈ transversal ∧ t⁻¹ * δ ∈ relative
  y1 : (W.baseChange H).toAffine.Point
  yr : (W.baseChange H).toAffine.Point
  hy1 : ∀ n ∈ relative, geometricPointAction W H n y1 = y1
  trace : ℤ
  frobenius : H ≃ₐ[K] H
  norm : GeometricSplitNormRelation W H relative y1 yr trace frobenius
  pointTrace : geometricPointInclusion W H P =
    ∑ t ∈ transversal, geometricPointAction W H t y1

attribute [instance] SpecifiedNormGeometry.normal SpecifiedNormGeometry.finite

/-- The norm stage is computed from the specified geometric objects, not an extra stage field. -/
def SpecifiedNormGeometry.stage (A : SpecifiedNormGeometry (S0 := S0) W P) : SplitNormStage P :=
  geometricSplitNormStage W A.H A.abelian A.relative A.transversal A.htransversal
    A.y1 A.yr A.hy1 A.trace A.frobenius A.norm P A.pointTrace

omit [NumberField K] in
/-- The stage point group and trace are determined by those same geometric inputs. -/
theorem SpecifiedNormGeometry.stage_spec (A : SpecifiedNormGeometry (S0 := S0) W P) :
    A.stage.Pt = (W.baseChange A.H).toAffine.Point ∧
      A.stage.Δ = (A.H ≃ₐ[K] A.H) ∧ A.stage.a = A.trace ∧
      A.stage.incl = geometricPointInclusion W A.H ∧
      A.stage.yr = A.yr := ⟨rfl, rfl, rfl, rfl, rfl⟩

end Geometry

section Representative

variable {R : Type} [CommRing R]

/-- A named finite Heegner cone representative supplied by the construction.
The wrapper takes this object before any packet or model is formed and never chooses it.
Its identification with the actual arithmetic construction is an external obligation. -/
structure SpecifiedHeegnerCycle (D : SelData R) : Type where
  zG : D.G.X 1
  zU : D.U.X 1
  zL : D.L.X 0
  hzG : D.G.d 1 2 rfl zG = 0
  hzU : D.U.d 1 2 rfl zU = 0
  hz : D.res.f 1 1 rfl zG - D.ι.f 1 1 rfl zU = D.L.d 0 1 rfl zL

end Representative

section Construction

variable {K : Type} [Field K] [NumberField K] [DecidableEq K]
  {S S0 : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K) [W.IsElliptic]
  (i : ℕ) (hS : S0 ⊆ S) (hFull : FullTorsion K S0 W (2 ^ i))
  (Pold : Set (HeightOneSpectrum (𝓞 K)))
  (hdiv : GlobalDivisionPointsInSupport (S0 := S0) W i)
  (P : W.toAffine.Point) (conductor : ℕ)
  (Z : SpecifiedHeegnerCycle (centralSelData W i hS hFull Pold))

/-- A specified finite Heegner construction parameter for the independently supplied cycle.
This record cannot choose or replace the global/local Heegner representatives. It is not
an existence assertion or a construction of the arithmetic class, geometry or moving prime. -/
structure SpecifiedFiniteHeegner
    (sourceCycle : SpecifiedHeegnerCycle (centralSelData W i hS hFull Pold)) : Type 1 where
  geometry : SpecifiedNormGeometry (S0 := S0) W P
  fixedOld : FixedPlacesIncluded (K := K) conductor Pold
  dyadic : HeightOneSpectrum (𝓞 K)
  hdyadic : (2 : 𝓞 K) ∈ dyadic.asIdeal
  oldSupport : Pold ⊆ S0
  moving : HeightOneSpectrum (𝓞 K)
  movingSupport : moving ∈ S0
  movingFull : moving ∉ Pold
  jU : (centralSelData W i hS hFull Pold).U.X 1
  jL : (centralSelData W i hS hFull Pold).L.X 0
  hjU : (centralSelData W i hS hFull Pold).U.d 1 2 rfl jU = 0
  hj : (centralSelData W i hS hFull Pold).res.f 1 1 rfl
      (globalKummerCocycle W i hdiv hS hFull Pold P) -
    (centralSelData W i hS hFull Pold).ι.f 1 1 rfl jU =
      (centralSelData W i hS hFull Pold).L.d 0 1 rfl jL

variable (A : SpecifiedFiniteHeegner W i hS hFull Pold hdiv P conductor Z) (L : ℤ)

/-- The class-identity obligation for the specified finite Heegner representative.
This remains an explicit arithmetic premise, not a proved printed leaf. -/
def ConstructedClassIdentity : Prop :=
  cochainClass (centralSelData W i hS hFull Pold) Z.zG =
    globalKummerMap W i hdiv hS hFull Pold (L • A.geometry.stage.W)

include A in
/-- The stronger specified-construction contract rules out the empty-partition example. -/
theorem specifiedConstruction_partition_not_empty : Pold ≠ ∅ :=
  fixedPlacesIncluded_not_empty conductor Pold A.fixedOld A.dyadic A.hdyadic

/-- The marked moving place is not one of the fixed places above 2N. -/
theorem specifiedConstruction_moving_not_fixed :
    A.moving ∉ fixedPlacesAboveTwoN (K := K) conductor :=
  fun hv => A.movingFull (A.fixedOld hv)

variable (M : FiniteFreeModel i)
  (F : ModelComparison (centralSelData W i hS hFull Pold) M)
  (zeta jay : Fin (M.rank 1) → ℤ_[2])

/-- The chosen integral coordinates reduce to the projection of the specified source cycles.
Only the lifts are supplied here; the projection and the source representatives cannot be changed. -/
def PinnedCoordinates : Prop :=
  modelProjection1 (centralSelData W i hS hFull Pold) M F (Z.zG, Z.zU, Z.zL) =
      (fun a => Ideal.Quotient.mk (twoAdicStage i) (zeta a)) ∧
  modelProjection1 (centralSelData W i hS hFull Pold) M F
      (globalKummerCocycle W i hdiv hS hFull Pold P, A.jU, A.jL) =
      (fun a => Ideal.Quotient.mk (twoAdicStage i) (jay a))

variable (hclass : ConstructedClassIdentity W i hS hFull Pold hdiv P conductor Z A L)
  (hcoords : PinnedCoordinates W i hS hFull Pold hdiv P conductor Z A M F zeta jay)

/-- The unrestricted packet obtained from the pinned source, geometry and complete model comparison.
The class identity remains an explicit premise for that fixed source; it is not obtained by
choosing the source to be a multiplied Kummer cocycle. -/
def pinnedPacket :
    CentralRetainedInput W i hS hFull Pold hdiv A.geometry.stage L (M.rank 1) (M.rank 0) :=
  { zG := Z.zG
    hzG := Z.hzG
    zU := Z.zU
    jU := A.jU
    zL := Z.zL
    jL := A.jL
    hzU := Z.hzU
    hjU := A.hjU
    hz := Z.hz
    hj := A.hj
    hzcls := hclass
    p1 := modelProjection1 (centralSelData W i hS hFull Pold) M F
    p0 := modelProjection0 (centralSelData W i hS hFull Pold) M F
    dC := M.d01
    hdC := modelProjection_d (centralSelData W i hS hFull Pold) M F
    zeta := zeta
    jay := jay
    hzeta := hcoords.1
    hjay := hcoords.2 }

/-- A stronger conditional retained-stage wrapper with source, geometry, partition and model pinned.
It requires actual arithmetic realization and a verified normalized model comparison before use. -/
def pinnedRetainedStage : RetainedStage45 P L i (M.rank 1) (M.rank 0) :=
  centralRetainedStage W i hS hFull Pold hdiv A.geometry.stage L (M.rank 1) (M.rank 0)
    (pinnedPacket W i hS hFull Pold hdiv P conductor Z A L M F zeta jay hclass hcoords)

/-- Every relevant field comes from the fixed inputs, not a newly chosen packet. -/
theorem pinnedRetainedStage_spec :
    (pinnedRetainedStage W i hS hFull Pold hdiv P conductor Z A L M F zeta jay hclass hcoords).S =
        A.geometry.stage ∧
      (pinnedRetainedStage W i hS hFull Pold hdiv P conductor Z A L M F zeta jay hclass hcoords).zG =
        Z.zG ∧
      (pinnedRetainedStage W i hS hFull Pold hdiv P conductor Z A L M F zeta jay hclass hcoords).zU =
        Z.zU ∧
      (pinnedRetainedStage W i hS hFull Pold hdiv P conductor Z A L M F zeta jay hclass hcoords).p1 =
        modelProjection1 (centralSelData W i hS hFull Pold) M F ∧
      (pinnedRetainedStage W i hS hFull Pold hdiv P conductor Z A L M F zeta jay hclass hcoords).p0 =
        modelProjection0 (centralSelData W i hS hFull Pold) M F ∧
      (pinnedRetainedStage W i hS hFull Pold hdiv P conductor Z A L M F zeta jay hclass hcoords).dC =
        M.d01 ∧
      (pinnedRetainedStage W i hS hFull Pold hdiv P conductor Z A L M F zeta jay hclass hcoords).zeta =
        zeta ∧
      (pinnedRetainedStage W i hS hFull Pold hdiv P conductor Z A L M F zeta jay hclass hcoords).jay =
        jay := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Erasing the output projection is inconsistent with the same nonzero retract model. -/
theorem pinnedRetainedStage_projection_not_zero
    (a : Fin (M.rank 1)) (u : ℤ_[2] ⧸ twoAdicStage i) (hu : u ≠ 0) :
    (pinnedRetainedStage W i hS hFull Pold hdiv P conductor Z A L M F zeta jay hclass hcoords).p1 ≠ 0 :=
  modelProjection1_not_zero (centralSelData W i hS hFull Pold) M F a u hu

/-- At positive precision and positive model ranks, neither output projection can be erased. -/
theorem pinnedRetainedStage_projections_not_zero
    (hi : 0 < i) (h0 : 0 < M.rank 0) (h1 : 0 < M.rank 1) :
    (pinnedRetainedStage W i hS hFull Pold hdiv P conductor Z A L M F zeta jay hclass hcoords).p0 ≠ 0 ∧
    (pinnedRetainedStage W i hS hFull Pold hdiv P conductor Z A L M F zeta jay hclass hcoords).p1 ≠ 0 := by
  have : Subsingleton ((centralSelData W i hS hFull Pold).L.X (-1)) := by
    change Subsingleton (∀ v : Places K S, PUnit)
    infer_instance
  exact ⟨modelProjection0_not_zero_of_positive_precision (centralSelData W i hS hFull Pold) M F hi h0,
    modelProjection1_not_zero_of_positive_precision (centralSelData W i hS hFull Pold) M F hi h1⟩

/-- A manufactured multiplied Kummer representative cannot replace a distinct pinned source. -/
theorem pinnedRetainedStage_source_not_replaced
    (hc : Z.zG ≠ (L * (A.geometry.trace - 2)) •
      globalKummerCocycle W i hdiv hS hFull Pold P) :
    (pinnedRetainedStage W i hS hFull Pold hdiv P conductor Z A L M F zeta jay hclass hcoords).zG ≠
      (L * (A.geometry.trace - 2)) • globalKummerCocycle W i hdiv hS hFull Pold P := hc

include hclass hcoords in
/-- The finite-coordinate boundary for the same pinned source and normalized model comparison.
The specified class identity and arithmetic/model realization are still required inputs. -/
theorem pinnedRetainedStage_exists_witness :
    ∃ v : Fin (M.rank 0) → ℤ_[2], ∀ a : Fin (M.rank 1),
      zeta a - ((L * (A.geometry.trace - 2) : ℤ) : ℤ_[2]) * jay a - (M.d01 *ᵥ v) a ∈
        twoAdicStage i :=
  (pinnedRetainedStage W i hS hFull Pold hdiv P conductor Z A L M F zeta jay hclass hcoords).exists_witness

end Construction

end ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned
