import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Data.Fintype.Powerset
import ZInQKernel.Contrib.AbVarBC.Main
import ZInQKernel.Contrib.OneProof.TateLatticeTorsion
import ZInQKernel.Contrib.HDecomp.I3Linalg.RhoCont
import ZInQKernel.Contrib.OneProof.SemistablePrintedReadings
import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Main
import ZInQKernel.Contrib.OneProof.FaltingsLemma5Lower.Ker
import ZInQKernel.Contrib.CloudR2Poincare.L3.Cartier

/-! A uniform quasi-inverse scalar from the effective isogeny bound. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3.AbVar ZInQ.DefFaltings
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.GRUniformQuasiInverse
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

attribute [local instance] ZInQ.Contrib.MilneQuasiInverse.Kernel.kernelGroup

/-- Geometric points over an algebraic closure detect equality of morphisms from a reduced
scheme locally of finite type over a field to a separated scheme over the same field. -/
theorem overHom_ext_geometricPoints {K : Type} [Field K]
    {X Y : Over (Spec (.of K))} [LocallyOfFiniteType X.hom] [IsReduced X.left] [IsSeparated Y.hom]
    (f g : X ⟶ Y)
    (h : ∀ p : ZInQ.DefFaltings.ptObj K (AlgebraicClosure K) ⟶ X, p ≫ f = p ≫ g) : f = g := by
  haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hd : Dense (closedPoints X.left) := by
    rw [dense_iff_closure_eq, ← Set.univ_inter (closedPoints X.left),
      JacobsonSpace.closure_inter_closedPoints_eq_closure isOpen_univ.isLocallyClosed, closure_univ]
  apply Over.OverMorphism.ext
  refine ext_of_fromSpecResidueField_eq f.left g.left Y.hom (closedPoints X.left) hd ?_
    (by rw [Over.w, Over.w])
  intro x hx
  let i := X.left.fromSpecResidueField x
  haveI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp hx
  let a : CommRingCat.of K ⟶ X.left.residueField x := Spec.preimage (i ≫ X.hom)
  have ha : Spec.map a = i ≫ X.hom := Spec.map_preimage _
  let : Algebra K (X.left.residueField x) := a.hom.toAlgebra
  haveI : IsFinite (i ≫ X.hom) :=
    (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace (f := i ≫ X.hom)).mpr inferInstance
  haveI : Module.Finite K (X.left.residueField x) := by
    change a.hom.Finite
    rw [← IsFinite.SpecMap_iff, ha]
    infer_instance
  let b : X.left.residueField x →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let j := Spec.map (CommRingCat.ofHom b.toRingHom)
  have hw : (j ≫ i) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) := by
    rw [Category.assoc, ← ha, ← Spec.map_comp]
    congr 1
    ext k
    exact b.commutes k
  let p : ZInQ.DefFaltings.ptObj K (AlgebraicClosure K) ⟶ X := Over.homMk (j ≫ i) hw
  haveI : Surjective j := ⟨fun y => ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
  apply ext_of_isDominant_of_isSeparated Y.hom
    (by simp only [Category.assoc, Over.w]) j
  have hp := congrArg Over.Hom.left (h p)
  change (j ≫ i) ≫ f.left = (j ≫ i) ≫ g.left at hp
  simpa only [Category.assoc] using hp

/-- The geometric kernel cardinal of a finite homomorphism is positive. -/
theorem isogDeg_pos {K : Type} [Field K] {A B : PkgI3.AbVar K}
    (f : Hom A B) [IsFinite f.hom.left] : 0 < isogDeg f.hom := by
  haveI := GapHeight.finite_kerSchPts f.hom (algebraMap K (AlgebraicClosure K))
  have : Finite {P : ZInQ.DefFaltings.ptObj K (AlgebraicClosure K) ⟶ A.X // P ≫ f.hom = 1} :=
    Finite.of_equiv _ (GapHeight.kerSchEquiv f.hom (algebraMap K (AlgebraicClosure K))).symm
  have : Nonempty {P : ZInQ.DefFaltings.ptObj K (AlgebraicClosure K) ⟶ A.X // P ≫ f.hom = 1} :=
    ⟨⟨1, MonObj.one_comp f.hom⟩⟩
  exact Nat.card_pos

private theorem reduced_kernel {K : Type} [Field K] [CharZero K] {A B : PkgI3.AbVar K}
    (f : Hom A B) [IsFinite f.hom.left] :
    IsReduced (MilneQuasiInverse.Kernel.kernelObject f.hom).left := by
  let X := MilneQuasiInverse.Kernel.kernelObject f.hom
  haveI : IsFinite X.hom := MilneQuasiInverse.Kernel.kernel_isFinite f.hom
  have hX : X = Over.mk X.hom := by cases X; rfl
  letI : GrpObj (Over.mk X.hom) := hX ▸
    (MilneQuasiInverse.Kernel.kernelGroup f.hom : GrpObj X)
  exact ZInQ.Contrib.CloudR2Poincare.L3.isReduced_groupScheme_charZero K X.left X.hom

/-- In characteristic zero, the geometric kernel cardinal of a finite abelian-variety
homomorphism annihilates the kernel on every test scheme. -/
theorem isogDeg_annihilates_kernel {K : Type} [Field K] [CharZero K] {A B : PkgI3.AbVar K}
    (f : Hom A B) [IsFinite f.hom.left] :
    ∀ (T : Over (Spec (.of K))) (x : T ⟶ A.X), x ≫ f.hom = 1 →
      x ^ isogDeg f.hom = 1 := by
  let G := MilneQuasiInverse.Kernel.kernelGrp f.hom
  let X := G.X
  let T₀ := ZInQ.DefFaltings.ptObj K (AlgebraicClosure K)
  letI : GrpObj X := MilneQuasiInverse.Kernel.kernelGroup f.hom
  haveI : IsFinite X.hom := MilneQuasiInverse.Kernel.kernelGrp_isFinite f.hom
  haveI : LocallyOfFiniteType X.hom := inferInstance
  haveI : IsReduced X.left := reduced_kernel f
  haveI : IsSeparated X.hom := inferInstance
  let e := MilneQuasiInverse.Kernel.kernelPointsEquiv f.hom T₀
  have hc : Nat.card (T₀ ⟶ X) = isogDeg f.hom := Nat.card_congr e
  have hpow : (𝟙 X : X ⟶ X) ^ isogDeg f.hom = 1 := by
    apply overHom_ext_geometricPoints
    intro p
    rw [MonObj.comp_pow, Category.comp_id, MonObj.comp_one, ← hc]
    exact pow_card_eq_one'
  apply MilneQuasiInverse.Kernel.pow_eq_one_of_kernelGrp f.hom (isogDeg f.hom)
  intro T z
  have h := congrArg (fun p : X ⟶ X => z ≫ p) hpow
  rw [MonObj.comp_pow, MonObj.comp_one] at h
  exact (congrArg (fun y : T ⟶ X => y ^ isogDeg f.hom) (Category.comp_id z).symm).trans h

/-- For a fixed source with a stable height witness, the effective isogeny bound
provides one positive integer whose multiplication factors in both directions
through every isogenous target. -/
theorem exists_uniform_quasiInverse_of_gaudronRemond
    (hGR : ZInQ.SemistabAssembly.GaudronRemondThm14AnSS)
    (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (g : ℕ) (height : ℝ) (hDim : A.dim = (g : WithBot ℕ∞))
    (hHeight : ZInQ.SemistabAssembly.IsAnStableHeightSS A height) :
    ∃ N : ℕ, 0 < N ∧ ∀ B : PkgI3.AbVar K,
      (∃ φ : A.X ⟶ B.X, IsIsogeny φ) →
      ∃ f : Hom A B, IsIsogeny f.hom ∧ ∃ r : Hom B A,
        f.hom ≫ r.hom = (𝟙 A.X : A.X ⟶ A.X) ^ N ∧
        r.hom ≫ f.hom = (𝟙 B.X : B.X ⟶ B.X) ^ N := by
  let C := grKappa g (Module.finrank ℚ K) height
  let D := Nat.ceil C
  refine ⟨D.factorial, Nat.factorial_pos D, fun B hAB => ?_⟩
  obtain ⟨⟨φ, hφ, hbound⟩, _⟩ := hGR K A B g height hDim hHeight hAB
  haveI : IsMonHom φ := hφ.1
  let f : Hom A B := Hom.mk' φ
  haveI : IsFinite f.hom.left := hφ.2.1
  haveI : Surjective f.hom.left := hφ.2.2
  haveI : Flat f.hom.left :=
    MilneQuasiInverse.finite_surjective_abVarHom_flat (f := f) hφ.2
  haveI : QuasiCompact f.hom.left := inferInstance
  have hle : isogDeg f.hom ≤ D := by
    exact_mod_cast hbound.trans (Nat.le_ceil C)
  obtain ⟨j, hj⟩ := Nat.dvd_factorial (isogDeg_pos f) hle
  have hkill (T : Over (Spec (.of K))) (x : T ⟶ A.X) (hx : x ≫ f.hom = 1) :
      x ^ D.factorial = 1 := by
    rw [hj, pow_mul, isogDeg_annihilates_kernel f T x hx, one_pow]
  obtain ⟨r, hr, hfr, hrf⟩ :=
    MilneQuasiInverse.Descent.FppfPowerComplement.Construction.exists_fppf_power_complement
      f.hom D.factorial hkill
  haveI : IsMonHom r := hr
  exact ⟨f, hφ, Hom.mk' r, hfr, hrf⟩

/-- Containment of geometric kernels extends to containment on all test schemes. -/
theorem kernel_containment_of_geometric_points {K : Type} [Field K] [CharZero K]
    {A B C : PkgI3.AbVar K} (f : Hom A B) (g : Hom A C) [IsFinite f.hom.left]
    (h : ∀ P : ZInQ.DefFaltings.ptObj K (AlgebraicClosure K) ⟶ A.X,
      P ≫ f.hom = 1 → P ≫ g.hom = 1) :
    ∀ (T : Over (Spec (.of K))) (P : T ⟶ A.X),
      P ≫ f.hom = 1 → P ≫ g.hom = 1 := by
  let X := MilneQuasiInverse.Kernel.kernelObject f.hom
  let i : X ⟶ A.X := MilneQuasiInverse.Kernel.kernelInclusion f.hom
  have hi : i ≫ f.hom = 1 := MilneQuasiInverse.Kernel.kernelInclusion_comp f.hom
  haveI : IsFinite X.hom := MilneQuasiInverse.Kernel.kernel_isFinite f.hom
  haveI : LocallyOfFiniteType X.hom := inferInstance
  haveI : IsReduced X.left := reduced_kernel f
  have hk : i ≫ g.hom = 1 := by
    apply overHom_ext_geometricPoints
    intro P
    rw [MonObj.comp_one, ← Category.assoc]
    apply h
    rw [Category.assoc, hi, MonObj.comp_one]
  intro T P hP
  let v : T ⟶ X := (MilneQuasiInverse.Kernel.kernelPointsEquiv f.hom T).symm ⟨P, hP⟩
  have hv : v ≫ i = P :=
    MilneQuasiInverse.Kernel.kernelPointsEquiv_symm_comp f.hom T P hP
  rw [← hv, Category.assoc, hk, MonObj.comp_one]

private theorem epi_and_descend_of_geometric_kernel {K : Type} [Field K] [CharZero K]
    {A B C : PkgI3.AbVar K} (f : Hom A B) (g : Hom A C) (hf : IsIsogeny f.hom)
    (h : ∀ P : ZInQ.DefFaltings.ptObj K (AlgebraicClosure K) ⟶ A.X,
      P ≫ f.hom = 1 → P ≫ g.hom = 1) :
    Epi f.hom ∧ ∃ r : B.X ⟶ C.X, IsMonHom r ∧ f.hom ≫ r = g.hom := by
  haveI : IsFinite f.hom.left := hf.2.1
  haveI : Surjective f.hom.left := hf.2.2
  haveI : Flat f.hom.left :=
    MilneQuasiInverse.finite_surjective_abVarHom_flat (f := f) hf.2
  haveI : QuasiCompact f.hom.left := inferInstance
  haveI : EffectiveEpi f.hom :=
    MilneQuasiInverse.Descent.GroupDescent.Construction.effectiveEpi_over_of_fpqc f.hom
  haveI : EffectiveEpi (f.hom ⊗ₘ f.hom) :=
    MilneQuasiInverse.Descent.GroupDescent.Construction.effectiveEpi_tensor_over_of_fpqc f.hom f.hom
  exact ⟨inferInstance,
    MilneQuasiInverse.Descent.GroupKernelPowerDescent.Construction.groupHom_descends_of_kernel
      f.hom g.hom (kernel_containment_of_geometric_points f g h)⟩

/-- Isogenies from the same abelian variety with the same geometric kernel
have isomorphic targets as group schemes in characteristic zero. -/
theorem iso_of_same_geometric_kernel {K : Type} [Field K] [CharZero K]
    {A B C : PkgI3.AbVar K} (f : Hom A B) (g : Hom A C)
    (hf : IsIsogeny f.hom) (hg : IsIsogeny g.hom)
    (h : ∀ P : ZInQ.DefFaltings.ptObj K (AlgebraicClosure K) ⟶ A.X,
      P ≫ f.hom = 1 ↔ P ≫ g.hom = 1) :
    ∃ e : B.X ≅ C.X, IsMonHom e.hom := by
  obtain ⟨hef, r, hR, hr⟩ := epi_and_descend_of_geometric_kernel f g hf fun P => (h P).mp
  obtain ⟨heg, s, _, hs⟩ := epi_and_descend_of_geometric_kernel g f hg fun P => (h P).mpr
  haveI : Epi f.hom := hef
  haveI : Epi g.hom := heg
  have hrs : r ≫ s = 𝟙 _ := by
    apply (cancel_epi f.hom).mp
    rw [← Category.assoc, hr, hs, Category.comp_id]
  have hsr : s ≫ r = 𝟙 _ := by
    apply (cancel_epi g.hom).mp
    rw [← Category.assoc, hs, hr, Category.comp_id]
  exact ⟨⟨r, s, hrs, hsr⟩, hR⟩

/-- The effective bound implies finiteness of the isogeny class up to
isomorphism for each source with a witness for its stable height. -/
theorem finite_isogeny_class_of_gaudronRemond
    (hGR : ZInQ.SemistabAssembly.GaudronRemondThm14AnSS)
    (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (g : ℕ) (height : ℝ) (hDim : A.dim = (g : WithBot ℕ∞))
    (hHeight : ZInQ.SemistabAssembly.IsAnStableHeightSS A height) :
    ∃ S : Set (PkgI3.AbVar K), S.Finite ∧ ∀ B : PkgI3.AbVar K,
      (∃ f : A.X ⟶ B.X, IsIsogeny f) →
      ∃ C ∈ S, ∃ e : B.X ≅ C.X, IsMonHom e.hom := by
  classical
  obtain ⟨N, hN, hIsog⟩ :=
    exists_uniform_quasiInverse_of_gaudronRemond hGR K A g height hDim hHeight
  let T := ZInQ.DefFaltings.ptObj K (AlgebraicClosure K)
  let U := {P : T ⟶ A.X // P ^ N = 1}
  let nA := ((N : ℤ) : End A).hom
  have : IsFinite nA.left :=
    (ZInQ.Contrib.AbVarBC.mulIsogeny K A (N : ℤ) (Nat.cast_ne_zero.mpr hN.ne')).1
  haveI := GapHeight.finite_kerSchPts nA (algebraMap K (AlgebraicClosure K))
  haveI : Finite U := by
    let e : U ≃ {P : T ⟶ A.X // P ≫ nA = 1} :=
      Equiv.subtypeEquivRight (fun P => by rw [show P ≫ nA = P ^ N from AvSplit.comp_natCast_hom' A P N])
    have : Finite {P : T ⟶ A.X // P ≫ nA = 1} :=
      Finite.of_equiv _ (GapHeight.kerSchEquiv nA (algebraMap K (AlgebraicClosure K))).symm
    exact Finite.of_equiv _ e.symm
  let Cond (V : Set U) (B : PkgI3.AbVar K) : Prop :=
    ∃ f : Hom A B, IsIsogeny f.hom ∧
      (∀ P : T ⟶ A.X, P ≫ f.hom = 1 → P ^ N = 1) ∧
      ∀ P : U, P ∈ V ↔ P.1 ≫ f.hom = 1
  let I := {V : Set U // ∃ B : PkgI3.AbVar K, Cond V B}
  haveI : Finite I := inferInstance
  let chooseTarget (V : I) : PkgI3.AbVar K := V.2.choose
  have hChoose (V : I) : Cond V.1 (chooseTarget V) := V.2.choose_spec
  refine ⟨Set.range chooseTarget, Set.finite_range chooseTarget, fun B hAB => ?_⟩
  obtain ⟨f, hf, r, hfr, _⟩ := hIsog B hAB
  have hkill (P : T ⟶ A.X) (hP : P ≫ f.hom = 1) : P ^ N = 1 := by
    have hh := congrArg (fun a : A.X ⟶ A.X => P ≫ a) hfr
    rw [← Category.assoc, hP, MonObj.one_comp, MonObj.comp_pow, Category.comp_id] at hh
    exact hh.symm
  let V : Set U := {P | P.1 ≫ f.hom = 1}
  let v : I := ⟨V, B, f, hf, hkill, fun _ => Iff.rfl⟩
  refine ⟨chooseTarget v, ⟨v, rfl⟩, ?_⟩
  obtain ⟨f', hf', hkill', hkernel⟩ := hChoose v
  apply iso_of_same_geometric_kernel f f' hf hf'
  intro P
  constructor
  · intro hP
    exact (hkernel ⟨P, hkill P hP⟩).mp hP
  · intro hP
    exact (hkernel ⟨P, hkill' P hP⟩).mpr hP

private theorem homT_comp_eq_nsmul_id {K : Type} [Field K] {A B : PkgI3.AbVar K}
    (f : Hom A B) (r : Hom B A) (N ℓ : ℕ) [Fact ℓ.Prime]
    (h : f.hom ≫ r.hom = (𝟙 A.X : A.X ⟶ A.X) ^ N) :
    (homT (ℓ := ℓ) r).comp (homT (ℓ := ℓ) f) =
      N • (LinearMap.id : A.T ℓ →ₗ[ℤ_[ℓ]] A.T ℓ) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  change Additive.ofMul ((Additive.toMul (x.1 n) ≫ f.hom) ≫ r.hom) = (N • x).1 n
  rw [Category.assoc, h, MonObj.comp_pow, Category.comp_id]
  rfl

/-- The effective bound gives the same bounded denominators on all integral Tate modules
in the isogeny class of a fixed source. -/
theorem exists_uniform_tate_quasiInverse_of_gaudronRemond
    (hGR : ZInQ.SemistabAssembly.GaudronRemondThm14AnSS)
    (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (g : ℕ) (height : ℝ) (hDim : A.dim = (g : WithBot ℕ∞))
    (hHeight : ZInQ.SemistabAssembly.IsAnStableHeightSS A height) :
    ∃ N : ℕ, 0 < N ∧ ∀ B : PkgI3.AbVar K,
      (∃ φ : A.X ⟶ B.X, IsIsogeny φ) →
      ∃ f : Hom A B, IsIsogeny f.hom ∧ ∃ r : Hom B A,
        ∀ (ℓ : ℕ) [Fact ℓ.Prime],
          (homT (ℓ := ℓ) r).comp (homT (ℓ := ℓ) f) =
              N • (LinearMap.id : A.T ℓ →ₗ[ℤ_[ℓ]] A.T ℓ) ∧
          (homT (ℓ := ℓ) f).comp (homT (ℓ := ℓ) r) =
              N • (LinearMap.id : B.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ) := by
  obtain ⟨N, hN, h⟩ :=
    exists_uniform_quasiInverse_of_gaudronRemond hGR K A g height hDim hHeight
  refine ⟨N, hN, fun B hB => ?_⟩
  obtain ⟨f, hf, r, hfr, hrf⟩ := h B hB
  exact ⟨f, hf, r, fun ℓ _ => ⟨homT_comp_eq_nsmul_id f r N ℓ hfr,
    homT_comp_eq_nsmul_id r f N ℓ hrf⟩⟩

/-- The usual Néron-model, semistable-reduction and uniformization inputs supply
the analytic stable-height witness required by the effective isogeny bound. -/
theorem exists_anStableHeightSS
    (hN : ZInQ.H5Neron.NeronModelExists) (hSS : ZInQ.HeightSplit.SemistableReductionThm)
    (hU : ZInQ.LeafPush2.UniformizationExists) (hD : ZInQ.HeightFix.SemiAbelianDescendsPerfect)
    (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) :
    ∃ (g : ℕ) (height : ℝ), A.dim = (g : WithBot ℕ∞) ∧
      ZInQ.SemistabAssembly.IsAnStableHeightSS A height := by
  obtain ⟨L, iF, iN, iA, hss⟩ := hSS K A
  obtain ⟨𝒩, h𝒩⟩ := hN K A L
  have hsem := hss 𝒩 h𝒩
  obtain ⟨g, M, rfl⟩ := ZInQ.HeightGlue.neronMetrizable_of_t35 hU K A L 𝒩 h𝒩
  let height := M.hodge.modelHeight
  have h : ZInQ.HeightSplit.IsStableFaltingsHeight A height :=
    ⟨L, iF, iN, iA, M.model, h𝒩, hsem,
      ZInQ.HeightSplit.groupModel_height_eq
        (ZInQ.HeightGlue.analyticUniformizationUnique_of_t35 hU)
        ZInQ.HeightSplit.metrizedDimUnique M⟩
  have hPrinted := ZInQ.HeightFix.isPrintedStableHeight_of hU hD h
  have hAn := ZInQ.SemistabAssembly.isAnStableHeightSS_of
    ((ZInQ.R3Residual.isAnStableHeight_iff hU A height).mpr hPrinted)
  obtain ⟨_, _, _, _, _, g', _, _, hdim, _⟩ := hPrinted
  exact ⟨g', height, hdim, hAn⟩

/-- For a quotient killed by `ℓ^n`, the reverse isogeny realizes the integral
Tate sublattice specified by the geometric kernel at coordinate `n`. -/
theorem mem_range_homT_iff_coord_in_kernel {K : Type} [Field K] {A B : PkgI3.AbVar K}
    (f : Hom A B) (r : Hom B A) (ℓ n : ℕ) [Fact ℓ.Prime]
    (hfr : f.hom ≫ r.hom = (𝟙 A.X : A.X ⟶ A.X) ^ (ℓ ^ n))
    (hrf : r.hom ≫ f.hom = (𝟙 B.X : B.X ⟶ B.X) ^ (ℓ ^ n))
    (x : A.T ℓ) :
    x ∈ LinearMap.range (homT (ℓ := ℓ) r) ↔ Additive.toMul (x.1 n) ≫ f.hom = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    change (Additive.toMul (y.1 n) ≫ r.hom) ≫ f.hom = 1
    rw [Category.assoc, hrf, MonObj.comp_pow, Category.comp_id]
    exact congrArg Additive.toMul (PkgI3.Tate.pow_smul_eq_zero y.2 n)
  · intro hx
    let z := homT (ℓ := ℓ) f x
    have hz : z.1 n = 0 := congrArg Additive.ofMul hx
    obtain ⟨y, hy⟩ := (PkgI3.Tate.coord_eq_zero_iff z n).mp hz
    have he : z = (ℓ ^ n : ℕ) • y := by
      rw [hy, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    refine ⟨y, ?_⟩
    have hmul : (ℓ ^ n : ℕ) • x = (ℓ ^ n : ℕ) • homT (ℓ := ℓ) r y := by
      calc
        _ = homT (ℓ := ℓ) r z :=
          (congrArg (fun m : A.T ℓ →ₗ[ℤ_[ℓ]] A.T ℓ => m x)
            (homT_comp_eq_nsmul_id f r (ℓ ^ n) ℓ hfr)).symm
        _ = _ := by rw [he, map_nsmul]
    apply Subtype.ext
    funext j
    have hj := congrArg (fun v : A.T ℓ => v.1 (j + n)) hmul
    change (ℓ ^ n) • x.1 (j + n) = (ℓ ^ n) • (homT (ℓ := ℓ) r y).1 (j + n) at hj
    rw [PkgI3.Tate.pow_smul_shift x.2 n j,
      PkgI3.Tate.pow_smul_shift (homT (ℓ := ℓ) r y).2 n j] at hj
    exact hj.symm

/-- An isogeny with geometric kernel killed by `ℓ^n` supplies the Tate lattice
defined by that kernel at level `n`. -/
theorem exists_homT_range_of_geometric_kernel {K : Type} [Field K] [CharZero K]
    {A B : PkgI3.AbVar K} (f : Hom A B) (hf : IsIsogeny f.hom) (ℓ n : ℕ) [Fact ℓ.Prime]
    (hk : ∀ P : ZInQ.DefFaltings.ptObj K (AlgebraicClosure K) ⟶ A.X,
      P ≫ f.hom = 1 → P ^ (ℓ ^ n) = 1) :
    ∃ r : Hom B A, ∀ x : A.T ℓ,
      x ∈ LinearMap.range (homT (ℓ := ℓ) r) ↔ Additive.toMul (x.1 n) ≫ f.hom = 1 := by
  haveI : IsMonHom ((𝟙 A.X : A.X ⟶ A.X) ^ (ℓ ^ n)) :=
    MilneQuasiInverse.Descent.GroupDescent.Construction.groupHom_pow_isMonHom _ _
  let m : Hom A A := Hom.mk' ((𝟙 A.X : A.X ⟶ A.X) ^ (ℓ ^ n))
  obtain ⟨hepi, r, hr, hcomp⟩ := epi_and_descend_of_geometric_kernel f m hf (fun P hP => by
    change P ≫ (𝟙 A.X : A.X ⟶ A.X) ^ (ℓ ^ n) = 1
    rw [MonObj.comp_pow, Category.comp_id]
    exact hk P hP)
  haveI : IsMonHom r := hr
  haveI : Epi f.hom := hepi
  change f.hom ≫ r = (𝟙 A.X : A.X ⟶ A.X) ^ (ℓ ^ n) at hcomp
  have hrc : r ≫ f.hom = (𝟙 B.X : B.X ⟶ B.X) ^ (ℓ ^ n) := by
    apply (cancel_epi f.hom).mp
    rw [← Category.assoc, hcomp, MonObj.pow_comp, Category.id_comp, MonObj.comp_pow, Category.comp_id]
  exact ⟨Hom.mk' r, mem_range_homT_iff_coord_in_kernel f (Hom.mk' r) ℓ n hcomp hrc⟩

/-- Divisibility on the Tate module detects divisibility of the original
abelian-variety homomorphism by the same prime power. -/
theorem exists_eq_nsmul_of_homT_dvd {K : Type} [Field K] [CharZero K] {A B : PkgI3.AbVar K}
    (f : Hom A B) (ℓ n : ℕ) [hℓ : Fact ℓ.Prime]
    (h : ∀ x : A.T ℓ, ∃ y : B.T ℓ, homT f x = (ℓ : ℤ_[ℓ]) ^ n • y) :
    ∃ g : Hom A B, f = (ℓ ^ n : ℕ) • g := by
  let m : End A := ((ℓ ^ n : ℕ) : ℤ)
  have hm' : IsIsogenyMor m.hom :=
    AbVarBC.mulIsogeny K A (ℓ ^ n : ℕ) (Nat.cast_ne_zero.mpr (pow_ne_zero n hℓ.out.ne_zero))
  have hm : IsIsogeny m.hom := ⟨inferInstance, hm'⟩
  obtain ⟨_, r, hr, hmrf⟩ := epi_and_descend_of_geometric_kernel m f hm (fun P hP => by
    have hp : ℓ ^ n • Additive.ofMul P = 0 := by
      rw [AvSplit.comp_natCast_hom' A P (ℓ ^ n)] at hP
      exact congrArg Additive.ofMul hP
    obtain ⟨x, hx⟩ := TateLatticeTorsion.exists_tateCoord_of_geometric_torsion A hp
    have hZero := (PkgI3.Tate.coord_eq_zero_iff (homT f x) n).mpr (h x)
    change Additive.ofMul (Additive.toMul (x.1 n) ≫ f.hom) = 0 at hZero
    rw [hx] at hZero
    exact congrArg Additive.toMul hZero)
  haveI : IsMonHom r := hr
  refine ⟨Hom.mk' r, Hom.ext' ?_⟩
  change f.hom = r ^ (ℓ ^ n)
  rw [← hmrf]
  change (((ℓ ^ n : ℕ) : ℤ) : End A).hom ≫ r = r ^ (ℓ ^ n)
  rw [← Category.id_comp (_ ≫ r), ← Category.assoc, AvSplit.comp_natCast_hom',
    MonObj.pow_comp, Category.id_comp]

end ZInQ.Contrib.GRUniformQuasiInverse

#print axioms ZInQ.Contrib.GRUniformQuasiInverse.overHom_ext_geometricPoints
#print axioms ZInQ.Contrib.GRUniformQuasiInverse.isogDeg_annihilates_kernel

#print axioms ZInQ.Contrib.GRUniformQuasiInverse.exists_uniform_quasiInverse_of_gaudronRemond

#print axioms ZInQ.Contrib.GRUniformQuasiInverse.finite_isogeny_class_of_gaudronRemond

#print axioms ZInQ.Contrib.GRUniformQuasiInverse.exists_uniform_tate_quasiInverse_of_gaudronRemond

#print axioms ZInQ.Contrib.GRUniformQuasiInverse.exists_anStableHeightSS

#print axioms ZInQ.Contrib.GRUniformQuasiInverse.mem_range_homT_iff_coord_in_kernel

#print axioms ZInQ.Contrib.GRUniformQuasiInverse.exists_homT_range_of_geometric_kernel

#print axioms ZInQ.Contrib.GRUniformQuasiInverse.exists_eq_nsmul_of_homT_dvd
