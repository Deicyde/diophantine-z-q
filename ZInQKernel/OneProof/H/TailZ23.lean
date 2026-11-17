import ZInQKernel.OneProof.H.TailZ22
import ZInQKernel.OneProof.H.TailZ40
import ZInQKernel.Contrib.OneProof.FaltingsLemma5Lower

/-! # OneProof H, leaf-fold14 (1/2): the reduct fold, `OpenResearchLeaves14` and `sixContactMin_of_open17`

reduct-b (docs/research/reduct-b.md; `scratch/reduct-b/Body.lean`, copied below as namespace `ReductB` without its
fold check and `#print` lines) proves the three SGA 7 IX DVR fields of `OpenResearchLeaves13`, all strict GLUE:
* `semistableReductionDVR` (SGA 7 IX 3.6 over a DVR) by **K1** (`ReductB.semistableReductionDVR_of_raynaud`) from
  Raynaud's criterion, Mumford's torsion count and `[m]` étale;
* `raynaudSemistable` (4.7 over a DVR) from the strictly henselian printed leaf `ReductGlue.RaynaudSemistableSH`
  (unrestricted: `r6` is stated over every field) and `ReductGlue.StrictHenselizationPair`;
* `semistablePersistsDVR` (3.3a over a DVR): its only uses, SS1 and SS3 (`TailZ15`), are proved at number fields
  from the restricted printed leaf `ReductB.SemistablePersistsSHcp` (`[CharZero K]`, perfect, hence algebraically
  closed, residue field) and the pair (`ReductB.ss1_ss3_of_cp`).

The restricted leaf does not give the general-DVR field `semistablePersistsDVR` (imperfect residue fields), so the new
bundles cannot be mapped to `OpenResearchLeaves13`. They are mapped to leaf-fold9's `OpenResearchLeaves9` (with
leaf-fold10's `OpenAddedLeaves9`), the newest generation that has SS1 and SS3 as fields, by composing the maps of
`TailZ15`, `TailZ17`, `TailZ18`, `TailZ19` and `TailZ22` (each step copied, with the same terms), and
`sixContactMin_of_open17` calls `sixContactMin_of_open11`. docs/research/leaf-fold14.md lists the fields. -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)

namespace ReductB
open ReductSplit ReductGlue ZInQ.Contrib.AbVarBC

section Descent

variable {K : Type} [Field K]

/-- A separable element of `K̄` over an intermediate field `F`, fixed by `Aut(K̄/F)`, lies in `F`. -/
theorem mem_of_isSeparable_of_fixed_inter (F : IntermediateField K (AlgebraicClosure K))
    (a : AlgebraicClosure K) (ha : IsSeparable F a)
    (hfix : ∀ σ : AlgebraicClosure K ≃ₐ[F] AlgebraicClosure K, σ a = a) :
    a ∈ Set.range (algebraMap F (AlgebraicClosure K)) := by
  have : IsAlgClosure F (AlgebraicClosure K) :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := K) F⟩
  let L := separableClosure F (AlgebraicClosure K)
  have haL : a ∈ L := (mem_separableClosure_iff).mpr ha
  let a' : L := ⟨a, haL⟩
  have : a' ∈ Set.range (algebraMap F L) := by
    rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
    intro τ
    apply Subtype.ext
    have h1 := AlgEquiv.liftNormal_commutes τ (AlgebraicClosure K) a'
    have h2 : (algebraMap L (AlgebraicClosure K)) a' = a := rfl
    rw [h2, hfix] at h1
    exact h1.symm
  obtain ⟨c, hc⟩ := this
  exact ⟨c, by rw [IsScalarTower.algebraMap_apply F L (AlgebraicClosure K), hc]; rfl⟩

/-- **Galois descent to an intermediate field for points of an étale `K`-scheme**: a `K̄`-point
fixed by every `σ ∈ Aut(K̄/K)` that fixes `F` pointwise comes from an `F`-point. -/
theorem exists_rational_of_fixed_etale_inter (F : IntermediateField K (AlgebraicClosure K))
    (X : Over (Spec (CommRingCat.of K)))
    [Etale X.hom] (q : PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K) ⟶ X)
    (hq : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, (∀ y ∈ F, σ y = y) →
      PkgI3.AbVar.galHom σ ≫ q = q) :
    ∃ y : PkgI3.AbVar.ptObj (K := K) F ⟶ X, extHom F.val ≫ y = q := by
  classical
  let q0 : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ X.left := q.left
  have hq0 : q0 ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) :=
    Over.w q
  let p : X.left := q0 (IsLocalRing.closedPoint (AlgebraicClosure K))
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  change X.left.Opens at U
  change IsAffineOpen U at hU
  have hrange : Set.range q0 ⊆ Set.range U.ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : s = IsLocalRing.closedPoint (AlgebraicClosure K) :=
      Subsingleton.elim (α := PrimeSpectrum (AlgebraicClosure K)) _ _
    rw [this]
    exact hpU
  let q' := IsOpenImmersion.lift U.ι q0 hrange
  have hq' : q' ≫ U.ι = q0 := IsOpenImmersion.lift_fac _ _ _
  let e := hU.isoSpec
  let φ : Γ(X.left, U) ⟶ CommRingCat.of (AlgebraicClosure K) := Spec.preimage (q' ≫ e.hom)
  let θ : CommRingCat.of K ⟶ Γ(X.left, U) := Spec.preimage (e.inv ≫ U.ι ≫ X.hom)
  have hφ : Spec.map φ = q' ≫ e.hom := Spec.map_preimage _
  have hθ : Spec.map θ = e.inv ≫ U.ι ≫ X.hom := Spec.map_preimage _
  have hql : q0 = Spec.map φ ≫ e.inv ≫ U.ι := by
    rw [hφ, Category.assoc, e.hom_inv_id_assoc, hq']
  have hcomp : θ ≫ φ = CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hθ, Category.assoc, e.hom_inv_id_assoc, ← Category.assoc q', hq', hq0]
  have hfixφ : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, (∀ y ∈ F, σ y = y) →
      φ ≫ CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K) = φ := by
    intro σ hσ
    have h1 := congrArg Over.Hom.left (hq σ hσ)
    change Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫ q0 =
      q0 at h1
    rw [hql, ← Category.assoc, ← Spec.map_comp] at h1
    have h2 := (cancel_mono (e.inv ≫ U.ι)).mp h1
    exact Spec.map_injective h2
  have hθet : RingHom.Etale θ.hom := by
    have : Etale (Spec.map θ) := by rw [hθ]; infer_instance
    exact HasRingHomProperty.Spec_iff.mp this
  letI : Algebra K Γ(X.left, U) := θ.hom.toAlgebra
  have : Algebra.Etale K Γ(X.left, U) := hθet
  let f : Γ(X.left, U) →ₐ[K] AlgebraicClosure K :=
    { φ.hom with
      commutes' := fun a => congrArg (fun g => CommRingCat.Hom.hom g a) hcomp }
  have hmem : ∀ r, φ.hom r ∈ Set.range (algebraMap F (AlgebraicClosure K)) := by
    intro r
    refine mem_of_isSeparable_of_fixed_inter F _ ((isSeparable_of_etale f r).tower_top F)
      fun τ => ?_
    exact congrArg (fun f => CommRingCat.Hom.hom f r)
      (hfixφ (τ.restrictScalars K) (fun y hy => τ.commutes ⟨y, hy⟩))
  choose c hc using hmem
  have hinj := (algebraMap F (AlgebraicClosure K)).injective
  let ψ : Γ(X.left, U) →+* F :=
    { toFun := c
      map_one' := hinj (by rw [hc, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [hc, map_mul, map_mul, hc, hc])
      map_zero' := hinj (by rw [hc, map_zero, map_zero])
      map_add' := fun a b => hinj (by rw [hc, map_add, map_add, hc, hc]) }
  have hθψ : θ ≫ CommRingCat.ofHom ψ = CommRingCat.ofHom (algebraMap K F) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    apply hinj
    have := congrArg (fun f => CommRingCat.Hom.hom f a) hcomp
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this ⊢
    rw [show algebraMap F (AlgebraicClosure K) (ψ (θ.hom a)) = φ.hom (θ.hom a) from hc _, this]
    rfl
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι) ?_, ?_⟩
  · show (Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K F))
    rw [Category.assoc, Category.assoc, ← hθ, ← Spec.map_comp, hθψ]
  · apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom ((F.val : F →ₐ[K] AlgebraicClosure K) :
        F →+* AlgebraicClosure K)) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι = q0
    rw [hql, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext r
    exact hc r

/-- **Torsion points fixed by `Aut(K̄/F)` are `F`-rational** (from the bundle leaf
`MulEtaleAbelianScheme`): the intermediate-field form of `fixedTorsionRational_of_mulEtale`. -/
theorem fixedTorsionRational_inter (hE : AvSplit.T4.MulEtaleAbelianScheme)
    (F : IntermediateField K (AlgebraicClosure K)) (A : PkgI3.AbVar K) (m : ℕ) (hm : (m : K) ≠ 0)
    (x : A.Pt (AlgebraicClosure K)) (hx : x ^ m = 1)
    (hfix : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, (∀ y ∈ F, σ y = y) →
      A.galAct σ x = x) :
    ∃ z : A.Pt F, extPt A F.val z = x := by
  haveI : PkgI2.IsAbelianScheme (Grp.mk A.X) := ⟨inferInstanceAs (IsProper A.X.hom),
    inferInstanceAs (Smooth A.X.hom), inferInstanceAs (GeometricallyConnected A.X.hom)⟩
  have het : Etale ((𝟙 A.X ^ m : A.X ⟶ A.X).left) :=
    hE K (Grp.mk A.X) m (isUnit_iff_ne_zero.mpr hm)
  let M : A.X ⟶ A.X := 𝟙 A.X ^ m
  let P : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd M.left (η[A.X]).left)
  haveI : Etale P.hom := by
    change Etale (pullback.snd M.left (η[A.X]).left)
    infer_instance
  have hxm : x ≫ M = 1 := by rw [comp_pow_one]; exact hx
  have hw : x.left ≫ M.left =
      (PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K)).hom ≫ (η[A.X]).left := by
    have h1 := congrArg Over.Hom.left hxm
    rw [Over.comp_left] at h1
    rw [h1]
    change (toUnit _ ≫ η[A.X]).left = _
    rw [Over.comp_left]
    congr 1
  let x' : PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K) ⟶ P :=
    Over.homMk (pullback.lift x.left _ hw) (by simp [P])
  have hfix' : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, (∀ y ∈ F, σ y = y) →
      PkgI3.AbVar.galHom σ ≫ x' = x' := by
    intro σ hσ
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [x', Over.comp_left, Over.homMk_left, Category.assoc, pullback.lift_fst]
      exact congrArg Over.Hom.left (hfix σ hσ)
    · simp only [x', Over.comp_left, Over.homMk_left, Category.assoc, pullback.lift_snd]
      exact Over.w (PkgI3.AbVar.galHom σ)
  obtain ⟨y', hy'⟩ := exists_rational_of_fixed_etale_inter F P x' hfix'
  have hpr : pullback.fst M.left (η[A.X]).left ≫ A.X.hom = P.hom := by
    change _ = pullback.snd M.left (η[A.X]).left
    rw [← Over.w M, ← Category.assoc, pullback.condition, Category.assoc, Over.w η[A.X]]
    simp
  let pr : P ⟶ A.X := Over.homMk (pullback.fst M.left (η[A.X]).left) hpr
  refine ⟨y' ≫ pr, ?_⟩
  change extHom _ ≫ y' ≫ pr = x
  rw [← Category.assoc, hy']
  apply Over.OverMorphism.ext
  simp [x', pr]

end Descent

/-- `3` or `4` is a unit in a local ring (`4 - 3 = 1`). -/
theorem exists_three_le_isUnit {R : Type} [CommRing R] [IsLocalRing R] :
    ∃ m : ℕ, 3 ≤ m ∧ IsUnit (m : R) := by
  by_cases h3 : IsUnit ((3 : ℕ) : R)
  · exact ⟨3, le_rfl, h3⟩
  · refine ⟨4, by norm_num, ?_⟩
    have h1 : IsUnit (((4 : ℕ) : R) + -((3 : ℕ) : R)) := by
      rw [show ((4 : ℕ) : R) + -((3 : ℕ) : R) = 1 by push_cast; ring]
      exact isUnit_one
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1 with h | h
    · exact h
    · exact absurd (IsUnit.neg_iff _ |>.mp h) h3

/-- **K1: SGA 7 IX 3.6 over a DVR from Raynaud's criterion (4.7)**, with the bundle leaves
`MumfordTorsionAlgClosed` (finiteness of `A(K̄)[m]`) and `MulEtaleAbelianScheme` (`[m]` étale).
Take `m ∈ {3, 4}` invertible in `O`, `K'` a finite field of definition of `A(K̄)[m]`
(`torsionFieldOfDefinition_of`); at every DVR `O'` of `K'` over `O` the points of order `m` of
`A_{K'}` are `K'`-rational (`torsion_descends_etale` and `fixedTorsionRational_inter`), so Raynaud's
criterion applies to `A_{K'}` over `O'`. -/
theorem semistableReductionDVR_of_raynaud (hR : RaynaudSemistable)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hE : AvSplit.T4.MulEtaleAbelianScheme) :
    SemistableReductionDVR := by
  intro K _ O _ A
  obtain ⟨m, hm3, hmu⟩ := exists_three_le_isUnit (R := O)
  have hmK : (m : K) ≠ 0 := natCast_ne_zero_of_isUnit O hmu
  obtain ⟨K', hfin, hfix⟩ :=
    torsionFieldOfDefinition_of (AvSplit.torsionStructure_of_mumford hM) K A m hmK
  refine ⟨K', hfin, fun O' hO'dvr hO => ?_⟩
  haveI := hO'dvr
  have hmu' : IsUnit (m : O') := by
    have := hmu.map (comapHom hO)
    rwa [map_natCast] at this
  refine hR K' O' (A.baseChange K') m hm3 hmu' ?_
  intro x hx
  haveI : Algebra.IsAlgebraic K' (AlgebraicClosure K) := Algebra.IsAlgebraic.tower_top (K := K) K'
  haveI : Module.IsTorsionFree K' (AlgebraicClosure K') :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap K' (AlgebraicClosure K')).injective
  haveI : Module.IsTorsionFree K' (AlgebraicClosure K) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap K' (AlgebraicClosure K)).injective
  let κ' : AlgebraicClosure K →ₐ[K'] AlgebraicClosure K' := IsAlgClosed.lift
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K' := κ'.restrictScalars K
  obtain ⟨p, hp, hpx⟩ := torsion_descends_etale hE A κ m hmK x hx
  obtain ⟨z, hz⟩ := fixedTorsionRational_inter hE K' A m hmK p hp (fun σ hσ => hfix σ hσ p hp)
  refine ⟨(bcPt A K').symm z, ?_⟩
  rw [← hpx, ← hz]
  apply (bcPt A (AlgebraicClosure K')).injective
  rw [MulEquiv.apply_symm_apply, bcPt_extPt, MulEquiv.apply_symm_apply, extPt_extPt]
  have hκ : AlgHom.restrictScalars K (Algebra.ofId K' (AlgebraicClosure K')) = κ.comp K'.val := by
    refine AlgHom.ext fun a => ?_
    exact (κ'.commutes a).symm
  rw [hκ]


/-! ## Route B: 4.7 and 3.3a over a DVR from their strictly henselian forms and one
strict-henselization leaf -/

section RouteB

theorem comap_algebraMap_self {K : Type} [Field K] (O : ValuationSubring K) :
    O.comap (algebraMap K K) = O := by
  ext x
  rfl

/-- **`StrictHenselizationPair` implies `StrictHenselizationNeron`**: the instance `K' = K`,
`O' = O` of the pair; `IsSHNeronExt`'s body is `StrictHenselizationNeron`'s body. -/
theorem strictHenselizationNeron_of_pair (hPair : StrictHenselizationPair) :
    StrictHenselizationNeron := by
  intro K _ O _
  obtain ⟨E, E', _, _, _, _, _, _, _, _, _, P, P', hP, hP', hSHP, -, -⟩ :=
    hPair K O K O (comap_algebraMap_self O)
  exact ⟨E, inferInstance, inferInstance, P, hP, hSHP⟩

/-- **SGA 7 IX 4.7 over a DVR** (`RaynaudSemistable`, the bundle field) from the strictly henselian
form, `StrictHenselizationPair` and the bundle leaf `MulEtaleAbelianScheme`. -/
theorem raynaudSemistable_of_SH_pair (hR : RaynaudSemistableSH) (hPair : StrictHenselizationPair)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : RaynaudSemistable :=
  raynaudSemistable_of_SH' hR (strictHenselizationNeron_of_pair hPair) hE

/-- **SGA 7 IX 3.3, first assertion, over a DVR** (`SemistablePersistsDVR`, the bundle field) from
the strictly henselian form and `StrictHenselizationPair`. -/
theorem semistablePersistsDVR_of_SH_pair (hP : SemistablePersistsSH)
    (hPair : StrictHenselizationPair) : SemistablePersistsDVR :=
  persistsFromSH_of hPair hP

/-- **SGA 7 IX 3.6 over a DVR** (`SemistableReductionDVR`, the bundle field) from the strictly
henselian 4.7, `StrictHenselizationPair` and the bundle leaves `MumfordTorsionAlgClosed`,
`MulEtaleAbelianScheme` (K1 composed with Route B). -/
theorem semistableReductionDVR_of_SH_pair (hR : RaynaudSemistableSH)
    (hPair : StrictHenselizationPair) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : SemistableReductionDVR :=
  semistableReductionDVR_of_raynaud (raynaudSemistable_of_SH_pair hR hPair hE) hM hE

/-- The three bundle fields from the printed (strictly henselian) leaves. -/
theorem three_fields_of_printed (hR : RaynaudSemistableSH) (hP : SemistablePersistsSH)
    (hPair : StrictHenselizationPair) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) :
    SemistableReductionDVR ∧ RaynaudSemistable ∧ SemistablePersistsDVR :=
  ⟨semistableReductionDVR_of_SH_pair hR hPair hM hE, raynaudSemistable_of_SH_pair hR hPair hE,
    semistablePersistsDVR_of_SH_pair hP hPair⟩

end RouteB

/-! ## Route B with `[CharZero K]` and `[PerfectField (ResidueField O)]` on the strictly henselian
forms (perfect + separably closed residue field = algebraically closed residue field) -/

section RouteBCP

/-- **LEAF (printed base, restricted) `RaynaudSemistableSHcp`**: Raynaud's criterion (SGA 7 I,
Exp. IX, Prop. 4.7; number UNVERIFIED) for a strictly henselian DVR `O` of a field of characteristic
`0` whose residue field is perfect (hence algebraically closed). A specialization of
`RaynaudSemistableSH`. -/
def RaynaudSemistableSHcp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)],
    IsStrictlyHenselianDVR O → ∀ (A : PkgI3.AbVar K) (m : ℕ), 3 ≤ m → IsUnit (m : O) →
    (∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 →
      ∃ y : A.Pt K, ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y = x) →
    SemistableNeronModels A O

/-- **LEAF (printed base, restricted) `SemistablePersistsSHcp`**: SGA 7 I, Exp. IX, Prop. 3.3,
first assertion (number UNVERIFIED), over a strictly henselian base DVR `O` of a field of
characteristic `0` with perfect (hence algebraically closed) residue field. A specialization of
`SemistablePersistsSH`. -/
def SemistablePersistsSHcp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)], IsStrictlyHenselianDVR O →
    ∀ (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'], O'.comap (algebraMap K K') = O →
    ∀ A : PkgI3.AbVar K, HasSemistableReduction A O → SemistableNeronModels (A.baseChange K') O'

/-- `RaynaudSemistable` with the two instances (the DVR form reachable from `RaynaudSemistableSHcp`). -/
def RaynaudSemistableCP : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)] (A : PkgI3.AbVar K)
    (m : ℕ), 3 ≤ m → IsUnit (m : O) →
    (∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 →
      ∃ y : A.Pt K, ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y = x) →
    SemistableNeronModels A O

/-- `SemistablePersistsDVR` with the two instances on the base. -/
def SemistablePersistsDVRcp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'], O'.comap (algebraMap K K') = O →
    ∀ A : PkgI3.AbVar K, HasSemistableReduction A O → SemistableNeronModels (A.baseChange K') O'

/-- The restricted printed leaves are specializations of the general-DVR forms (so not stronger). -/
theorem cp_of_general (h47 : RaynaudSemistable) (h33 : SemistablePersistsDVR) :
    RaynaudSemistableSHcp ∧ SemistablePersistsSHcp :=
  ⟨fun K _ _ O _ _ _ A m hm hmu ht => h47 K O A m hm hmu ht,
   fun K _ _ O _ _ _ K' _ _ _ O' _ hO A hA => h33 K O K' O' hO A hA⟩

theorem charZero_of_algebra (K E : Type) [Field K] [Field E] [Algebra K E] [CharZero K] :
    CharZero E :=
  charZero_of_injective_algebraMap (algebraMap K E).injective

theorem perfectField_of_isSHNeronExt {K E : Type} [Field K] [Field E] [Algebra K E]
    {O : ValuationSubring K} {P : ValuationSubring E} {hP : P.comap (algebraMap K E) = O}
    [PerfectField (IsLocalRing.ResidueField O)] (h : IsSHNeronExt O P hP) :
    PerfectField (IsLocalRing.ResidueField P) := by
  obtain ⟨-, halg, -⟩ := h
  letI := (resMap hP).toAlgebra
  exact Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField O)

/-- **`RaynaudSemistableCP` from `RaynaudSemistableSHcp`**, `StrictHenselizationPair` and
`MulEtaleAbelianScheme`. -/
theorem raynaudSemistableCP_of_SH (hR : RaynaudSemistableSHcp) (hPair : StrictHenselizationPair)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : RaynaudSemistableCP := by
  intro K _ _ O _ _ A m hm3 hmu htors 𝒩 h𝒩
  obtain ⟨E, E', _, _, _, _, _, _, _, _, _, P, P', hP, hP', hSHP, -, -⟩ :=
    hPair K O K O (comap_algebraMap_self O)
  haveI : CharZero E := charZero_of_algebra K E
  haveI : PerfectField (IsLocalRing.ResidueField P) := perfectField_of_isSHNeronExt hSHP
  obtain ⟨hSH, halg, hbc⟩ := hSHP
  haveI : IsDiscreteValuationRing P := hSH.1
  have hmu' : IsUnit (m : P) := by
    have := hmu.map (comapHom hP)
    rwa [map_natCast] at this
  rw [isSemistable_bcDVR_iff hP halg]
  refine hR E P hSH (A.baseChange E) m hm3 hmu' ?_ _ (hbc A 𝒩 h𝒩)
  intro x hx
  have hmK : (m : K) ≠ 0 := natCast_ne_zero_of_isUnit O hmu
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure E := IsAlgClosed.lift
  obtain ⟨p, hp, hpx⟩ := torsion_descends_etale hE A κ m hmK x hx
  obtain ⟨z, hz⟩ := htors p hp
  refine ⟨(bcPt A E).symm (extPt A (Algebra.ofId K E) z), ?_⟩
  rw [← hpx, ← hz]
  apply (bcPt A (AlgebraicClosure E)).injective
  rw [MulEquiv.apply_symm_apply, bcPt_extPt, MulEquiv.apply_symm_apply, extPt_extPt, extPt_extPt]
  congr 1
  ext a
  simp

/-- **`SemistablePersistsDVRcp` from `SemistablePersistsSHcp`** and `StrictHenselizationPair`
(the proof of `persistsFromSH_of`, with the instances carried to the strict henselization). -/
theorem semistablePersistsDVRcp_of_SH (hSH : SemistablePersistsSHcp)
    (hPair : StrictHenselizationPair) : SemistablePersistsDVRcp := by
  intro K _ _ O _ _ K' _ _ _ O' _ hO A hA 𝒩' h𝒩'
  obtain ⟨E, E', _, _, _, _, _, _, _, _, _, P, P', hP, hP', hSHP0, ⟨hSHP', halgP', hbcP'⟩, hPP'⟩ :=
    hPair K O K' O' hO
  haveI : CharZero E := charZero_of_algebra K E
  haveI : PerfectField (IsLocalRing.ResidueField P) := perfectField_of_isSHNeronExt hSHP0
  obtain ⟨hSHP, halgP, hbcP⟩ := hSHP0
  haveI : IsDiscreteValuationRing P := hSHP.1
  haveI : IsDiscreteValuationRing P' := hSHP'.1
  have hAE : HasSemistableReduction (A.baseChange E) P := by
    obtain ⟨𝒩, h𝒩, hs⟩ := hA
    exact ⟨bcDVR hP 𝒩, hbcP A 𝒩 h𝒩, (isSemistable_bcDVR_iff hP halgP 𝒩).mp hs⟩
  have h1 : SemistableNeronModels ((A.baseChange E).baseChange E') P' :=
    hSH E P hSHP E' P' hPP' (A.baseChange E) hAE
  have he : IsMonHom (bcbcIso A E E' ≪≫ (bcbcIso A K' E').symm).hom := by
    haveI := bcbcIso_isMonHom A E E'
    have : IsMonHom (bcbcIso A K' E').inv := by
      haveI := bcbcIso_isMonHom A K' E'
      infer_instance
    exact @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ (bcbcIso_isMonHom A E E') this
  have h2 : SemistableNeronModels ((A.baseChange K').baseChange E') P' :=
    semistableNeronModels_transport (bcbcIso A E E' ≪≫ (bcbcIso A K' E').symm) he h1
  rw [isSemistable_bcDVR_iff hP' halgP']
  exact h2 _ (hbcP' (A.baseChange K') 𝒩' h𝒩')

/-- The residue field of a DVR of a number field is finite, hence perfect. -/
theorem perfectField_residue_nf {L : Type} [Field L] [NumberField L] (O : ValuationSubring L)
    [IsDiscreteValuationRing O] : PerfectField (IsLocalRing.ResidueField O) := by
  haveI : (center O).IsMaximal := center_isMaximal O
  haveI : Finite (𝓞 L ⧸ center O) := Ideal.finiteQuotientOfFreeOfNeBot (center O) (center_ne_bot O)
  haveI : Finite (center O).ResidueField :=
    Finite.of_surjective _ (center O).bijective_algebraMap_quotient_residueField.2
  haveI : Finite (IsLocalRing.ResidueField O) := Finite.of_equiv _ (resIso O).toEquiv
  infer_instance

/-- `SemistablePersistsDVR` at number fields (the generality of every use: SS1, SS3). -/
def SemistablePersistsDVRnf : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'], O'.comap (algebraMap K K') = O →
    ∀ A : PkgI3.AbVar K, HasSemistableReduction A O → SemistableNeronModels (A.baseChange K') O'

theorem persistsNF_of_cp (h : SemistablePersistsDVRcp) : SemistablePersistsDVRnf := by
  intro K _ _ O _ K' _ _ _ O' _ hO A hA
  haveI := perfectField_residue_nf O
  exact h K O K' O' hO A hA

theorem persistsNF_of_general (h : SemistablePersistsDVR) : SemistablePersistsDVRnf :=
  fun K _ _ O _ K' _ _ _ O' _ hO A hA => h K O K' O' hO A hA

/-- **SS3** (`HeightSplit.SemistablePersists`) from the number-field form of 3.3a: reduct-split's
`semistablePersists_of_leaves` with `h33` retyped (proof unchanged). -/
theorem semistablePersists_of_leaves_nf (h33 : SemistablePersistsDVRnf)
    (hN : NeronSchemeModelExistsDVR) (hLG : SemistableLocalGlobal) (hDown : DVRComapFinite) :
    ZInQ.HeightSplit.SemistablePersists := by
  intro K _ _ A L _ _ _ 𝒩 h𝒩 hss L' _ _ _ _ _ 𝒩' h𝒩'
  rw [hLG K A L 𝒩 h𝒩] at hss
  rw [hLG K A L' 𝒩' h𝒩']
  intro O' hO'
  haveI := hO'
  haveI : IsDiscreteValuationRing (O'.comap (algebraMap L L')) := hDown L L' O' hO'
  haveI : FiniteDimensional L L' := Module.Finite.of_restrictScalars_finite ℚ L L'
  have h1 := h33 L (O'.comap (algebraMap L L')) L' O' rfl (A.baseChange L)
    (hss _ inferInstance)
  exact hasSemistableReduction_of hN O' _
    (semistableNeronModels_transport (bcbcIso A L L') (bcbcIso_isMonHom A L L') h1)


/-- `SemistableReductionDVR` at number fields (the generality of its use in SS1; its other use, r8,
is over every field). -/
def SemistableReductionDVRnf : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : PkgI3.AbVar K),
    ∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
      ∀ O' : ValuationSubring K', IsDiscreteValuationRing O' →
        O'.comap (algebraMap K K') = O → SemistableNeronModels (A.baseChange K') O'

theorem reductionNF_of_general (h : SemistableReductionDVR) : SemistableReductionDVRnf :=
  fun K _ _ O _ A => h K O A

/-- **K1 at number fields from the restricted 4.7** (`RaynaudSemistableCP`): the proof of
`semistableReductionDVR_of_raynaud`, with `K'` a number field, so `κ(O')` is finite. -/
theorem semistableReductionDVRnf_of_raynaudCP (hR : RaynaudSemistableCP)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hE : AvSplit.T4.MulEtaleAbelianScheme) :
    SemistableReductionDVRnf := by
  intro K _ _ O _ A
  obtain ⟨m, hm3, hmu⟩ := exists_three_le_isUnit (R := O)
  have hmK : (m : K) ≠ 0 := natCast_ne_zero_of_isUnit O hmu
  obtain ⟨K', hfin, hfix⟩ :=
    torsionFieldOfDefinition_of (AvSplit.torsionStructure_of_mumford hM) K A m hmK
  refine ⟨K', hfin, fun O' hO'dvr hO => ?_⟩
  haveI := hO'dvr
  haveI : NumberField K' := NumberField.of_module_finite K K'
  haveI := perfectField_residue_nf O'
  have hmu' : IsUnit (m : O') := by
    have := hmu.map (comapHom hO)
    rwa [map_natCast] at this
  refine hR K' O' (A.baseChange K') m hm3 hmu' ?_
  intro x hx
  haveI : Algebra.IsAlgebraic K' (AlgebraicClosure K) := Algebra.IsAlgebraic.tower_top (K := K) K'
  haveI : Module.IsTorsionFree K' (AlgebraicClosure K') :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap K' (AlgebraicClosure K')).injective
  haveI : Module.IsTorsionFree K' (AlgebraicClosure K) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap K' (AlgebraicClosure K)).injective
  let κ' : AlgebraicClosure K →ₐ[K'] AlgebraicClosure K' := IsAlgClosed.lift
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K' := κ'.restrictScalars K
  obtain ⟨p, hp, hpx⟩ := torsion_descends_etale hE A κ m hmK x hx
  obtain ⟨z, hz⟩ := fixedTorsionRational_inter hE K' A m hmK p hp (fun σ hσ => hfix σ hσ p hp)
  refine ⟨(bcPt A K').symm z, ?_⟩
  rw [← hpx, ← hz]
  apply (bcPt A (AlgebraicClosure K')).injective
  rw [MulEquiv.apply_symm_apply, bcPt_extPt, MulEquiv.apply_symm_apply, extPt_extPt]
  have hκ : AlgHom.restrictScalars K (Algebra.ofId K' (AlgebraicClosure K')) = κ.comp K'.val := by
    refine AlgHom.ext fun a => ?_
    exact (κ'.commutes a).symm
  rw [hκ]

/-- **SS1** (`HeightSplit.SemistableReductionThm`) from 3.6 and the number-field form of 3.3a:
reduct-split's `semistableReductionThm_of_leaves` with `h33` retyped; the only addition is the
`NumberField (F O)` instance at the one use of `h33` over `F O`. -/
theorem semistableReductionThm_of_leaves_nf (h36 : SemistableReductionDVRnf)
    (h33 : SemistablePersistsDVRnf) (hN : NeronSchemeModelExistsDVR) (hLG : SemistableLocalGlobal)
    (hAA : SemistableAlmostAll) (hDown : DVRComapFinite) :
    ZInQ.HeightSplit.SemistableReductionThm := by
  classical
  intro K _ _ A
  set S := {O : ValuationSubring K | IsDiscreteValuationRing O ∧ ¬ HasSemistableReduction A O}
  have hS : S.Finite := hAA K A
  have hch : ∀ O : ValuationSubring K, ∃ K' : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K K' ∧ (IsDiscreteValuationRing O →
        ∀ O' : ValuationSubring K', IsDiscreteValuationRing O' →
          O'.comap (algebraMap K K') = O → SemistableNeronModels (A.baseChange K') O') := by
    intro O
    by_cases hO : IsDiscreteValuationRing O
    · obtain ⟨K', h1, h2⟩ := h36 K O A
      exact ⟨K', h1, fun _ => h2⟩
    · exact ⟨⊥, inferInstance, fun h => absurd h hO⟩
  choose F hFfin hF using hch
  let L₀ : IntermediateField K (AlgebraicClosure K) := ⨆ O ∈ hS.toFinset, F O
  haveI : FiniteDimensional K L₀ :=
    IntermediateField.finiteDimensional_iSup_of_finset' (fun O _ => hFfin O)
  haveI : NumberField L₀ := NumberField.of_module_finite K L₀
  refine ⟨L₀, inferInstance, inferInstance, inferInstance, fun 𝒩 h𝒩 => ?_⟩
  rw [hLG K A L₀ 𝒩 h𝒩]
  intro O'' hO''
  haveI := hO''
  haveI hO : IsDiscreteValuationRing (O''.comap (algebraMap K L₀)) := hDown K L₀ O'' hO''
  by_cases hOS : O''.comap (algebraMap K L₀) ∈ S
  · -- a place of bad reduction: go through `F O ≤ L₀`
    set O := O''.comap (algebraMap K L₀) with hOdef
    have hle : F O ≤ L₀ := le_iSup₂ (f := fun O _ => F O) O (hS.mem_toFinset.mpr hOS)
    letI : Algebra (F O) L₀ := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    haveI : IsScalarTower K (F O) L₀ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : FiniteDimensional (F O) L₀ := by
      haveI := hFfin O
      exact FiniteDimensional.right K (F O) L₀
    haveI : NumberField (F O) := by
      haveI := hFfin O
      exact NumberField.of_module_finite K (F O)
    haveI hOi : IsDiscreteValuationRing (O''.comap (algebraMap (F O) L₀)) :=
      hDown (F O) L₀ O'' hO''
    have hc : (O''.comap (algebraMap (F O) L₀)).comap (algebraMap K (F O)) = O := by
      rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq]
    have h1 : SemistableNeronModels (A.baseChange (F O)) (O''.comap (algebraMap (F O) L₀)) :=
      hF O hO _ hOi hc
    have h2 := hasSemistableReduction_of hN _ _ h1
    have h3 := h33 (F O) (O''.comap (algebraMap (F O) L₀)) L₀ O'' rfl (A.baseChange (F O)) h2
    exact hasSemistableReduction_of hN O'' _
      (semistableNeronModels_transport (bcbcIso A (F O) L₀) (bcbcIso_isMonHom A (F O) L₀) h3)
  · -- a place of semistable reduction of `A`
    have hgood : HasSemistableReduction A (O''.comap (algebraMap K L₀)) := by
      by_contra hc
      exact hOS ⟨hO, hc⟩
    exact hasSemistableReduction_of hN O'' _ (h33 K _ L₀ O'' rfl A hgood)

/-- **SS3** from the number-field form of 3.3a, `DVRComapFinite` discharged (as
`semistablePersists_final`). -/
theorem semistablePersists_final_nf (h33 : SemistablePersistsDVRnf)
    (hN : NeronSchemeModelExistsDVR) (hLG : SemistableLocalGlobal) :
    ZInQ.HeightSplit.SemistablePersists :=
  semistablePersists_of_leaves_nf h33 hN hLG dvrComapFinite

/-- **SS1** from 3.6 and the number-field form of 3.3a, `DVRComapFinite` discharged (as
`semistableReductionThm_final`). -/
theorem semistableReductionThm_final_nf (h36 : SemistableReductionDVRnf)
    (h33 : SemistablePersistsDVRnf) (hN : NeronSchemeModelExistsDVR) (hLG : SemistableLocalGlobal)
    (hAA : SemistableAlmostAll) : ZInQ.HeightSplit.SemistableReductionThm :=
  semistableReductionThm_of_leaves_nf h36 h33 hN hLG hAA dvrComapFinite

/-- The two uses of 3.3a (SS1 and SS3, as in `TailZ15`) from the restricted printed leaf
`SemistablePersistsSHcp` and `StrictHenselizationPair`. -/
theorem ss1_ss3_of_cp (hSH : SemistablePersistsSHcp) (hPair : StrictHenselizationPair)
    (h36 : SemistableReductionDVR) (hN : NeronSchemeModelExistsDVR) (hLG : SemistableLocalGlobal)
    (hAA : SemistableAlmostAll) :
    ZInQ.HeightSplit.SemistableReductionThm ∧ ZInQ.HeightSplit.SemistablePersists :=
  ⟨semistableReductionThm_final_nf (reductionNF_of_general h36) (persistsNF_of_cp (semistablePersistsDVRcp_of_SH hSH hPair))
      hN hLG hAA,
    semistablePersists_final_nf (persistsNF_of_cp (semistablePersistsDVRcp_of_SH hSH hPair)) hN hLG⟩

/-- **SS1 and SS3 from the restricted printed leaves only** (no general-field SGA 7 leaf):
`RaynaudSemistableSHcp`, `SemistablePersistsSHcp`, `StrictHenselizationPair`, Mumford and `[m]` étale.
(r6 and r8, the other uses of 4.7 and 3.6, are over every field and are not covered.) -/
theorem ss1_ss3_of_cp_full (hR : RaynaudSemistableSHcp) (hSH : SemistablePersistsSHcp)
    (hPair : StrictHenselizationPair) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) (hN : NeronSchemeModelExistsDVR)
    (hLG : SemistableLocalGlobal) (hAA : SemistableAlmostAll) :
    ZInQ.HeightSplit.SemistableReductionThm ∧ ZInQ.HeightSplit.SemistablePersists :=
  ⟨semistableReductionThm_final_nf
      (semistableReductionDVRnf_of_raynaudCP (raynaudSemistableCP_of_SH hR hPair hE) hM hE)
      (persistsNF_of_cp (semistablePersistsDVRcp_of_SH hSH hPair)) hN hLG hAA,
    semistablePersists_final_nf (persistsNF_of_cp (semistablePersistsDVRcp_of_SH hSH hPair)) hN hLG⟩

end RouteBCP

end ReductB

namespace HDec

namespace HSyn

/-! ## The bundle -/

/-- **The research leaves still open** (leaf-fold14, reduct fold): x6-fold's `OpenResearchLeaves13` without
`semistableReductionDVR`, `raynaudSemistable` and `semistablePersistsDVR` (reduct-b), with
`raynaudSemistableSH`, `semistablePersistsSHcp` and `strictHenselizationPair` added. 35 fields. -/
structure OpenResearchLeaves14 : Prop where
  /-- H-139, printed form: Shimura's family over the fine moduli scheme of abelian schemes. Replaces
  `shimuraFamily`. -/
  shimuraFamilyAb : QMSplit.Moduli.ShimuraFamilyAb
  igusaPsi4 : QMSplit.Theta.IgusaPsi4
  igusaChi10 : QMSplit.Theta.IgusaChi10
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.BostLowerBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- reduct-split, r8: SGA 7 IX Prop. 3.5, "semistable ⇒ `(σ - 1)² = 0` on `T_ℓ`" (weakest reading). -/
  semistableUnipotent : _root_.ReductSplit.SemistableUnipotent
  /-- shimura-split, r5count, printed form: González–Rotger 2006 Prop. 5.6 at `(D, N) = (6, 1)` on the points of
  one canonical coarse witness `X₆` of the fine moduli scheme of abelian schemes. Replaces
  `gonzalezRotgerCountX6`. -/
  gonzalezRotgerCountX6Ab : _root_.ShimuraSplit.GonzalezRotgerCountX6Ab
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune proves that each
  `ι(a)` is a homomorphism from the field points). -/
  mumfordGroupLaw : _root_.ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw
  /-- c-to-printed, printed form: Bosch–Lütkebohmert–Raynaud, *Néron models*, §1.2 Prop. 4 (over a Dedekind
  domain, a smooth separated model of finite type is a Néron model iff its localizations at the closed points are;
  locator UNVERIFIED). Replaces `neronLocalizesDVR`. -/
  blr_1_2_4 : _root_.CToPrinted.BLR_1_2_4
  -- fold33-combine (sga3-nbhd): field `sga3_VIB_3_10` deleted (its readers no longer need SGA 3 VI_B 3.10)
  /-- c-to-printed, printed form: SGA 7 IX 3.3 (`N⁰ ⊗ R' ≅ N'⁰` for semistable reduction; locator UNVERIFIED). -/
  sga7_IX_3_3 : _root_.CToPrinted.SGA7_IX_3_3
  /-- c-to-printed, printed form: EGA IV 8.10.5, open immersions descend through limits (locator UNVERIFIED). -/
  egaIV_8_10_5_openImm : _root_.CToPrinted.EGAIV_8_10_5_openImm
  /-- x6-glue, printed form (on abelian schemes): Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 and Lemma 3.1
  (read by the locator audit), on one canonical coarse witness `X₆`: a coordinate `π : X₆ → P¹` whose fibres are the
  `Aut(𝒪)`-twist classes, with three distinct rational values at the CM points of discriminants `−4, −3, −24` (the
  CM assignment read from the §3.1 table, UNVERIFIED). -/
  babaGranathRationalAb : QMSplit.Moduli.BabaGranathRationalAb
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- x6-glue, printed form (on abelian schemes): Elkies, *Shimura curve computations*, ANTS-III, LNCS 1423 (1998),
  §3 (display, section number and the `0`/`∞` orientation UNVERIFIED): `X₆` over the `t`-line is
  `s² = −t, r² = 3(t − 1)` (`X6Glue.ElkiesCharts`), with `t` a coordinate on `X₆/W` and `t = 0, 1, ∞` at the CM
  points of discriminants `−24, −4, −3`. -/
  elkiesEquationsX6Ab : QMSplit.Moduli.ElkiesEquationsX6Ab
  /-- x6-glue, **consequence** (on abelian schemes): Shimura reciprocity at CM points of the canonical model
  (Shimura, Ann. of Math. 85 (1967) Main Thm I; Deligne 1971 §3; locators UNVERIFIED) in ray-class form: the
  residue field of a CM point by `ℚ(i)`, `ℚ(ζ₃)`, `ℚ(√−6)` embeds into the ray class field of conductor `3`. -/
  rayClassCMAb : _root_.ShimuraGlue.Ray.RayClassCMAb
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O` and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- reduct-b, printed form, restricted: SGA 7 I Exp. IX Prop. 3.3, first assertion (number UNVERIFIED), over a
  strictly henselian DVR of a field of characteristic `0` with perfect, hence algebraically closed, residue field
  (a specialization of every reading of the print). With `strictHenselizationPair` replaces `semistablePersistsDVR`
  at its two uses, SS1 and SS3, which are over number fields. -/
  semistablePersistsSHcp : _root_.ReductB.SemistablePersistsSHcp
  /-- reduct-glue, composite (GLUE): strict henselization along a finite extension of DVRs (EGA IV₄ 18.8.10 and
  18.6.8, Stacks 05WR) with Néron models commuting with it (BLR §1.2 Prop. 2); numbers UNVERIFIED. -/
  strictHenselizationPair : _root_.ReductGlue.StrictHenselizationPair

/-! ## From the new bundle to leaf-fold9's and leaf-fold10's

The terms are those of `researchLeaves12_of_open13`, `addedLeaves11_of_open12` (`TailZ22`),
`researchLeaves11_of_open12` (`TailZ19`), `addedLeaves10_of_open11` (`TailZ18`), `researchLeaves10_of_open11`,
`addedLeaves9_of_open10` (`TailZ17`) and `researchLeaves9_of_open10` (`TailZ15`), composed; only the three reduct
fields change. -/

/-- **The two `X₆` rows from the new bundles** (the term of `x6Rows_of_open13`). pi0-fold: the weak row
`R1R2fpRepW` from `x6Rows_of_leavesW`, whose base witness is González–Rotger's (`GonzalezRotgerX6`); the added leaves
`deligneComponentsX6PrintedAb` and `geomConnOfAlgClosure` are no longer read. -/
theorem x6Rows_of_open14 (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12) :
    LeafAdopt.R1R2fpRepW ∧ X6Kummer.X6ConicModel :=
  have hR := _root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw r.mumfordGroupLaw
  QMSplit.Moduli.x6Rows_of_leavesW
    { t5 := _root_.AvSplit.torsionStructure_of_mumford t.mumfordTorsionAlgClosed
      babaGranathR := (_root_.LeafQM.AV.R1UnivRigid.babaGranathRational_iff_ab_gl hR).mpr r.babaGranathRationalAb
      rayClass := (_root_.LeafQM.AV.R1UnivRigid.rayClassCM_iff_ab_gl hR).mpr r.rayClassCMAb
      gonzalezRotger := (_root_.LeafQM.AV.R1UnivRigid.gonzalezRotgerX6_iff_ab_gl hR).mpr r.gonzalezRotgerX6Ab
      elkiesEq := (_root_.LeafQM.AV.R1UnivRigid.elkiesEquationsX6_iff_ab_gl hR).mpr r.elkiesEquationsX6Ab }

/-- **SGA 7 IX 4.7 over a DVR** (the old field `raynaudSemistable`) from the strictly henselian printed leaf, the
pair and the textbook field `mulEtaleAbelianScheme` (reduct-b, Route B). -/
theorem raynaudSemistable_of14 (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) :
    _root_.ReductSplit.RaynaudSemistable :=
  _root_.ReductB.raynaudSemistable_of_SH_pair r.raynaudSemistableSH r.strictHenselizationPair
    t.mulEtaleAbelianScheme

/-- **SGA 7 IX 3.6 over a DVR** (the old field `semistableReductionDVR`) by reduct-b's K1 from 4.7, Mumford's torsion
count and `[m]` étale (textbook fields). -/
theorem semistableReductionDVR_of14 (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) :
    _root_.ReductSplit.SemistableReductionDVR :=
  _root_.ReductB.semistableReductionDVR_of_raynaud (raynaudSemistable_of14 r t) t.mumfordTorsionAlgClosed
    t.mulEtaleAbelianScheme

/-- leaf-fold10's added-leaf bundle from leaf-fold14's (the composite of `addedLeaves11_of_open12`,
`addedLeaves10_of_open11` and `addedLeaves9_of_open10`). -/
theorem addedLeaves9_of_open14 (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12) :
    OpenAddedLeaves9 where
  qmCentralizerCMC := l.qmCentralizerCMC
  tateTwistInvariants := l.tateTwistInvariants
  axSenTate := l.axSenTate
  t09SymmIsogenyExists := l.t09SymmIsogenyExists
  milneIsogenyQuasiInverse := l.milneIsogenyQuasiInverse
  x6ConicModel := (x6Rows_of_open14 r t l).2
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  valenceFormulaCocompactEq := l.valenceFormulaCocompactEq
  shimizuCovolumeO1 := l.shimizuCovolumeO1
  igusaCMValue24 := _root_.CM24.igusaCMValue24_field

/-- leaf-fold9's research bundle from leaf-fold14's (the composite of `researchLeaves12_of_open13`,
`researchLeaves11_of_open12`, `researchLeaves10_of_open11` and `researchLeaves9_of_open10`, with the three reduct
fields replaced by reduct-b's theorems). r6-nf: r6 (at number fields) and SS1, SS3 are arguments, supplied in
`sixContactMin_of_open20` (TailZ26) by `raynaudCriterionNF_of14` and `ss1_ss3_of14NF` from neron-dvr's
number-field Néron theorem (N1 alone), which replaced BLR 1.4/3 over every DVR. -/
theorem researchLeaves9_of_open14 (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12)
    (h6 : PkgI2.RaynaudCriterionNF.{0})
    (hSS : _root_.ZInQ.HeightSplit.SemistableReductionThm ∧ _root_.ZInQ.HeightSplit.SemistablePersists)
    (hNBC : _root_.ZInQ.HeightSplit.SemistableNeronBaseChange) :
    OpenResearchLeaves9 where
  r1r2 := (x6Rows_of_open14 r t l).1
  shimuraFamily := (_root_.LeafQM.AV.R1UnivRigid.shimuraFamily_iff_ab_gl
      (_root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw r.mumfordGroupLaw)).mpr
    r.shimuraFamilyAb
  igusaPsi4 := r.igusaPsi4
  igusaChi10 := r.igusaChi10
  r6 := h6
  r7a := r.r7a
  r9a := r.r9a
  r9b := r.r9b
  hodgeTateDecompAbVar := r.hodgeTateDecompAbVar
  deRhamH1AbVarT := r.deRhamH1AbVarT
  r11r12 := r.r11r12
  eigenformHTNew := r.eigenformHTNew
  dsThm965 := r.dsThm965
  dsThm966 := r.dsThm966
  r16 := r.r16
  r17 := r.r17
  semistableReductionThm := hSS.1
  semistableNeronBaseChange := hNBC
  semistablePersists := hSS.2
  bostLowerBound := r.bostLowerBound
  javanpeykarBound := r.javanpeykarBound
  pazukiCor13Upper := r.pazukiCor13Upper
  gaudronRemondThm14 := r.gaudronRemondThm14
  gonzalezRotgerCountX6 :=
    (_root_.LeafQM.AV.R1UnivRigid.gonzalezRotgerCountX6_iff_ab_gl
      (_root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw r.mumfordGroupLaw)).mpr
      r.gonzalezRotgerCountX6Ab

/-- **G0 with only the open leaves and the open glue** (leaf-fold14, reduct fold; no `sorry`, standard axioms).
`ZInQ.SixContactMin` from `OpenResearchLeaves14` (35), `OpenTextbookLeaves10` (15), `OpenAddedLeaves12` (14) and
`OpenGlue7` (1). -/
theorem sixContactMin_of_open17 (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12)
    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) (h6 : PkgI2.RaynaudCriterionNF.{0})
    (hSS : _root_.ZInQ.HeightSplit.SemistableReductionThm ∧ _root_.ZInQ.HeightSplit.SemistablePersists)
    (hY3 : TSHecke.Y3Connected)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM)
    (hNBC : _root_.ZInQ.HeightSplit.SemistableNeronBaseChange) : ZInQ.SixContactMin :=
  sixContactMin_of_open11 (researchLeaves9_of_open14 r t l h6 hSS hNBC) t (addedLeaves9_of_open14 r t l) g
    (_root_.ReductSplit.faltingsLemma5BCLower_final _root_.GapHeight.faltingsLemma5Lower) hYu hY3 hθ

end HSyn

end HDec
