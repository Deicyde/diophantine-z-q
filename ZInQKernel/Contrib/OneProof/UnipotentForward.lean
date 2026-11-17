import ZInQKernel.OneProof.H.TailZ7
import ZInQKernel.OneProof.H.TailZ14
import ZInQKernel.Contrib.OneProof.StrictHenselizationPair

/-!
# `ReductSplit.SemistableUnipotent` from the forward half of SGA 7 IX 3.5 (task gt-unip)

The hypothesis `semistableUnipotent : ReductSplit.SemistableUnipotent` (`ZInQKernel/OneProof/H/TailZ7.lean`;
GLUE, flagged pending reading on the base) is SGA 7 I, Exp. IX, Prop. 3.5, direction "semistable ⇒ `(σ - 1)² = 0`
on `T_ℓ`", read over every discrete valuation ring and an algebraic closure. Its live consumer is the kernel row
r6 (`ReductGlue.raynaudCriterion_leaves`, `TailZ14`; called in `TailZ15` and `TailZ23`). That proof
(`ReductSplit.raynaudCriterion_of_leaves`, `TailZ7`) uses only the forward direction, only at `σ = τ`, only at
`Ω = AlgebraicClosure K`, and only for `σ` in the inertia group. The field is already exactly that clause, so no
consumer needs rerouting: the field keeps its statement and is proved here.

This file proves the field (statement unchanged) from the printed-base form of the forward half of 3.5 and leaves
the chain already has:

* `UnipotentForward.semistableUnipotent_of_forwardGeom`
  `(hP : SGA7_IX_3_5_ForwardGeom) (hE : AvSplit.T4.MulEtaleAbelianScheme)`
  `(hN : GapSHPair.NeronBaseChangeStrictHenselization) : ReductSplit.SemistableUnipotent`.
  There is no glue. `hE` and `hN` are fields of the current bundles. The new leaf is SGA 7 IX 3.5, forward
  direction, one `σ` at a time, as printed over a strictly henselian trait, with `K^s` and `T_ℓ = lim A(K^s)[ℓⁿ]`.
  Semistability is read on the geometric special fibre. Reading risk (as for the chain's `raynaudSemistableSH`):
  if SGA 7 IX reads semistability over `k(s)` itself, this form exceeds the print by the descent statement
  `SemiAbelianDescendsSepClosed` below, and only for imperfect residue fields.
* `UnipotentForward.semistableUnipotent_of_forward`
  `(hP : SGA7_IX_3_5_Forward) (hD : SemiAbelianDescendsSepClosed) (hE) (hN) : ReductSplit.SemistableUnipotent`.
  This is the reading-robust alternative. The leaf assumes semistability both over `k(s)` and geometrically, so
  it is a consequence of the print under either reading. The price is the GLUE `SemiAbelianDescendsSepClosed`,
  which is proved here for perfect residue fields (`semiAbelianDescends_of_perfect`).

The other base axis, `ReductGlue.StrictHenselizationInside` (reduct-glue's leaf candidate, not in the chain), is
proved here from the chain's leaf `GapSHPair.NeronBaseChangeStrictHenselization` and gt-shpair's inertia field
(`strictHenselizationInside_of_neron`). The `K^s` versus `K̄` axis is proved from the bundle leaf
`MulEtaleAbelianScheme`.

The proofs of §2 and §3 are task unipotent-b's (`scratch/unipotent-b/UnipotentB.lean`, branch
`wip/unipotent-b`, which is not in the chain), copied here. No `sorry`, no `axiom`.
docs/research/gt-unip.md is the report.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
open ReductSplit ReductGlue ZInQ.HeightSplit

set_option linter.style.haveILetI false

namespace UnipotentForward

/-! ## §0. The base axis: `StrictHenselizationInside` from the chain's Néron leaf -/

/-- **`ReductGlue.StrictHenselizationInside`, PROVED** from the chain's leaf
`GapSHPair.NeronBaseChangeStrictHenselization` (BLR §1.2 Prop. 2). `E` is gt-shpair's inertia field of `w`, and
`w ∩ E` is an unramified, strictly henselian extension of `O` with separable residue extension
(`GapSHPair.isSHSep_inertia`, proved). Néron models base change to it by the leaf, and the inertia group of `w`
fixes it pointwise (`GapSHPair.inertia_fixes`). -/
theorem strictHenselizationInside_of_neron (hN : GapSHPair.NeronBaseChangeStrictHenselization) :
    ReductGlue.StrictHenselizationInside := by
  intro K _ O _ Ω _ _ _ w hw
  exact ⟨GapSHPair.inertiaField (K := K) w, GapSHPair.hE_eq w hw,
    GapSHPair.isSHNeronExt_of hN (GapSHPair.isSHSep_inertia w hw),
    fun σ hσ x hx => GapSHPair.inertia_fixes w hσ hx⟩

/-! ## §1. Semistability over the residue field `k(s)` (unipotent-b's definitions and proofs) -/

section ResFibre

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {O : ValuationSubring K}

/-- `Spec k(s) → Spec O`. -/
abbrev sRes (O : ValuationSubring K) :
    Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ Spec (CommRingCat.of O) :=
  Spec.map (CommRingCat.ofHom (algebraMap O (IsLocalRing.ResidueField O)))

/-- The special fibre `𝒩 ×_O k(s)` over the residue field itself (not its algebraic closure). -/
def specialFibre (𝒩 : GroupModelO A O) : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField O))) :=
  (Over.pullback (sRes O)).obj 𝒩.G

instance (𝒩 : GroupModelO A O) : GrpObj (specialFibre 𝒩) := Functor.grpObjObj

/-- **Semistable special fibre over `k(s)`** (SGA 7 IX Déf. 3.4 read over the residue field
`k(s)`, as printed; locators UNVERIFIED): the identity component of `𝒩 ×_O k(s)` is an extension of
an abelian variety by a split torus (`HasSemiAbelianIdentityComponent`). Over a separably closed
`k(s)` every torus is split. -/
def IsSemistableRes (𝒩 : GroupModelO A O) : Prop :=
  HasSemiAbelianIdentityComponent (specialFibre 𝒩)

/-- `A` has semistable reduction at `O` in the printed sense: a Néron model whose special fibre over
`k(s)` is semistable. -/
def HasSemistableReductionRes (A : PkgI3.AbVar K) (O : ValuationSubring K) : Prop :=
  ∃ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel ∧ IsSemistableRes 𝒩

/-- For an algebraically closed residue field, `k(s) → κ̄` is an isomorphism. -/
def resBarEquiv (O : ValuationSubring K) [IsAlgClosed (IsLocalRing.ResidueField O)] :
    IsLocalRing.ResidueField O ≃+* ResBarO O :=
  RingEquiv.ofBijective (algebraMap (IsLocalRing.ResidueField O) (ResBarO O))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

theorem spec_resBarEquiv_comp (O : ValuationSubring K) [IsAlgClosed (IsLocalRing.ResidueField O)] :
    Spec.map (CommRingCat.ofHom ((resBarEquiv O : _ ≃+* _) : _ →+* _)) ≫ sRes O =
      Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

/-- **For an algebraically closed residue field, semistability over `k(s)` and over `κ̄` agree**
(fibre identification `κ̄ ≅ k(s)` + `semiAbelianFieldIsoInvariant`). -/
theorem isSemistableRes_iff (O : ValuationSubring K) [IsAlgClosed (IsLocalRing.ResidueField O)]
    (𝒩 : GroupModelO A O) : IsSemistableRes 𝒩 ↔ 𝒩.IsSemistable := by
  unfold IsSemistableRes GroupModelO.IsSemistable
  rw [semiAbelianFieldIsoInvariant _ _ (resBarEquiv O) (specialFibre 𝒩)]
  let E := pbCompIso _ _ _ (spec_resBarEquiv_comp O) (Grp.mk 𝒩.G)
  exact ⟨fun h => @hasSemiAbelian_of_iso _ _ _ (geomSpecialFibre 𝒩) Functor.grpObjObj _
      (isoX E) (inferInstanceAs (IsMonHom E.hom.hom.hom)) h,
    fun h => @hasSemiAbelian_of_iso _ _ (geomSpecialFibre 𝒩) _ _ Functor.grpObjObj
      (isoX E.symm) (inferInstanceAs (IsMonHom E.inv.hom.hom)) h⟩

theorem hasSemistableReductionRes_iff (O : ValuationSubring K)
    [IsAlgClosed (IsLocalRing.ResidueField O)] (A : PkgI3.AbVar K) :
    HasSemistableReductionRes A O ↔ HasSemistableReduction A O :=
  ⟨fun ⟨𝒩, h1, h2⟩ => ⟨𝒩, h1, (isSemistableRes_iff O 𝒩).mp h2⟩,
    fun ⟨𝒩, h1, h2⟩ => ⟨𝒩, h1, (isSemistableRes_iff O 𝒩).mpr h2⟩⟩

end ResFibre

/-! ## §2a. Lemmas for the `K^s` axis (unipotent-b's proofs) -/

/-- `(σ - 1)² = 0` as an endomorphism gives the field's pointwise form. -/
theorem sq_form {ℓ : ℕ} [Fact ℓ.Prime] {M : Type} [AddCommGroup M] [Module ℤ_[ℓ] M] (f : M →ₗ[ℤ_[ℓ]] M)
    (h : (f - 1) * (f - 1) = 0) (t : M) : f (f t) - 2 • f t + t = 0 := by
  have := LinearMap.congr_fun h t
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub,
    LinearMap.zero_apply] at this
  rw [two_nsmul]
  rw [← this]
  abel

/-- **A Tate-module surjectivity criterion**: an injective `φ : M →+ N` onto the `ℓ`-power torsion
of `N` induces a surjection `T_ℓ M → T_ℓ N`. -/
theorem tateMap_surjective {ℓ : ℕ} [Fact ℓ.Prime] {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (φ : M →+ N) (hinj : Function.Injective φ)
    (hsurj : ∀ (n : ℕ) (y : N), (ℓ ^ n) • y = 0 → ∃ x : M, φ x = y) :
    Function.Surjective (PkgI3.Tate.map (ℓ := ℓ) φ) := by
  intro t
  choose s hs using fun n => hsurj n (t.1 n) (PkgI3.Tate.pow_smul_eq_zero t.2 n)
  refine ⟨⟨s, ?_, fun n => ?_⟩, Subtype.ext (funext fun n => hs n)⟩
  · apply hinj
    rw [hs, map_zero]
    exact t.2.1
  · apply hinj
    rw [map_nsmul, hs, hs]
    exact t.2.2 n

section SepClosure

open ZInQ.Contrib.AbVarBC

variable {K : Type} [Field K]

/-- Elements in the image of an étale `K`-algebra in any field `Ω` are separable over `K`
(`ReductGlue.isSeparable_of_etale` with `Ω` for `K̄`, same proof). -/
theorem isSeparable_of_etale' {Ω : Type} [Field Ω] [Algebra K Ω] {R : Type} [CommRing R]
    [Algebra K R] [Algebra.Etale K R] (f : R →ₐ[K] Ω) (r : R) : IsSeparable K (f r) := by
  haveI : Module.Finite K R := Algebra.FormallyUnramified.finite_of_free K R
  haveI : Algebra.IsIntegral K f.range := by
    refine ⟨fun ⟨y, hy⟩ => ?_⟩
    obtain ⟨s, rfl⟩ := hy
    have : IsIntegral K (f.rangeRestrict s) := (Algebra.IsIntegral.isIntegral (R := K) s).map _
    exact this
  let E : IntermediateField K Ω :=
    Subalgebra.toIntermediateField' f.range (isField_of_isIntegral_of_isField' (Field.toIsField K))
  let f' : R →ₐ[K] E := f.codRestrict E.toSubalgebra (fun r => ⟨r, rfl⟩)
  have hsurj : Function.Surjective f' := by
    rintro ⟨y, hy⟩
    obtain ⟨r, hr⟩ : y ∈ f.range := hy
    exact ⟨r, Subtype.ext hr⟩
  have : Algebra.FormallyUnramified K E := Algebra.FormallyUnramified.of_surjective f' hsurj
  have : Algebra.FiniteType K E := Algebra.FiniteType.of_surjective f' hsurj
  have : Algebra.IsSeparable K E := Algebra.FormallyUnramified.isSeparable K E
  have h := Algebra.IsSeparable.isSeparable K (f' r)
  have h2 : IsSeparable K (E.val (f' r)) := IsSeparable.map E.val Subtype.val_injective h
  exact h2

/-- **Points of an étale `K`-scheme with values in a field `Ω` come from the separable closure
`K^s ⊆ Ω`** (`ReductGlue.exists_lift_of_etale` with `K^s` for the algebraically closed field; the
coordinates are separable over `K`). -/
theorem exists_lift_of_etale_sep {Ω₂ : Type} [Field Ω₂] [Algebra K Ω₂]
    (X : Over (Spec (CommRingCat.of K))) [Etale X.hom]
    (q : Spec (CommRingCat.of Ω₂) ⟶ X.left)
    (hq : q ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K Ω₂))) :
    ∃ p : Spec (CommRingCat.of (separableClosure K Ω₂)) ⟶ X.left,
      Spec.map (CommRingCat.ofHom (algebraMap (separableClosure K Ω₂) Ω₂)) ≫ p = q ∧
        p ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K (separableClosure K Ω₂))) := by
  classical
  let Ω := separableClosure K Ω₂
  let κ : Ω →ₐ[K] Ω₂ := IsScalarTower.toAlgHom K Ω Ω₂
  let pt : X.left := q (IsLocalRing.closedPoint Ω₂)
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ pt) isOpen_univ
  change X.left.Opens at U
  change IsAffineOpen U at hU
  have hrange : Set.range q ⊆ Set.range U.ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : s = IsLocalRing.closedPoint Ω₂ :=
      Subsingleton.elim (α := PrimeSpectrum Ω₂) _ _
    rw [this]
    exact hpU
  let q' := IsOpenImmersion.lift U.ι q hrange
  have hq' : q' ≫ U.ι = q := IsOpenImmersion.lift_fac _ _ _
  let e := hU.isoSpec
  let φ : Γ(X.left, U) ⟶ CommRingCat.of Ω₂ := Spec.preimage (q' ≫ e.hom)
  let θ : CommRingCat.of K ⟶ Γ(X.left, U) := Spec.preimage (e.inv ≫ U.ι ≫ X.hom)
  have hφ : Spec.map φ = q' ≫ e.hom := Spec.map_preimage _
  have hθ : Spec.map θ = e.inv ≫ U.ι ≫ X.hom := Spec.map_preimage _
  have hql : q = Spec.map φ ≫ e.inv ≫ U.ι := by
    rw [hφ, Category.assoc, e.hom_inv_id_assoc, hq']
  have hcomp : θ ≫ φ = CommRingCat.ofHom (algebraMap K Ω₂) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hθ, Category.assoc, e.hom_inv_id_assoc, ← Category.assoc q', hq', hq]
  have hθet : RingHom.Etale θ.hom := by
    have : Etale (Spec.map θ) := by rw [hθ]; infer_instance
    exact HasRingHomProperty.Spec_iff.mp this
  letI : Algebra K Γ(X.left, U) := θ.hom.toAlgebra
  have : Algebra.Etale K Γ(X.left, U) := hθet
  let f : Γ(X.left, U) →ₐ[K] Ω₂ :=
    { φ.hom with
      commutes' := fun a => congrArg (fun g => CommRingCat.Hom.hom g a) hcomp }
  have : Module.Finite K Γ(X.left, U) := Algebra.FormallyUnramified.finite_of_free K _
  have hsep : ∀ r, IsSeparable K (φ.hom r) := fun r => isSeparable_of_etale' f r
  let ψ0 : Γ(X.left, U) → Ω := fun r => ⟨φ.hom r, mem_separableClosure_iff.mpr (hsep r)⟩
  have hψ0 : ∀ r, (κ : Ω →+* Ω₂) (ψ0 r) = φ.hom r := fun r => rfl
  have hκinj : Function.Injective (κ : Ω →+* Ω₂) := (κ : Ω →+* Ω₂).injective
  let ψ : Γ(X.left, U) →+* Ω :=
    { toFun := ψ0
      map_one' := hκinj (by rw [hψ0, map_one, map_one])
      map_mul' := fun a b => hκinj (by rw [hψ0, map_mul, map_mul, hψ0, hψ0])
      map_zero' := hκinj (by rw [hψ0, map_zero, map_zero])
      map_add' := fun a b => hκinj (by rw [hψ0, map_add, map_add, hψ0, hψ0]) }
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (κ : Ω →+* Ω₂) = φ := by
    ext r
    exact hψ0 r
  have hlift : Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)) ≫
      (Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι) = q := by
    rw [← Category.assoc, ← Spec.map_comp, hψ, hql]
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι, hlift, ?_⟩
  haveI := epi_spec_map_field (κ : Ω →+* Ω₂)
  apply (cancel_epi (Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)))).1
  rw [← Category.assoc, hlift, hq, ← Spec.map_comp, ← CommRingCat.ofHom_comp, κ.comp_algebraMap]

/-- **Torsion points of order prime to the characteristic come from `K^s`** (from `[m]` étale, the
bundle leaf `AvSplit.T4.MulEtaleAbelianScheme`; same proof as `ReductGlue.torsion_descends_etale`). -/
theorem torsion_from_sepClosure (hE : AvSplit.T4.MulEtaleAbelianScheme) (Ω : Type) [Field Ω]
    [Algebra K Ω] (A : PkgI3.AbVar K) (m : ℕ) (hm : (m : K) ≠ 0) (x : A.Pt Ω) (hx : x ^ m = 1) :
    ∃ y : A.Pt (separableClosure K Ω),
      extPt A (IsScalarTower.toAlgHom K (separableClosure K Ω) Ω) y = x := by
  haveI : PkgI2.IsAbelianScheme (Grp.mk A.X) := ⟨inferInstanceAs (IsProper A.X.hom),
    inferInstanceAs (Smooth A.X.hom), inferInstanceAs (GeometricallyConnected A.X.hom)⟩
  have het : Etale ((𝟙 A.X ^ m : A.X ⟶ A.X).left) :=
    hE K (Grp.mk A.X) m (isUnit_iff_ne_zero.mpr hm)
  let κ := IsScalarTower.toAlgHom K (separableClosure K Ω) Ω
  let M : A.X ⟶ A.X := 𝟙 A.X ^ m
  let P : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd M.left (η[A.X]).left)
  haveI : Etale P.hom := by
    change Etale (pullback.snd M.left (η[A.X]).left)
    infer_instance
  have hxm : x ≫ M = 1 := by rw [comp_pow_one]; exact hx
  have hw : x.left ≫ M.left =
      (PkgI3.AbVar.ptObj (K := K) Ω).hom ≫ (η[A.X]).left := by
    have h1 := congrArg Over.Hom.left hxm
    rw [Over.comp_left] at h1
    rw [h1]
    change (toUnit _ ≫ η[A.X]).left = _
    rw [Over.comp_left]
    congr 1
  let z : Spec (CommRingCat.of Ω) ⟶ P.left := pullback.lift x.left _ hw
  have hz : z ≫ P.hom = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) :=
    pullback.lift_snd _ _ _
  obtain ⟨p0, hp0, hp0g⟩ := exists_lift_of_etale_sep P z hz
  have hpr : pullback.fst M.left (η[A.X]).left ≫ A.X.hom = P.hom := by
    change _ = pullback.snd M.left (η[A.X]).left
    rw [← Over.w M, ← Category.assoc, pullback.condition, Category.assoc, Over.w η[A.X]]
    simp
  let p : A.Pt (separableClosure K Ω) :=
    Over.homMk (p0 ≫ pullback.fst M.left (η[A.X]).left) (by
      change (p0 ≫ pullback.fst M.left (η[A.X]).left) ≫ A.X.hom = _
      rw [Category.assoc, hpr, hp0g]
      rfl)
  refine ⟨p, ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (κ : separableClosure K Ω →+* Ω)) ≫
    p0 ≫ pullback.fst M.left (η[A.X]).left = x.left
  rw [← Category.assoc]
  erw [hp0]
  exact pullback.lift_fst _ _ _

end SepClosure

open scoped Pointwise in
/-- **Inertia restricts to `K^s`** (unipotent-b, proved): `AlgEquiv.restrictNormal` to the Galois extension
`K^s/K`; decomposition from `σ • w = w`; inertia through `w ∩ K^s → w`, which maps units to units. -/
theorem inertiaRestrict' (K : Type) [Field K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω) (hσ : IsInertia w σ) :
      ∃ σs : separableClosure K Ω ≃ₐ[K] separableClosure K Ω,
        IsInertia (w.comap (algebraMap (separableClosure K Ω) Ω)) σs ∧
        ∀ x : separableClosure K Ω, (σs x : Ω) = σ x := by
  set E := separableClosure K Ω
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  let σs : E ≃ₐ[K] E := σ.restrictNormal E
  have hres : ∀ x : E, (σs x : Ω) = σ x := fun x => AlgEquiv.restrictNormal_commutes σ E x
  refine ⟨σs, ?_, hres⟩
  obtain ⟨hd, hi⟩ := hσ
  have hs : σ • w = w := hd
  set w' := w.comap (algebraMap E Ω)
  have hd' : σs ∈ w'.decompositionSubgroup K := by
    show σs • w' = w'
    ext y
    simp only [← SetLike.mem_coe, ValuationSubring.coe_pointwise_smul, Set.mem_smul_set,
      AlgEquiv.smul_def]
    constructor
    · rintro ⟨z, hz, rfl⟩
      show ((σs z : E) : Ω) ∈ w
      rw [hres, ← hs]
      exact ⟨(z : Ω), hz, rfl⟩
    · intro hy
      refine ⟨σs.symm y, ?_, σs.apply_symm_apply y⟩
      have hy' : ((y : E) : Ω) ∈ σ • w := by rw [hs]; exact hy
      have hy'' : ((y : E) : Ω) ∈ σ • (w : Set Ω) := by
        rw [← ValuationSubring.coe_pointwise_smul]; exact hy'
      obtain ⟨u, hu, hu'⟩ := Set.mem_smul_set.mp hy''
      rw [AlgEquiv.smul_def] at hu'
      have : ((σs.symm y : E) : Ω) = u := by
        apply σ.injective
        rw [← hres, σs.apply_symm_apply]
        exact hu'.symm
      show ((σs.symm y : E) : Ω) ∈ w
      rw [this]; exact hu
  refine ⟨hd', ?_⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hi ⊢
  refine RingEquiv.ext fun r => ?_
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  -- the image of `a` in `w`
  let b : w := ⟨((a : E) : Ω), a.2⟩
  have h1 := RingEquiv.congr_fun hi (IsLocalRing.residue w b)
  change (⟨σ, hd⟩ : w.decompositionSubgroup K) • IsLocalRing.residue w b =
    IsLocalRing.residue w b at h1
  change (⟨σs, hd'⟩ : w'.decompositionSubgroup K) • IsLocalRing.residue w' a =
    IsLocalRing.residue w' a
  rw [← IsLocalRing.ResidueField.residue_smul] at h1 ⊢
  -- `c = σs a - a` maps into the maximal ideal of `w`
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at h1 ⊢
  let f : w' →+* w :=
    { toFun := fun x => ⟨((x : E) : Ω), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hfc : f ((⟨σs, hd'⟩ : w'.decompositionSubgroup K) • a - a) =
      (⟨σ, hd⟩ : w.decompositionSubgroup K) • b - b := by
    apply Subtype.ext
    change ((σs (a : E) : E) : Ω) - ((a : E) : Ω) = σ ((a : E) : Ω) - ((a : E) : Ω)
    rw [hres]
  intro hu
  exact h1 (by rw [← hfc]; exact hu.map f)

/-! ## §2. The `K^s` versus `K̄` axis (unipotent-b's proofs) -/

open ZInQ.Contrib.AbVarBC in
/-- **The restriction to `K^s`** (from the bundle leaf `MulEtaleAbelianScheme`). `Ω` is an algebraic closure of `K`,
`w` a valuation ring of `Ω`, and `ℓ` is invertible in `K`. Every `σ` in the inertia group of `w` restricts to some
`σs ∈ Aut(K^s/K)` in the inertia group of `w ∩ K^s`. Also, `A(K^s) → A(Ω)` induces a surjection
`T_ℓ(A)_{K^s} → T_ℓ(A)_Ω` that intertwines `σs` and `σ`. -/
theorem sepClosure_tate (hE : AvSplit.T4.MulEtaleAbelianScheme) (K : Type) [Field K] (Ω : Type) [Field Ω]
    [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω) (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : K) ≠ 0) (σ : Ω ≃ₐ[K] Ω) (hσ : IsInertia w σ) :
    ∃ σs : separableClosure K Ω ≃ₐ[K] separableClosure K Ω,
      IsInertia (w.comap (algebraMap (separableClosure K Ω) Ω)) σs ∧
      ∃ φ : TΩ A (separableClosure K Ω) ℓ →ₗ[ℤ_[ℓ]] TΩ A Ω ℓ, Function.Surjective φ ∧
        ∀ s, φ (galTΩ A ℓ σs s) = galTΩ A ℓ σ (φ s) := by
  obtain ⟨σs, hσs, hres⟩ := inertiaRestrict' K Ω w σ hσ
  let κ := IsScalarTower.toAlgHom K (separableClosure K Ω) Ω
  let φ0 : Additive (A.Pt (separableClosure K Ω)) →+ Additive (A.Pt Ω) :=
    MonoidHom.toAdditive (extPt A κ)
  refine ⟨σs, hσs, PkgI3.Tate.map φ0, ?_, fun s => ?_⟩
  · refine tateMap_surjective φ0 (extPt_injective A κ) fun n y hy => ?_
    have hℓn : ((ℓ ^ n : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hℓ
    obtain ⟨x, hx⟩ := torsion_from_sepClosure hE Ω A (ℓ ^ n) hℓn (Additive.toMul y) (by
      have : Additive.toMul ((ℓ ^ n) • y) = 1 := by rw [hy]; rfl
      rwa [toMul_nsmul] at this)
    exact ⟨Additive.ofMul x, by change Additive.ofMul (extPt A κ x) = y; rw [hx]; rfl⟩
  · apply Subtype.ext
    funext n
    change Additive.ofMul (extPt A κ (A.galAct σs (Additive.toMul (s.1 n)))) =
      Additive.ofMul (A.galAct σ (extPt A κ (Additive.toMul (s.1 n))))
    rw [extPt_galAct A κ σs σ (fun x => hres x)]

/-! ## §3. The printed-base leaves and the `k(s)` glue -/

/-- **LEAF `SGA7_IX_3_5_ForwardGeom`** (Grothendieck, SGA 7 I, Exp. IX, Prop. 3.5, the direction "semistable ⇒
unipotent of echelon `≤ 2`", one `σ` at a time; number and wording UNVERIFIED, from memory, since no network was
available). The setting is that of SGA 7 IX §3 over a strictly local trait:
* `O` is a strictly henselian discrete valuation ring (`IsStrictlyHenselianDVR`) with fraction field `K`;
* `Ω = K^s` is a separable closure of `K`, and `w` is the valuation ring of `Ω` over `O` (unique, since `O` is
  henselian);
* `ℓ` is a prime invertible in `O`, so different from the residue characteristic;
* `T_ℓ(A) = lim A(K^s)[ℓⁿ]` (`TΩ`).

If `A` has semistable reduction at `O`, every `σ` in the inertia group `I` of `w` satisfies `(σ - 1)² = 0` on
`T_ℓ(A)`. Here `I = Gal(K^s/K)`, and `IsInertia` is only an extra hypothesis. The print gives `(σ - 1)(τ - 1) = 0`
for `σ, τ ∈ I` (echelon `≤ 2`), and also the converse. This leaf keeps only `σ = τ` and only the forward
direction, which are the only parts r6 uses.

Semistable reduction is read on the geometric special fibre (`HasSemistableReduction`: a Néron model whose
special fibre over `κ̄` has an identity component that is an extension of an abelian variety by a torus). Reading
risk: if SGA 7 IX Déf. 3.4 reads this over `k(s)`, the leaf follows from the print only together with
`SemiAbelianDescendsSepClosed`. That matters only when `k(s)` is imperfect: for perfect `k(s)` the two readings
agree (`isSemistableRes_iff`). The reading-robust form is `SGA7_IX_3_5_Forward`. -/
def SGA7_IX_3_5_ForwardGeom : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → HasSemistableReduction A O →
      ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → (galTΩ A ℓ σ - 1) * (galTΩ A ℓ σ - 1) = 0

/-- **LEAF `SGA7_IX_3_5_Forward`** (the same theorem, reading-robust form). This is `SGA7_IX_3_5_ForwardGeom` with
the semistability hypothesis taken in **both** readings:
* over `k(s)` itself (`HasSemistableReductionRes`: a Néron model whose special fibre `𝒩 ×_O k(s)` has semi-abelian
  identity component);
* on the geometric special fibre (`HasSemistableReduction`).

So it is a consequence of the print whichever of the two SGA 7 IX uses: drop the hypothesis that the print does
not use. Source as for `SGA7_IX_3_5_ForwardGeom` (SGA 7 I, Exp. IX, Prop. 3.5; UNVERIFIED). -/
def SGA7_IX_3_5_Forward : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) →
      HasSemistableReductionRes A O → HasSemistableReduction A O →
      ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → (galTΩ A ℓ σ - 1) * (galTΩ A ℓ σ - 1) = 0

/-- The geometric form implies the reading-robust form. -/
theorem forward_of_forwardGeom (h : SGA7_IX_3_5_ForwardGeom) : SGA7_IX_3_5_Forward :=
  fun K _ O _ hO Ω _ _ _ w hw A ℓ _ hℓ _ hA σ hσ => h K O hO Ω w hw A ℓ hℓ hA σ hσ

/-- **GLUE `SemiAbelianDescendsSepClosed`** (the `k(s)` axis, for imperfect residue fields). `O` is a discrete
valuation ring whose residue field `k` is separably closed. Then a group model whose geometric special fibre (over
`κ̄`, purely inseparable over `k`) has semi-abelian identity component already has one over `k`.

Believed true (SPECULATIVE argument, locators UNVERIFIED):
* the maximal torus `T` of the smooth connected group `G⁰_k` exists over `k` (SGA 3 II, Exp. XIV, Thm 1.1), and
  `T_κ̄` is maximal;
* `G⁰_k / T` is smooth and connected, and becomes an abelian variety over `κ̄`, so it is proper (properness
  descends along field extensions, EGA IV₂ 2.7.1);
* tori over a separably closed field are split.

Proved for perfect `k` (`semiAbelianDescends_of_perfect`). Not in Mathlib 4.35. -/
def SemiAbelianDescendsSepClosed : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsSepClosed (IsLocalRing.ResidueField O) →
    ∀ (A : PkgI3.AbVar K) (𝒩 : GroupModelO A O), 𝒩.IsSemistable → IsSemistableRes 𝒩

/-- `SemiAbelianDescendsSepClosed` holds for perfect residue fields (proved). -/
theorem semiAbelianDescends_of_perfect (K : Type) [Field K] (O : ValuationSubring K)
    [PerfectField (IsLocalRing.ResidueField O)] (hk : IsSepClosed (IsLocalRing.ResidueField O))
    (A : PkgI3.AbVar K) (𝒩 : GroupModelO A O) (h : 𝒩.IsSemistable) : IsSemistableRes 𝒩 := by
  haveI := hk
  haveI : IsAlgClosed (IsLocalRing.ResidueField O) := IsSepClosed.isAlgClosed_of_perfectField _
  exact (isSemistableRes_iff O 𝒩).mpr h

/-- With the glue, the reading-robust form gives the geometric form. -/
theorem forwardGeom_of_forward (h : SGA7_IX_3_5_Forward) (hD : SemiAbelianDescendsSepClosed) :
    SGA7_IX_3_5_ForwardGeom := by
  intro K _ O _ hO Ω _ _ _ w hw A ℓ _ hℓ hA σ hσ
  refine h K O hO Ω w hw A ℓ hℓ ?_ hA σ hσ
  obtain ⟨𝒩, h1, h2⟩ := hA
  exact ⟨𝒩, h1, hD K O hO.2.2 A 𝒩 h2⟩

/-! ## §4. The field -/

/-- **The strictly henselian form `ReductGlue.SemistableUnipotentSH` (statement unchanged) from the geometric
leaf** and the bundle leaf `MulEtaleAbelianScheme`. The proof restricts `σ` to `K^s = separableClosure K Ω`
(`sepClosure_tate`), applies the leaf there, and pushes the result to `T_ℓ` over `Ω` through the surjective
equivariant map. -/
theorem semistableUnipotentSH_of_forwardGeom (hP : SGA7_IX_3_5_ForwardGeom)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : ReductGlue.SemistableUnipotentSH := by
  intro K _ O _ hO Ω _ _ _ w hw A hA ℓ _ hℓ σ hσ t
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hℓK : (ℓ : K) ≠ 0 := natCast_ne_zero_of_isUnit O hℓ
  obtain ⟨σs, hσs, φ, hφ, hcomm⟩ := sepClosure_tate hE K Ω w A ℓ hℓK σ hσ
  have hws : (w.comap (algebraMap (separableClosure K Ω) Ω)).comap
      (algebraMap K (separableClosure K Ω)) = O := by
    rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq, hw]
  have key := hP K O hO (separableClosure K Ω) _ hws A ℓ hℓ hA σs hσs
  obtain ⟨s, rfl⟩ := hφ t
  have h2 := congrArg φ (sq_form _ key s)
  simp only [map_add, map_sub, map_nsmul, map_zero, hcomm] at h2
  exact h2

/-- **The field `semistableUnipotent : ReductSplit.SemistableUnipotent`, statement unchanged, with no glue**, from
the geometric printed-base leaf `SGA7_IX_3_5_ForwardGeom` and two leaves already in the bundles:
`MulEtaleAbelianScheme` (BLR 7.3/2) and `NeronBaseChangeStrictHenselization` (BLR §1.2 Prop. 2). The base axis
uses reduct-glue's `unipotentFromSH_of` with `strictHenselizationInside_of_neron`. -/
theorem semistableUnipotent_of_forwardGeom (hP : SGA7_IX_3_5_ForwardGeom)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) (hN : GapSHPair.NeronBaseChangeStrictHenselization) :
    ReductSplit.SemistableUnipotent :=
  unipotentFromSH_of (strictHenselizationInside_of_neron hN) (semistableUnipotentSH_of_forwardGeom hP hE)

/-- **The field, statement unchanged, from the reading-robust leaf `SGA7_IX_3_5_Forward`**, the GLUE
`SemiAbelianDescendsSepClosed` (needed only for imperfect residue fields) and the same two bundle leaves. -/
theorem semistableUnipotent_of_forward (hP : SGA7_IX_3_5_Forward) (hD : SemiAbelianDescendsSepClosed)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) (hN : GapSHPair.NeronBaseChangeStrictHenselization) :
    ReductSplit.SemistableUnipotent :=
  semistableUnipotent_of_forwardGeom (forwardGeom_of_forward hP hD) hE hN

end UnipotentForward
