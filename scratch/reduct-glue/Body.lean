import ReductSplitBase

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ReductGlue
open ReductSplit

variable {K : Type} [Field K]

/-- A separable element of `K̄` fixed by `Aut(K̄/K)` lies in `K`. -/
theorem mem_range_of_isSeparable_of_fixed (a : AlgebraicClosure K) (ha : IsSeparable K a)
    (hfix : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, σ a = a) :
    a ∈ Set.range (algebraMap K (AlgebraicClosure K)) := by
  let L := separableClosure K (AlgebraicClosure K)
  have haL : a ∈ L := (mem_separableClosure_iff).mpr ha
  let a' : L := ⟨a, haL⟩
  have : a' ∈ Set.range (algebraMap K L) := by
    rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
    intro τ
    apply Subtype.ext
    have h1 := AlgEquiv.liftNormal_commutes τ (AlgebraicClosure K) a'
    have h2 : (algebraMap L (AlgebraicClosure K)) a' = a := rfl
    rw [h2, hfix] at h1
    exact h1.symm
  obtain ⟨c, hc⟩ := this
  exact ⟨c, by rw [IsScalarTower.algebraMap_apply K L (AlgebraicClosure K), hc]; rfl⟩

example (A : PkgI3.AbVar K) : GeometricallyConnected A.X.hom :=
  ⟨fun _ _ _ _ _ _ h => by
    have := GeometricallyIrreducible.geometrically_irreducibleSpace (f := A.X.hom) _ _ _ h
    infer_instance⟩


/-- Elements in the image of an étale `K`-algebra in `K̄` are separable over `K`. -/
theorem isSeparable_of_etale {R : Type} [CommRing R] [Algebra K R] [Algebra.Etale K R]
    (f : R →ₐ[K] AlgebraicClosure K) (r : R) : IsSeparable K (f r) := by
  let E : IntermediateField K (AlgebraicClosure K) :=
    Subalgebra.toIntermediateField' f.range (Subalgebra.isField_of_algebraic _)
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

theorem exists_rational_of_fixed_etale (X : Over (Spec (CommRingCat.of K)))
    [Etale X.hom] (q : PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K) ⟶ X)
    (hq : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, PkgI3.AbVar.galHom σ ≫ q = q) :
    ∃ y : PkgI3.AbVar.ptObj (K := K) K ⟶ X,
      ZInQ.Contrib.AbVarBC.extHom (Algebra.ofId K (AlgebraicClosure K)) ≫ y = q := by
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
  -- every `φ r` is fixed by `Aut(K̄/K)`
  have hfixφ : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      φ ≫ CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K) = φ := by
    intro σ
    have h1 := congrArg Over.Hom.left (hq σ)
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
  have hmem : ∀ r, φ.hom r ∈ Set.range (algebraMap K (AlgebraicClosure K)) := by
    intro r
    refine mem_range_of_isSeparable_of_fixed _ (isSeparable_of_etale f r) fun σ => ?_
    exact congrArg (fun f => CommRingCat.Hom.hom f r) (hfixφ σ)
  choose c hc using hmem
  have hinj := (algebraMap K (AlgebraicClosure K)).injective
  let ψ : Γ(X.left, U) →+* K :=
    { toFun := c
      map_one' := hinj (by rw [hc, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [hc, map_mul, map_mul, hc, hc])
      map_zero' := hinj (by rw [hc, map_zero, map_zero])
      map_add' := fun a b => hinj (by rw [hc, map_add, map_add, hc, hc]) }
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) = φ := by
    ext r
    exact hc r
  have hθψ : θ ≫ CommRingCat.ofHom ψ = CommRingCat.ofHom (algebraMap K K) := by
    ext a
    apply hinj
    have := congrArg (fun f => CommRingCat.Hom.hom f a) hcomp
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this ⊢
    rw [show algebraMap K (AlgebraicClosure K) (ψ (θ.hom a)) = φ.hom (θ.hom a) from hc _, this]
    rfl
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι) ?_, ?_⟩
  · show (Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K K))
    rw [Category.assoc, Category.assoc, ← hθ, ← Spec.map_comp, hθψ]
  · apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom ((Algebra.ofId K (AlgebraicClosure K) : K →ₐ[K] _) :
        K →+* AlgebraicClosure K)) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι = q0
    rw [hql, ← Category.assoc, ← Spec.map_comp]
    congr 2

theorem comp_pow_one (A : PkgI3.AbVar K) {Y : Over (Spec (CommRingCat.of K))} (x : Y ⟶ A.X) (n : ℕ) :
    x ≫ (𝟙 A.X ^ n : A.X ⟶ A.X) = x ^ n := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

instance geometricallyConnected_abVar (A : PkgI3.AbVar K) : GeometricallyConnected A.X.hom :=
  ⟨fun _ _ _ _ _ _ h => by
    have := GeometricallyIrreducible.geometrically_irreducibleSpace (f := A.X.hom) _ _ _ h
    infer_instance⟩

/-- **`FixedTorsionRational` (all fields, perfect or not) from the bundle leaf
`MulEtaleAbelianScheme`** (BLR 7.3/2: `[m]` is étale for `m` invertible). The `m`-torsion
`A[m] = [m]⁻¹(0)` is étale over `K`; a `K̄`-point of an étale `K`-scheme fixed by `Aut(K̄/K)` is
`K`-rational (`exists_rational_of_fixed_etale`). -/
theorem fixedTorsionRational_of_mulEtale (hE : AvSplit.T4.MulEtaleAbelianScheme) :
    FixedTorsionRational := by
  intro K _ A m hm hfix x hx
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
  have hfix' : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      PkgI3.AbVar.galHom σ ≫ x' = x' := by
    intro σ
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [x', Over.comp_left, Over.homMk_left, Category.assoc, pullback.lift_fst]
      exact congrArg Over.Hom.left (hfix σ x hx)
    · simp only [x', Over.comp_left, Over.homMk_left, Category.assoc, pullback.lift_snd]
      exact Over.w (PkgI3.AbVar.galHom σ)
  obtain ⟨y', hy'⟩ := exists_rational_of_fixed_etale P x' hfix'
  have hpr : pullback.fst M.left (η[A.X]).left ≫ A.X.hom = P.hom := by
    change _ = pullback.snd M.left (η[A.X]).left
    rw [← Over.w M, ← Category.assoc, pullback.condition, Category.assoc, Over.w η[A.X]]
    simp
  let pr : P ⟶ A.X := Over.homMk (pullback.fst M.left (η[A.X]).left) hpr
  refine ⟨y' ≫ pr, ?_⟩
  change ZInQ.Contrib.AbVarBC.extHom _ ≫ y' ≫ pr = x
  rw [← Category.assoc, hy']
  apply Over.OverMorphism.ext
  simp [x', pr]

/-- **GLUE `FixedTorsionRationalImperfect` (reduct-split), PROVED** from the bundle leaf. -/
theorem fixedTorsionRationalImperfect_of_mulEtale (hE : AvSplit.T4.MulEtaleAbelianScheme) :
    FixedTorsionRationalImperfect :=
  fun K _ _ A m hm hfix x hx => fixedTorsionRational_of_mulEtale hE K A m hm hfix x hx

/-- **r6 `PkgI2.RaynaudCriterion` from published-form leaves only** (over every field). -/
theorem raynaudCriterion_leaves (hR : RaynaudSemistable) (hU : SemistableUnipotent)
    (hN : NeronSchemeModelExistsDVR) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : PkgI2.RaynaudCriterion.{0} :=
  raynaudCriterion_final hR hU hN hM (fixedTorsionRational_of_mulEtale hE)

end ReductGlue
