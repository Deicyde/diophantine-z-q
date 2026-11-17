import ZInQKernel.OneProof.H.TailZ13
import ZInQKernel.Contrib.CloudW03NeronSurj.Main
import ZInQKernel.Contrib.FrobChain.Pieces

/-! # OneProof H, leaf-fold10: reduct-glue's proofs of reduct-split's glue

reduct-glue's `scratch/reduct-glue/Body.lean` (namespace `ReductGlue`) verbatim after its import lines, with only its
`#print axioms` lines dropped. Its first import, `ReductSplitBase` (reduct-split's `Reduction.lean`, compiled alone),
is replaced by the import of `TailZ13`, the current top of the chain, which contains the same file as `TailZ7`
(leaf-fold9); its other two imports are kept. reduct-glue's deliverable `ReductGlue.lean` is `Base.lean` followed by
this body. The proofs used in `TailZ15`: `ReductGlue.raynaudCriterion_leaves` (field `r6`) and
`ReductGlue.semistableLocalGlobal_leaf`, `semistableAlmostAll_of` (fields `semistableReductionThm`,
`semistablePersists`, with reduct-split's `semistableReductionThm_final`, `semistablePersists_final`). -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

open NumberField

open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)

/-!
# reduct-glue: reduct-split's four glue Props proved from published leaves; the leaves over their
printed bases

Task reduct-glue (2026-11-14). Everything above this point is a verbatim copy of
`scratch/reduct-split/Reduction.lean` (namespace `ReductSplit`; statements unchanged). Below
(namespace `ReductGlue`):

* `fixedTorsionRationalImperfect_of_mulEtale`: `FixedTorsionRationalImperfect` (indeed
  `FixedTorsionRational` for every field) from the bundle leaf `AvSplit.T4.MulEtaleAbelianScheme`.
* `semistableAlmostAll_of`: `SemistableAlmostAll` from the kernel's `AbVarSpreadsOut` and
  `ProperSmoothGenConnected` (and the vendored Néron mapping property of abelian schemes).
* `semistableLocalGlobal_leaf`: `SemistableLocalGlobal` from the new leaf `NeronLocalizesDVR`
  (BLR §1.2 Prop. 4); the transport glue `SemiAbelianFieldIsoInvariant` is proved.
* `semistableNeronBaseChangeLocalGlobal_of`: `SemistableNeronBaseChangeLocalGlobal` from the new
  leaves `IdentityComponentOL` (SGA 3 VI_B 3.10), `OpenImmersionOfLocal` (EGA IV₃ 8.10.5) and
  `NeronLocalizesDVR`.
* `rows_of_leaves_noGlue`: reduct-split's seven rows with no named glue Prop. This holds only
  relative to reduct-split's `ReductLeaves`, whose six SGA 7 and Serre–Tate fields count as (b)
  under the strict rule; on the printed route three named glue Props remain.
* Printed bases: `IsStrictlyHenselianDVR`, `IsCompleteDVR`, the six printed-base leaves, and the
  reductions `raynaudSemistable_of_SH'` (4.7), `persistsFromSH_of` (3.3, first assertion),
  `unipotentFromSH_of` (3.5) from strict-henselization leaves; three reductions remain named glue
  (`ReductionFromSH`, `IdentityComponentFromSH`, `SerreTateFromComplete`).

No `sorry`, no `axiom`; `#print axioms` lines at the end.
-/

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


section DVRNumberField

variable {L : Type} [Field L] [NumberField L]

/-- Every valuation ring of a number field contains `𝓞_L` (it is integrally closed). -/
theorem int_mem (O : ValuationSubring L) (x : 𝓞 L) : (x : L) ∈ O := by
  have h1 : IsIntegral ℤ (x : L) := x.2
  have h2 : IsIntegral O (x : L) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]; exact y.2

/-- `𝓞_L → O`. -/
def toOL (O : ValuationSubring L) : 𝓞 L →+* O :=
  (algebraMap (𝓞 L) L).codRestrict O.toSubring (fun x => int_mem O x)

@[simp] theorem toOL_coe (O : ValuationSubring L) (x : 𝓞 L) : ((toOL O x : O) : L) = (x : L) := rfl

/-- The center `𝔭_O = 𝓞_L ∩ 𝔪_O`. -/
def center (O : ValuationSubring L) : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal O).comap (toOL O)

theorem isUnit_toOL (O : ValuationSubring L) {s : 𝓞 L} (hs : s ∉ center O) : IsUnit (toOL O s) := by
  by_contra h
  exact hs ((IsLocalRing.mem_maximalIdeal _).mpr h)

theorem center_isMaximal (O : ValuationSubring L) [IsDiscreteValuationRing O] :
    (center O).IsMaximal := by
  have hp : (center O).IsPrime := Ideal.comap_isPrime _ _
  refine hp.isMaximal ?_
  intro hbot
  apply IsDiscreteValuationRing.not_isField O
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha => ?_⟩
  -- every element of `L` lies in `O`
  have hall : ∀ z : L, z ∈ O := by
    intro z
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) z
    have hy0 : y ∉ center O := by
      rw [hbot, Ideal.mem_bot]; exact nonZeroDivisors.ne_zero hy
    obtain ⟨u, hu⟩ := isUnit_toOL O hy0
    have h1 : ((u : O) : L) = algebraMap (𝓞 L) L y := by rw [hu]; rfl
    have h2 : (((u⁻¹ : Oˣ) : O) : L) * ((u : O) : L) = 1 := by
      exact congrArg (fun z : O => (z : L)) (Units.inv_mul u)
    rw [h1] at h2
    rw [div_eq_mul_inv, ← eq_inv_of_mul_eq_one_left h2]
    exact mul_mem (int_mem O x) (u⁻¹ : Oˣ).1.2
  have ha0 : (a : L) ≠ 0 := fun h => ha (Subtype.ext h)
  refine ⟨⟨(a : L)⁻¹, hall _⟩, Subtype.ext ?_⟩
  change (a : L) * (a : L)⁻¹ = 1
  exact mul_inv_cancel₀ ha0

theorem mem_of_mul_eq (O : ValuationSubring L) {x : L} {a s : 𝓞 L} (hs : s ∉ center O)
    (h : x * (s : L) = a) : x ∈ O := by
  obtain ⟨u, hu⟩ := isUnit_toOL O hs
  have h1 : ((u : O) : L) = (s : L) := by rw [hu]; rfl
  have h2 : (((u⁻¹ : Oˣ) : O) : L) * ((u : O) : L) = 1 :=
    congrArg (fun z : O => (z : L)) (Units.inv_mul u)
  have : x = (a : L) * (((u⁻¹ : Oˣ) : O) : L) := by
    rw [← h, h1.symm, _root_.mul_assoc, mul_comm ((u : O) : L), h2, _root_.mul_one]
  rw [this]
  exact mul_mem (int_mem O a) (u⁻¹ : Oˣ).1.2

theorem center_ne_bot (O : ValuationSubring L) [IsDiscreteValuationRing O] : center O ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField (center_isMaximal O) (RingOfIntegers.not_isField L)

/-- **A discrete valuation ring of a number field is the localization of `𝓞_L` at its center**:
`x ∈ O` iff `x = a/s` with `a, s ∈ 𝓞_L`, `s ∉ 𝔭_O`. Proof: `(𝓞_L)_𝔭 ⊆ O` is a valuation ring;
for `x = a/b ∈ O`, either `x` or `x⁻¹` is `r/s`, and `x⁻¹ = r/s` with `r ∈ 𝔭` would put
`1 = x·x⁻¹` in `𝔪_O`. -/
theorem mem_iff_exists (O : ValuationSubring L) [IsDiscreteValuationRing O] (x : L) :
    x ∈ O ↔ ∃ a s : 𝓞 L, s ∉ center O ∧ x * (s : L) = a := by
  constructor
  swap
  · rintro ⟨a, s, hs, h⟩; exact mem_of_mul_eq O hs h
  intro hx
  haveI := center_isMaximal O
  let 𝔭 := center O
  let B := Localization.AtPrime 𝔭
  haveI : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) (center_ne_bot O) B
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  have hb0 : (algebraMap (𝓞 L) L b) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).mpr (nonZeroDivisors.ne_zero hb)
  obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap (𝓞 L) B a) (algebraMap (𝓞 L) B b)
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl c
  have hinj := IsLocalization.injective B 𝔭.primeCompl_le_nonZeroDivisors
  have hspec := IsLocalization.mk'_spec B r s
  have hs : (s : 𝓞 L) ∉ center O := s.2
  rcases hc with h | h
  · have h' : a * r = b * s := by
      apply hinj
      rw [map_mul, map_mul, ← h, ← hspec]
      ring
    have hL : (algebraMap (𝓞 L) L a) * (algebraMap (𝓞 L) L r) =
        (algebraMap (𝓞 L) L b) * (algebraMap (𝓞 L) L s) := by
      rw [← map_mul, ← map_mul, h']
    by_cases hr : r ∈ 𝔭
    · exfalso
      apply hs
      have hX : (⟨_, hx⟩ : O) * toOL O r = toOL O s := by
        apply Subtype.ext
        change (algebraMap (𝓞 L) L a / algebraMap (𝓞 L) L b) * (algebraMap (𝓞 L) L r) =
          algebraMap (𝓞 L) L s
        rw [div_mul_eq_mul_div, hL, mul_div_cancel_left₀ _ hb0]
      change toOL O s ∈ IsLocalRing.maximalIdeal O
      rw [← hX]
      exact Ideal.mul_mem_left _ _ hr
    · refine ⟨s, r, hr, ?_⟩
      change (algebraMap (𝓞 L) L a / algebraMap (𝓞 L) L b) * (algebraMap (𝓞 L) L r) =
        algebraMap (𝓞 L) L s
      rw [div_mul_eq_mul_div, hL, mul_div_cancel_left₀ _ hb0]
  · have h' : b * r = a * s := by
      apply hinj
      rw [map_mul, map_mul, ← h, ← hspec]
      ring
    refine ⟨r, s, hs, ?_⟩
    change (algebraMap (𝓞 L) L a / algebraMap (𝓞 L) L b) * (algebraMap (𝓞 L) L s) =
      algebraMap (𝓞 L) L r
    rw [div_mul_eq_mul_div, ← map_mul, ← h', map_mul, mul_div_cancel_left₀ _ hb0]

/-- Two discrete valuation rings of `L` with the same center are equal. -/
theorem eq_of_center_eq {O₁ O₂ : ValuationSubring L} [IsDiscreteValuationRing O₁]
    [IsDiscreteValuationRing O₂] (h : center O₁ = center O₂) : O₁ = O₂ := by
  ext x
  rw [mem_iff_exists, mem_iff_exists, h]

instance (O : ValuationSubring L) : (center O).IsPrime := Ideal.comap_isPrime _ _

/-- `(𝓞_L)_𝔭 → O` for `𝔭` the center of `O`. -/
noncomputable def locToO (O : ValuationSubring L) : Localization.AtPrime (center O) →+* O :=
  IsLocalization.lift (M := (center O).primeCompl) (g := toOL O) (fun s => isUnit_toOL O s.2)

instance (O : ValuationSubring L) : IsLocalHom (locToO O) := by
  constructor
  intro y hy
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (center O).primeCompl y
  rw [IsLocalization.AtPrime.isUnit_mk'_iff]
  intro hr
  have h1 : locToO O (IsLocalization.mk' _ r s) * toOL O s = toOL O r := by
    rw [mul_comm]
    exact ((IsLocalization.lift_mk'_spec _ _ _ _).mp rfl).symm
  have h2 : toOL O r ∈ IsLocalRing.maximalIdeal O := hr
  rw [← h1] at h2
  exact (IsLocalRing.mem_maximalIdeal _).mp
    ((Ideal.IsPrime.mem_or_mem inferInstance h2).resolve_right s.2) hy

/-- **The residue fields of `𝓞_L` at `𝔭_O` and of `O` agree.** -/
noncomputable def resIso (O : ValuationSubring L) [IsDiscreteValuationRing O] :
    (center O).ResidueField ≃+* IsLocalRing.ResidueField O :=
  RingEquiv.ofBijective (IsLocalRing.ResidueField.map (locToO O)) ⟨RingHom.injective _, by
    intro z
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨a, s, hs, h⟩ := (mem_iff_exists O (y : L)).mp y.2
    refine ⟨IsLocalRing.residue _ (IsLocalization.mk' _ a (⟨s, show s ∈ (center O).primeCompl from hs⟩ : (center O).primeCompl)), ?_⟩
    rw [IsLocalRing.ResidueField.map_residue]
    congr 1
    unfold locToO
    rw [IsLocalization.lift_mk'_spec]
    apply Subtype.ext
    change (a : L) = (s : L) * (y : L)
    rw [← h, mul_comm]⟩

theorem resIso_algebraMap (O : ValuationSubring L) [IsDiscreteValuationRing O] (a : 𝓞 L) :
    resIso O (algebraMap (𝓞 L) (center O).ResidueField a) = IsLocalRing.residue O (toOL O a) := by
  rw [IsScalarTower.algebraMap_apply (𝓞 L) (Localization.AtPrime (center O))]
  change IsLocalRing.ResidueField.map (locToO O) (IsLocalRing.residue _ _) = _
  rw [IsLocalRing.ResidueField.map_residue]
  congr 1
  exact IsLocalization.lift_eq _ a

/-- The isomorphism `κ̄(𝔭_O) ≅ κ̄(O)` of the chosen algebraic closures, over `𝓞_L`. -/
noncomputable def barIso (O : ValuationSubring L) [IsDiscreteValuationRing O] :
    ZInQ.HeightSplit.ResBar (center O) ≃+* ResBarO O :=
  IsAlgClosure.equivOfEquiv _ _ (resIso O)

theorem barIso_comp (O : ValuationSubring L) [IsDiscreteValuationRing O] :
    ((barIso O : _ →+* _).comp (algebraMap (𝓞 L) (ZInQ.HeightSplit.ResBar (center O)))) =
      (algebraMap O (ResBarO O)).comp (toOL O) := by
  ext a
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply (𝓞 L) (center O).ResidueField]
  have := congrArg (fun f => f (algebraMap (𝓞 L) (center O).ResidueField a))
    (IsAlgClosure.equivOfEquiv_comp_algebraMap (ZInQ.HeightSplit.ResBar (center O)) (ResBarO O)
      (resIso O))
  simp only [RingHom.comp_apply] at this
  change barIso O _ = _ at this
  change barIso O _ = _
  rw [this]
  change algebraMap (IsLocalRing.ResidueField O) (ResBarO O) (resIso O _) = _
  rw [resIso_algebraMap, RingHom.comp_apply, IsScalarTower.algebraMap_apply O
    (IsLocalRing.ResidueField O) (ResBarO O)]
  rfl

open IsDedekindDomain in
/-- The valuation ring of the `𝔭`-adic valuation, for a maximal ideal `𝔭` of `𝓞_L`. -/
noncomputable def dvrAt (𝔭 : Ideal (𝓞 L)) [h𝔭 : 𝔭.IsMaximal] : ValuationSubring L :=
  ((⟨𝔭, h𝔭.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField L)⟩ :
    HeightOneSpectrum (𝓞 L)).valuation L).valuationSubring

open IsDedekindDomain in
instance (𝔭 : Ideal (𝓞 L)) [h𝔭 : 𝔭.IsMaximal] : IsDiscreteValuationRing (dvrAt 𝔭) := by
  set v : HeightOneSpectrum (𝓞 L) :=
    ⟨𝔭, h𝔭.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField L)⟩
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer L
  haveI : Nontrivial (v.valuation L).valueGroup := by
    have h0 : v.valuation L π ≠ 0 := by rw [hπ]; exact WithZero.coe_ne_zero
    refine ⟨⟨⟨Units.mk0 _ h0, MonoidWithZeroHom.mem_valueGroup _ ⟨π, rfl⟩⟩, 1, ?_⟩⟩
    intro h
    have := congrArg (fun u : (v.valuation L).valueGroup => ((u : (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ))) h
    simp only [Units.val_mk0, OneMemClass.coe_one, Units.val_one] at this
    rw [hπ] at this
    exact absurd this (by decide)
  exact Valuation.valuationSubring_isDiscreteValuationRing _

open IsDedekindDomain in
theorem center_dvrAt (𝔭 : Ideal (𝓞 L)) [h𝔭 : 𝔭.IsMaximal] : center (dvrAt 𝔭) = 𝔭 := by
  set v : HeightOneSpectrum (𝓞 L) :=
    ⟨𝔭, h𝔭.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField L)⟩
  ext a
  change toOL _ a ∈ IsLocalRing.maximalIdeal _ ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hlt := v.valuation_lt_one_iff_mem (K := L) a
  change _ ↔ a ∈ v.asIdeal
  rw [← hlt]
  constructor
  · intro hnu
    rcases (v.valuation_le_one (K := L) a).lt_or_eq with h | h
    · exact h
    · exfalso; apply hnu
      have hv : v.valuation L (algebraMap (𝓞 L) L a) ≠ 0 := by rw [h]; exact one_ne_zero
      have ha0 : (a : L) ≠ 0 := (Valuation.ne_zero_iff _).mp hv
      refine ⟨⟨toOL _ a, ⟨(a : L)⁻¹, ?_⟩, ?_, ?_⟩, rfl⟩
      · change v.valuation L (a : L)⁻¹ ≤ 1
        rw [map_inv₀]
        change (v.valuation L (algebraMap (𝓞 L) L a))⁻¹ ≤ 1
        rw [h, inv_one]
      · exact Subtype.ext (mul_inv_cancel₀ ha0)
      · exact Subtype.ext (inv_mul_cancel₀ ha0)
  · rintro hlt1 ⟨u, hu⟩
    have h1 : ((u : dvrAt 𝔭) : L) * (((u⁻¹ : (dvrAt 𝔭)ˣ) : dvrAt 𝔭) : L) = 1 :=
      congrArg (fun z : dvrAt 𝔭 => (z : L)) (Units.mul_inv u)
    have h2 : v.valuation L (((u⁻¹ : (dvrAt 𝔭)ˣ) : dvrAt 𝔭) : L) ≤ 1 := (u⁻¹ : (dvrAt 𝔭)ˣ).1.2
    rw [hu] at h1
    have h3 := congrArg (v.valuation L) h1
    rw [map_mul, map_one] at h3
    have : v.valuation L (a : L) * v.valuation L (((u⁻¹ : (dvrAt 𝔭)ˣ) : dvrAt 𝔭) : L) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h2) hlt1
    exact absurd h3 (ne_of_lt this)

end DVRNumberField


section AbSchemeNeron

variable {K : Type} [Field K]

/-- **An abelian scheme over a discrete valuation ring has the Néron mapping property** (BLR §1.2
Prop. 8), from the vendored FLT-project theorem in `Contrib/CloudW03NeronSurj` (Weil's extension
theorem; full mapping property for smooth test schemes). -/
theorem abelianScheme_neron (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (𝒜 : Grp (Over (Spec (.of O)))) [h𝒜 : PkgI2.IsAbelianScheme 𝒜]
    (Y : Over (Spec (CommRingCat.of O))) [hY : Smooth Y.hom] :
    Function.Bijective fun f : Y ⟶ 𝒜.X => (Over.pullback (jO O)).map f := by
  haveI : Smooth 𝒜.X.hom := PkgI2.IsAbelianScheme.smooth
  haveI : IsProper 𝒜.X.hom := PkgI2.IsAbelianScheme.proper
  haveI : GeometricallyConnected 𝒜.X.hom := PkgI2.IsAbelianScheme.geomConnected
  haveI : GrpObj (Over.mk 𝒜.X.hom) := by
    change GrpObj 𝒜.X
    infer_instance
  let h𝒜' : ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.AbelianSchemePropertyBundle O
      𝒜.X.hom :=
    { smooth := inferInstance
      proper := inferInstance
      connectedFibres := fun s => 𝒜.X.hom.isConnected_preimage_singleton s
      hasGroupLaw := ⟨ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.relativeGroupLawOfGrpObj
        O 𝒜.X.hom⟩ }
  have hN := ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle.solution
    O K h𝒜'
  have hb := hN.neronMapping Y.left Y.hom hY
  constructor
  · intro f g hfg
    have h1 : (ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.genericFibreRestrict O K 𝒜.X.hom
        Y.hom ⟨f.left, Over.w f⟩) =
        ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.genericFibreRestrict O K 𝒜.X.hom
        Y.hom ⟨g.left, Over.w g⟩ := by
      apply Subtype.ext
      exact congrArg Over.Hom.left hfg
    have := hb.1 h1
    exact Over.OverMorphism.ext (congrArg Subtype.val this)
  · intro uK
    let uK' : ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.SchemeHomOver
        (pullback.snd Y.hom (ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.specGenericFibreInclusion O K))
        (pullback.snd 𝒜.X.hom (ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.specGenericFibreInclusion O K)) :=
      ⟨uK.left, Over.w uK⟩
    obtain ⟨φ, hφ⟩ := hb.2 uK'
    refine ⟨Over.homMk φ.1 φ.2, ?_⟩
    ext1
    exact congrArg Subtype.val hφ

end AbSchemeNeron


section SemiAbelian

open ZInQ.HeightSplit

/-- `HasSemiAbelianIdentityComponent` is invariant under isomorphisms of group schemes. -/
theorem hasSemiAbelian_of_iso {k : Type} [Field k] {G G' : Over (Spec (CommRingCat.of k))}
    [GrpObj G] [GrpObj G'] (f : G ≅ G') [IsMonHom f.hom] (h : HasSemiAbelianIdentityComponent G) :
    HasSemiAbelianIdentityComponent G' := by
  obtain ⟨U, hU, inc, h1, h2, h3, rest⟩ := h
  exact ⟨U, hU, inc ≫ f.hom, by rw [Over.comp_left]; infer_instance, inferInstance, h3, rest⟩

/-- An abelian variety (over any field) has semi-abelian identity component: `U = G`, `π = 𝟙`,
torus of rank `0`. -/
theorem hasSemiAbelian_of_abVar {k : Type} [Field k] (B : PkgI3.AbVar k) :
    HasSemiAbelianIdentityComponent B.X := by
  haveI : GeometricallyConnected B.X.hom := geometricallyConnected_abVar B
  haveI : ConnectedSpace B.X.left := GeometricallyConnected.connectedSpace_of_subsingleton B.X.hom
  refine ⟨B.X, inferInstance, 𝟙 _, inferInstance, inferInstance, inferInstance, B, 𝟙 _,
    inferInstance, inferInstance, inferInstance, 0, fun R _ _ => 1, ?_, ?_, ?_⟩
  · intro R _ _ a b _
    exact Subsingleton.elim a b
  · intro R _ _ u
    rw [Category.comp_id, MonoidHom.range_one, Subgroup.mem_bot]
  · intro R S _ _ _ _ f t
    exact (MonObj.comp_one _).symm

end SemiAbelian

section GoodRed

variable {K : Type} [Field K]

/-- The group model over `O` given by an abelian scheme with generic fibre `≅ A`. -/
noncomputable def groupModelOfAbScheme (O : ValuationSubring K) (A : PkgI3.AbVar K)
    (𝒜 : Grp (Over (Spec (.of O)))) [h𝒜 : PkgI2.IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).mapGrp.obj 𝒜 ≅
      Grp.mk A.X) : GroupModelO A O :=
  haveI : Smooth 𝒜.X.hom := PkgI2.IsAbelianScheme.smooth
  haveI : IsProper 𝒜.X.hom := PkgI2.IsAbelianScheme.proper
  { G := 𝒜.X
    gen := (Grp.forget _).mapIso e
    gen_hom := inferInstanceAs (IsMonHom e.hom.hom.hom) }

/-- **Good reduction ⇒ semistable reduction**: an abelian scheme over a DVR is a Néron model
(`abelianScheme_neron`), and its geometric special fibre is an abelian variety (smooth, proper,
geometrically connected ⇒ geometrically integral, `FrobPieces.smoothGeomConnIntegral`). -/
theorem hasSemistableReduction_of_goodReduction (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : PkgI3.AbVar K) (h : PkgI2.HasGoodReduction (Grp.mk A.X) O) :
    HasSemistableReduction A O := by
  obtain ⟨𝒜, h𝒜, ⟨e⟩⟩ := h
  haveI := h𝒜
  haveI : Smooth 𝒜.X.hom := PkgI2.IsAbelianScheme.smooth
  haveI : IsProper 𝒜.X.hom := PkgI2.IsAbelianScheme.proper
  haveI : GeometricallyConnected 𝒜.X.hom := PkgI2.IsAbelianScheme.geomConnected
  refine ⟨groupModelOfAbScheme O A 𝒜 e, ?_, ?_⟩
  · intro Y _
    have hb := abelianScheme_neron O 𝒜 Y
    have : (fun f : Y ⟶ 𝒜.X => (Over.pullback (jO O)).map f ≫ ((Grp.forget _).mapIso e).hom) =
        (fun g => g ≫ ((Grp.forget _).mapIso e).hom) ∘
          (fun f : Y ⟶ 𝒜.X => (Over.pullback (jO O)).map f) := rfl
    change Function.Bijective (fun f : Y ⟶ 𝒜.X =>
      (Over.pullback (jO O)).map f ≫ ((Grp.forget _).mapIso e).hom)
    rw [this]
    exact Function.Bijective.comp
      ⟨fun a b hab => (cancel_mono _).mp hab, fun c => ⟨c ≫ ((Grp.forget _).mapIso e).inv, by
        simp only; rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩⟩ hb
  · let G := geomSpecialFibre (groupModelOfAbScheme O A 𝒜 e)
    haveI hs : Smooth G.hom := by
      change Smooth (pullback.snd 𝒜.X.hom _); infer_instance
    haveI hp : IsProper G.hom := by
      change IsProper (pullback.snd 𝒜.X.hom _); infer_instance
    haveI hc : GeometricallyConnected G.hom := by
      change GeometricallyConnected (pullback.snd 𝒜.X.hom _); infer_instance
    haveI : GeometricallyIntegral G.hom :=
      FrobPieces.smoothGeomConnIntegral _ G.left G.hom hs hc inferInstance
    let B : PkgI3.AbVar (ResBarO O) := ⟨G⟩
    exact hasSemiAbelian_of_abVar B

end GoodRed

section AlmostAll

variable {K : Type} [Field K] [NumberField K]

open IsDedekindDomain in
/-- Only finitely many discrete valuation rings of `K` have a given nonzero `f ∈ 𝓞_K` in their
center. -/
theorem finite_dvr_mem_center {f : 𝓞 K} (hf : f ≠ 0) :
    {O : ValuationSubring K | IsDiscreteValuationRing O ∧ f ∈ center O}.Finite := by
  classical
  have hT := Ideal.finite_factors (R := 𝓞 K) (I := Ideal.span {f})
    (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
  let F : ValuationSubring K → Ideal (𝓞 K) := center
  refine Set.Finite.of_finite_image (f := F) ?_ ?_
  · refine (hT.image HeightOneSpectrum.asIdeal).subset ?_
    rintro _ ⟨O, ⟨hO, hfO⟩, rfl⟩
    haveI := hO
    refine ⟨⟨center O, inferInstance, center_ne_bot O⟩, ?_, rfl⟩
    change center O ∣ Ideal.span {f}
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    exact hfO
  · rintro O₁ ⟨h₁, -⟩ O₂ ⟨h₂, -⟩ h
    haveI := h₁; haveI := h₂
    exact eq_of_center_eq h

set_option synthInstance.maxHeartbeats 400000 in
/-- **GLUE `SemistableAlmostAll` (reduct-split), PROVED** from neron-lg's N1-g1 `AbVarSpreadsOut`
(itself proved in the kernel from the EGA IV leaves, `abVarSpreadsOut_of_ega4`) and frob-pieces'
leaf candidate `ProperSmoothGenConnected` (Zariski's connectedness theorem): spread `A` out to an
abelian scheme over `𝓞_K[1/f]`; at a DVR `O` with `f ∉ 𝔭_O`, `𝓞_K[1/f] → K` factors through `O`,
so `A` has good reduction at `O` (`hasGoodReduction_of_base`), hence semistable reduction
(`hasSemistableReduction_of_goodReduction`); only finitely many `O` have `f ∈ 𝔭_O`. -/
theorem semistableAlmostAll_of (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected) : SemistableAlmostAll := by
  intro K _ _ A
  obtain ⟨f, hf0, hf⟩ := hsp K A
  have hfL : IsUnit (algebraMap (𝓞 K) K f) :=
    isUnit_iff_ne_zero.2 (by simpa using hf0)
  let R := Localization.Away f
  letI : Algebra R K := (IsLocalization.Away.lift f hfL).toAlgebra
  haveI : IsScalarTower (𝓞 K) R K := IsScalarTower.of_algebraMap_eq (fun x =>
    (IsLocalization.Away.lift_eq f hfL x).symm)
  obtain ⟨G, hG, hGs, hGp, gen, hgen⟩ := hf R
  have hgc : GeometricallyConnected G.hom := by
    refine hc K f R G hGs hGp ?_
    have h1 : GeometricallyConnected A.X.hom := geometricallyConnected_abVar A
    have h2 : ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj G).hom =
        gen.hom.left ≫ A.X.hom := (Over.w gen.hom).symm
    rw [h2]
    have hR : MorphismProperty.RespectsIso (@GeometricallyConnected : MorphismProperty Scheme.{0}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (MorphismProperty.cancel_left_of_respectsIso
      (@GeometricallyConnected : MorphismProperty Scheme.{0}) gen.hom.left A.X.hom).2 h1
  refine (finite_dvr_mem_center hf0).subset ?_
  rintro O ⟨hO, hbad⟩
  refine ⟨hO, ?_⟩
  by_contra hfO
  haveI := hO
  apply hbad
  have hfu : IsUnit (toOL O f) := isUnit_toOL O hfO
  let φ : R →+* O := IsLocalization.Away.lift f hfu
  have hφ : (algebraMap O K).comp φ = algebraMap R K := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, φ, IsLocalization.Away.lift_eq]
    exact (IsLocalization.Away.lift_eq f hfL x).symm
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj G) :=
    Functor.grpObjObj
  exact hasSemistableReduction_of_goodReduction O A
    (FrobPiecesNeron.hasGoodReduction_of_base _ (algebraMap R K) φ hφ _ (Grp.mk G) ⟨hGp, hGs, hgc⟩
      (Grp.mkIso' gen))

end AlmostAll


/-- The underlying isomorphism of an isomorphism of group objects. -/
def isoX {C : Type*} [Category C] [CartesianMonoidalCategory C] {G H : Grp C} (E : G ≅ H) :
    G.X ≅ H.X := (Grp.forget C).mapIso E

instance {C : Type*} [Category C] [CartesianMonoidalCategory C] {G H : Grp C} (E : G ≅ H) :
    IsMonHom (isoX E).hom := inferInstanceAs (IsMonHom E.hom.hom.hom)

section NeronUnique

variable {K : Type} [Field K]

/-- **Uniqueness of Néron models over a valuation ring**, as group schemes (from the mapping
property: the comparison maps are inverse, and postcomposition with them is a homomorphism on
`T`-points for every smooth `T`, in particular for `T = 𝟙_` and `T = 𝒩 ⊗ 𝒩`). -/
theorem neronO_unique {B : PkgI3.AbVar K} {O : ValuationSubring K} (𝒩₁ 𝒩₂ : GroupModelO B O)
    (h₁ : 𝒩₁.IsNeronModel) (h₂ : 𝒩₂.IsNeronModel) : ∃ e : 𝒩₁.G ≅ 𝒩₂.G, IsMonHom e.hom := by
  let F := Over.pullback (jO O)
  letI : GrpObj (F.obj 𝒩₁.G) := Functor.grpObjObj
  letI : GrpObj (F.obj 𝒩₂.G) := Functor.grpObjObj
  haveI := 𝒩₁.gen_hom
  haveI := 𝒩₂.gen_hom
  obtain ⟨f12, hf12⟩ := (h₂ 𝒩₁.G).2 𝒩₁.gen.hom
  obtain ⟨f21, hf21⟩ := (h₁ 𝒩₂.G).2 𝒩₂.gen.hom
  simp only at hf12 hf21
  have e1 : f12 ≫ f21 = 𝟙 _ := (h₁ 𝒩₁.G).1 (by
    simp only
    rw [Functor.map_comp, Category.assoc, hf21, hf12, CategoryTheory.Functor.map_id, Category.id_comp])
  have e2 : f21 ≫ f12 = 𝟙 _ := (h₂ 𝒩₂.G).1 (by
    simp only
    rw [Functor.map_comp, Category.assoc, hf12, hf21, CategoryTheory.Functor.map_id, Category.id_comp])
  -- postcomposition with `f12` on `T`-points, `T` smooth
  have key : ∀ (T : Over (Spec (CommRingCat.of O))) [Smooth T.hom] (a : T ⟶ 𝒩₁.G),
      F.map (a ≫ f12) ≫ 𝒩₂.gen.hom = F.map a ≫ 𝒩₁.gen.hom := by
    intro T _ a
    rw [Functor.map_comp, Category.assoc, hf12]
  have hmul : ∀ (T : Over (Spec (CommRingCat.of O))) [Smooth T.hom] (a b : T ⟶ 𝒩₁.G),
      (a * b) ≫ f12 = a ≫ f12 * b ≫ f12 := by
    intro T _ a b
    apply (h₂ T).1
    simp only
    rw [key, Functor.map_mul, Functor.map_mul, MonObj.mul_comp, MonObj.mul_comp, key, key]
  have hone : ∀ (T : Over (Spec (CommRingCat.of O))) [Smooth T.hom],
      (1 : T ⟶ 𝒩₁.G) ≫ f12 = 1 := by
    intro T _
    apply (h₂ T).1
    simp only
    rw [key, Functor.map_one, Functor.map_one, MonObj.one_comp, MonObj.one_comp]
  haveI : Smooth (𝟙_ (Over (Spec (CommRingCat.of O)))).hom :=
    ZInQ.Contrib.NeronC.smooth_tensorUnit _
  haveI : Smooth (𝒩₁.G ⊗ 𝒩₁.G).hom :=
    ZInQ.Contrib.NeronC.smooth_tensor _ _ inferInstance inferInstance
  refine ⟨⟨f12, f21, e1, e2⟩, ⟨?_, ?_⟩⟩
  · change η[𝒩₁.G] ≫ f12 = η[𝒩₂.G]
    rw [MonObj.one_eq_one, MonObj.one_eq_one, hone]
  · change μ[𝒩₁.G] ≫ f12 = (f12 ⊗ₘ f12) ≫ μ[𝒩₂.G]
    rw [MonObj.mul_eq_mul, MonObj.mul_eq_mul, hmul, MonObj.comp_mul]
    simp

/-- Semistability transfers along an isomorphism of group models over `O`. -/
theorem isSemistable_of_iso {B : PkgI3.AbVar K} {O : ValuationSubring K} (𝒩₁ 𝒩₂ : GroupModelO B O)
    (e : 𝒩₁.G ≅ 𝒩₂.G) (he : IsMonHom e.hom) (h : 𝒩₁.IsSemistable) : 𝒩₂.IsSemistable := by
  let P := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))))
  haveI := he
  let E : P.mapGrp.obj (Grp.mk 𝒩₁.G) ≅ P.mapGrp.obj (Grp.mk 𝒩₂.G) :=
    P.mapGrp.mapIso (Grp.mkIso' e)
  exact @hasSemiAbelian_of_iso _ _ (geomSpecialFibre 𝒩₁) (geomSpecialFibre 𝒩₂) _ _ (isoX E)
    (inferInstanceAs (IsMonHom E.hom.hom.hom)) h

/-- Semistable reduction (some Néron model) gives all Néron models semistable. -/
theorem semistableNeronModels_of_has {B : PkgI3.AbVar K} {O : ValuationSubring K}
    (h : HasSemistableReduction B O) : SemistableNeronModels B O := by
  obtain ⟨𝒩, h𝒩, hs⟩ := h
  intro 𝒩' h𝒩'
  obtain ⟨e, he⟩ := neronO_unique 𝒩 𝒩' h𝒩 h𝒩'
  exact isSemistable_of_iso 𝒩 𝒩' e he hs

end NeronUnique

section LocalGlobal

open ZInQ.HeightSplit ZInQ.DefFaltings

/-- `(F_f ∘ F_g)(𝒢) ≅ F_h(𝒢)` for `f ≫ g = h`, as group objects (`F_• = Over.pullback •`). -/
noncomputable irreducible_def pbCompIso {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (hfg : f ≫ g = h) (𝒢 : Grp (Over Z)) :
    (Over.pullback f).mapGrp.obj ((Over.pullback g).mapGrp.obj 𝒢) ≅
      (Over.pullback h).mapGrp.obj 𝒢 :=
  (Functor.mapGrpCompIso.app 𝒢).symm ≪≫
    (Functor.mapGrpNatIso (Over.pullbackComp f g).symm).app 𝒢 ≪≫
    (Functor.mapGrpNatIso (eqToIso (show Over.pullback (f ≫ g) = Over.pullback h by rw [hfg]))).app 𝒢

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- `Spec O → Spec 𝓞_L`. -/
noncomputable abbrev gO (O : ValuationSubring L) : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (toOL O))

theorem jO_gO (O : ValuationSubring L) :
    jO O ≫ gO O = Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)) := by
  rw [← Spec.map_comp]
  rfl

/-- **The base change `𝒩 ×_{𝓞_L} O` of a group model over `𝓞_L` to a valuation ring `O` of `L`**,
as a group model of `A_L` over `O` (generic fibre identified through `𝒩.gen`). -/
noncomputable def toO (𝒩 : GroupModel A L) (O : ValuationSubring L) : GroupModelO (A.baseChange L) O where
  G := (Over.pullback (gO O)).obj 𝒩.G
  grp := Functor.grpObjObj
  smooth := by change Smooth (pullback.snd 𝒩.G.hom (gO O)); infer_instance
  separated := by change IsSeparated (pullback.snd 𝒩.G.hom (gO O)); infer_instance
  qc := by change QuasiCompact (pullback.snd 𝒩.G.hom (gO O)); infer_instance
  gen := isoX (pbCompIso (jO O) (gO O) _ (jO_gO O) (Grp.mk 𝒩.G)) ≪≫ 𝒩.gen
  gen_hom := by
    letI : GrpObj ((Over.pullback (gO O)).obj 𝒩.G) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback (jO O)).obj ((Over.pullback (gO O)).obj 𝒩.G)) :=
      Functor.grpObjObj
    letI : GrpObj (genericFibre L 𝒩.G) := Functor.grpObjObj
    haveI := 𝒩.gen_hom
    have h1 : IsMonHom (pbCompIso (jO O) (gO O) _ (jO_gO O) (Grp.mk 𝒩.G)).hom.hom.hom :=
      inferInstance
    exact @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ h1 𝒩.gen_hom

end LocalGlobal

section LocalGlobal2

open ZInQ.HeightSplit ZInQ.DefFaltings

/-- **GLUE `SemiAbelianFieldIsoInvariant`** (new; pure transport). Having semi-abelian identity
component is invariant under base change along an isomorphism of fields `σ : k ≃ k'`. Needs only
transport of structure: `Over.pullback (Spec σ)` is an equivalence of categories which preserves
products, open immersions, connectedness, flatness, surjectivity, abelian varieties
(`AbVar.baseChange`) and, through `R ↦ R` with the `k`-algebra structure via `σ`, the functor of
points of `𝔾_m^r`. No algebraic geometry beyond `Over.pullback` of an isomorphism. -/
def SemiAbelianFieldIsoInvariant : Prop :=
  ∀ (k k' : Type) [Field k] [Field k'] (σ : k ≃+* k') (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G],
    HasSemiAbelianIdentityComponent G ↔
      (letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (σ : k →+* k')))).obj G) :=
        Functor.grpObjObj
       HasSemiAbelianIdentityComponent ((Over.pullback (Spec.map (CommRingCat.ofHom (σ : k →+* k')))).obj G))

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

theorem spec_barIso_comp (O : ValuationSubring L) [IsDiscreteValuationRing O] :
    Spec.map (CommRingCat.ofHom ((barIso O : _ ≃+* _) : _ →+* _)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (ResBar (center O)))) =
    Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))) ≫ gO O := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    barIso_comp]

/-- **Fibre identification**: the geometric special fibre of `𝒩 ×_{𝓞_L} O` is the base change of
the geometric fibre of `𝒩` at `𝔭_O` along `κ̄(𝔭_O) ≅ κ̄(O)`, as group schemes. -/
noncomputable def fibreIso (𝒩 : GroupModel A L) (O : ValuationSubring L) [IsDiscreteValuationRing O] :
    (Over.pullback (Spec.map (CommRingCat.ofHom ((barIso O : _ ≃+* _) : _ →+* _)))).mapGrp.obj
        (Grp.mk (geomFibre 𝒩 (center O))) ≅
      Grp.mk (geomSpecialFibre (toO 𝒩 O)) :=
  pbCompIso _ _ _ (spec_barIso_comp O) (Grp.mk 𝒩.G) ≪≫
    (pbCompIso _ _ _ rfl (Grp.mk 𝒩.G)).symm

theorem fibre_semistable_iff (hT : SemiAbelianFieldIsoInvariant) (𝒩 : GroupModel A L)
    (O : ValuationSubring L) [IsDiscreteValuationRing O] :
    HasSemiAbelianIdentityComponent (geomFibre 𝒩 (center O)) ↔ (toO 𝒩 O).IsSemistable := by
  rw [hT _ _ (barIso O) (geomFibre 𝒩 (center O))]
  let E := fibreIso 𝒩 O
  exact ⟨fun h => @hasSemiAbelian_of_iso _ _ _ (geomSpecialFibre (toO 𝒩 O)) Functor.grpObjObj _
      (isoX E) (inferInstanceAs (IsMonHom E.hom.hom.hom)) h,
    fun h => @hasSemiAbelian_of_iso _ _ (geomSpecialFibre (toO 𝒩 O)) _ _ Functor.grpObjObj
      (isoX E.symm) (inferInstanceAs (IsMonHom E.inv.hom.hom)) h⟩

theorem fibre_semistable_iff' (hT : SemiAbelianFieldIsoInvariant) (𝒩 : GroupModel A L)
    (O : ValuationSubring L) [IsDiscreteValuationRing O] (𝔭 : Ideal (𝓞 L)) [𝔭.IsMaximal]
    (h : center O = 𝔭) :
    HasSemiAbelianIdentityComponent (geomFibre 𝒩 𝔭) ↔ (toO 𝒩 O).IsSemistable := by
  subst h
  exact fibre_semistable_iff hT 𝒩 O

/-- **LEAF `NeronLocalizesDVR` (Bosch–Lütkebohmert–Raynaud, *Néron models*, §1.2 Prop. 4;
number UNVERIFIED: over a Dedekind ring `R`, a smooth separated `R`-model of finite type is a
Néron model iff its localizations at the closed points are).** The direction used: for a Néron
model `𝒩` of `A_L` over `𝓞_L` and a discrete valuation ring `O` of `L` (necessarily `(𝓞_L)_𝔭`,
`mem_iff_exists`), `𝒩 ×_{𝓞_L} O` is a Néron model over `O`. (`𝒩` is quasi-compact and smooth,
hence of finite type.) -/
def NeronLocalizesDVR : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒩 : GroupModel A L), 𝒩.IsNeronModel →
    ∀ (O : ValuationSubring L) [IsDiscreteValuationRing O], (toO 𝒩 O).IsNeronModel

/-- **GLUE `SemistableLocalGlobal` (reduct-split), PROVED** from the leaf `NeronLocalizesDVR`
(BLR §1.2 Prop. 4) and the transport glue `SemiAbelianFieldIsoInvariant`. Proved here: DVRs of
`L` are the `(𝓞_L)_𝔭` with matching residue fields (`mem_iff_exists`, `resIso`, `dvrAt`),
uniqueness of Néron models over a DVR (`neronO_unique`), and the fibre identification
(`fibreIso`). -/
theorem semistableLocalGlobal_of (hL : NeronLocalizesDVR) (hT : SemiAbelianFieldIsoInvariant) :
    SemistableLocalGlobal := by
  intro K _ A L _ _ _ 𝒩 h𝒩
  constructor
  · intro hss O hO
    haveI := hO
    haveI := center_isMaximal O
    exact ⟨toO 𝒩 O, hL K A L 𝒩 h𝒩 O, (fibre_semistable_iff hT 𝒩 O).mp (hss (center O))⟩
  · intro h 𝔭 _
    have hs := semistableNeronModels_of_has (h (dvrAt 𝔭) inferInstance)
    exact (fibre_semistable_iff' hT 𝒩 (dvrAt 𝔭) 𝔭 (center_dvrAt 𝔭)).mpr
      (hs _ (hL K A L 𝒩 h𝒩 (dvrAt 𝔭)))

end LocalGlobal2

section Transport

open ZInQ.HeightSplit

variable {k k' : Type} [Field k] [Field k'] (σ : k ≃+* k')

/-- `Spec σ : Spec k' → Spec k`. -/
noncomputable abbrev sσ : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (σ : k →+* k'))

instance : IsIso (sσ σ) := by
  have : IsIso (CommRingCat.ofHom (σ : k →+* k')) :=
    ⟨⟨CommRingCat.ofHom (σ.symm : k' →+* k), by ext x; simp, by ext x; simp⟩⟩
  infer_instance

theorem pb_map_left {X Y : Over (Spec (CommRingCat.of k))} (f : X ⟶ Y) :
    ((Over.pullback (sσ σ)).map f).left =
      pullback.fst X.hom (sσ σ) ≫ f.left ≫ inv (pullback.fst Y.hom (sσ σ)) := by
  rw [← Category.assoc, IsIso.eq_comp_inv]
  simp

theorem homEquiv_mul' (X : Over (Spec (CommRingCat.of k'))) (Y : Over (Spec (CommRingCat.of k)))
    [GrpObj Y] (p q : (Over.map (sσ σ)).obj X ⟶ Y) :
    letI : GrpObj ((Over.pullback (sσ σ)).obj Y) := Functor.grpObjObj
    (Over.mapPullbackAdj (sσ σ)).homEquiv X Y (p * q) =
      (Over.mapPullbackAdj (sσ σ)).homEquiv X Y p * (Over.mapPullbackAdj (sσ σ)).homEquiv X Y q := by
  letI : GrpObj ((Over.pullback (sσ σ)).obj Y) := Functor.grpObjObj
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

/-- A `k'`-algebra as a `k`-algebra through `σ`. -/
@[reducible] noncomputable def algK (R : Type) [CommRing R] [Algebra k' R] : Algebra k R :=
  ((algebraMap k' R).comp (σ : k →+* k')).toAlgebra

/-- `Over.map (Spec σ) (Spec R / k') ≅ Spec R / k`. -/
noncomputable def ιR (R : Type) [CommRing R] [Algebra k' R] :
    letI := algK σ R
    (Over.map (sσ σ)).obj (algPt k' R) ≅ algPt k R :=
  letI := algK σ R
  Over.isoMk (Iso.refl _) (by
    simp only [Over.map_obj_hom, Iso.refl_hom, algPt, Over.mk_hom]
    erw [Category.id_comp]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])

/-- `(Spec R / k' ⟶ U_{k'}) ≃* (Spec R / k ⟶ U)`. -/
noncomputable def Φ (U : Over (Spec (CommRingCat.of k))) [GrpObj U] (R : Type) [CommRing R]
    [Algebra k' R] :
    letI := algK σ R
    letI : GrpObj ((Over.pullback (sσ σ)).obj U) := Functor.grpObjObj
    (algPt k' R ⟶ (Over.pullback (sσ σ)).obj U) ≃* (algPt k R ⟶ U) :=
  letI := algK σ R
  letI : GrpObj ((Over.pullback (sσ σ)).obj U) := Functor.grpObjObj
  { toFun p := (ιR σ R).inv ≫ ((Over.mapPullbackAdj (sσ σ)).homEquiv _ _).symm p
    invFun x := (Over.mapPullbackAdj (sσ σ)).homEquiv _ _ ((ιR σ R).hom ≫ x)
    left_inv p := by
      simp only
      rw [Iso.hom_inv_id_assoc, Equiv.apply_symm_apply]
    right_inv x := by
      simp only
      rw [Equiv.symm_apply_apply, Iso.inv_hom_id_assoc]
    map_mul' p q := by
      obtain ⟨p', rfl⟩ := ((Over.mapPullbackAdj (sσ σ)).homEquiv _ U).surjective p
      obtain ⟨q', rfl⟩ := ((Over.mapPullbackAdj (sσ σ)).homEquiv _ U).surjective q
      rw [← homEquiv_mul', Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
        MonObj.comp_mul] }

theorem Φ_comp (U V : Over (Spec (CommRingCat.of k))) [GrpObj U] [GrpObj V] (R : Type) [CommRing R]
    [Algebra k' R] (u : algPt k' R ⟶ (Over.pullback (sσ σ)).obj U) (g : U ⟶ V) :
    letI := algK σ R
    letI : GrpObj ((Over.pullback (sσ σ)).obj U) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback (sσ σ)).obj V) := Functor.grpObjObj
    Φ σ V R (u ≫ (Over.pullback (sσ σ)).map g) = Φ σ U R u ≫ g := by
  show (ιR σ R).inv ≫ ((Over.mapPullbackAdj (sσ σ)).homEquiv _ _).symm
      (u ≫ (Over.pullback (sσ σ)).map g) =
    ((ιR σ R).inv ≫ ((Over.mapPullbackAdj (sσ σ)).homEquiv _ _).symm u) ≫ g
  rw [Adjunction.homEquiv_naturality_right_symm, Category.assoc]

theorem Φ_natural (U : Over (Spec (CommRingCat.of k))) [GrpObj U] (R S : Type) [CommRing R]
    [Algebra k' R] [CommRing S] [Algebra k' S] (f : R →ₐ[k'] S)
    (u : algPt k' R ⟶ (Over.pullback (sσ σ)).obj U) :
    letI := algK σ R
    letI := algK σ S
    letI : GrpObj ((Over.pullback (sσ σ)).obj U) := Functor.grpObjObj
    Φ σ U S (algPtMap f ≫ u) =
      algPtMap (k := k) ({ (f : R →+* S) with commutes' := fun a => f.commutes (σ a) } : R →ₐ[k] S)
        ≫ Φ σ U R u := by
  show (ιR σ S).inv ≫ ((Over.mapPullbackAdj (sσ σ)).homEquiv _ _).symm (algPtMap f ≫ u) = _ ≫
    (ιR σ R).inv ≫ ((Over.mapPullbackAdj (sσ σ)).homEquiv _ _).symm u
  rw [Adjunction.homEquiv_naturality_left_symm, ← Category.assoc, ← Category.assoc]
  congr 1

theorem left_pb_map_fst {X Y : Over (Spec (CommRingCat.of k))} (f : X ⟶ Y) :
    ((Over.pullback (sσ σ)).map f).left =
      (asIso (pullback.fst X.hom (sσ σ))).hom ≫ f.left ≫ (asIso (pullback.fst Y.hom (sσ σ))).inv :=
  pb_map_left σ f

/-- **Base change along a field isomorphism preserves semi-abelian identity components.** -/
theorem hasSemiAbelian_pullback (G : Over (Spec (CommRingCat.of k))) [GrpObj G]
    (h : HasSemiAbelianIdentityComponent G) :
    letI : GrpObj ((Over.pullback (sσ σ)).obj G) := Functor.grpObjObj
    HasSemiAbelianIdentityComponent ((Over.pullback (sσ σ)).obj G) := by
  obtain ⟨U, hU, inc, hoi, hmh, hcon, B, π, hπm, hfl, hsu, r, e, he_inj, he_ker, he_nat⟩ := h
  let F := Over.pullback (sσ σ)
  letI : GrpObj (F.obj G) := Functor.grpObjObj
  letI : GrpObj (F.obj U) := Functor.grpObjObj
  letI : GrpObj (F.obj B.X) := Functor.grpObjObj
  let B' : PkgI3.AbVar k' :=
    { X := F.obj B.X
      grp := Functor.grpObjObj
      proper := by change IsProper (pullback.snd B.X.hom (sσ σ)); infer_instance
      smooth := by change Smooth (pullback.snd B.X.hom (sσ σ)); infer_instance
      geomInt := by change GeometricallyIntegral (pullback.snd B.X.hom (sσ σ)); infer_instance }
  refine ⟨F.obj U, inferInstance, F.map inc, ?_, inferInstance, ?_, B', F.map π, inferInstance, ?_,
    ?_, r, fun R _ _ => (Φ σ U R).symm.toMonoidHom.comp (@e R _ (algK σ R)), ?_, ?_, ?_⟩
  · rw [left_pb_map_fst]; infer_instance
  · exact (Scheme.homeoOfIso (asIso (pullback.fst U.hom (sσ σ)))).connectedSpace_iff.mpr hcon
  · change Flat ((Over.pullback (sσ σ)).map π).left
    rw [left_pb_map_fst]; infer_instance
  · change Surjective ((Over.pullback (sσ σ)).map π).left
    rw [left_pb_map_fst]; infer_instance
  · intro R _ _
    exact (Φ σ U R).symm.injective.comp (@he_inj R _ (algK σ R))
  · intro R _ _ u
    letI := algK σ R
    have h1 : u ≫ F.map π = 1 ↔ Φ σ U R u ≫ π = 1 := by
      rw [← Φ_comp]
      constructor
      · intro h; rw [h, map_one]
      · intro h; exact (Φ σ B.X R).injective (by rw [h, map_one])
    rw [h1, he_ker]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, by simp [ht]⟩
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply] at ht
      rw [← ht, MulEquiv.apply_symm_apply]
  · intro R S _ _ _ _ f t
    letI := algK σ R
    letI := algK σ S
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    apply (Φ σ U S).injective
    rw [MulEquiv.apply_symm_apply, Φ_natural, MulEquiv.apply_symm_apply]
    exact he_nat R S ({ (f : R →+* S) with commutes' := fun a => f.commutes (σ a) } : R →ₐ[k] S) t

/-- **GLUE `SemiAbelianFieldIsoInvariant`, PROVED.** -/
theorem semiAbelianFieldIsoInvariant : SemiAbelianFieldIsoInvariant := by
  intro k k' _ _ σ G _
  refine ⟨hasSemiAbelian_pullback σ G, fun h => ?_⟩
  letI : GrpObj ((Over.pullback (sσ σ)).obj G) := Functor.grpObjObj
  have h2 := hasSemiAbelian_pullback σ.symm _ h
  have hc : sσ σ.symm ≫ sσ σ = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (σ.symm : k' →+* k).comp (σ : k →+* k') = RingHom.id k := by ext x; simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  let E := pbCompIso (sσ σ.symm) (sσ σ) (𝟙 _) hc (Grp.mk G) ≪≫
    (Functor.mapGrpNatIso (Over.pullbackId)).app _ ≪≫ Functor.mapGrpIdIso.app _
  exact @hasSemiAbelian_of_iso _ _ _ G Functor.grpObjObj _ (isoX E)
    (inferInstanceAs (IsMonHom E.hom.hom.hom)) h2

end Transport

/-- **`SemistableLocalGlobal` from the single leaf `NeronLocalizesDVR`** (BLR §1.2 Prop. 4). -/
theorem semistableLocalGlobal_leaf (hL : NeronLocalizesDVR) : SemistableLocalGlobal :=
  semistableLocalGlobal_of hL semiAbelianFieldIsoInvariant


/-! ## §6. The leaves over their printed bases (strictly henselian, complete) -/

section Printed

/-- A strictly henselian discrete valuation ring: henselian, with separably closed residue field. -/
def IsStrictlyHenselianDVR {K : Type} [Field K] (O : ValuationSubring K) : Prop :=
  IsDiscreteValuationRing O ∧ HenselianLocalRing O ∧ IsSepClosed (IsLocalRing.ResidueField O)

/-- A complete discrete valuation ring (complete and separated for the `𝔪`-adic topology). -/
def IsCompleteDVR {K : Type} [Field K] (O : ValuationSubring K) : Prop :=
  IsDiscreteValuationRing O ∧ IsAdicComplete (IsLocalRing.maximalIdeal O) O

/-- **LEAF (printed base) `SemistableUnipotentSH`**: `SemistableUnipotent` for a strictly
henselian `O` (SGA 7 I, Exp. IX, Prop. 3.5, if printed over a strictly henselian trait;
UNVERIFIED). The base is not the only open reading (all UNVERIFIED): SGA 7 may define semistability over
`k(s)` rather than on the geometric special fibre, as `HasSemistableReduction` does (this matters
for imperfect `k`), and the 3.5 display may include the echelon clause. -/
def SemistableUnipotentSH : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, HasSemistableReduction A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
      ∀ t : TΩ A Ω ℓ, galTΩ A ℓ σ (galTΩ A ℓ σ t) - 2 • galTΩ A ℓ σ t + t = 0

/-- **LEAF (printed base) `RaynaudSemistableSH`**: Raynaud's criterion for a strictly henselian
`O` (SGA 7 I, Exp. IX, Prop. 4.7, if printed over a strictly henselian trait; UNVERIFIED). Other
open readings (UNVERIFIED): the print may state a Galois-form conclusion rather than the Néron
form, and may require `n > 3` (here `m = 3` is allowed). -/
def RaynaudSemistableSH : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O → ∀ (A : PkgI3.AbVar K) (m : ℕ), 3 ≤ m → IsUnit (m : O) →
    (∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 →
      ∃ y : A.Pt K, ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y = x) →
    SemistableNeronModels A O

/-- **LEAF (printed base) `SemistableReductionSH`** (SGA 7 I, Exp. IX, Thm. 3.6 over a strictly
henselian trait; UNVERIFIED which base is printed). -/
def SemistableReductionSH : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O → ∀ A : PkgI3.AbVar K,
    ∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
      ∀ O' : ValuationSubring K', IsDiscreteValuationRing O' →
        O'.comap (algebraMap K K') = O → SemistableNeronModels (A.baseChange K') O'

/-- **LEAF (printed base) `SemistablePersistsSH`** (SGA 7 I, Exp. IX, Cor. 3.3, first assertion,
over a strictly henselian base trait; UNVERIFIED). Other open readings (UNVERIFIED): SGA 7 may
define semistability over `k(s)` rather than on the geometric special fibre, as
`HasSemistableReduction` does (this matters for imperfect `k`), and may require `S'` finite over
`S`. -/
def SemistablePersistsSH : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O →
    ∀ (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'], O'.comap (algebraMap K K') = O →
    ∀ A : PkgI3.AbVar K, HasSemistableReduction A O → SemistableNeronModels (A.baseChange K') O'

/-- **LEAF (printed base) `IdentityComponentBaseChangeSH`** (SGA 7 I, Exp. IX, Cor. 3.3, second
assertion, over a strictly henselian base trait; UNVERIFIED). Other open readings (UNVERIFIED):
SGA 7 may define semistability over `k(s)` rather than on the geometric special fibre, as
`HasSemistableReduction` does (this matters for imperfect `k`), and may require `S'` finite over
`S`. -/
def IdentityComponentBaseChangeSH : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O →
    ∀ (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'] (hO : O'.comap (algebraMap K K') = O) (A : PkgI3.AbVar K),
    HasSemistableReduction A O →
    ∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel →
    ∀ 𝒩' : GroupModelO (A.baseChange K') O', 𝒩'.IsNeronModel →
    ∀ (U : Over (Spec (CommRingCat.of O))) [GrpObj U] (i : U ⟶ 𝒩.G), IsOpenImmersion i.left →
      IsMonHom i → ConnectedSpace ((Over.pullback (jO O)).obj U).left →
      ConnectedSpace ((Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap O (ResBarO O))))).obj U).left →
      ∃ j : (Over.pullback (Spec.map (CommRingCat.ofHom (comapHom hO)))).obj U ⟶ 𝒩'.G,
        IsOpenImmersion j.left ∧
        (letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (comapHom hO)))).obj U) :=
          Functor.grpObjObj
         IsMonHom j)

/-- **LEAF (printed base) `SerreTateThm2Complete`**: Serre–Tate's Thm. 2 for a complete discrete
valuation ring (if Serre–Tate 1968 assume `K` complete; UNVERIFIED). Other open reading
(UNVERIFIED): Serre–Tate may build `T_ℓ` over a separable closure `K_s`; in characteristic `p` the
statement here (over an algebraic closure, with `K'` possibly inseparable) can then be stronger
than the print. -/
def SerreTateThm2Complete : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O], IsCompleteDVR O →
    ∀ (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (ℓ : ℕ) [Fact ℓ.Prime],
      IsUnit (ℓ : O) →
      ((∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
          HasGoodReduction (PkgI2.baseChange A K') (w.comap (algebraMap K' (AlgebraicClosure K)))) ↔
       (Set.range fun σ : {σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K // IsInertia w σ} =>
          (ObjBridge.ofGrp A).galT (ℓ := ℓ) σ.1).Finite)

/-- The general-DVR leaves imply the printed-base leaves (each printed-base leaf is a
specialization of the general one): sanity check that the new statements are no stronger than
reduct-split's. -/
theorem printed_of_general (h35 : SemistableUnipotent) (h47 : RaynaudSemistable)
    (h36 : SemistableReductionDVR) (h33a : SemistablePersistsDVR)
    (h33b : IdentityComponentBaseChangeDVR) (hST : SerreTateThm2) :
    SemistableUnipotentSH ∧ RaynaudSemistableSH ∧ SemistableReductionSH ∧ SemistablePersistsSH ∧
      IdentityComponentBaseChangeSH ∧ SerreTateThm2Complete :=
  ⟨fun K _ O _ _ => h35 K O, fun K _ O _ _ => h47 K O, fun K _ O _ _ => h36 K O,
   fun K _ O _ _ => h33a K O, fun K _ O _ _ => h33b K O, fun K _ O _ _ => hST K O⟩

end Printed


section DVRBaseChange

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] {O : ValuationSubring K}
  {O' : ValuationSubring K'} (hO : O'.comap (algebraMap K K') = O)

theorem comapHom_isLocalHom : IsLocalHom (comapHom hO) := by
  constructor
  intro x hx
  obtain ⟨u, hu⟩ := hx
  have hx0 : (x : K) ≠ 0 := by
    intro h0
    have : (comapHom hO x : K') = 0 := by
      change algebraMap K K' (x : K) = 0
      rw [h0, map_zero]
    have h1 : ((u : O') : K') = 0 := by rw [hu]; exact this
    exact u.ne_zero (Subtype.ext h1)
  have hinv' : algebraMap K K' (x : K)⁻¹ ∈ O' := by
    rw [map_inv₀]
    have h2 : (((u⁻¹ : O'ˣ) : O') : K') * ((u : O') : K') = 1 :=
      congrArg (fun z : O' => (z : K')) (Units.inv_mul u)
    have h3 : ((u : O') : K') = algebraMap K K' (x : K) := by rw [hu]; rfl
    rw [h3] at h2
    rw [← eq_inv_of_mul_eq_one_left h2]
    exact (u⁻¹ : O'ˣ).1.2
  have hinv : (x : K)⁻¹ ∈ O := by
    have h4 : (x : K)⁻¹ ∈ O'.comap (algebraMap K K') := hinv'
    rwa [hO] at h4
  exact ⟨⟨x, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

/-- The residue map `κ(O) → κ(O')`. -/
noncomputable def resMap : IsLocalRing.ResidueField O →+* IsLocalRing.ResidueField O' :=
  @IsLocalRing.ResidueField.map _ _ _ _ _ _ (comapHom hO) (comapHom_isLocalHom hO)

theorem resMap_residue (a : O) :
    resMap hO (IsLocalRing.residue O a) = IsLocalRing.residue O' (comapHom hO a) :=
  @IsLocalRing.ResidueField.map_residue _ _ _ _ _ _ (comapHom hO) (comapHom_isLocalHom hO) a

/-- `κ̄(O) ≅ κ̄(O')` over `κ(O) → κ(O')`, for an algebraic residue extension. -/
noncomputable def barIsoDVR
    (halg : letI := (resMap hO).toAlgebra
      Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')) :
    ResBarO O ≃+* ResBarO O' :=
  letI := (resMap hO).toAlgebra
  (IsAlgClosure.equivOfAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')
    (ResBarO O') (ResBarO O)).symm.toRingEquiv

theorem barIsoDVR_comp
    (halg : letI := (resMap hO).toAlgebra
      Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')) :
    ((barIsoDVR hO halg : _ ≃+* _) : _ →+* _).comp (algebraMap O (ResBarO O)) =
      (algebraMap O' (ResBarO O')).comp (comapHom hO) := by
  letI := (resMap hO).toAlgebra
  ext a
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply O (IsLocalRing.ResidueField O) (ResBarO O),
    IsScalarTower.algebraMap_apply O' (IsLocalRing.ResidueField O') (ResBarO O')]
  change (IsAlgClosure.equivOfAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')
    (ResBarO O') (ResBarO O)).symm (algebraMap (IsLocalRing.ResidueField O) (ResBarO O) _) = _
  rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply (IsLocalRing.ResidueField O)
    (IsLocalRing.ResidueField O') (ResBarO O')]
  change algebraMap (IsLocalRing.ResidueField O') (ResBarO O') (resMap hO (IsLocalRing.residue O a)) = _
  rw [resMap_residue]
  rfl

/-- `Spec O' → Spec O`. -/
noncomputable abbrev gD : Spec (CommRingCat.of O') ⟶ Spec (CommRingCat.of O) :=
  Spec.map (CommRingCat.ofHom (comapHom hO))

/-- `Spec K' → Spec K`. -/
noncomputable abbrev sKK : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K K'))

theorem jO_gD : jO O' ≫ gD hO = sKK (K := K) (K' := K') ≫ jO O := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- **Base change of a group model along an extension of valuation rings `O ⊆ O'`.** -/
noncomputable def bcDVR {A : PkgI3.AbVar K} (𝒩 : GroupModelO A O) :
    GroupModelO (A.baseChange K') O' :=
  letI : GrpObj ((Over.pullback (jO O)).obj 𝒩.G) := Functor.grpObjObj
  haveI := 𝒩.gen_hom
  { G := (Over.pullback (gD hO)).obj 𝒩.G
    grp := Functor.grpObjObj
    smooth := by change Smooth (pullback.snd 𝒩.G.hom (gD hO)); infer_instance
    separated := by change IsSeparated (pullback.snd 𝒩.G.hom (gD hO)); infer_instance
    qc := by change QuasiCompact (pullback.snd 𝒩.G.hom (gD hO)); infer_instance
    gen := isoX (pbCompIso (jO O') (gD hO) _ (jO_gD hO) (Grp.mk 𝒩.G)) ≪≫
      (isoX (pbCompIso (sKK (K := K) (K' := K')) (jO O) _ rfl (Grp.mk 𝒩.G))).symm ≪≫
      isoX ((Over.pullback (sKK (K := K) (K' := K'))).mapGrp.mapIso (Grp.mkIso' 𝒩.gen))
    gen_hom := by
      letI : GrpObj ((Over.pullback (gD hO)).obj 𝒩.G) := Functor.grpObjObj
      letI : GrpObj ((Over.pullback (jO O')).obj ((Over.pullback (gD hO)).obj 𝒩.G)) :=
        Functor.grpObjObj
      have h1 : IsMonHom (pbCompIso (jO O') (gD hO) _ (jO_gD hO) (Grp.mk 𝒩.G)).hom.hom.hom :=
        inferInstance
      have h2 : IsMonHom (pbCompIso (sKK (K := K) (K' := K')) (jO O) _ rfl (Grp.mk 𝒩.G)).inv.hom.hom :=
        inferInstance
      have h3 : IsMonHom ((Over.pullback (sKK (K := K) (K' := K'))).mapGrp.mapIso
          (Grp.mkIso' 𝒩.gen)).hom.hom.hom := inferInstance
      exact @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ h1
        (@instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ h2 h3) }

theorem spec_barIsoDVR_comp
    (halg : letI := (resMap hO).toAlgebra
      Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')) :
    Spec.map (CommRingCat.ofHom ((barIsoDVR hO halg : _ ≃+* _) : _ →+* _)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))) =
    Spec.map (CommRingCat.ofHom (algebraMap O' (ResBarO O'))) ≫ gD hO := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    barIsoDVR_comp]

/-- **Semistability is invariant under base change along `O ⊆ O'` with algebraic residue
extension** (fibre identification + `semiAbelianFieldIsoInvariant`). -/
theorem isSemistable_bcDVR_iff
    (halg : letI := (resMap hO).toAlgebra
      Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O'))
    {A : PkgI3.AbVar K} (𝒩 : GroupModelO A O) :
    𝒩.IsSemistable ↔ (bcDVR hO 𝒩).IsSemistable := by
  unfold GroupModelO.IsSemistable
  rw [semiAbelianFieldIsoInvariant _ _ (barIsoDVR hO halg) (geomSpecialFibre 𝒩)]
  let E := pbCompIso _ _ _ (spec_barIsoDVR_comp hO halg) (Grp.mk 𝒩.G) ≪≫
    (pbCompIso _ _ _ rfl (Grp.mk 𝒩.G)).symm
  exact ⟨fun h => @hasSemiAbelian_of_iso _ _ _ (geomSpecialFibre (bcDVR hO 𝒩)) Functor.grpObjObj _
      (isoX E) (inferInstanceAs (IsMonHom E.hom.hom.hom)) h,
    fun h => @hasSemiAbelian_of_iso _ _ (geomSpecialFibre (bcDVR hO 𝒩)) _ _ Functor.grpObjObj
      (isoX E.symm) (inferInstanceAs (IsMonHom E.inv.hom.hom)) h⟩

end DVRBaseChange

open ZInQ.Contrib.AbVarBC

section EtaleDescent

variable {K : Type} [Field K]

/-- **Points of an étale `K`-scheme over a field `Ω₂` come from `Ω`** for any `K`-embedding
`κ : Ω → Ω₂` of an algebraically closed `Ω`: the image of an affine coordinate ring is separable
algebraic over `K`, hence lies in `κ(Ω)`. -/
theorem exists_lift_of_etale {Ω Ω₂ : Type} [Field Ω] [IsAlgClosed Ω] [Field Ω₂] [Algebra K Ω]
    [Algebra K Ω₂] (κ : Ω →ₐ[K] Ω₂) (X : Over (Spec (CommRingCat.of K))) [Etale X.hom]
    (q : Spec (CommRingCat.of Ω₂) ⟶ X.left)
    (hq : q ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K Ω₂))) :
    ∃ p : Spec (CommRingCat.of Ω) ⟶ X.left,
      Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)) ≫ p = q ∧
        p ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  classical
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
  have hint : ∀ r, IsIntegral K (φ.hom r) := fun r =>
    (Algebra.IsIntegral.isIntegral (R := K) r).map f
  choose ψ0 hψ0 using fun r => mem_range_of_isIntegral κ (hint r)
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

end EtaleDescent


section TorsionBC

variable {K : Type} [Field K]

theorem extHom_comp {Ω₀ Ω₁ Ω₂ : Type} [Field Ω₀] [Field Ω₁] [Field Ω₂] [Algebra K Ω₀] [Algebra K Ω₁]
    [Algebra K Ω₂] (κ₁ : Ω₀ →ₐ[K] Ω₁) (κ₂ : Ω₁ →ₐ[K] Ω₂) :
    extHom κ₂ ≫ extHom κ₁ = extHom (κ₂.comp κ₁) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, extHom_left, extHom_left, extHom_left]
  change Spec.map (CommRingCat.ofHom (κ₂ : Ω₁ →+* Ω₂)) ≫ Spec.map (CommRingCat.ofHom (κ₁ : Ω₀ →+* Ω₁)) = _
  rw [← Spec.map_comp]
  rfl

theorem extPt_extPt (A : PkgI3.AbVar K) {Ω₀ Ω₁ Ω₂ : Type} [Field Ω₀] [Field Ω₁] [Field Ω₂]
    [Algebra K Ω₀] [Algebra K Ω₁] [Algebra K Ω₂] (κ₁ : Ω₀ →ₐ[K] Ω₁) (κ₂ : Ω₁ →ₐ[K] Ω₂)
    (z : A.Pt Ω₀) : extPt A κ₂ (extPt A κ₁ z) = extPt A (κ₂.comp κ₁) z := by
  rw [extPt_apply, extPt_apply, extPt_apply, ← Category.assoc, extHom_comp]

theorem bcPt_extPt (A : PkgI3.AbVar K) {L : Type} [Field L] [Algebra K L] {Ω₁ Ω₂ : Type} [Field Ω₁]
    [Algebra L Ω₁] [Algebra K Ω₁] [IsScalarTower K L Ω₁] [Field Ω₂] [Algebra L Ω₂] [Algebra K Ω₂]
    [IsScalarTower K L Ω₂] (κ : Ω₁ →ₐ[L] Ω₂) (y : (A.baseChange L).Pt Ω₁) :
    bcPt A Ω₂ (extPt (A.baseChange L) κ y) = extPt A (κ.restrictScalars K) (bcPt A Ω₁ y) := by
  show (ptMapIso Ω₂).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm (extHom κ ≫ y) =
    extHom (κ.restrictScalars K) ≫ (ptMapIso Ω₁).inv ≫
      ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm y
  have hnat := Adjunction.homEquiv_naturality_left_symm (Over.mapPullbackAdj (sK K L))
    (extHom κ) (y : PkgI3.AbVar.ptObj Ω₁ ⟶ (Over.pullback (sK K L)).obj A.X)
  have hsq : (ptMapIso Ω₂).inv ≫ (Over.map (sK K L)).map (extHom κ) =
      extHom (κ.restrictScalars K) ≫ (ptMapIso Ω₁).inv := by
    apply Over.OverMorphism.ext
    simp [ptMapIso, extHom]
    rfl
  erw [hnat]
  rw [← Category.assoc, hsq, Category.assoc]

/-- **Torsion points of `A_L` over `L̄` of order prime to the characteristic come from `A(K̄)`**,
from `[m]` étale (the bundle leaf `MulEtaleAbelianScheme`): `A[m]` is étale over `K`
(`exists_lift_of_etale`). -/
theorem torsion_descends_etale (hE : AvSplit.T4.MulEtaleAbelianScheme) (A : PkgI3.AbVar K)
    {L : Type} [Field L] [Algebra K L] (κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) (m : ℕ)
    (hm : (m : K) ≠ 0) (q : (A.baseChange L).Pt (AlgebraicClosure L)) (hq : q ^ m = 1) :
    ∃ p : A.Pt (AlgebraicClosure K), p ^ m = 1 ∧
      (bcPt A (AlgebraicClosure L)).symm (extPt A κ p) = q := by
  haveI : PkgI2.IsAbelianScheme (Grp.mk A.X) := ⟨inferInstanceAs (IsProper A.X.hom),
    inferInstanceAs (Smooth A.X.hom), inferInstanceAs (GeometricallyConnected A.X.hom)⟩
  have het : Etale ((𝟙 A.X ^ m : A.X ⟶ A.X).left) :=
    hE K (Grp.mk A.X) m (isUnit_iff_ne_zero.mpr hm)
  let M : A.X ⟶ A.X := 𝟙 A.X ^ m
  let P : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd M.left (η[A.X]).left)
  haveI : Etale P.hom := by
    change Etale (pullback.snd M.left (η[A.X]).left)
    infer_instance
  set q₀ := bcPt A (AlgebraicClosure L) q with hq₀
  have h0 : q₀ ^ m = 1 := by rw [hq₀, ← map_pow, hq, map_one]
  have hxm : q₀ ≫ M = 1 := by rw [comp_pow_one]; exact h0
  have hw : q₀.left ≫ M.left =
      (PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure L)).hom ≫ (η[A.X]).left := by
    have h1 := congrArg Over.Hom.left hxm
    rw [Over.comp_left] at h1
    rw [h1]
    change (toUnit _ ≫ η[A.X]).left = _
    rw [Over.comp_left]
    congr 1
  let z : Spec (CommRingCat.of (AlgebraicClosure L)) ⟶ P.left := pullback.lift q₀.left _ hw
  have hz : z ≫ P.hom = Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure L))) :=
    pullback.lift_snd _ _ _
  obtain ⟨p0, hp0, hp0g⟩ := exists_lift_of_etale κ P z hz
  have hpr : pullback.fst M.left (η[A.X]).left ≫ A.X.hom = P.hom := by
    change _ = pullback.snd M.left (η[A.X]).left
    rw [← Over.w M, ← Category.assoc, pullback.condition, Category.assoc, Over.w η[A.X]]
    simp
  let p : A.Pt (AlgebraicClosure K) := Over.homMk (p0 ≫ pullback.fst M.left (η[A.X]).left) (by
    change (p0 ≫ pullback.fst M.left (η[A.X]).left) ≫ A.X.hom = _
    rw [Category.assoc, hpr, hp0g]
    rfl)
  have hext : extPt A κ p = q₀ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (κ : AlgebraicClosure K →+* AlgebraicClosure L)) ≫
      p0 ≫ pullback.fst M.left (η[A.X]).left = q₀.left
    rw [← Category.assoc, hp0]
    exact pullback.lift_fst _ _ _
  refine ⟨p, ?_, ?_⟩
  · apply extPt_injective A κ
    rw [map_pow, hext, h0, map_one]
  · rw [hext, hq₀, MulEquiv.symm_apply_apply]

end TorsionBC


section RaynaudSH

/-- **LEAF candidate `StrictHenselizationDVR`** (strict henselization of a discrete valuation ring:
EGA IV₄ 18.8.8 and 18.8.13, Stacks Tags 04GQ, 06LJ (`O^sh` of a DVR is a DVR with the same
uniformizer); all locators UNVERIFIED). For a DVR `O ⊆ K` there are a field `K' ⊇ K` and a
strictly henselian DVR `O' ⊆ K'` lying over `O` (`O' = O^sh`, `K' = Frac O^sh`) such that `K'/K`
is separable algebraic, a uniformizer of `O` stays a uniformizer of `O'` (ramification index 1),
and `κ(O')/κ(O)` is separable (algebraic; `κ(O^sh)` is a separable closure of `κ(O)`). -/
def StrictHenselizationDVR : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (O' : ValuationSubring K')
      (hO : O'.comap (algebraMap K K') = O),
      IsStrictlyHenselianDVR O' ∧ Algebra.IsSeparable K K' ∧
      (∀ ϖ : O, Irreducible ϖ → Irreducible (comapHom hO ϖ)) ∧
      (letI := (resMap hO).toAlgebra
       Algebra.IsSeparable (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O'))

/-- **LEAF `NeronBaseChangeUnramifiedDVR`** (Néron models commute with unramified base change with
separable residue extension, in particular with strict henselization: Bosch–Lütkebohmert–Raynaud,
*Néron models*, §1.2 Prop. 2 and §7.2 Thm. 1; numbers UNVERIFIED, and SPECULATIVE whether the print
covers every such extension or only étale maps, strict henselization and completion — in the
latter case restrict this leaf to `O' = O^sh`, which is all that is used). For an extension
`O ⊆ O'` of DVRs with `K'/K` separable algebraic, ramification index `1` and separable residue
extension, the base change `𝒩 ×_O O'` of a Néron model of `A` is a Néron model of `A_{K'}`. -/
def NeronBaseChangeUnramifiedDVR : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O] (K' : Type)
    [Field K'] [Algebra K K'] (O' : ValuationSubring K') [IsDiscreteValuationRing O']
    (hO : O'.comap (algebraMap K K') = O), Algebra.IsSeparable K K' →
    (∀ ϖ : O, Irreducible ϖ → Irreducible (comapHom hO ϖ)) →
    (letI := (resMap hO).toAlgebra
     Algebra.IsSeparable (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')) →
    ∀ (A : PkgI3.AbVar K) (𝒩 : GroupModelO A O), 𝒩.IsNeronModel → (bcDVR hO 𝒩).IsNeronModel

/-- **Raynaud's criterion over a general DVR from its strictly henselian (printed?) form**, by
strict henselization: the torsion hypothesis passes to `A_{K^sh}` (`torsion_descends_etale`, from the
bundle leaf `MulEtaleAbelianScheme`), the Néron model base changes (`NeronBaseChangeUnramifiedDVR`),
and semistability descends (`isSemistable_bcDVR_iff`, proved). -/
theorem raynaudSemistable_of_SH (hR : RaynaudSemistableSH) (hG1 : StrictHenselizationDVR)
    (hG2 : NeronBaseChangeUnramifiedDVR) (hE : AvSplit.T4.MulEtaleAbelianScheme) :
    RaynaudSemistable := by
  intro K _ O _ A m hm3 hmu htors 𝒩 h𝒩
  obtain ⟨K', _, _, O', hO, hSH, hsepK, hunr, hsep⟩ := hG1 K O
  haveI : IsDiscreteValuationRing O' := hSH.1
  have hmu' : IsUnit (m : O') := by
    have := hmu.map (comapHom hO)
    rwa [map_natCast] at this
  have halg : (letI := (resMap hO).toAlgebra
      Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')) := by
    letI := (resMap hO).toAlgebra
    exact Algebra.IsSeparable.isAlgebraic _ _
  rw [isSemistable_bcDVR_iff hO halg]
  refine hR K' O' hSH (A.baseChange K') m hm3 hmu' ?_ _ (hG2 K O K' O' hO hsepK hunr hsep A 𝒩 h𝒩)
  intro x hx
  have hmK : (m : K) ≠ 0 := natCast_ne_zero_of_isUnit O hmu
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K' := IsAlgClosed.lift
  obtain ⟨p, hp, hpx⟩ := torsion_descends_etale hE A κ m hmK x hx
  obtain ⟨z, hz⟩ := htors p hp
  refine ⟨(bcPt A K').symm (extPt A (Algebra.ofId K K') z), ?_⟩
  rw [← hpx, ← hz]
  apply (bcPt A (AlgebraicClosure K')).injective
  rw [MulEquiv.apply_symm_apply, bcPt_extPt, MulEquiv.apply_symm_apply, extPt_extPt, extPt_extPt]
  congr 1
  ext a
  simp

/-- **Leaf `StrictHenselizationNeron`, counted (b), redundant given `StrictHenselizationPair`**
(the form used; no single print: it combines EGA IV₄ 18.8.8/18.8.13 (strict henselization of a DVR
is a strictly henselian DVR with separably closed residue field) and BLR §1.2 Prop. 2 (Néron models
commute with strict henselization); numbers UNVERIFIED). For a DVR `O ⊆ K` there are `K' ⊇ K` and a
strictly henselian DVR `O' ⊆ K'` over `O` with algebraic residue extension, such that the base
change of every Néron model over `O` is a Néron model over `O'`. This replaces the pair
`StrictHenselizationDVR`, `NeronBaseChangeUnramifiedDVR` (whose second member is stated for all
unramified extensions, a generality that may exceed the print). It is the instance `K' = K`,
`O' = O` of `StrictHenselizationPair` (whose `IsSHNeronExt` has the same clauses), so on the final
printed route (`reductLeaves_of_printed''`, which also takes the pair) it is redundant once the
lemma `StrictHenselizationPair → StrictHenselizationNeron` is proved; that lemma is not in this
file. -/
def StrictHenselizationNeron : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (O' : ValuationSubring K')
      (hO : O'.comap (algebraMap K K') = O),
      IsStrictlyHenselianDVR O' ∧
      (letI := (resMap hO).toAlgebra
       Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')) ∧
      ∀ (A : PkgI3.AbVar K) (𝒩 : GroupModelO A O), 𝒩.IsNeronModel → (bcDVR hO 𝒩).IsNeronModel

theorem strictHenselizationNeron_of (hG1 : StrictHenselizationDVR)
    (hG2 : NeronBaseChangeUnramifiedDVR) : StrictHenselizationNeron := by
  intro K _ O _
  obtain ⟨K', _, _, O', hO, hSH, hsepK, hunr, hsep⟩ := hG1 K O
  haveI : IsDiscreteValuationRing O' := hSH.1
  refine ⟨K', inferInstance, inferInstance, O', hO, hSH, ?_, fun A 𝒩 h𝒩 =>
    hG2 K O K' O' hO hsepK hunr hsep A 𝒩 h𝒩⟩
  letI := (resMap hO).toAlgebra
  exact Algebra.IsSeparable.isAlgebraic _ _

/-- **Raynaud's criterion over a general DVR from the strictly henselian form**, with the single
leaf `StrictHenselizationNeron`. -/
theorem raynaudSemistable_of_SH' (hR : RaynaudSemistableSH) (hSN : StrictHenselizationNeron)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : RaynaudSemistable := by
  intro K _ O _ A m hm3 hmu htors 𝒩 h𝒩
  obtain ⟨K', _, _, O', hO, hSH, halg, hbc⟩ := hSN K O
  haveI : IsDiscreteValuationRing O' := hSH.1
  have hmu' : IsUnit (m : O') := by
    have := hmu.map (comapHom hO)
    rwa [map_natCast] at this
  rw [isSemistable_bcDVR_iff hO halg]
  refine hR K' O' hSH (A.baseChange K') m hm3 hmu' ?_ _ (hbc A 𝒩 h𝒩)
  intro x hx
  have hmK : (m : K) ≠ 0 := natCast_ne_zero_of_isUnit O hmu
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K' := IsAlgClosed.lift
  obtain ⟨p, hp, hpx⟩ := torsion_descends_etale hE A κ m hmK x hx
  obtain ⟨z, hz⟩ := htors p hp
  refine ⟨(bcPt A K').symm (extPt A (Algebra.ofId K K') z), ?_⟩
  rw [← hpx, ← hz]
  apply (bcPt A (AlgebraicClosure K')).injective
  rw [MulEquiv.apply_symm_apply, bcPt_extPt, MulEquiv.apply_symm_apply, extPt_extPt, extPt_extPt]
  congr 1
  ext a
  simp

end RaynaudSH


section PrintedGlue

/-- **GLUE `UnipotentFromSH`** (general-DVR SGA 7 IX 3.5 from the strictly henselian form; proved
below as `unipotentFromSH_of` from the leaf `StrictHenselizationInside`). Needs:
(i) a strict henselization of `O` *inside* `Ω` at `w`: a subfield `K^sh ⊆ Ω` with
`w ∩ K^sh` a strictly henselian DVR with algebraic residue extension over `O`, along which Néron
models base change, and fixed by the inertia group of `w` (decomposition/inertia theory of
valuations plus the universal property of `O^sh`; Raynaud, *Anneaux locaux henséliens*, or EGA IV
18.8, with Serre, *Corps locaux*, I §7; UNVERIFIED; not in Mathlib; this is the content of
`StrictHenselizationInside`); (ii) the hypothesis transfers: `HasSemistableReduction A O →
HasSemistableReduction A_{K^sh} (w ∩ K^sh)` by that Néron base change and `isSemistable_bcDVR_iff`
(proved here); (iii) `T_ℓ(A_{K^sh})` over `Ω` is `T_ℓ(A)` over `Ω` compatibly with `σ` (the
kernel's `bcPt_galAct`). -/
def UnipotentFromSH : Prop := SemistableUnipotentSH → SemistableUnipotent

/-- **GLUE `ReductionFromSH`** (general-DVR SGA 7 IX 3.6 from the strictly henselian form). Needs,
besides the strict henselization (`StrictHenselizationDVR`) and Néron base change
(`NeronBaseChangeUnramifiedDVR`): a finite extension `L/K^sh` making `A` semistable descends to a
finite `K'/K` inside `K̄` with `K' K^sh ⊇ L` at every place over `O` (`K^sh` is a filtered union of
finite étale `K`-algebras' fraction fields; Krasner's lemma for the henselian `K^sh`), and the
places of `K'` over `O` all become places over `O^sh` after composing with `K^sh`; and SGA 7 IX 3.3
(first assertion) to pass semistability from `L` up to `K' K^sh`. None of this is in Mathlib. -/
def ReductionFromSH : Prop := SemistableReductionSH → SemistableReductionDVR

/-- **GLUE `PersistsFromSH`** (SGA 7 IX 3.3, first assertion, from the strictly henselian form).
Needs: functoriality of strict henselization along a finite extension `O ⊆ O'` (an embedding
`O^sh → O'^sh` over `O → O'` with `Frac O'^sh` finite over `Frac O^sh`; EGA IV 18.8.10/18.8.13,
UNVERIFIED), then: semistability ascends `O → O^sh` and descends `O'^sh → O'` (both
`isSemistable_bcDVR_iff` with `NeronBaseChangeUnramifiedDVR`), and `(A_{K^sh})_{K''} ≅ (A_{K'})_{K''}`
(as `bcbcIso`). -/
def PersistsFromSH : Prop := SemistablePersistsSH → SemistablePersistsDVR

/-- **GLUE `IdentityComponentFromSH`** (SGA 7 IX 3.3, second assertion, from the strictly
henselian form). Needs, besides what `PersistsFromSH` needs: open immersions descend along the
faithfully flat `O' → O'^sh` (fpqc descent of the property "open immersion", EGA IV 2.7.1,
UNVERIFIED; Mathlib has descent of some properties along faithfully flat maps but not this one in
`Over`-category form); the comparison of the two extension maps by the Néron property; and the
transfer of the hypotheses on `U` (connected generic fibre, connected geometric special fibre) to
its base change over the strict henselization `P` of `O`. -/
def IdentityComponentFromSH : Prop := IdentityComponentBaseChangeSH → IdentityComponentBaseChangeDVR

/-- **GLUE `SerreTateFromComplete`** (Serre–Tate Thm. 2 over a general discrete valuation from the
complete form). Needs: the completion `K̂` of `K` at `O` (Mathlib has `Valued.Completion` but no
package "completion of a DVR is a complete DVR with the same residue field"), an extension of `w`
to an algebraic closure of `K̂` and the identification of inertia groups `I_ŵ ≅ I_w` (henselian
`K̂`; Serre, *Corps locaux*, II §3, UNVERIFIED), `T_ℓ` identification (kernel `bcPt_galAct`), and
good reduction ascends and descends along `O ⊆ Ô` (Néron models commute with completion, BLR §7.2
Thm. 1 / §1.2 Prop. 2, UNVERIFIED, plus the Néron criterion). It also needs: the descent of a
finite extension `K''` of `K̂` to a finite extension of `K` (Krasner's lemma, or density of `K` in
`K̂`); the identification of the completions involved; the choice of a `K`-embedding `ι` of `K̄`
into an algebraic closure of `K̂`; the bijection on `A[ℓ^n]` between the points over `K̄` and over
that algebraic closure; and, in characteristic `p`, the case of an inseparable `K'`, which needs
Serre–Tate Thm. 1 (the field `r7a`). -/
def SerreTateFromComplete : Prop := SerreTateThm2Complete → SerreTateThm2

/-- The leaves in printed form (strictly henselian / complete bases) and the inputs of the
base-change reductions. `StrictHenselizationNeron` is not one published statement: it combines two
prints (EGA IV 18.8 and BLR §1.2) and counts (b) under the strict rule. -/
structure ReductLeavesPrinted : Prop where
  neronDVR : NeronSchemeModelExistsDVR
  sga7_3_5 : SemistableUnipotentSH
  sga7_4_7 : RaynaudSemistableSH
  sga7_3_6 : SemistableReductionSH
  sga7_3_3a : SemistablePersistsSH
  sga7_3_3b : IdentityComponentBaseChangeSH
  serreTate2 : SerreTateThm2Complete
  mumford : AvSplit.MumfordTorsionAlgClosed
  strictHenselizationNeron : StrictHenselizationNeron
  mulEtale : AvSplit.T4.MulEtaleAbelianScheme

/-- The base-change reductions that remain glue (4.7's is proved: `raynaudSemistable_of_SH'`). -/
structure ReductPrintedGlue : Prop where
  unipotent : UnipotentFromSH
  reduction : ReductionFromSH
  persists : PersistsFromSH
  identityComponent : IdentityComponentFromSH
  serreTate : SerreTateFromComplete

/-- **reduct-split's `ReductLeaves` from the printed-base leaves.** -/
theorem reductLeaves_of_printed (l : ReductLeavesPrinted) (g : ReductPrintedGlue) : ReductLeaves :=
  { neronDVR := l.neronDVR
    sga7_3_5 := g.unipotent l.sga7_3_5
    sga7_4_7 := raynaudSemistable_of_SH' l.sga7_4_7 l.strictHenselizationNeron l.mulEtale
    sga7_3_6 := g.reduction l.sga7_3_6
    sga7_3_3a := g.persists l.sga7_3_3a
    sga7_3_3b := g.identityComponent l.sga7_3_3b
    serreTate2 := g.serreTate l.serreTate2
    mumford := l.mumford }

end PrintedGlue

section Final

/-- **reduct-split's `ReductGlue` from published leaves plus one glue.** Three of its four fields are
proved here: `FixedTorsionRationalImperfect` from the bundle leaf `MulEtaleAbelianScheme`;
`SemistableLocalGlobal` from the new leaf `NeronLocalizesDVR` (BLR §1.2 Prop. 4);
`SemistableAlmostAll` from the kernel's `AbVarSpreadsOut` (proved in the kernel from the EGA IV leaves,
`abVarSpreadsOut_of_ega4`) and the leaf candidate `ProperSmoothGenConnected`. The fourth,
`SemistableNeronBaseChangeLocalGlobal`, is passed through (see `SS2` below). -/
theorem reductGlue_of (hE : AvSplit.T4.MulEtaleAbelianScheme) (hL : NeronLocalizesDVR)
    (hsp : FrobPiecesNeron.AbVarSpreadsOut) (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hSS2 : SemistableNeronBaseChangeLocalGlobal) : ReductGlue :=
  { fixedTorsionImperfect := fixedTorsionRationalImperfect_of_mulEtale hE
    localGlobal := semistableLocalGlobal_leaf hL
    almostAll := semistableAlmostAll_of hsp hc
    ss2LocalGlobal := hSS2 }

/-- **reduct-split's seven rows from the printed-base leaves**, the new leaves, and the remaining
glue (`ReductPrintedGlue`, `SemistableNeronBaseChangeLocalGlobal`). -/
theorem rows_of_printed (l : ReductLeavesPrinted) (g : ReductPrintedGlue) (hL : NeronLocalizesDVR)
    (hsp : FrobPiecesNeron.AbVarSpreadsOut) (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hSS2 : SemistableNeronBaseChangeLocalGlobal) (hF5 : ZInQ.HeightSplit.FaltingsLemma5) :
    PkgI2.RaynaudCriterion.{0} ∧ PkgI2.SerreTatePotentialGood.{0} ∧
      PkgI2.GrothendieckMonodromy.{0} ∧ ZInQ.HeightSplit.SemistableReductionThm ∧
      ZInQ.HeightSplit.SemistableNeronBaseChange ∧ ZInQ.HeightSplit.SemistablePersists ∧
      ZInQ.HeightSplit.FaltingsLemma5BC :=
  rows_of_leaves (reductLeaves_of_printed l g) (reductGlue_of l.mulEtale hL hsp hc hSS2) hF5

end Final


section SS2Lemmas

variable {K : Type} [Field K]

/-- An open immersion of a scheme over `K` into an abelian variety, from a scheme isomorphic to
it, is an isomorphism (kernel's `isIso_of_openImmersion_self`, conjugated). -/
theorem isIso_of_openImmersion_of_iso (B : PkgI3.AbVar K) {T N : Over (Spec (CommRingCat.of K))}
    (eT : T ≅ B.X) (eN : N ≅ B.X) (f : T ⟶ N) [IsOpenImmersion f.left] : IsIso f := by
  let h : B.X ⟶ B.X := eT.inv ≫ f ≫ eN.hom
  haveI : IsIso eT.inv.left := Functor.map_isIso (Over.forget _) eT.inv
  haveI : IsIso eN.hom.left := Functor.map_isIso (Over.forget _) eN.hom
  haveI : IsOpenImmersion h.left := by
    show IsOpenImmersion (eT.inv.left ≫ f.left ≫ eN.hom.left)
    infer_instance
  haveI : IsIso h := by
    have hw : h.left ≫ B.X.hom = B.X.hom := Over.w h
    haveI : UniversallyClosed (h.left ≫ B.X.hom) := by rw [hw]; infer_instance
    haveI : UniversallyClosed h.left := UniversallyClosed.of_comp_of_isSeparated h.left B.X.hom
    haveI : IrreducibleSpace B.X.left :=
      GeometricallyIrreducible.irreducibleSpace_of_subsingleton B.X.hom
    have hrange : Set.range h.left = Set.univ := by
      have hc : IsClosed (Set.range h.left) := h.left.isClosedMap.isClosed_range
      have ho : IsOpen (Set.range h.left) := h.left.isOpenEmbedding.isOpen_range
      obtain ⟨x⟩ := (inferInstance : Nonempty B.X.left)
      exact IsClopen.eq_univ ⟨hc, ho⟩ ⟨h.left x, x, rfl⟩
    haveI : Surjective h.left := ⟨fun y => by
      have : y ∈ Set.range h.left := hrange ▸ Set.mem_univ y
      exact this⟩
    haveI : IsIso h.left := (isIso_iff_isOpenImmersion_and_surjective h.left).mpr ⟨‹_›, ‹_›⟩
    haveI : IsIso ((Over.forget _).map h) := inferInstanceAs (IsIso h.left)
    exact isIso_of_reflects_iso h (Over.forget _)
  have : f = eT.hom ≫ h ≫ eN.inv := by
    simp only [h, Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rw [this]
  infer_instance

/-- **Two maps into a Néron model with isomorphic generic fibres differ by an automorphism**; so if
one is an open immersion, so is the other. -/
theorem isOpenImmersion_of_neron {B : PkgI3.AbVar K} {O : ValuationSubring K}
    (N : GroupModelO B O) (hN : N.IsNeronModel) (T : Over (Spec (CommRingCat.of O))) [Smooth T.hom]
    (j₁ j₂ : T ⟶ N.G) [IsOpenImmersion j₂.left] (h₁ : IsIso ((Over.pullback (jO O)).map j₁))
    (h₂ : IsIso ((Over.pullback (jO O)).map j₂)) : IsOpenImmersion j₁.left := by
  let F := Over.pullback (jO O)
  let gg : F.obj N.G ⟶ F.obj N.G := inv (F.map j₂) ≫ F.map j₁
  let gg' : F.obj N.G ⟶ F.obj N.G := inv (F.map j₁) ≫ F.map j₂
  obtain ⟨β, hβ⟩ := (hN N.G).2 (gg ≫ N.gen.hom)
  obtain ⟨β', hβ'⟩ := (hN N.G).2 (gg' ≫ N.gen.hom)
  simp only at hβ hβ'
  have hβ0 : F.map β = gg := (cancel_mono N.gen.hom).mp hβ
  have hβ0' : F.map β' = gg' := (cancel_mono N.gen.hom).mp hβ'
  have e1 : β ≫ β' = 𝟙 _ := (hN N.G).1 (by
    simp only
    rw [Functor.map_comp, CategoryTheory.Functor.map_id, Category.id_comp, hβ0, hβ0']
    simp [gg, gg'])
  have e2 : β' ≫ β = 𝟙 _ := (hN N.G).1 (by
    simp only
    rw [Functor.map_comp, CategoryTheory.Functor.map_id, Category.id_comp, hβ0, hβ0']
    simp [gg, gg'])
  have hj : j₁ = j₂ ≫ β := (hN T).1 (by
    simp only
    rw [Functor.map_comp, Category.assoc, hβ0]
    simp [gg]
    rfl)
  haveI : IsIso β := ⟨⟨β', e1, e2⟩⟩
  haveI : IsIso β.left := Functor.map_isIso (Over.forget _) β
  rw [hj, Over.comp_left]
  infer_instance

end SS2Lemmas


section SS2Main

open ZInQ.HeightSplit ZInQ.DefFaltings

/-- **A morphism into a Néron model compatible with homomorphic generic identifications is a
homomorphism** (abstract form of the argument of `neronO_unique`). -/
theorem isMonHom_of_ext {C D : Type*} [Category C] [CartesianMonoidalCategory C] [Category D]
    [CartesianMonoidalCategory D] (F : C ⥤ D) [F.Monoidal] {N₁ N₂ : C} [GrpObj N₁] [GrpObj N₂]
    {B : D} [GrpObj B] (e₁ : F.obj N₁ ⟶ B) (e₂ : F.obj N₂ ⟶ B)
    (h₁ : letI : GrpObj (F.obj N₁) := Functor.grpObjObj; IsMonHom e₁)
    (h₂ : letI : GrpObj (F.obj N₂) := Functor.grpObjObj; IsMonHom e₂)
    (inj1 : Function.Injective fun f : 𝟙_ C ⟶ N₂ => F.map f ≫ e₂)
    (inj2 : Function.Injective fun f : N₁ ⊗ N₁ ⟶ N₂ => F.map f ≫ e₂)
    (f : N₁ ⟶ N₂) (hf : F.map f ≫ e₂ = e₁) : IsMonHom f := by
  letI : GrpObj (F.obj N₁) := Functor.grpObjObj
  letI : GrpObj (F.obj N₂) := Functor.grpObjObj
  have key : ∀ {T : C} (a : T ⟶ N₁), F.map (a ≫ f) ≫ e₂ = F.map a ≫ e₁ := by
    intro T a
    rw [Functor.map_comp, Category.assoc, hf]
  refine ⟨?_, ?_⟩
  · change η[N₁] ≫ f = η[N₂]
    rw [MonObj.one_eq_one, MonObj.one_eq_one]
    apply inj1
    simp only
    rw [key, Functor.map_one, Functor.map_one, MonObj.one_comp, MonObj.one_comp]
  · change μ[N₁] ≫ f = (f ⊗ₘ f) ≫ μ[N₂]
    rw [MonObj.mul_eq_mul, MonObj.mul_eq_mul, MonObj.comp_mul]
    apply inj2
    simp only
    rw [key, Functor.map_mul, Functor.map_mul, MonObj.mul_comp, MonObj.mul_comp]
    simp only [tensorHom_fst, tensorHom_snd]
    rw [key, key]

/-- **LEAF `IdentityComponentOL`** (SGA 3 I, Exp. VI_B, Thm. 3.10: a smooth group scheme `G` over
`S` has an open subgroup scheme `G⁰` whose fibres are the identity components of the fibres of
`G`; number UNVERIFIED). Over `𝓞_L`: every group model `𝒢` has an open subgroup group model `𝒢⁰`
whose geometric fibres at the maximal ideals are connected (`𝒢⁰` is quasi-compact since `Spec 𝓞_L`
and `𝒢` are noetherian; its generic fibre is that of `𝒢`, `A_L` being connected). -/
def IdentityComponentOL : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L), ∃ (𝒢₀ : GroupModel A L) (i : 𝒢₀.G ⟶ 𝒢.G), IsOpenImmersion i.left ∧
      IsMonHom i ∧ ∀ (𝔭 : Ideal (𝓞 L)) [𝔭.IsMaximal], ConnectedSpace (geomFibre 𝒢₀ 𝔭).left

/-- **LEAF `OpenImmersionOfLocal`** (EGA IV₃ 8.10.5, the item for open immersions, applied to
`Spec (𝓞_L)_𝔭 = lim U` over the open neighbourhoods of `𝔭`; numbers UNVERIFIED). A morphism of
smooth, separated, quasi-compact (so finitely presented) `𝓞_L`-schemes that is an open immersion
after base change to every discrete valuation ring `O = (𝓞_L)_𝔭` of `L` is an open immersion: it is
one over a neighbourhood of every closed point, these cover `Spec 𝓞_L`, and open immersions are
local on the target. -/
def OpenImmersionOfLocal : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (X Y : Over (Spec (CommRingCat.of (𝓞 L))))
    [Smooth X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [Smooth Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (f : X ⟶ Y),
    (∀ (O : ValuationSubring L) [IsDiscreteValuationRing O],
      IsOpenImmersion ((Over.pullback (gO O)).map f).left) → IsOpenImmersion f.left

end SS2Main


section SS2Final

open ZInQ.HeightSplit ZInQ.DefFaltings

/-- `pbCompIso` as a natural isomorphism. -/
noncomputable def pbCompNat {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (hfg : f ≫ g = h) :
    (Over.pullback g).mapGrp ⋙ (Over.pullback f).mapGrp ≅ (Over.pullback h).mapGrp :=
  Functor.mapGrpCompIso.symm ≪≫ Functor.mapGrpNatIso (Over.pullbackComp f g).symm ≪≫
    Functor.mapGrpNatIso (eqToIso (show Over.pullback (f ≫ g) = Over.pullback h by rw [hfg]))

theorem pbCompIso_eq {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h)
    (𝒢 : Grp (Over Z)) : pbCompIso f g h hfg 𝒢 = (pbCompNat f g h hfg).app 𝒢 := by
  rw [pbCompIso_def]; rfl

theorem pbCompIso_natural {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (hfg : f ≫ g = h) {𝒢 𝒢' : Grp (Over Z)} (φ : 𝒢 ⟶ 𝒢') :
    (Over.pullback f).map ((Over.pullback g).map φ.hom.hom) ≫ (isoX (pbCompIso f g h hfg 𝒢')).hom =
      (isoX (pbCompIso f g h hfg 𝒢)).hom ≫ (Over.pullback h).map φ.hom.hom := by
  have := congrArg (fun ψ => ψ.hom.hom) ((pbCompNat f g h hfg).hom.naturality φ)
  simp only [pbCompIso_eq]
  exact this

theorem pbCompIso_natural' {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (hfg : f ≫ g = h) {G G' : Over Z} [GrpObj G] [GrpObj G'] (φ : G ⟶ G') [IsMonHom φ] :
    (Over.pullback f).map ((Over.pullback g).map φ) ≫ (isoX (pbCompIso f g h hfg (Grp.mk G'))).hom =
      (isoX (pbCompIso f g h hfg (Grp.mk G))).hom ≫ (Over.pullback h).map φ :=
  pbCompIso_natural f g h hfg (Grp.homMk (A := Grp.mk G) (B := Grp.mk G') φ)

end SS2Final


section SS2Theorem

open ZInQ.HeightSplit ZInQ.DefFaltings

/-- **GLUE `SemistableNeronBaseChangeLocalGlobal` (reduct-split), PROVED** from the leaves
`IdentityComponentOL` (SGA 3 VI_B 3.10), `OpenImmersionOfLocal` (EGA IV₃ 8.10.5) and
`NeronLocalizesDVR` (BLR §1.2 Prop. 4), plus reduct-split's local leaf
`IdentityComponentBaseChangeDVR` (its hypothesis). `𝒱 = 𝒩 ×_{𝓞_L} 𝓞_{L'}`, `𝒰 = 𝒩⁰ ×_{𝓞_L} 𝓞_{L'}`,
and `𝒰 → 𝒩'` is the extension of the generic identification; it is an open immersion after
localization at every DVR `O'` of `L'` because it differs from the local leaf's open immersion by an
automorphism of the Néron model (`isOpenImmersion_of_neron`). -/
theorem semistableNeronBaseChangeLocalGlobal_of (hIC : IdentityComponentOL)
    (hOI : OpenImmersionOfLocal) (hL : NeronLocalizesDVR) :
    SemistableNeronBaseChangeLocalGlobal := by
  intro h33b _ K _ _ A L _ _ _ 𝒩 h𝒩 hss L' _ _ _ _ _ 𝒩' h𝒩'
  obtain ⟨𝒢₀, i, hoi, hmi, hconn⟩ := hIC K A L 𝒩
  haveI : FiniteDimensional L L' := Module.Finite.of_restrictScalars_finite ℚ L L'
  let gLL : Spec (CommRingCat.of (𝓞 L')) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L')))
  let 𝒱 : GroupModel A L' := ZInQ.H5Glue.GroupModel.baseChange L L' 𝒩
  let 𝒰 : GroupModel A L' := ZInQ.H5Glue.GroupModel.baseChange L L' 𝒢₀
  let jL' : Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of (𝓞 L')) :=
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L') L'))
  letI : GrpObj ((Over.pullback jL').obj 𝒰.G) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback jL').obj 𝒩'.G) := Functor.grpObjObj
  obtain ⟨j, hj⟩ := (h𝒩' 𝒰.G).2 𝒰.gen.hom
  simp only at hj
  haveI : Smooth (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L'))))).hom :=
    ZInQ.Contrib.NeronC.smooth_tensorUnit _
  haveI : Smooth (𝒰.G ⊗ 𝒰.G).hom := ZInQ.Contrib.NeronC.smooth_tensor _ _ inferInstance inferInstance
  have hjm : IsMonHom j :=
    isMonHom_of_ext (Over.pullback jL') 𝒰.gen.hom 𝒩'.gen.hom 𝒰.gen_hom 𝒩'.gen_hom
      (h𝒩' _).1 (h𝒩' _).1 j hj
  haveI := hmi
  letI : GrpObj ((Over.pullback gLL).obj 𝒢₀.G) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback gLL).obj 𝒩.G) := Functor.grpObjObj
  refine ⟨𝒰, 𝒱, ⟨Iso.refl _, (inferInstance : IsMonHom (𝟙 𝒱.G))⟩, ⟨j, ?_, hjm⟩,
    ⟨(Over.pullback gLL).map i, ZInQ.H5Glue.isOpenImmersion_pullback_map _ i,
      (inferInstance : IsMonHom ((Over.pullback gLL).map i))⟩⟩
  -- `j` is an open immersion: check at every DVR `O'` of `L'`
  refine hOI L' 𝒰.G 𝒩'.G j (fun O' _ => ?_)
  let O : ValuationSubring L := O'.comap (algebraMap L L')
  haveI : IsDiscreteValuationRing O := dvrComapFinite L L' O' inferInstance
  haveI := center_isMaximal O
  have hO : O'.comap (algebraMap L L') = O := rfl
  have hssO : HasSemistableReduction (A.baseChange L) O :=
    (semistableLocalGlobal_leaf hL K A L 𝒩 h𝒩).mp hss O inferInstance
  let N := toO 𝒩' O'
  have hN : N.IsNeronModel := hL K A L' 𝒩' h𝒩' O'
  let N' := N.transport (bcbcIso A L L') (bcbcIso_isMonHom A L L')
  have hN' : N'.IsNeronModel := N.transport_isNeronModel _ _ hN
  let U := (Over.pullback (gO O)).obj 𝒢₀.G
  letI : GrpObj U := Functor.grpObjObj
  letI : GrpObj ((Over.pullback (gO O)).obj 𝒩.G) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback (gO O)).obj 𝒢₀.G) := Functor.grpObjObj
  have hmiO : IsMonHom ((Over.pullback (gO O)).map i) := inferInstance
  -- connected fibres of `U`
  have hcg : ConnectedSpace ((Over.pullback (jO O)).obj U).left := by
    let e := isoX (pbCompIso (jO O) (gO O) _ (jO_gO O) (Grp.mk 𝒢₀.G)) ≪≫ 𝒢₀.gen
    haveI : IrreducibleSpace (A.baseChange L).X.left :=
      GeometricallyIrreducible.irreducibleSpace_of_subsingleton (A.baseChange L).X.hom
    exact (Scheme.homeoOfIso ((Over.forget _).mapIso e)).connectedSpace_iff.mpr
      (inferInstanceAs (ConnectedSpace (A.baseChange L).X.left))
  have hcs : ConnectedSpace ((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap O (ResBarO O))))).obj U).left := by
    let e := isoX (fibreIso 𝒢₀ O)
    haveI := hconn (center O)
    have h1 : ConnectedSpace ((Over.pullback (sσ (barIso O))).obj (geomFibre 𝒢₀ (center O))).left :=
      (Scheme.homeoOfIso (asIso (pullback.fst (geomFibre 𝒢₀ (center O)).hom
        (sσ (barIso O))))).connectedSpace_iff.mpr inferInstance
    exact (Scheme.homeoOfIso ((Over.forget _).mapIso e)).connectedSpace_iff.mp h1
  obtain ⟨j', hj'o, hj'm⟩ := h33b L O L' O' hO (A.baseChange L) hssO (toO 𝒩 O)
    (hL K A L 𝒩 h𝒩 O) N' hN' U ((Over.pullback (gO O)).map i)
    (ZInQ.H5Glue.isOpenImmersion_pullback_map _ i) hmiO hcg hcs
  -- compare `T = 𝒰 ×_{𝓞_{L'}} O'` with `U ×_O O'`
  have hsq : gO O' ≫ gLL = Spec.map (CommRingCat.ofHom (comapHom hO)) ≫ gO O := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  let c := isoX (pbCompIso (gO O') gLL _ hsq (Grp.mk 𝒢₀.G)) ≪≫
    (isoX (pbCompIso (Spec.map (CommRingCat.ofHom (comapHom hO))) (gO O) _ rfl (Grp.mk 𝒢₀.G))).symm
  let T := (Over.pullback (gO O')).obj 𝒰.G
  haveI : Smooth T.hom := by change Smooth (pullback.snd 𝒰.G.hom (gO O')); infer_instance
  let j₂ : T ⟶ N.G := c.hom ≫ j'
  haveI : IsOpenImmersion j₂.left := by
    have h1 : IsOpenImmersion c.hom.left := by
      haveI : IsIso c.hom.left := Functor.map_isIso (Over.forget _) c.hom
      infer_instance
    have h2 : IsOpenImmersion j'.left := hj'o
    show IsOpenImmersion (c.hom.left ≫ j'.left)
    exact @IsOpenImmersion.comp _ _ _ _ _ h1 h2
  -- generic identification of `T`
  let eT : (Over.pullback (jO O')).obj T ≅ (A.baseChange L').X :=
    isoX (pbCompIso (jO O') (gO O') _ (jO_gO O') (Grp.mk 𝒰.G)) ≪≫ 𝒰.gen
  have h₂ : IsIso ((Over.pullback (jO O')).map j₂) := by
    haveI : IsOpenImmersion ((Over.pullback (jO O')).map j₂).left :=
      ZInQ.H5Glue.isOpenImmersion_pullback_map _ j₂
    exact isIso_of_openImmersion_of_iso (A.baseChange L') eT N.gen _
  have hcomp := pbCompIso_natural' (jO O') (gO O') _ (jO_gO O') j
  have hjL : IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L') L')))).map j) := by
    have : IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L') L')))).map j ≫
        𝒩'.gen.hom) := by
      rw [hj]; exact Iso.isIso_hom 𝒰.gen
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (Iso.isIso_hom 𝒩'.gen) this
  have h₁ : IsIso ((Over.pullback (jO O')).map ((Over.pullback (gO O')).map j)) := by
    have : IsIso ((Over.pullback (jO O')).map ((Over.pullback (gO O')).map j) ≫
        (isoX (pbCompIso (jO O') (gO O') _ (jO_gO O') (Grp.mk 𝒩'.G))).hom) := by
      rw [hcomp]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) hjL
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (Iso.isIso_hom _) this
  exact isOpenImmersion_of_neron N hN T ((Over.pullback (gO O')).map j) j₂ h₁ h₂

end SS2Theorem

section Final2

/-- **All four glue Props of reduct-split's `ReductGlue`, proved from published leaves**:
`MulEtaleAbelianScheme` (bundle leaf, BLR 7.3/2), `NeronLocalizesDVR` (BLR §1.2 Prop. 4),
`IdentityComponentOL` (SGA 3 VI_B 3.10), `OpenImmersionOfLocal` (EGA IV₃ 8.10.5), and the kernel's
`AbVarSpreadsOut` (proved in the kernel from EGA IV leaves) and leaf candidate
`ProperSmoothGenConnected` (Zariski connectedness). -/
theorem reductGlue_leaves (hE : AvSplit.T4.MulEtaleAbelianScheme) (hL : NeronLocalizesDVR)
    (hIC : IdentityComponentOL) (hOI : OpenImmersionOfLocal)
    (hsp : FrobPiecesNeron.AbVarSpreadsOut) (hc : FrobPiecesNeron.ProperSmoothGenConnected) :
    ReductGlue :=
  reductGlue_of hE hL hsp hc (semistableNeronBaseChangeLocalGlobal_of hIC hOI hL)

/-- The further hypotheses of this task's general route (besides reduct-split's `ReductLeaves`).
Only `NeronLocalizesDVR`, `IdentityComponentOL` and `OpenImmersionOfLocal` are new leaves, each
counted (b) under the strict rule; `MulEtaleAbelianScheme` is an existing bundle leaf, and
`AbVarSpreadsOut` and `ProperSmoothGenConnected` are kernel theorems (`abVarSpreadsOut_of_ega4`,
`properSmoothGenConnected_of_zariski4`). -/
structure ReductGlueLeaves : Prop where
  mulEtale : AvSplit.T4.MulEtaleAbelianScheme
  neronLocalizes : NeronLocalizesDVR
  identityComponent : IdentityComponentOL
  openImmersionOfLocal : OpenImmersionOfLocal
  spreadsOut : FrobPiecesNeron.AbVarSpreadsOut
  properSmoothGenConnected : FrobPiecesNeron.ProperSmoothGenConnected

/-- **reduct-split's seven rows with no project glue left**: from `ReductLeaves`, the new leaves and
`HeightSplit.FaltingsLemma5` (t10 is not among the rows). -/
theorem rows_of_leaves_noGlue (l : ReductLeaves) (n : ReductGlueLeaves)
    (hF5 : ZInQ.HeightSplit.FaltingsLemma5) :
    PkgI2.RaynaudCriterion.{0} ∧ PkgI2.SerreTatePotentialGood.{0} ∧
      PkgI2.GrothendieckMonodromy.{0} ∧ ZInQ.HeightSplit.SemistableReductionThm ∧
      ZInQ.HeightSplit.SemistableNeronBaseChange ∧ ZInQ.HeightSplit.SemistablePersists ∧
      ZInQ.HeightSplit.FaltingsLemma5BC :=
  rows_of_leaves l (reductGlue_leaves n.mulEtale n.neronLocalizes n.identityComponent
    n.openImmersionOfLocal n.spreadsOut n.properSmoothGenConnected) hF5

end Final2


section Persists

/-- `O₁ ⊇ O` is a strict henselization of `O` for the purposes here: a strictly henselian DVR over
`O` with algebraic residue extension, along which Néron models base change. -/
def IsSHNeronExt {K K₁ : Type} [Field K] [Field K₁] [Algebra K K₁] (O : ValuationSubring K)
    (O₁ : ValuationSubring K₁) (hO : O₁.comap (algebraMap K K₁) = O) : Prop :=
  IsStrictlyHenselianDVR O₁ ∧
    (letI := (resMap hO).toAlgebra
     Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O₁)) ∧
    ∀ (A : PkgI3.AbVar K) (𝒩 : GroupModelO A O), 𝒩.IsNeronModel → (bcDVR hO 𝒩).IsNeronModel

/-- **LEAF candidate `StrictHenselizationPair`** (strict henselization along a finite extension:
EGA IV₄ 18.8.10 and 18.6.8 (`O' ⊗_O O^sh` is a finite product of strictly henselian local rings, one
of which is `O'^sh`), Stacks Tag 05WR, with BLR §1.2 Prop. 2 for the Néron models; numbers
UNVERIFIED). For a finite `K'/K` and a DVR `O' ⊆ K'` over a DVR `O ⊆ K` there are strict
henselizations `P ⊆ E` of `O` and `P' ⊆ E'` of `O'` (in the sense of `IsSHNeronExt`) with `E'/E`
finite and `P'` over `P`. -/
def StrictHenselizationPair : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'] (hO : O'.comap (algebraMap K K') = O),
    ∃ (E E' : Type) (_ : Field E) (_ : Field E') (_ : Algebra K E) (_ : Algebra K' E')
      (_ : Algebra E E') (_ : Algebra K E') (_ : IsScalarTower K E E') (_ : IsScalarTower K K' E')
      (_ : FiniteDimensional E E') (P : ValuationSubring E) (P' : ValuationSubring E')
      (hP : P.comap (algebraMap K E) = O) (hP' : P'.comap (algebraMap K' E') = O'),
      IsSHNeronExt O P hP ∧ IsSHNeronExt O' P' hP' ∧ P'.comap (algebraMap E E') = P

/-- **SGA 7 IX 3.3 (first assertion) over a general DVR from the strictly henselian form.** -/
theorem persistsFromSH_of (hPair : StrictHenselizationPair) : PersistsFromSH := by
  intro hSH K _ O _ K' _ _ _ O' _ hO A hA 𝒩' h𝒩'
  obtain ⟨E, E', _, _, _, _, _, _, _, _, _, P, P', hP, hP', ⟨hSHP, halgP, hbcP⟩,
    ⟨hSHP', halgP', hbcP'⟩, hPP'⟩ := hPair K O K' O' hO
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

end Persists

section Printed2

/-- The base-change reductions that remain glue after `persistsFromSH_of` and
`raynaudSemistable_of_SH'`. -/
structure ReductPrintedGlue' : Prop where
  unipotent : UnipotentFromSH
  reduction : ReductionFromSH
  identityComponent : IdentityComponentFromSH
  serreTate : SerreTateFromComplete

/-- **reduct-split's `ReductLeaves` from the printed-base leaves**, the strict-henselization leaves,
and four base-change glue Props. -/
theorem reductLeaves_of_printed' (l : ReductLeavesPrinted) (hPair : StrictHenselizationPair)
    (g : ReductPrintedGlue') : ReductLeaves :=
  reductLeaves_of_printed l ⟨g.unipotent, g.reduction, persistsFromSH_of hPair,
    g.identityComponent, g.serreTate⟩

end Printed2

open ZInQ.Contrib.AbVarBC

section Unipotent

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]

/-- An automorphism of `Ω/K` fixing the intermediate field `E` pointwise, as an automorphism of
`Ω/E`. -/
def toE (E : IntermediateField K Ω) (σ : Ω ≃ₐ[K] Ω) (h : ∀ x ∈ E, σ x = x) : Ω ≃ₐ[E] Ω :=
  { σ with commutes' := fun a => h a a.2 }

theorem toE_restrictScalars (E : IntermediateField K Ω) (σ : Ω ≃ₐ[K] Ω) (h : ∀ x ∈ E, σ x = x) :
    (toE E σ h).restrictScalars K = σ := by
  ext x; rfl

theorem isInertia_toE (E : IntermediateField K Ω) (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω)
    (h : ∀ x ∈ E, σ x = x) (hσ : IsInertia w σ) : IsInertia w (toE E σ h) := by
  obtain ⟨h1, h2⟩ := hσ
  exact ⟨h1, h2⟩


/-- **LEAF candidate `StrictHenselizationInside`** (the strict henselization of `O` realized inside an
algebraic closure at a place `w`: the valuation ring of `w` on the inertia field `T` of `w`; Stacks
Tags 0BSK–0BSL / Raynaud, *Anneaux locaux henséliens*, VIII; Néron base change by BLR §1.2 Prop. 2;
all locators UNVERIFIED). For a DVR `O ⊆ K`, an algebraic closure `Ω` and a valuation ring `w` of `Ω`
over `O`, there is an intermediate field `E` (the inertia field) such that `w ∩ E` is a strict
henselization of `O` (`IsSHNeronExt`) and every `σ` in the inertia group of `w` fixes `E`
pointwise. -/
def StrictHenselizationInside : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O →
    ∃ (E : IntermediateField K Ω) (hE : (w.comap (algebraMap E Ω)).comap (algebraMap K E) = O),
      IsSHNeronExt O (w.comap (algebraMap E Ω)) hE ∧
      ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → ∀ x ∈ E, σ x = x

/-- **SGA 7 IX 3.5 over a general DVR from the strictly henselian form**: apply it to `A_E` over
the inertia field `E`; `T_ℓ(A_E) ≅ T_ℓ(A)` over `Ω` compatibly with `σ` (kernel `bcPt_galAct`). -/
theorem unipotentFromSH_of (hIn : StrictHenselizationInside) : UnipotentFromSH := by
  intro hSH K _ O _ Ω _ _ _ w hw A hA ℓ _ hℓ σ hσ t
  obtain ⟨E, hE, ⟨hSHP, halg, hbc⟩, hfix⟩ := hIn K O Ω w hw
  haveI : IsDiscreteValuationRing (w.comap (algebraMap E Ω)) := hSHP.1
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) E⟩
  have hAE : HasSemistableReduction (A.baseChange E) (w.comap (algebraMap E Ω)) := by
    obtain ⟨𝒩, h𝒩, hs⟩ := hA
    exact ⟨bcDVR hE 𝒩, hbc A 𝒩 h𝒩, (isSemistable_bcDVR_iff hE halg 𝒩).mp hs⟩
  have hℓP : IsUnit (ℓ : w.comap (algebraMap E Ω)) := by
    have := hℓ.map (comapHom hE)
    rwa [map_natCast] at this
  let σ₁ := toE E σ (hfix σ hσ)
  have hσ₁ : IsInertia w σ₁ := isInertia_toE E w σ (hfix σ hσ) hσ
  let φ : TΩ (A.baseChange E) Ω ℓ →ₗ[ℤ_[ℓ]] TΩ A Ω ℓ :=
    PkgI3.Tate.map (MonoidHom.toAdditive (bcPt A Ω).toMonoidHom)
  let ψ : TΩ A Ω ℓ →ₗ[ℤ_[ℓ]] TΩ (A.baseChange E) Ω ℓ :=
    PkgI3.Tate.map (MonoidHom.toAdditive (bcPt A Ω).symm.toMonoidHom)
  have hφψ : φ (ψ t) = t := by
    apply Subtype.ext
    funext n
    change Additive.ofMul (bcPt A Ω ((bcPt A Ω).symm (Additive.toMul (t.1 n)))) = t.1 n
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hcomm : ∀ s, φ (galTΩ (A.baseChange E) ℓ σ₁ s) = galTΩ A ℓ σ (φ s) := by
    intro s
    apply Subtype.ext
    funext n
    change Additive.ofMul (bcPt A Ω ((A.baseChange E).galAct σ₁ (Additive.toMul (s.1 n)))) =
      Additive.ofMul (A.galAct σ (bcPt A Ω (Additive.toMul (s.1 n))))
    rw [bcPt_galAct, toE_restrictScalars]
  have key := hSH E (w.comap (algebraMap E Ω)) hSHP Ω w rfl (A.baseChange E) hAE ℓ hℓP σ₁ hσ₁
    (ψ t)
  have := congrArg φ key
  simp only [map_add, map_sub, map_nsmul, map_zero, hcomm, hφψ] at this
  exact this

end Unipotent

section Printed3

/-- The base-change reductions that remain glue (3.6, 3.3 second assertion, Serre–Tate). -/
structure ReductPrintedGlue'' : Prop where
  reduction : ReductionFromSH
  identityComponent : IdentityComponentFromSH
  serreTate : SerreTateFromComplete

/-- **reduct-split's `ReductLeaves` from the printed-base leaves**, three strict-henselization
leaves, and three base-change glue Props. -/
theorem reductLeaves_of_printed'' (l : ReductLeavesPrinted) (hPair : StrictHenselizationPair)
    (hIn : StrictHenselizationInside) (g : ReductPrintedGlue'') : ReductLeaves :=
  reductLeaves_of_printed l ⟨unipotentFromSH_of hIn, g.reduction, persistsFromSH_of hPair,
    g.identityComponent, g.serreTate⟩

end Printed3

end ReductGlue
