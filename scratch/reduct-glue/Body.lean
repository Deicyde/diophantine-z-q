import ReductSplitBase
import ZInQKernel.Contrib.CloudW03NeronSurj.Main
import ZInQKernel.Contrib.FrobChain.Pieces

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

open NumberField

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
noncomputable def pbCompIso {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
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
end ReductGlue
