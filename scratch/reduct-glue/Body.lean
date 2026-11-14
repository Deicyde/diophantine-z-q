import ReductSplitBase

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

end ReductGlue
