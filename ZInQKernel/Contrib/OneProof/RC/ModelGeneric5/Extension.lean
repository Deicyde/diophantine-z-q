import ZInQKernel.Contrib.OneProof.RC.ModelGeneric5.RationalChart
import ZInQKernel.Contrib.OneProof.RC.ModelNeron.GoodRow
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric.FibreJ
import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0LevelReducedFibres
import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0LevelFinite

/-! **The integral Atkin–Lehner operator on the pinned model** (`GoodRow.extension`).

Let `R = ℤ_(ℓ)`, `A_R = Pinned.Y0LevelAlgebra h₅ htame h₂` and `A_ℚ = Y0RationalAlgebra h₂`.
The generic-fibre map `levelToRat : A_R → ℚ ⊗_R A_R ≃ A_ℚ` is injective (`A_R` is flat),
every element of `A_ℚ` becomes integral after multiplication by a power of `ℓ`, and
`A_R / ℓA_R` is reduced (the special fibre is reduced, `levelQuotient_fibre_reduced` at the
residue field). The rational Atkin–Lehner ring map `atkinRat hQ` moves `j` to `j_Q`, which
is integral over `ℤ[j]` (the monic modular polynomial `Φ_Q`), and `A_R` is finite over
`R[j]` (`Y0LevelJMap_finite`). Hence `atkinRat hQ` sends `A_R` into its integral closure in
`A_ℚ`, and that closure is `A_R` (`mem_range_of_isIntegral`). The restriction is
`atkinLevel hQ`, and `Wint hQ := Spec (atkinLevel hQ)` over `Spec R`.

`extendsAtkin_Wint`: `ExtendsAtkin (ModelNeron.source h₅ htame h₂) q (Wint …)` for every
`q`, at the exact divisor `q^{v_q(N)}` used by `PMWire.rationalW`. It is proved, not
defined: the generic fibre of `Spec (atkinLevel)` is conjugate to `Spec (atkinRat)`
through the pinned fibre isomorphism, and `atkinRat_openImmersion` identifies that with the
actual `rationalAtkin` on the open.

Provenance: on the spot (c). Integral closure: Atiyah–Macdonald 1969, Ch. 5 (UNVERIFIED).
The normality criterion used is the elementary one (`A` flat over a DVR, `A/πA` reduced
⇒ `A` integrally closed in `A[1/π]`); it needs no regularity theory. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits ModularCurve Polynomial
open scoped TauCeti.ExactDivisor TensorProduct
open WeierstrassCurve.ModelTorsion WeierstrassCurve.ModelLevels
  WeierstrassCurve.ModelLevels.ModelGeneric WeierstrassCurve.ModelLevels.ModelGeneric2
open ZInQ.Manuscript.RC.AtkinRational

namespace ZInQ.Manuscript.RC.ModelGeneric5

attribute [local instance] X0Model.jAlgebra X0Model.finite_jAlgebra

variable {ell N : ℕ} [Fact ell.Prime] [NeZero N]
  (h₅ : 5 ≤ ell) (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N)

/-- The ring structure of the pinned algebra as a subalgebra (the synthesized instance takes a
different path, which defeats unification with `Subalgebra.toSemiring`). -/
noncomputable abbrev levelCommRing : CommRing (Pinned.Y0LevelAlgebra h₅ htame h₂) :=
  Subalgebra.toCommRing _

attribute [local instance 2000] levelCommRing

/-! ### The detector ring -/

omit [NeZero N] in
/-- Every rational number times a power of `ℓ` lies in `ℤ_(ℓ)`. -/
theorem exists_pow_mul_mem_localIntegers (x : ℚ) :
    ∃ (n : ℕ) (r : LocalIntegers ell), algebraMap (LocalIntegers ell) ℚ r = (ell : ℚ) ^ n * x := by
  have hp : ell.Prime := Fact.out
  obtain ⟨k, d, hd, hden⟩ := Nat.exists_eq_pow_mul_and_not_dvd x.den_nz ell hp.ne_one
  have hmem : (d : ℤ) ∈ (integerPrimeIdeal ell).primeCompl := by
    intro h
    apply hd
    exact Int.natCast_dvd_natCast.mp (by simpa [integerPrimeIdeal, Ideal.mem_span_singleton] using h)
  letI := IsLocalization.localization_isScalarTower_of_submonoid_le (LocalIntegers ell) ℚ
    (integerPrimeIdeal ell).primeCompl (nonZeroDivisors ℤ)
    (integerPrimeIdeal ell).primeCompl_le_nonZeroDivisors
  refine ⟨k, IsLocalization.mk' (LocalIntegers ell) x.num ⟨(d : ℤ), hmem⟩, ?_⟩
  have hspec := congrArg (algebraMap (LocalIntegers ell) ℚ)
    (IsLocalization.mk'_spec (LocalIntegers ell) x.num ⟨(d : ℤ), hmem⟩)
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at hspec
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_natCast] at hspec
  have hd0 : (d : ℚ) ≠ 0 := by
    have : d ≠ 0 := by
      rintro rfl
      exact x.den_nz (by simpa using hden)
    exact_mod_cast this
  have hcast : (ell : ℚ) ^ k * d = (x.den : ℚ) := by rw [hden]; push_cast; ring
  have hxd : (ell : ℚ) ^ k * x * d = x.num := by
    rw [mul_assoc, mul_comm x, ← mul_assoc, hcast, mul_comm]
    exact Rat.mul_den_eq_num x
  exact mul_right_cancel₀ hd0 (hspec.trans hxd.symm)

/-! ### The generic-fibre map -/

/-- The generic-fibre map `A_R → ℚ ⊗_R A_R ≃ A_ℚ` of the pinned model. -/
def levelToRat : Pinned.Y0LevelAlgebra h₅ htame h₂ →+* Y0RationalAlgebra h₂ :=
  (Y0RationalBaseChange h₅ htame h₂).toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := LocalIntegers ell) (A := ℚ)).toRingHom

theorem levelToRat_injective : Function.Injective (levelToRat h₅ htame h₂) := by
  letI := Pinned.levelQuotient_flat h₅ htame h₂
  letI := rational_isFractionRing ell
  exact (Y0RationalBaseChange h₅ htame h₂).injective.comp
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective _ ℚ))

theorem levelToRat_algebraMap (r : LocalIntegers ell) :
    levelToRat h₅ htame h₂ (algebraMap _ _ r) =
      algebraMap ℚ (Y0RationalAlgebra h₂) (algebraMap (LocalIntegers ell) ℚ r) := by
  change Y0RationalBaseChange h₅ htame h₂ ((1 : ℚ) ⊗ₜ algebraMap _ _ r) = _
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, ← Algebra.TensorProduct.one_def,
    ← Algebra.algebraMap_eq_smul_one,
    IsScalarTower.algebraMap_apply (LocalIntegers ell) ℚ
      (ℚ ⊗[LocalIntegers ell] Pinned.Y0LevelAlgebra h₅ htame h₂), AlgEquiv.commutes]

theorem levelToRat_J :
    levelToRat h₅ htame h₂ (Pinned.Y0LevelJ h₅ htame h₂) = Y0RationalJ h₂ :=
  Y0RationalBaseChange_j h₅ htame h₂

theorem levelToRat_ell :
    levelToRat h₅ htame h₂ (ell : Pinned.Y0LevelAlgebra h₅ htame h₂) =
      algebraMap ℚ (Y0RationalAlgebra h₂) ell := by
  rw [map_natCast, map_natCast]

/-- Every element of `A_ℚ` times a power of `ℓ` is in the image of `A_R`. -/
theorem exists_pow_mul_mem_range (x : Y0RationalAlgebra h₂) :
    ∃ (n : ℕ) (a : Pinned.Y0LevelAlgebra h₅ htame h₂),
      levelToRat h₅ htame h₂ a = (ell : Y0RationalAlgebra h₂) ^ n * x := by
  let e := Y0RationalBaseChange h₅ htame h₂
  obtain ⟨t, rfl⟩ := e.surjective x
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by rw [map_zero, map_zero, mul_zero]⟩
  | tmul q a =>
    obtain ⟨n, r, hr⟩ := exists_pow_mul_mem_localIntegers (ell := ell) q
    refine ⟨n, r • a, ?_⟩
    change e ((1 : ℚ) ⊗ₜ (r • a)) = _
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one, hr,
      ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, Algebra.smul_def, map_pow, map_natCast]
  | add t t' ht ht' =>
    obtain ⟨n, a, ha⟩ := ht
    obtain ⟨n', a', ha'⟩ := ht'
    refine ⟨n + n', (ell : Pinned.Y0LevelAlgebra h₅ htame h₂) ^ n' * a +
      (ell : Pinned.Y0LevelAlgebra h₅ htame h₂) ^ n * a', ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, ha, ha', map_add]
    ring

/-! ### Reducedness of the special fibre -/

/-- `ℓ A_R` is a radical ideal: the special fibre `𝔽_ℓ ⊗ A_R` is reduced. -/
theorem isRadical_span_ell :
    (Ideal.span {(ell : Pinned.Y0LevelAlgebra h₅ htame h₂)}).IsRadical := by
  have hπ : IsLocalRing.maximalIdeal (LocalIntegers ell) =
      Ideal.span {algebraMap ℤ (LocalIntegers ell) (ell : ℤ)} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := integerPrimeIdeal ell)]
    exact (Ideal.map_span (algebraMap ℤ (LocalIntegers ell)) {(ell : ℤ)}).trans
      (by rw [Set.image_singleton])
  haveI : IsReduced (IsLocalRing.ResidueField (LocalIntegers ell) ⊗[LocalIntegers ell]
      Pinned.Y0LevelAlgebra h₅ htame h₂) :=
    Pinned.levelQuotient_fibre_reduced h₅ htame h₂ (IsLocalRing.ResidueField (LocalIntegers ell))
  have h := isRadical_span_of_residue_reduced (A := Pinned.Y0LevelAlgebra h₅ htame h₂) hπ
  rwa [eq_intCast (algebraMap ℤ (LocalIntegers ell)), map_intCast, Int.cast_natCast] at h

/-! ### The integral operator -/

theorem isIntegral_atkinRat_levelToRat {Q : ℕ} (hQ : Q ∥ N)
    (a : Pinned.Y0LevelAlgebra h₅ htame h₂) :
    letI := (levelToRat h₅ htame h₂).toAlgebra
    IsIntegral (Pinned.Y0LevelAlgebra h₅ htame h₂) (atkinRat h₂ hQ (levelToRat h₅ htame h₂ a)) := by
  letI := (levelToRat h₅ htame h₂).toAlgebra
  letI := neZero_of_exact hQ
  let A := Pinned.Y0LevelAlgebra h₅ htame h₂
  let B := Y0RationalAlgebra h₂
  letI := (Pinned.Y0LevelJMap h₅ htame h₂).toRingHom.toAlgebra
  have hfin := (RingHom.finite_algebraMap (A := Polynomial (LocalIntegers ell))
    (B := Pinned.Y0LevelAlgebra h₅ htame h₂)).mpr (Pinned.Y0LevelJMap_finite h₅ htame h₂)
  refine isIntegral_of_finite (A := A) (algebraMap (Polynomial (LocalIntegers ell)) A) hfin
    ((atkinRat h₂ hQ).comp (levelToRat h₅ htame h₂)) (fun f => ?_) a
  let φ : Polynomial (LocalIntegers ell) →+* B :=
    ((atkinRat h₂ hQ).comp (levelToRat h₅ htame h₂)).comp (Pinned.Y0LevelJMap h₅ htame h₂).toRingHom
  change IsIntegral A (φ f)
  -- `j_Q` is a root of `Φ_Q(X, j)` over `A_R`
  have hX : IsIntegral A (φ X) := by
    have hφX : φ X = atkinRat h₂ hQ (Y0RationalJ h₂) := by
      change atkinRat h₂ hQ (levelToRat h₅ htame h₂ (Pinned.Y0LevelJMap h₅ htame h₂ X)) = _
      rw [show Pinned.Y0LevelJMap h₅ htame h₂ X = Pinned.Y0LevelJ h₅ htame h₂ from aeval_X _,
        levelToRat_J]
    rw [hφX]
    let data := Classical.choice (nonempty_modularPolynomialData Q)
    let g := eval₂RingHom (Int.castRingHom A) (Pinned.Y0LevelJ h₅ htame h₂)
    refine ⟨data.Φ.map g, data.monic.map g, ?_⟩
    rw [eval₂_map]
    have hg : (algebraMap A B).comp g = eval₂RingHom (Int.castRingHom B) (Y0RationalJ h₂) := by
      apply Polynomial.ringHom_ext
      · intro c
        exact RingHom.congr_fun (Subsingleton.elim (((algebraMap A B).comp g).comp C)
          ((eval₂RingHom (Int.castRingHom B) (Y0RationalJ h₂)).comp C)) c
      · change levelToRat h₅ htame h₂ (g X) = _
        simp only [g, coe_eval₂RingHom, eval₂_X]
        exact levelToRat_J h₅ htame h₂
    rw [hg]
    apply ratToField_injective h₂
    rw [map_zero, hom_eval₂, atkinRat_J]
    have hk : (ratToField h₂).comp (eval₂RingHom (Int.castRingHom B) (Y0RationalJ h₂)) =
        eval₂RingHom (Int.castRingHom (modularFunctionField N)) ⟨jq, jq_mem N⟩ := by
      apply Polynomial.ringHom_ext
      · intro c
        exact RingHom.congr_fun (Subsingleton.elim
          (((ratToField h₂).comp (eval₂RingHom (Int.castRingHom B) (Y0RationalJ h₂))).comp C)
          ((eval₂RingHom (Int.castRingHom (modularFunctionField N)) ⟨jq, jq_mem N⟩).comp C)) c
      · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X]
        exact ratToField_J h₂
    rw [hk]
    exact modularPolynomial_eval_field hQ.dvd data
  have hC : ∀ c : LocalIntegers ell, IsIntegral A (φ (C c)) := by
    intro c
    have : φ (C c) = algebraMap A B (algebraMap (LocalIntegers ell) A c) := by
      change atkinRat h₂ hQ (levelToRat h₅ htame h₂ (Pinned.Y0LevelJMap h₅ htame h₂ (C c))) = _
      rw [show Pinned.Y0LevelJMap h₅ htame h₂ (C c) = algebraMap _ A c from aeval_C _ _]
      change atkinRat h₂ hQ (levelToRat h₅ htame h₂ _) = levelToRat h₅ htame h₂ _
      rw [levelToRat_algebraMap]
      exact RingHom.congr_fun (Subsingleton.elim ((atkinRat h₂ hQ).comp (algebraMap ℚ B))
        (algebraMap ℚ B)) _
    rw [this]
    exact isIntegral_algebraMap
  induction f using Polynomial.induction_on with
  | C c => exact hC c
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | monomial n c _ =>
    rw [map_mul, map_pow]
    exact (hC c).mul (hX.pow _)

theorem exists_atkinLevel {Q : ℕ} (hQ : Q ∥ N) (a : Pinned.Y0LevelAlgebra h₅ htame h₂) :
    ∃ c, levelToRat h₅ htame h₂ c = atkinRat h₂ hQ (levelToRat h₅ htame h₂ a) := by
  obtain ⟨n, b, hb⟩ := exists_pow_mul_mem_range h₅ htame h₂ (atkinRat h₂ hQ (levelToRat h₅ htame h₂ a))
  have hp : (ell : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : ell.Prime).ne_zero
  have hunit : IsUnit (levelToRat h₅ htame h₂ (ell : Pinned.Y0LevelAlgebra h₅ htame h₂)) := by
    rw [levelToRat_ell]
    exact (IsUnit.mk0 _ hp).map _
  have hb' : levelToRat h₅ htame h₂ b =
      levelToRat h₅ htame h₂ (ell : Pinned.Y0LevelAlgebra h₅ htame h₂) ^ n *
        atkinRat h₂ hQ (levelToRat h₅ htame h₂ a) := by
    rw [hb, map_natCast]
  exact exists_eq_of_isIntegralElem (levelToRat h₅ htame h₂) (levelToRat_injective h₅ htame h₂)
    (ell : Pinned.Y0LevelAlgebra h₅ htame h₂) hunit (isRadical_span_ell h₅ htame h₂)
    (isIntegral_atkinRat_levelToRat h₅ htame h₂ hQ a) n b hb'

/-- **The integral Atkin–Lehner ring map**: the restriction of `atkinRat hQ` to `A_R`. -/
def atkinLevel {Q : ℕ} (hQ : Q ∥ N) :
    Pinned.Y0LevelAlgebra h₅ htame h₂ →+* Pinned.Y0LevelAlgebra h₅ htame h₂ :=
  restrictRange (levelToRat h₅ htame h₂) (levelToRat_injective h₅ htame h₂) (atkinRat h₂ hQ)
    (exists_atkinLevel h₅ htame h₂ hQ)

theorem levelToRat_atkinLevel {Q : ℕ} (hQ : Q ∥ N) (a : Pinned.Y0LevelAlgebra h₅ htame h₂) :
    levelToRat h₅ htame h₂ (atkinLevel h₅ htame h₂ hQ a) =
      atkinRat h₂ hQ (levelToRat h₅ htame h₂ a) :=
  restrictRange_spec _ _ _ _ a

theorem atkinLevel_algebraMap {Q : ℕ} (hQ : Q ∥ N) (r : LocalIntegers ell) :
    atkinLevel h₅ htame h₂ hQ (algebraMap _ _ r) = algebraMap _ _ r := by
  apply levelToRat_injective h₅ htame h₂
  rw [levelToRat_atkinLevel, levelToRat_algebraMap]
  exact RingHom.congr_fun (Subsingleton.elim ((atkinRat h₂ hQ).comp (algebraMap ℚ _))
    (algebraMap ℚ _)) _

private theorem spec_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom (g.comp f)) := by
  rw [← Spec.map_comp]
  rfl

/-- **The integral Atkin–Lehner operator on the pinned model**, at an exact divisor
`Q ∥ N`: `Spec` of the restriction of the rational Atkin–Lehner ring map. -/
def Wint {Q : ℕ} (hQ : Q ∥ N) : Pinned.Y0Level h₅ htame h₂ ⟶ Pinned.Y0Level h₅ htame h₂ :=
  Over.homMk (Spec.map (CommRingCat.ofHom (atkinLevel h₅ htame h₂ hQ))) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [spec_comp]
    congr 2
    exact RingHom.ext fun r => atkinLevel_algebraMap h₅ htame h₂ hQ r)

/-! ### The generic fibre of `Wint` -/

private theorem spec_to_rat_eq {R : Type} [CommRing R]
    (u v : Spec (.of R) ⟶ Spec (.of ℚ)) : u = v := by
  apply Spec.homEquiv.injective
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

/-- The pinned fibre isomorphism followed by the projection to the integral model is
`Spec` of `levelToRat`. -/
theorem genericIso_inv_fst :
    (ModelNeron.genericIso h₅ htame h₂).inv.left ≫
        pullback.fst (Pinned.Y0Level h₅ htame h₂).hom
          (Spec.map (CommRingCat.ofHom (algebraMap (LocalIntegers ell) ℚ))) =
      Spec.map (CommRingCat.ofHom (levelToRat h₅ htame h₂)) := by
  simp only [ModelNeron.genericIso, Y0RationalFibreIso, detectorFibreIso, Iso.trans_inv,
    Over.comp_left, Over.isoMk_inv_left, Category.assoc]
  erw [pullbackSymmetry_inv_comp_fst, pullbackSpecIso_inv_snd]
  change Spec.map _ ≫ _ = _
  rw [← Spec.map_comp]
  rfl

omit [Fact ell.Prime] [NeZero N] in
/-- An endomorphism of a pullback, conjugated by an isomorphism to `Y`, is `σ` once both
projections are compatible. -/
theorem conj_of_pullback {C : Type*} [Category C] {M S T Y : C} {f : M ⟶ S} {g : T ⟶ S}
    [HasPullback f g] (G' : pullback f g ⟶ pullback f g) (i : pullback f g ≅ Y) (u : Y ⟶ M)
    (W : M ⟶ M) (σ : Y ⟶ Y) (hf : i.inv ≫ pullback.fst f g = u)
    (hG : G' ≫ pullback.fst f g = pullback.fst f g ≫ W) (hs : σ ≫ u = u ≫ W)
    (hGs : G' ≫ pullback.snd f g = pullback.snd f g) (hT : ∀ a b : Y ⟶ T, a = b) :
    G' ≫ i.hom = i.hom ≫ σ := by
  have hfst : pullback.fst f g = i.hom ≫ u := by rw [← hf, Iso.hom_inv_id_assoc]
  suffices h : G' = i.hom ≫ σ ≫ i.inv by
    rw [h, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply pullback.hom_ext
  · rw [hG, Category.assoc, Category.assoc, hf, hs, hfst, Category.assoc]
  · rw [hGs]
    apply (cancel_epi i.inv).mp
    exact hT _ _

theorem generic_map_Wint {Q : ℕ} (hQ : Q ∥ N) :
    ((GoodReduction.generic (LocalIntegers ell) ℚ).map (Wint h₅ htame h₂ hQ)).left ≫
        (ModelNeron.genericIso h₅ htame h₂).hom.left =
      (ModelNeron.genericIso h₅ htame h₂).hom.left ≫
        Spec.map (CommRingCat.ofHom (atkinRat h₂ hQ)) := by
  have hG : ((GoodReduction.generic (LocalIntegers ell) ℚ).map (Wint h₅ htame h₂ hQ)).left ≫
      pullback.fst (Pinned.Y0Level h₅ htame h₂).hom
        (Spec.map (CommRingCat.ofHom (algebraMap (LocalIntegers ell) ℚ))) =
      pullback.fst _ _ ≫ (Wint h₅ htame h₂ hQ).left := by simp
  have hGs : ((GoodReduction.generic (LocalIntegers ell) ℚ).map (Wint h₅ htame h₂ hQ)).left ≫
      pullback.snd (Pinned.Y0Level h₅ htame h₂).hom
        (Spec.map (CommRingCat.ofHom (algebraMap (LocalIntegers ell) ℚ))) =
      pullback.snd _ _ := by simp
  have hr : CommRingCat.ofHom (levelToRat h₅ htame h₂) ≫ CommRingCat.ofHom (atkinRat h₂ hQ) =
      CommRingCat.ofHom (atkinLevel h₅ htame h₂ hQ) ≫ CommRingCat.ofHom (levelToRat h₅ htame h₂) :=
    CommRingCat.hom_ext (RingHom.ext fun a => (levelToRat_atkinLevel h₅ htame h₂ hQ a).symm)
  have hs : Spec.map (CommRingCat.ofHom (atkinRat h₂ hQ)) ≫
      Spec.map (CommRingCat.ofHom (levelToRat h₅ htame h₂)) =
      Spec.map (CommRingCat.ofHom (levelToRat h₅ htame h₂)) ≫ (Wint h₅ htame h₂ hQ).left :=
    (Spec.map_comp _ _).symm.trans ((congrArg Spec.map hr).trans (Spec.map_comp _ _))
  let i : pullback (Pinned.Y0Level h₅ htame h₂).hom
      (Spec.map (CommRingCat.ofHom (algebraMap (LocalIntegers ell) ℚ))) ≅ (Y0Rational h₂).left :=
    ⟨(ModelNeron.genericIso h₅ htame h₂).hom.left, (ModelNeron.genericIso h₅ htame h₂).inv.left,
      by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]; rfl,
      by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]⟩
  exact conj_of_pullback _ i _ _ _ (genericIso_inv_fst h₅ htame h₂) hG hs hGs
    (fun a b => spec_to_rat_eq a b)

/-- **The integral operator extends the actual rational Atkin–Lehner involution**
(`PMWire.ExtendsAtkin` on the pinned generic source, at `q^{v_q(N)}`). -/
theorem extendsAtkin_Wint (q : ℕ) :
    PMWire.ExtendsAtkin (ModelNeron.source h₅ htame h₂) q
      (Wint h₅ htame h₂ (TauCeti.Nat.isExactDivisor_primePow (N := N) (p := q))) := by
  let hQ := TauCeti.Nat.isExactDivisor_primePow (N := N) (p := q)
  unfold PMWire.ExtendsAtkin
  rw [ModelNeron.jX_eq_incl]
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  rw [ModelNeron.incl_left]
  change _ ≫ _ ≫ rationalOpenImmersion h₂ =
    ((ModelNeron.genericIso h₅ htame h₂).hom.left ≫ rationalOpenImmersion h₂) ≫
      (rationalAtkin hQ).hom
  rw [Category.assoc, ← atkinRat_openImmersion h₂ hQ, ← Category.assoc, ← Category.assoc,
    generic_map_Wint]

/-- **`GoodRow.extension` at the pinned model** (`RC/PMWire/Model.lean:59`): for every prime
`q` dividing `N`, an integral endomorphism extending `rationalW N q` exists. -/
theorem goodRow_extension :
    ∀ q : ℕ, q.Prime → 0 < N.factorization q →
      ∃ W : Pinned.Y0Level h₅ htame h₂ ⟶ Pinned.Y0Level h₅ htame h₂,
        PMWire.ExtendsAtkin (ModelNeron.source h₅ htame h₂) q W :=
  fun q _ _ => ⟨_, extendsAtkin_Wint h₅ htame h₂ q⟩

/-- It is the only extension (`PMWire.extendsAtkin_unique`). -/
theorem eq_Wint_of_extendsAtkin (q : ℕ) {W : Pinned.Y0Level h₅ htame h₂ ⟶ Pinned.Y0Level h₅ htame h₂}
    (hW : PMWire.ExtendsAtkin (ModelNeron.source h₅ htame h₂) q W) :
    W = Wint h₅ htame h₂ (TauCeti.Nat.isExactDivisor_primePow (N := N) (p := q)) := by
  letI := ModelNeron.reducedM h₅ htame h₂
  letI := ModelNeron.separatedM h₅ htame h₂
  haveI : IsDominant (PMWire.genericProjection (Pinned.Y0Level h₅ htame h₂)) :=
    ModelNeron.denseGeneric h₅ htame h₂
  exact PMWire.extendsAtkin_unique _ hW (extendsAtkin_Wint h₅ htame h₂ q)

#print axioms exists_pow_mul_mem_localIntegers
#print axioms levelToRat_injective
#print axioms exists_pow_mul_mem_range
#print axioms isRadical_span_ell
#print axioms isIntegral_atkinRat_levelToRat
#print axioms atkinLevel
#print axioms levelToRat_atkinLevel
#print axioms Wint
#print axioms genericIso_inv_fst
#print axioms conj_of_pullback
#print axioms generic_map_Wint
#print axioms extendsAtkin_Wint
#print axioms goodRow_extension
#print axioms eq_Wint_of_extendsAtkin

end ZInQ.Manuscript.RC.ModelGeneric5
