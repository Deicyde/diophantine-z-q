import ZInQKernel.Contrib.OneProof.RC.AppEK1.Comparison

/-! The retained finite anchor (tex 7118–7142) and its finite-coefficient
comparison, isolated from the old Iwasawa interface. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KatoP2

open CategoryTheory NumberField IsDedekindDomain SelmerComplex CoefModules LambdaCoef
open AppEK1 PrintsArith ZInQ.Contrib.CloudB3RC53 _root_.ZInQ.Manuscript.RC.Even

/-- The existing explicit reciprocity input on the old subfamily. It
concerns the finite periods and continued partial L-series only. -/
structure RetainedReciprocity (E : WeierstrassCurve ℚ) (Sig Sbad : Finset ℕ)
    (es : EulerSystemData ℤ_[2]) where
  per : ∀ m, es.H m →+ ℂ
  s : ℂ
  s_ne_zero : s ≠ 0
  b : ∀ {m : ℕ}, DirichletCharacter ℂ m → ℂ
  b_ne_zero : ∀ {m : ℕ} (χ : DirichletCharacter ℂ m), b χ ≠ 0
  Lcont : ∀ {m : ℕ}, DirichletCharacter ℂ m → ℂ → ℂ
  Lcont_entire : ∀ {m : ℕ} (χ : DirichletCharacter ℂ m), Differentiable ℂ (Lcont χ)
  Lcont_eq : ∀ {m : ℕ} (χ : DirichletCharacter ℂ m) (s : ℂ), 3 / 2 < s.re →
    Lcont χ s = LSeries (twistedCoeffS E (Sbad ∪ m.primeFactors) χ) s
  recip : ∀ (m : ℕ) [NeZero m], KatoXi 2 Sig m → ∀ χ : DirichletCharacter ℂ m,
    ∑ g : (ZMod m)ˣ, χ (g : ZMod m) * per m (MonoidAlgebra.of ℤ_[2] (ZMod m)ˣ g • es.z m) =
      s * b χ * Lcont χ 1

/-- The retained class is nonzero if one of its partial central values is nonzero. -/
theorem RetainedReciprocity.z_ne_zero_of_L_ne_zero {E : WeierstrassCurve ℚ}
    {Sig Sbad : Finset ℕ} {es : EulerSystemData ℤ_[2]}
    (K : RetainedReciprocity E Sig Sbad es) {m : ℕ} [NeZero m] (hm : KatoXi 2 Sig m)
    (χ : DirichletCharacter ℂ m) (hL : K.Lcont χ 1 ≠ 0) : es.z m ≠ 0 := by
  intro hz
  have h := K.recip m hm χ
  simp only [hz, smul_zero, map_zero, mul_zero, Finset.sum_const_zero] at h
  exact mul_ne_zero (mul_ne_zero K.s_ne_zero (K.b_ne_zero χ)) hL h.symm

/-- The existing signed-sum anchor needs only finite reciprocity. -/
theorem anchored_weightedSum_nsmul_ne_zero_p2 {E : WeierstrassCurve ℚ}
    {Sig Sbad : Finset ℕ} {es : EulerSystemData ℤ_[2]}
    (K : RetainedReciprocity E Sig Sbad es) {m : ℕ} [NeZero m] (hm : KatoXi 2 Sig m)
    (χ : DirichletCharacter ℂ m) (signs : (ZMod m)ˣ → ℤ)
    (hχ : ∀ g, (signs g : ℂ) = χ (g : ZMod m))
    (hL : K.Lcont χ 1 ≠ 0) {k : ℕ} (hk : k ≠ 0) :
    k • (∑ g : (ZMod m)ˣ, signs g • (MonoidAlgebra.of ℤ_[2] _ g • es.z m)) ≠ 0 := by
  intro h
  have h' := congrArg (K.per m) h
  simp only [map_nsmul, map_sum, map_zsmul, map_zero, zsmul_eq_mul, hχ, nsmul_eq_mul] at h'
  rw [K.recip m hm χ] at h'
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hk)
    (mul_ne_zero (mul_ne_zero K.s_ne_zero (K.b_ne_zero χ)) hL) h'

local instance (S : Set (HeightOneSpectrum (𝓞 ℚ))) (E : WeierstrassCurve ℚ) (i : ℕ) :
    TopologicalSpace (Lev ℚ S E i) := ⊥

local instance (S : Set (HeightOneSpectrum (𝓞 ℚ))) (E : WeierstrassCurve ℚ) (i : ℕ) :
    DiscreteTopology (Lev ℚ S E i) := ⟨rfl⟩

local instance (S : Set (HeightOneSpectrum (𝓞 ℚ))) (E : WeierstrassCurve ℚ) (i : ℕ) :
    ContinuousAdd (Lev ℚ S E i) := ⟨continuous_of_discreteTopology⟩

local instance (S : Set (HeightOneSpectrum (𝓞 ℚ))) (E : WeierstrassCurve ℚ) (i : ℕ) :
    ContinuousSMul (GKS ℚ S) (Lev ℚ S E i) :=
  continuousSMul_iff_stabilizer_isOpen.mpr fun P => isOpen_stabilizer_torsS P

/-- Exact finite comparison on the retained modules: reduction, trace,
deck action and detection modulo the lattice's possible dyadic torsion. -/
def RetainedFiniteComparison {E : WeierstrassCurve ℚ}
    (es : EulerSystemData ℤ_[2]) {N : ℕ} (fam : BinaryFamily N)
    (μ : ∀ m : FamilyIndex fam, HasRootsOfUnity ℚ (familyPlaces fam) (m : ℕ))
    (nested : ∀ (m m' : FamilyIndex fam), (m : ℕ) ∣ (m' : ℕ) →
      cyclotomicKernel (μ m') ≤ cyclotomicKernel (μ m)) : Prop :=
  ∃ J : ∀ (m : FamilyIndex fam) (i : ℕ),
      es.H m →+ subgroupH1 (cyclotomicKernel (μ m)) (Lev ℚ (familyPlaces fam) E i),
    (∀ m i z, reduceH1 (cyclotomicKernel (μ m)) i (J m (i + 1) z) = J m i z) ∧
    (∀ (m m' : FamilyIndex fam) (h : (m : ℕ) ∣ (m' : ℕ))
        (R : RightTransversal ((cyclotomicKernel (μ m')).subgroupOf (cyclotomicKernel (μ m))))
        (i : ℕ) (z : es.H m'),
      nestedCorH1 (nested m m' h) (IsOpenKer.isOpen_ker (α := cycS (μ m'))) R (J m' i z) =
        J m i (es.cor m m' h z)) ∧
    (∀ m i (g : GKS ℚ (familyPlaces fam)) z,
      deckH1 (cyclotomicKernel (μ m)) g (J m i z) =
        J m i (MonoidAlgebra.of ℤ_[2] _ (cycS (μ m) g) • z)) ∧
    (∀ m z, (∀ i, J m i z = 0) → ∃ c : ℕ, (2 ^ c : ℕ) • z = 0)

/-- The same comparison at the fixed curve and newform level. -/
abbrev FixedRetainedFiniteComparison (ℓ : ℕ) (es : EulerSystemData ℤ_[2])
    (fam : BinaryFamily (CST.newformLevel (Ecurve ℓ)))
    (μ : ∀ m : FamilyIndex fam, HasRootsOfUnity ℚ (familyPlaces fam) (m : ℕ))
    (nested : ∀ (m m' : FamilyIndex fam), (m : ℕ) ∣ (m' : ℕ) →
      cyclotomicKernel (μ m') ≤ cyclotomicKernel (μ m)) : Prop :=
  RetainedFiniteComparison (E := Ecurve ℓ) es fam μ nested

/-- Finite-coefficient detection of the signed anchor, with no Iwasawa input. -/
theorem exists_nonzero_image_of_anchored_weightedSum_p2 {E : WeierstrassCurve ℚ}
    {Sig Sbad : Finset ℕ} {es : EulerSystemData ℤ_[2]}
    (K : RetainedReciprocity E Sig Sbad es) {N : ℕ} (fam : BinaryFamily N)
    (μ : ∀ m : FamilyIndex fam, HasRootsOfUnity ℚ (familyPlaces fam) (m : ℕ))
    (nested : ∀ (m m' : FamilyIndex fam), (m : ℕ) ∣ (m' : ℕ) →
      cyclotomicKernel (μ m') ≤ cyclotomicKernel (μ m))
    (hcomp : RetainedFiniteComparison (E := E) es fam μ nested)
    (m : FamilyIndex fam) (hm : KatoXi 2 Sig m)
    (χ : DirichletCharacter ℂ (m : ℕ)) (signs : (ZMod (m : ℕ))ˣ → ℤ)
    (hχ : ∀ g, (signs g : ℂ) = χ (g : ZMod (m : ℕ))) (hL : K.Lcont χ 1 ≠ 0) :
    ∃ i, hcomp.choose m i
      (∑ g : (ZMod (m : ℕ))ˣ, signs g • (MonoidAlgebra.of ℤ_[2] _ g • es.z m)) ≠ 0 := by
  classical
  by_contra! h
  obtain ⟨c, hc⟩ := hcomp.choose_spec.2.2.2 _ _ h
  exact anchored_weightedSum_nsmul_ne_zero_p2 K hm χ signs hχ hL
    (pow_ne_zero c (by decide)) hc

end ZInQ.Manuscript.RC.KatoP2
