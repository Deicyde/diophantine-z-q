import ZInQKernel.OneProof.H.TailZ4
import ZInQKernel.Contrib.OneProof.HeightDictionary.TorusVolume
import ZInQKernel.Contrib.OneProof.HeightDictionary.Holomorphic
import ZInQKernel.Contrib.OneProof.HeightDictionary.Conormal

/-! # height-dict: the kernel's Faltings height is the printed one

`ZInQ.HeightSplit.BostLowerBound` and `ZInQ.HeightSplit.GaudronRemondThm14` are stated over
`IsStableFaltingsHeight A x`, whose archimedean data is the kernel's coordinate form: the metric of
`η ∈ ⋀^g ω` at `τ` is `torusMetricSq Λ c = |c|² covol(Λ)`, read off an analytic uniformization
`Φ : ℂ^g → 𝒢(ℂ)_τ` with kernel `Λ` and `c = jacDet Φ f` (the coefficient of `Φ*η` on
`dz₁ ∧ ⋯ ∧ dz_g`).

This file restates both leaves over `IsPrintedStableHeight A x`, in which the metric at `τ` is
built as the print builds it: `‖η‖²_τ = (i/2)^g ∫_{A_τ(ℂ)} η ∧ η̄` for the invariant `g`-form `η`,
i.e. the total mass of the measure `(i/2)^g η ∧ η̄` on the compact group `A_τ(ℂ) = 𝒢(ℂ)_τ` with its
analytic topology (`HeightGlue.anTop`): a finite left-invariant Borel measure `μ` whose density at the
identity, in any algebraic local coordinates `f₁, …, f_g` (regular functions vanishing at `0`) with
`η = l · df₁ ∧ ⋯ ∧ df_g`, is `|τ(l)|²` with respect to Lebesgue measure `dx₁dy₁⋯dx_gdy_g`
(`IsFaltingsMetricSq`). No uniformization enters the definition. The lattice is
`ω = ⋀^g Γ(S, e*Ω¹)` built from the stalks `𝒪_{S,s} ⊗ Ω[𝒪_{𝒩,e(s)}/𝓞_L]` (`printedDetLattice`,
`Conormal.printedOmega`), proved equal to the kernel's `detLattice` (`printedDetLattice_eq`).

It proves (`isFaltingsMetricSq_of_metrized`, from `TorusVolume.volume_eq_of_normalized`: Haar
uniqueness, the fundamental domain of `Λ`, and the Jacobian estimates of change of variables) that
every metrized model computes this printed metric, hence `IsStableFaltingsHeight A x →
IsPrintedStableHeight A x` (`isPrintedStableHeight_of`, using the kernel's uniqueness of analytic
uniformizations and `UniformizationDim`, both from T35), the converse (`isPrintedStableHeight_iff`),
non-vacuity of the printed metric (`exists_isNormalizedBy`), and the consumer forms from the restated
leaves (also for `JavanpeykarBound` and `PazukiCor13Upper`). -/

open CategoryTheory AlgebraicGeometry MeasureTheory Topology Set MonObj
open MonoidalCategory CartesianMonoidalCategory
open ZInQ.DefFaltings ZInQ.HeightSplit ZInQ.HeightGlue
open scoped NumberField

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace ZInQ.HeightDict

section Defs

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- The Borel `σ`-algebra of the analytic topology of `𝒢(ℂ)_τ = A_τ(ℂ)`. -/
noncomputable def anBorel (𝒢 : GroupModel A L) (τ : L →+* ℂ) : MeasurableSpace (𝒢.Pts τ) :=
  @borel _ (anTop 𝒢 τ)

/-- The map `p ↦ (f₁(p), …, f_g(p))` of a tuple of regular functions `fᵢ ∈ Γ(Uᵢ, 𝒪_𝒢)`. -/
noncomputable def coordMap (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (U : Fin g → 𝒢.G.left.Opens) (s : ∀ i, Γ(𝒢.G.left, U i)) : 𝒢.Pts τ → (Fin g → ℂ) :=
  fun p i => 𝒢.evalAt p (U i) (s i)

/-- **`μ` is the measure `(i/2)^g η ∧ η̄` at the identity.** For every tuple of regular functions
`fᵢ ∈ Γ(Uᵢ, 𝒪_𝒢)` defined and vanishing at the origin `ξ` of the generic fibre, and every `l ∈ L`
with `η = l · df₁ ∧ ⋯ ∧ df_g`, the image of `μ` under `F = (f₁, …, f_g)` has density `|τ(l)|²` at
`F(1)` relative to Lebesgue measure on `ℂ^g` (`(i/2)^g dz ∧ dz̄ = dx dy`): near `1`,
`|μ(E) − |τ l|² λ(F(E))| ≤ ε λ(F(E))`. -/
def IsNormalizedBy (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (mu : @Measure (𝒢.Pts τ) (anBorel 𝒢 τ)) (eta : 𝒢.hodgeSpace g) : Prop :=
  letI := anTop 𝒢 τ
  letI := anBorel 𝒢 τ
  ∀ (U : Fin g → 𝒢.G.left.Opens) (hU : ∀ i, 𝒢.genericUnit ∈ U i) (s : ∀ i, Γ(𝒢.G.left, U i))
    (hm : ∀ i, 𝒢.G.left.presheaf.germ (U i) 𝒢.genericUnit (hU i) (s i) ∈
      IsLocalRing.maximalIdeal 𝒢.genStalk)
    (l : L), eta = l • 𝒢.wedge (fun i => ⟨_, hm i⟩) →
    ∀ ε : ℝ, 0 < ε → ∃ W ∈ 𝓝 (1 : 𝒢.Pts τ), ∀ E ⊆ W, MeasurableSet E →
      |(mu E).toReal - ‖τ l‖ ^ 2 * (volume (coordMap 𝒢 τ U s '' E)).toReal| ≤
        ε * (volume (coordMap 𝒢 τ U s '' E)).toReal

/-- **The printed archimedean Faltings metric** `‖η‖²_τ = (i/2)^g ∫_{A_τ(ℂ)} η ∧ η̄ = r`: every finite
left-invariant Borel measure on `A_τ(ℂ)` (analytic topology) that is `(i/2)^g η ∧ η̄` at the identity
has total mass `r`. -/
def IsFaltingsMetricSq (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ} (eta : 𝒢.hodgeSpace g) (r : ℝ) :
    Prop :=
  letI := anTop 𝒢 τ
  letI := anBorel 𝒢 τ
  ∀ mu : Measure (𝒢.Pts τ), IsFiniteMeasure mu → mu.IsMulLeftInvariant → IsNormalizedBy 𝒢 τ mu eta →
    (mu univ).toReal = r

end Defs

section PrintedOmega

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- `⋀^g ω` inside the Hodge line `L ⊗ ⋀^g ω_{A_L}`, for the printed `ω = Γ(S, e*Ω¹)`
(`Conormal.printedOmega`). -/
noncomputable def printedDetLattice (𝒢 : GroupModel A L) (g : ℕ) :
    Submodule (𝓞 L) (𝒢.hodgeSpace g) :=
  Submodule.span (𝓞 L) (Set.range fun v : Fin g → Conormal.printedOmega 𝒢 =>
    (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => (v i : 𝒢.cotangent)))

theorem printedDetLattice_eq (𝒢 : GroupModel A L) (g : ℕ) :
    printedDetLattice 𝒢 g = 𝒢.detLattice g := by
  unfold printedDetLattice GroupModel.detLattice
  rw [Conormal.printedOmega_eq]

end PrintedOmega

/-- **Faltings' stable height, as the print builds it** (Faltings 1983 §1; Deligne, Sém. Bourbaki
616 §1; locators UNVERIFIED): `x = deg(ω̄_𝒩)/[L:ℚ]` for the Néron model `𝒩` of `A_L` over a number
field `L ⊇ K` where `A` has semistable reduction everywhere, `g = dim A`, `ω_𝒩 = ⋀^g Γ(S, e*Ω¹)`
(`printedDetLattice`, built from the stalks of `e*Ω¹` by Kähler differentials), computed with any
nonzero section `η`:
`deg = log #(ω_𝒩/𝓞_L η) − ½ ∑_{τ : L → ℂ} log ‖η‖²_τ` with the printed metric
`‖η‖²_τ = (i/2)^g ∫_{A_τ(ℂ)} η ∧ η̄` (`IsFaltingsMetricSq`). -/
def IsPrintedStableHeight {K : Type} [Field K] (A : PkgI3.AbVar K) (x : ℝ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (𝒩 : GroupModel A L) (g : ℕ),
    𝒩.IsNeronModel ∧ IsSemistable 𝒩 ∧ A.dim = (g : WithBot ℕ∞) ∧
    ∃ eta ∈ printedDetLattice 𝒩 g, eta ≠ 0 ∧ secIndex (printedDetLattice 𝒩 g) eta ≠ 0 ∧
      ∃ r : (L →+* ℂ) → ℝ, (∀ τ, IsFaltingsMetricSq 𝒩 τ eta (r τ)) ∧
        x = (Real.log (secIndex (printedDetLattice 𝒩 g) eta) -
          (1 / 2) * ∑ τ : L →+* ℂ, Real.log (r τ)) / Module.finrank ℚ L

/-- **Leaf R21-Bost over the printed height** (J.-B. Bost, Sém. Bourbaki 795 (1994/95), Astérisque
237 (1996); display UNVERIFIED): `ZInQ.HeightSplit.BostLowerBound` with `IsStableFaltingsHeight`
replaced by `IsPrintedStableHeight` (Deligne's normalization `h_D = h_F + (g/2) log π`). -/
def BostLowerBoundPrinted : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ x : ℝ, IsPrintedStableHeight A x →
      -((g : ℝ) / 2 * Real.log (2 * Real.pi)) ≤ x + (g : ℝ) / 2 * Real.log Real.pi

/-- **Leaf R19-GR over the printed height** (Gaudron–Rémond, Duke Math. J. 163 (2014), Thm 1.4,
p. 2060; `κ` p. 2058; read by the locator audit): `ZInQ.HeightSplit.GaudronRemondThm14` with
`IsStableFaltingsHeight` replaced by `IsPrintedStableHeight` (stable height, Faltings' original
normalization). -/
def GaudronRemondThm14Printed : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (g : ℕ) (x : ℝ),
    A.dim = (g : WithBot ℕ∞) → IsPrintedStableHeight A x →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ) →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ ∧ (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) ∧
    (∃ ψ : B.X ⟶ A.X, IsIsogeny ψ ∧ (isogDeg ψ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x)


/-! ## The dictionary: a metrized model computes the printed metric -/

section Dict

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- **The archimedean dictionary.** For a metrized model `M` (analytic uniformization `Φ` with kernel
`Λ_τ`, coefficient map `c_τ`), the kernel's metric `torusMetricSq Λ_τ (c_τ η) = |c_τ η|² covol(Λ_τ)`
is the printed metric `(i/2)^g ∫_{A_τ(ℂ)} η ∧ η̄`. -/
theorem isFaltingsMetricSq_of_metrized {g : ℕ} (M : MetrizedModel A L g) (τ : L →+* ℂ)
    (eta : M.model.hodgeSpace g) :
    IsFaltingsMetricSq M.model τ eta
      (torusMetricSq (M.hodge.periods τ) (M.hodge.coeff τ eta)) := by
  obtain ⟨Φ, hΦ, hc⟩ := M.arch τ
  letI := anTop M.model τ
  letI := anBorel M.model τ
  haveI : BorelSpace (M.model.Pts τ) := ⟨rfl⟩
  haveI : T2Space (M.model.Pts τ) := analyticPointsT2 K A L M.model τ
  haveI := M.hodge.periods_discrete τ
  haveI := M.hodge.periods_isZLattice τ
  intro mu hfin hinv hnorm
  -- a wedge `1 ⊗ df₁ ∧ ⋯ ∧ df_g ≠ 0`
  have hw : ∃ f : Fin g → IsLocalRing.maximalIdeal M.model.genStalk, M.model.wedge f ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply M.hodge.coeff_ne_zero τ
    refine GroupModel.semilinear_ext_wedge M.model _ _ fun f => ?_
    rw [hcon f, map_zero, LinearMap.zero_apply]
  obtain ⟨f, hf⟩ := hw
  obtain ⟨l, hl⟩ := (finrank_eq_one_iff_of_nonzero' _ hf).mp M.hodge.finrank_eq_one eta
  -- representatives of the germs `fᵢ` (the ones `germAlong` uses)
  let U : Fin g → M.model.G.left.Opens := fun i => (M.model.exists_rep (f i)).choose
  have hU : ∀ i, M.model.genericUnit ∈ U i := fun i =>
    (M.model.exists_rep (f i)).choose_spec.choose
  let s : ∀ i, Γ(M.model.G.left, U i) := fun i =>
    (M.model.exists_rep (f i)).choose_spec.choose_spec.choose
  have hgerm : ∀ i, M.model.G.left.presheaf.germ (U i) M.model.genericUnit (hU i) (s i) =
      (f i : M.model.genStalk) := fun i =>
    (M.model.exists_rep (f i)).choose_spec.choose_spec.choose_spec
  have hm : ∀ i, M.model.G.left.presheaf.germ (U i) M.model.genericUnit (hU i) (s i) ∈
      IsLocalRing.maximalIdeal M.model.genStalk := fun i => by rw [hgerm]; exact (f i).2
  have hwf : M.model.wedge (fun i => ⟨_, hm i⟩) = M.model.wedge f := by
    congr 1; funext i; exact Subtype.ext (hgerm i)
  have hnormal := hnorm U hU s hm l (by rw [hwf, hl])
  -- `F ∘ Φ` is holomorphic near `0`
  set F := coordMap M.model τ U s
  have hψ : F ∘ Φ = fun z i => M.model.germAlong Φ (f i) z := rfl
  set V := ⋂ i, M.model.dom Φ (U i)
  have hVo : IsOpen V := isOpen_iInter_of_finite fun i => hΦ.2.2.2.1 (U i)
  have h0V : (0 : Fin g → ℂ) ∈ V :=
    mem_iInter.mpr fun i => ZInQ.Metrization.zero_mem_dom M.model hΦ (U i) (hU i)
  have hdi : ∀ i, DifferentiableOn ℂ (fun z => M.model.germAlong Φ (f i) z) V := fun i =>
    (hΦ.2.2.2.2 (U i) (s i)).mono (iInter_subset _ i)
  have hψd : DifferentiableOn ℂ (F ∘ Φ) V := by
    rw [hψ]; exact differentiableOn_pi.mpr hdi
  have hstrict := (Holomorphic.hasStrictFDerivAt hVo hψd h0V).restrictScalars ℝ
  have hUnif : TorusVolume.IsUnif (M.hodge.periods τ) Φ :=
    ⟨continuous_of_isAnalyticUniformization M.model τ hΦ, hΦ.1, hΦ.2.1, hΦ.2.2.1⟩
  have key := TorusVolume.volume_eq_of_normalized hUnif mu F (fderiv ℂ (F ∘ Φ) 0) hstrict
    (‖τ l‖ ^ 2) hnormal
  rw [key]
  -- the determinant is `jacDet Φ f`
  have hdet : LinearMap.det ((fderiv ℂ (F ∘ Φ) 0 : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) :
      (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) = M.model.jacDet Φ f := by
    rw [← LinearMap.det_toMatrix', GroupModel.jacDet]
    congr 1
    ext i j
    rw [LinearMap.toMatrix'_apply, hψ,
      fderiv_pi fun i => (hdi i).differentiableAt (hVo.mem_nhds h0V)]
    rfl
  have hcoeff : M.hodge.coeff τ eta = τ l * M.model.jacDet Φ f := by
    rw [← hl, map_smulₛₗ, hc f, smul_eq_mul]
  rw [torusMetricSq, hcoeff, hdet, norm_mul, mul_pow]


/-- `det (fderiv (F ∘ Φ) 0) = jacDet Φ f` for any representatives of the germs `fᵢ`. -/
theorem det_fderiv_coordMap {g : ℕ} (𝒢 : GroupModel A L) {τ : L →+* ℂ}
    {Λ : Submodule ℤ (Fin g → ℂ)} {Φ : (Fin g → ℂ) → 𝒢.Pts τ}
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (U : Fin g → 𝒢.G.left.Opens)
    (hU : ∀ i, 𝒢.genericUnit ∈ U i) (s : ∀ i, Γ(𝒢.G.left, U i))
    (hm : ∀ i, 𝒢.G.left.presheaf.germ (U i) 𝒢.genericUnit (hU i) (s i) ∈
      IsLocalRing.maximalIdeal 𝒢.genStalk) :
    LinearMap.det ((fderiv ℂ (coordMap 𝒢 τ U s ∘ Φ) 0 : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) :
      (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) = 𝒢.jacDet Φ (fun i => ⟨_, hm i⟩) := by
  have hev : coordMap 𝒢 τ U s ∘ Φ =ᶠ[𝓝 0]
      fun z i => 𝒢.germAlong Φ (𝒢.G.left.presheaf.germ (U i) 𝒢.genericUnit (hU i) (s i)) z := by
    have h := Filter.eventually_all.mpr fun i =>
      ZInQ.Metrization.germAlong_eventuallyEq 𝒢 hΦ (U i) (hU i) (s i)
    filter_upwards [h] with z hz
    funext i
    exact (hz i).symm
  rw [hev.fderiv_eq, ← LinearMap.det_toMatrix', GroupModel.jacDet]
  congr 1
  ext i j
  rw [LinearMap.toMatrix'_apply,
    fderiv_pi fun i => ZInQ.Metrization.germAlong_differentiableAt 𝒢 hΦ _]
  rfl

/-- `F ∘ Φ` is strictly differentiable at `0` (holomorphic in several variables). -/
theorem hasStrictFDerivAt_coordMap {g : ℕ} (𝒢 : GroupModel A L) {τ : L →+* ℂ}
    {Λ : Submodule ℤ (Fin g → ℂ)} {Φ : (Fin g → ℂ) → 𝒢.Pts τ}
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (U : Fin g → 𝒢.G.left.Opens)
    (hU : ∀ i, 𝒢.genericUnit ∈ U i) (s : ∀ i, Γ(𝒢.G.left, U i)) :
    HasStrictFDerivAt (coordMap 𝒢 τ U s ∘ Φ)
      ((fderiv ℂ (coordMap 𝒢 τ U s ∘ Φ) 0).restrictScalars ℝ) 0 := by
  set V := ⋂ i, 𝒢.dom Φ (U i)
  have hVo : IsOpen V := isOpen_iInter_of_finite fun i => hΦ.2.2.2.1 (U i)
  have h0V : (0 : Fin g → ℂ) ∈ V :=
    mem_iInter.mpr fun i => ZInQ.Metrization.zero_mem_dom 𝒢 hΦ (U i) (hU i)
  have hψd : DifferentiableOn ℂ (coordMap 𝒢 τ U s ∘ Φ) V :=
    differentiableOn_pi.mpr fun i => (hΦ.2.2.2.2 (U i) (s i)).mono (iInter_subset _ i)
  exact (Holomorphic.hasStrictFDerivAt hVo hψd h0V).restrictScalars ℝ

/-- **Non-vacuity of the printed metric.** For `η ≠ 0` there is a finite left-invariant Borel measure
on `A_τ(ℂ)` that is `(i/2)^g η ∧ η̄` at the identity (namely `|c_τ η|² Φ_*(Lebesgue|_D)`). -/
theorem exists_isNormalizedBy {g : ℕ} (M : MetrizedModel A L g) (τ : L →+* ℂ)
    (eta : M.model.hodgeSpace g) (heta : eta ≠ 0) :
    letI := anBorel M.model τ
    ∃ mu : Measure (M.model.Pts τ), IsFiniteMeasure mu ∧ mu.IsMulLeftInvariant ∧
      IsNormalizedBy M.model τ mu eta := by
  obtain ⟨Φ, hΦ, hc⟩ := M.arch τ
  letI := anTop M.model τ
  letI := anBorel M.model τ
  haveI : BorelSpace (M.model.Pts τ) := ⟨rfl⟩
  haveI : T2Space (M.model.Pts τ) := analyticPointsT2 K A L M.model τ
  haveI := M.hodge.periods_discrete τ
  haveI := M.hodge.periods_isZLattice τ
  have hUnif : TorusVolume.IsUnif (M.hodge.periods τ) Φ :=
    ⟨continuous_of_isAnalyticUniformization M.model τ hΦ, hΦ.1, hΦ.2.1, hΦ.2.2.1⟩
  haveI := hUnif.isTopologicalGroup
  obtain ⟨r₀, hr₀, DD, -, hfd, hB, hsep, hfin⟩ :=
    TorusVolume.exists_fundamentalDomain_ball (M.hodge.periods τ)
  set π := TorusVolume.piMeasure Φ DD
  haveI : IsFiniteMeasure π := ⟨by rw [hUnif.piMeasure_univ]; exact hfin⟩
  haveI := hUnif.piMeasure_leftInvariant hfd
  set c : ℝ := ‖M.hodge.coeff τ eta‖ ^ 2
  refine ⟨Real.toNNReal c • π, inferInstance, inferInstance, ?_⟩
  intro U hU s hm l hrep ε hε
  have hdet := det_fderiv_coordMap M.model hΦ U hU s hm
  have hcoeff : M.hodge.coeff τ eta = τ l * M.model.jacDet Φ (fun i => ⟨_, hm i⟩) := by
    rw [hrep, map_smulₛₗ, hc, smul_eq_mul]
  have hdet0 : LinearMap.det ((fderiv ℂ (coordMap M.model τ U s ∘ Φ) 0 :
      (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) ≠ 0 := by
    rw [hdet]
    intro h0
    apply M.hodge.coeff_apply_ne_zero τ heta
    rw [hcoeff, h0, mul_zero]
  obtain ⟨W, hW, hWn⟩ := TorusVolume.piMeasure_normalized hUnif hr₀ hB hsep _ _
    (hasStrictFDerivAt_coordMap M.model hΦ U hU s) hdet0 (‖τ l‖ ^ 2) (sq_nonneg _) ε hε
  refine ⟨W, hW, fun E hEW hE => ?_⟩
  have hc' : c = ‖τ l‖ ^ 2 * ‖LinearMap.det ((fderiv ℂ (coordMap M.model τ U s ∘ Φ) 0 :
      (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))‖ ^ 2 := by
    rw [hdet, ← mul_pow, ← norm_mul, ← hcoeff]
  have hmuE : ((Real.toNNReal c • π) E).toReal = c * (π E).toReal := by
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
      Real.coe_toNNReal _ (by positivity)]
  rw [hmuE, hc']
  exact hWn E hEW hE

/-- **The printed metric is the kernel's metric** (for `η ≠ 0`, the printed metric is well defined
and equals `torusMetricSq`). -/
theorem isFaltingsMetricSq_iff {g : ℕ} (M : MetrizedModel A L g) (τ : L →+* ℂ)
    (eta : M.model.hodgeSpace g) (heta : eta ≠ 0) (r : ℝ) :
    IsFaltingsMetricSq M.model τ eta r ↔
      r = torusMetricSq (M.hodge.periods τ) (M.hodge.coeff τ eta) := by
  constructor
  · intro h
    obtain ⟨mu, h1, h2, h3⟩ := exists_isNormalizedBy M τ eta heta
    rw [← h mu h1 h2 h3, isFaltingsMetricSq_of_metrized M τ eta mu h1 h2 h3]
  · rintro rfl
    exact isFaltingsMetricSq_of_metrized M τ eta

end Dict

/-! ## The identification and the consumer forms -/

/-- **`IsStableFaltingsHeight A x → IsPrintedStableHeight A x`**: the kernel's stable height is the
printed one. Uses the kernel's uniqueness of analytic uniformizations (so that the height of `𝒩` is
the model height of any metrization) and `UniformizationDim` (so that `g = dim A`); both follow
from T35 (`HeightGlue.analyticUniformizationUnique_of_t35`, `HeightGlue.uniformizationDim_of_t35`). -/
theorem isPrintedStableHeight_of (hU : AnalyticUniformizationUnique) (hDim : UniformizationDim)
    {K : Type} [Field K] {A : PkgI3.AbVar K} {x : ℝ} (hx : IsStableFaltingsHeight A x) :
    IsPrintedStableHeight A x := by
  obtain ⟨L, iF, iN, iA, 𝒩, hN, hS, hh⟩ := hx
  have hM : ∃ (g : ℕ) (M : MetrizedModel A L g), M.model = 𝒩 := by
    by_contra hcon
    push Not at hcon
    have htop : 𝒩.height = ⊤ :=
      le_antisymm le_top (le_iInf fun g => le_iInf fun M => le_iInf fun h => absurd h (hcon g M))
    rw [htop] at hh
    exact EReal.coe_ne_top x hh.symm
  obtain ⟨g, M, rfl⟩ := hM
  have hxM : x = M.hodge.modelHeight := by
    have := groupModel_height_eq hU metrizedDimUnique M
    rw [hh] at this
    exact_mod_cast this
  obtain ⟨τ₀⟩ : Nonempty (L →+* ℂ) := ⟨(IsAlgClosed.lift : L →ₐ[ℚ] ℂ).toRingHom⟩
  obtain ⟨Φ₀, hΦ₀, -⟩ := M.arch τ₀
  have hdim : A.dim = (g : WithBot ℕ∞) := hDim K A L M.model τ₀ g _ Φ₀
    (M.hodge.periods_discrete τ₀) (M.hodge.periods_isZLattice τ₀) hΦ₀
  obtain ⟨eta, hetaM, heta0, hsec⟩ := M.hodge.isLattice
  have hetaM' : eta ∈ printedDetLattice M.model g := by
    rw [printedDetLattice_eq]; exact M.lattice_eq ▸ hetaM
  have hsec' : secIndex (printedDetLattice M.model g) eta ≠ 0 := by
    rw [printedDetLattice_eq]; exact M.lattice_eq ▸ hsec
  refine ⟨L, iF, iN, iA, M.model, g, hN, hS, hdim, eta, hetaM', heta0, hsec',
    fun τ => torusMetricSq (M.hodge.periods τ) (M.hodge.coeff τ eta),
    fun τ => isFaltingsMetricSq_of_metrized M τ eta, ?_⟩
  rw [hxM, M.hodge.modelHeight_eq hetaM heta0, M.lattice_eq, printedDetLattice_eq]

/-- **The converse identification** `IsPrintedStableHeight A x → IsStableFaltingsHeight A x`, given
that Néron models are metrizable (`NeronMetrizable`, from T35). With `isPrintedStableHeight_of`, the
printed height and the kernel's coincide. -/
theorem isStableFaltingsHeight_of_printed (hU : AnalyticUniformizationUnique)
    (hDim : UniformizationDim) (hMet : NeronMetrizable) {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} {x : ℝ} (hx : IsPrintedStableHeight A x) : IsStableFaltingsHeight A x := by
  obtain ⟨L, iF, iN, iA, 𝒩, g, hN, hS, hdim, eta, hetaM, heta0, hsec, r, hr, hxr⟩ := hx
  obtain ⟨g', M, rfl⟩ := hMet K A L 𝒩 hN
  obtain ⟨τ₀⟩ : Nonempty (L →+* ℂ) := ⟨(IsAlgClosed.lift : L →ₐ[ℚ] ℂ).toRingHom⟩
  obtain ⟨Φ₀, hΦ₀, -⟩ := M.arch τ₀
  have hdim' : A.dim = (g' : WithBot ℕ∞) := hDim K A L M.model τ₀ g' _ Φ₀
    (M.hodge.periods_discrete τ₀) (M.hodge.periods_isZLattice τ₀) hΦ₀
  have hgg : g = g' := by
    have := hdim.symm.trans hdim'
    exact_mod_cast this
  subst hgg
  have hrτ : ∀ τ, r τ = torusMetricSq (M.hodge.periods τ) (M.hodge.coeff τ eta) := fun τ =>
    (isFaltingsMetricSq_iff M τ eta heta0 (r τ)).mp (hr τ)
  rw [printedDetLattice_eq] at hetaM hxr
  have hetaL : eta ∈ M.hodge.lattice := M.lattice_eq ▸ hetaM
  refine ⟨L, iF, iN, iA, M.model, hN, hS, ?_⟩
  rw [groupModel_height_eq hU metrizedDimUnique M, M.hodge.modelHeight_eq hetaL heta0, hxr,
    M.lattice_eq]
  simp only [hrτ]

/-- **The printed stable height and the kernel's coincide** (given the T35 glue). -/
theorem isPrintedStableHeight_iff (hU : AnalyticUniformizationUnique) (hDim : UniformizationDim)
    (hMet : NeronMetrizable) {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (x : ℝ) :
    IsPrintedStableHeight A x ↔ IsStableFaltingsHeight A x :=
  ⟨isStableFaltingsHeight_of_printed hU hDim hMet, isPrintedStableHeight_of hU hDim⟩

/-- **`BostLowerBound` from Bost's bound over the printed height**, given the kernel's uniqueness of
analytic uniformizations and `UniformizationDim`. -/
theorem bostLowerBound_of_printed' (hB : BostLowerBoundPrinted)
    (hU : AnalyticUniformizationUnique) (hDim : UniformizationDim) : BostLowerBound :=
  fun K _ _ A g hg x hx => hB K A g hg x (isPrintedStableHeight_of hU hDim hx)

/-- **`GaudronRemondThm14` from Gaudron–Rémond over the printed height**, given the kernel's
uniqueness of analytic uniformizations and `UniformizationDim`. -/
theorem gaudronRemondThm14_of_printed' (hGR : GaudronRemondThm14Printed)
    (hU : AnalyticUniformizationUnique) (hDim : UniformizationDim) : GaudronRemondThm14 :=
  fun K _ _ A B g x hg hx hiso => hGR K A B g x hg (isPrintedStableHeight_of hU hDim hx) hiso

/-- **The field `bostLowerBound`** from the printed leaf and the textbook fields
`uniformizationLeafAll`, `mumfordTorsionAlgClosed` (which give T35). -/
theorem bostLowerBound_of_printed (hB : BostLowerBoundPrinted)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hMT : AvSplit.MumfordTorsionAlgClosed) : BostLowerBound :=
  bostLowerBound_of_printed' hB (analyticUniformizationUnique_of_t35 (AvSplit.Final.h38 hUL hMT))
    (uniformizationDim_of_t35 (AvSplit.Final.h38 hUL hMT))

/-- **The field `gaudronRemondThm14`** from the printed leaf and the textbook fields
`uniformizationLeafAll`, `mumfordTorsionAlgClosed`. -/
theorem gaudronRemondThm14_of_printed (hGR : GaudronRemondThm14Printed)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hMT : AvSplit.MumfordTorsionAlgClosed) : GaudronRemondThm14 :=
  gaudronRemondThm14_of_printed' hGR
    (analyticUniformizationUnique_of_t35 (AvSplit.Final.h38 hUL hMT))
    (uniformizationDim_of_t35 (AvSplit.Final.h38 hUL hMT))


/-! ## The other two height-split rows over the printed height

`JavanpeykarBound` and `PazukiCor13Upper` are also stated over `IsStableFaltingsHeight`; the same
dictionary restates them over `IsPrintedStableHeight` (verbatim otherwise). -/

section OtherRows

open LeafModCurves (IsCurve IsJacobian IsBelyiFunction)
open LeafPush2 (ffAlgebra javanpeykarBound CPts IsUniformization IsSiegel IsPeriodMatrix Char2
  thetaConst pazukiC2)

/-- **Leaf R18-Javanpeykar over the printed height** (Javanpeykar, Algebra Number Theory 8 (2014),
Thm 1.1.1, read by the locator audit): `ZInQ.HeightSplit.JavanpeykarBound` with
`IsStableFaltingsHeight` replaced by `IsPrintedStableHeight`. -/
def JavanpeykarBoundPrinted : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (X : Over (Spec (CommRingCat.of K))) [IsCurve X]
    [IsIntegral X.left] (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X) (J : PkgI3.AbVar K)
    (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
    ∀ g : ℕ, J.dim = (g : WithBot ℕ∞) → 1 ≤ g →
    ∀ t : X.left.functionField,
      letI := ffAlgebra X
      IsBelyiFunction K X.left.functionField t →
      ∀ d : ℕ, Module.finrank (IntermediateField.adjoin K {t}) X.left.functionField = d → 0 < d →
      ∀ x : ℝ, IsPrintedStableHeight J x → x ≤ javanpeykarBound g d

/-- **Leaf R22-Pazuki (upper half) over the printed height** (Pazuki, Bull. SMF 140 (2012),
Cor. 1.3(2), read by the locator audit; the level-2 coordinate risk of `PazukiCor13Upper` is
unchanged): `ZInQ.HeightSplit.PazukiCor13Upper` with `IsStableFaltingsHeight` replaced by
`IsPrintedStableHeight`. -/
def PazukiCor13UpperPrinted : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K), A.dim = (2 : WithBot ℕ∞) →
    ∀ x : ℝ, IsPrintedStableHeight A x →
    ∀ (σ : K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φ : (Fin 2 → ℂ) → CPts A σ),
      IsUniformization σ Λ Φ →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → IsPeriodMatrix Λ Ω →
    ∀ (F : Type) [Field F] [NumberField F] (emb : F →+* ℂ) (z : Char2 → F) (c : ℂ), c ≠ 0 →
      (∀ m, emb (z m) = c * thetaConst Ω m) →
      max 1 (absLogHeightL2 z) - max 1 (x + Real.log Real.pi) / 2 ≤
        pazukiC2 * Real.log (min (max 1 (absLogHeightL2 z)) (max 1 (x + Real.log Real.pi)) + 2)

/-- `JavanpeykarBound` from the printed-height leaf (and the T35 fields). -/
theorem javanpeykarBound_of_printed (hJ : JavanpeykarBoundPrinted)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hMT : AvSplit.MumfordTorsionAlgClosed) : JavanpeykarBound :=
  fun K _ _ X _ _ P₀ J aj hJac g hg hg1 t hB d hd hd0 x hx =>
    hJ K X P₀ J aj hJac g hg hg1 t hB d hd hd0 x
      (isPrintedStableHeight_of (analyticUniformizationUnique_of_t35 (AvSplit.Final.h38 hUL hMT))
        (uniformizationDim_of_t35 (AvSplit.Final.h38 hUL hMT)) hx)

/-- `PazukiCor13Upper` from the printed-height leaf (and the T35 fields). -/
theorem pazukiCor13Upper_of_printed (hP : PazukiCor13UpperPrinted)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hMT : AvSplit.MumfordTorsionAlgClosed) : PazukiCor13Upper :=
  fun K _ _ A hA x hx σ Λ Φ hΦ Ω hΩ hPer F _ _ emb z c hc hz =>
    hP K A hA x
      (isPrintedStableHeight_of (analyticUniformizationUnique_of_t35 (AvSplit.Final.h38 hUL hMT))
        (uniformizationDim_of_t35 (AvSplit.Final.h38 hUL hMT)) hx)
      σ Λ Φ hΦ Ω hΩ hPer F emb z c hc hz

end OtherRows

end ZInQ.HeightDict
