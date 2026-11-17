import ZInQKernel.Contrib.OneProof.RC.Limits.FiniteFreeModel
import ZInQKernel.Contrib.OneProof.RC.Limits.Ultralimit
import ZInQKernel.Contrib.OneProof.RC.Limits.ResidualBound
import ZInQKernel.Contrib.OneProof.RC.Limits.ResidualAlgebra
import ZInQKernel.Contrib.OneProof.RC.Limits.LocalPrints
import ZInQKernel.Contrib.OneProof.RC.Limits.OuterDVR
import ZInQKernel.Contrib.OneProof.RC.Limits.Evaluation

/-!
# Lane RC6 (limits): the three lemmas of tex 4391–4745, as Elliot states them

This file gathers, under the manuscript labels, the main statements of
* Lemma `ex:limits-inner-limit` (tex 4391–4451): finite free models and the inner ultrafilter limit;
* Lemma `ex:limits-residual-bound` (tex 4453–4648): `N(E,A,j) ≤ 56 ω(2N) + 8A + 56j + 70`;
* Lemma `ex:limits-outer-evaluation` (tex 4650–4745): the evaluation identities (5.2), evaluation
  injectivity, and the outer ring `𝒪_∞` of (5.3), a DVR with uniformizer two.

Every theorem below is `PROVED` (each is a restatement of, or a short combination of, theorems of
the companion files).  The arithmetic inputs that are not available in Lean enter as explicit,
named hypotheses: `ResidualRankCounts` (the cohomological counts behind (5.1)) and the PRINT
propositions `MilneADT_I_2_8`, `MilneADT_I_2_3_trivial` (local Galois cohomology).  Elliot's outer
ring `𝒪 = (Λ_{(2)})^∧` enters through its only property used in (5.3), "a DVR with uniformizer two"
(GLUE for the completion; the uncompleted `Λ_{(2)}` is a DVR with uniformizer two by
`ScalarRing.isDiscreteValuationRing_Λ_two`, PROVED).
-/

namespace ZInQ.Manuscript.RC.Limits

open scoped PowerSeries.WithPiTopology Matrix
open IsLocalRing

universe u v

/-! ## Lemma `ex:limits-inner-limit` -/

/-- **Lemma `ex:limits-inner-limit`, finite free models** (tex 4391–4399, proof 4408–4442).
PROVED (`exists_finiteFreeModel`).

Over a local ring `A` with nilpotent maximal ideal, a (total) complex `(M, d)` of flat modules with
finite residual cohomology admits a finite free model `A^{(ι)}`, `#ι = dim_k H(M ⊗ k)`, with actual
inclusion `i`, projection `p` and contraction homotopy `h`.  Transport of every fixed finite
diagram of maps and homotopies is `retractTransport` and its lemmas in `Perturbation`. -/
theorem ex_limits_inner_limit_finiteFreeModel {A : Type u} [CommRing A] [IsLocalRing A]
    (hnil : IsNilpotent (maximalIdeal A)) {M : Type v} [AddCommGroup M] [Module A M]
    [Module.Flat A M] (d : Module.End A M) (hd : d * d = 0)
    (hfin : Module.Finite (ResidueField A) (residualCohomology d)) :
    ∃ (ι : Type (max u v)) (_ : Fintype ι) (dC : Module.End A (ι →₀ A)) (i : (ι →₀ A) →ₗ[A] M)
      (p : M →ₗ[A] (ι →₀ A)) (h : Module.End A M),
      IsNormalizedDeformationRetract d dC i p h ∧
      Fintype.card ι = Module.finrank (ResidueField A) (residualCohomology d) :=
  exists_finiteFreeModel hnil d hd hfin

/-- **Lemma `ex:limits-inner-limit`: the actual continuous cochains are covered** (tex 4393–4395,
4413–4414).  PROVED (`free_continuousCochains`, `flat_continuousCochains`).

Continuous cochains `Gⁿ → Aʳ` of a compact group with discrete finite free coefficients are a
filtered union of functions on finite clopen partitions, hence flat, hence free over a local ring
with nilpotent maximal ideal. -/
theorem ex_limits_inner_limit_cochains {A : Type u} [CommRing A] [IsLocalRing A]
    (hnil : IsNilpotent (maximalIdeal A)) (G : Type v) [TopologicalSpace G] [CompactSpace G]
    (n r : ℕ) :
    Module.Flat A (LocallyConstant (Fin n → G) (Fin r → A)) ∧
      Module.Free A (LocallyConstant (Fin n → G) (Fin r → A)) :=
  ⟨flat_continuousCochains A G n r, free_continuousCochains A hnil G n r⟩

/-- **Lemma `ex:limits-inner-limit`, the inner ultrafilter limit over `Λ`** (tex 4401–4406,
4444–4450).  PROVED (`eventually_sub_ulim_mem`, `stageIdeal_isOpen`,
`lambda_polynomial_identity_survives_of_A`, `ulimVec_eq_of_sub_mem`).

Let `x i : σ → Λ` lift a finite tuple of matrix entries at coefficient stage `A_i = Λ/(2^i, t^i)`
(`StageA i = (ℤ/2^i)[t]/(t^i)`, `stageMap`), and let `U` be a nonprincipal ultrafilter.  Then the
entrywise ultralimit `ulimVec U x ∈ Λ^σ`
1. is a compatible limit at every coefficient precision `(2^n, t^n)`;
2. satisfies every polynomial identity (integer coefficients) that holds in the stages `A_i` for
   `U`-almost every `i` ("Every polynomial identity between the matrices survives");
3. does not depend on the chosen lifts. -/
theorem ex_limits_inner_limit_ultrafilter {σ : Type*} [Finite σ] {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ Filter.cofinite) (x : ℕ → σ → Lambda) :
    (∀ n, ∀ᶠ i in (U : Filter ℕ), ∀ s, x i s - ulimVec U x s ∈ stageIdeal n) ∧
    (∀ P : MvPolynomial σ ℤ,
      (∀ᶠ i in (U : Filter ℕ), MvPolynomial.eval₂ (Int.castRingHom (StageA i))
        (fun s => stageMap i (x i s)) P = 0) →
      MvPolynomial.eval₂ (Int.castRingHom Lambda) (ulimVec U x) P = 0) ∧
    (∀ y : ℕ → σ → Lambda, (∀ᶠ i in (U : Filter ℕ), ∀ s, y i s - x i s ∈ stageIdeal i) →
      ulimVec U y = ulimVec U x) := by
  refine ⟨fun n => ?_, fun P hP => lambda_polynomial_identity_survives_of_A hU x P hP,
    fun y hy => ?_⟩
  · rw [Filter.eventually_all]
    intro s
    simpa [ulimVec_apply] using eventually_sub_ulim_mem (stageIdeal_isOpen n) U (fun i => x i s)
  · exact ulimVec_eq_of_sub_mem stageIdeal_tendsToZero hU hy

/-- **Lemma `ex:limits-inner-limit`: bounded ranks are fixed on a set in the ultrafilter**
(tex 4401–4402, 4444–4445).  PROVED (`bounded_ranks_fixed`). -/
theorem ex_limits_inner_limit_bounded_ranks (U : Ultrafilter ℕ) {B : ℕ} (r : ℕ → ℕ)
    (hr : ∀ i, r i ≤ B) : ∃ r₀ ≤ B, ∀ᶠ i in (U : Filter ℕ), r i = r₀ :=
  bounded_ranks_fixed U r hr

/-- **Lemma `ex:limits-inner-limit`: retained homotopy inverses remain homotopy inverses**
(tex 4448–4449).  PROVED (`homotopy_inverse_survives`, over `Λ` with the stage ideals). -/
theorem ex_limits_inner_limit_homotopy_inverse {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (f : ℕ → Matrix m n Lambda) (g : ℕ → Matrix n m Lambda) (d s d' : ℕ → Matrix m m Lambda)
    (h : ∀ᶠ i in (U : Filter ℕ), ∀ a b,
      (f i * g i - 1 - (d i * s i + s i * d' i) : Matrix m m Lambda) a b ∈ stageIdeal i) :
    ulimMat U f * ulimMat U g - 1 = ulimMat U d * ulimMat U s + ulimMat U s * ulimMat U d' :=
  homotopy_inverse_survives stageIdeal_tendsToZero hU f g d s d' h

/-! ## Lemma `ex:limits-residual-bound` -/

/-- **Lemma `ex:limits-residual-bound`** (tex 4453–4610).  PROVED from the named cohomological
counts `ResidualRankCounts` (`ResidualRankCounts.rank_le`):

  `N(E, A, j) ≤ 56 ω(2N) + 8A + 56j + 70`,  `j = |D|`.

The bound involves only `ω(2N)`, `A` and `j`: it is independent of the number and sizes of the
active primes and of `v₂(r_i − 1)` (tex 4461–4462).  The local counts of the table follow from the
local PRINT propositions by `local_cohomology_dims`; the transfer to the original support
(tex 4612–4647) is in `ResidualAlgebra` (units `((1+t)^{±e} − 1)/t`, contractible active blocks,
`𝔽₂((t))[G]` local with nilpotent augmentation ideal). -/
theorem ex_limits_residual_bound (R : ResidualRankCounts) :
    R.rankTot ≤ 56 * (2 * R.N).primeFactors.card + 8 * R.A + 56 * R.D.card + 70 :=
  R.rank_le

/-- **Transfer to the original support, units** (tex 4620–4626).  PROVED
(`onePlusX_zpow_sub_one_eq_X_mul_unit`, `isUnit_laurentSeries_onePlusX_zpow_sub_one`).

For every odd integer `e` (both `e` and the conjugate exponent `−e`), `(1 + t)^e − 1 = t · u` with
`u` a unit of `𝔽₂[[t]]`; hence `(1 + t)^e − 1` becomes a unit after inverting `t`, in `𝔽₂((t))`. -/
theorem ex_limits_residual_bound_units {e : ℤ} (he : Odd e) :
    (∃ u : PowerSeries (ZMod 2), IsUnit u ∧
      (((onePlusX (ZMod 2)) ^ e : (PowerSeries (ZMod 2))ˣ) : PowerSeries (ZMod 2)) - 1 =
        PowerSeries.X * u) ∧
    IsUnit (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))
      ((((onePlusX (ZMod 2)) ^ e : (PowerSeries (ZMod 2))ˣ) : PowerSeries (ZMod 2)) - 1)) :=
  ⟨onePlusX_zpow_sub_one_eq_X_mul_unit he, isUnit_laurentSeries_onePlusX_zpow_sub_one he⟩

/-- **Transfer to the original support, contractible active blocks** (tex 4618–4627, with the
local model (4.4) of tex 3471–3481).  PROVED (`localModel_contractible`).

With `C = 0` and `A`, `D` invertible (after reduction mod two and inversion of `t`,
`A = D = ((1 + t)^{±e} − 1) I₂`), the local model `V → V × V → V`, `d⁰ v = (A v, C v)`,
`d¹ (v, w) = −C v + D w`, is a complex with an explicit contraction. -/
theorem ex_limits_residual_bound_active_contractible {B V : Type*} [CommRing B] [AddCommGroup V]
    [Module B V] {A C D : V →ₗ[B] V} (hC : C = 0) (hA : IsUnit A) (hD : IsUnit D) :
    localModel_d1 C D ∘ₗ localModel_d0 A C = 0 ∧
      Nonempty (ThreeTermContraction (localModel_d0 A C) (localModel_d1 C D)) :=
  localModel_contractible hC hA hD

/-- **Transfer to the original support, the binary setting** (tex 4633–4640).  PROVED
(`isLocalRing_laurentSeries_monoidAlgebra`, `isNilpotent_ker_augmentation_laurentSeries`).

For a finite elementary abelian two-group `G` (`g² = 1`), `𝔽₂((t))[G]` is a local ring and its
augmentation ideal is nilpotent. -/
theorem ex_limits_residual_bound_binary (G : Type*) [CommGroup G] [Finite G]
    (h : ∀ g : G, g * g = 1) :
    IsLocalRing (MonoidAlgebra (LaurentSeries (ZMod 2)) G) ∧
      IsNilpotent (RingHom.ker (augmentation (LaurentSeries (ZMod 2)) G)) :=
  ⟨isLocalRing_laurentSeries_monoidAlgebra G h, isNilpotent_ker_augmentation_laurentSeries G h⟩

/-! ## Lemma `ex:limits-outer-evaluation` -/

/-- **(5.2) at a finite stage** (tex 4674–4680).  PROVED (`evalOne_comp_d`, `evalTwo_comp_d`).

For a retained cochain map `ι` from a model `C⁰ → C¹ → C²` into the low-degree inhomogeneous
cochains `A → (G → A) → (G × G → A)` (Mathlib's `d₀₁`, `d₁₂`, whose signs are Elliot's), the
evaluations satisfy `e¹_g d = (ρ(g) − 1) e⁰` and `e²_{g,h} d = ρ(g) e¹_h − e¹_{gh} + e¹_g`. -/
theorem ex_limits_outer_evaluation_5_2 {k G : Type u} [CommRing k] [Group G] {A : Rep.{u} k G}
    {C₀ C₁ C₂ : Type*} [AddCommGroup C₀] [Module k C₀] [AddCommGroup C₁] [Module k C₁]
    [AddCommGroup C₂] [Module k C₂] (d₀ : C₀ →ₗ[k] C₁) (d₁ : C₁ →ₗ[k] C₂)
    {ι₀ : C₀ →ₗ[k] A} {ι₁ : C₁ →ₗ[k] (G → A)} {ι₂ : C₂ →ₗ[k] (G × G → A)}
    (h₀ : (groupCohomology.d₀₁ A).hom ∘ₗ ι₀ = ι₁ ∘ₗ d₀)
    (h₁ : (groupCohomology.d₁₂ A).hom ∘ₗ ι₁ = ι₂ ∘ₗ d₁) (g h : G) :
    evalOne ι₁ g ∘ₗ d₀ = (A.ρ g - 1) ∘ₗ evalZero ι₀ ∧
      evalTwo ι₂ g h ∘ₗ d₁ = A.ρ g ∘ₗ evalOne ι₁ h - evalOne ι₁ (g * h) + evalOne ι₁ g :=
  ⟨evalOne_comp_d d₀ h₀ g, evalTwo_comp_d d₁ h₁ g h⟩

/-- **(5.2) in the inner limit: a cycle defines an abstract crossed homomorphism of the product
group** (tex 4681–4684).  PROVED (`crossed_homomorphism_inner_limit`, over `Λ`). -/
theorem ex_limits_outer_evaluation_inner_crossedHom {G : ℕ → Type*} [∀ i, Group (G i)]
    {n : Type*} [Fintype n] {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (ρ : ∀ i, G i → Matrix n n Lambda) (c : ∀ i, G i → n → Lambda)
    (hcoc : ∀ᶠ i in (U : Filter ℕ), ∀ g h : G i, ∀ a,
      (ρ i g *ᵥ c i h - c i (g * h) + c i g) a ∈ stageIdeal i) (g h : ∀ i, G i) :
    rhoInf U ρ g *ᵥ cInf U c h - cInf U c (g * h) + cInf U c g = 0 :=
  crossed_homomorphism_inner_limit stageIdeal_tendsToZero hU ρ c hcoc g h

/-- **Evaluation injectivity: finite detecting lists** (tex 4686–4690).  PROVED
(`exists_detecting_list_pairEvaluation`).

With representatives `V` for `H¹` (`V ∩ B¹ = 0`) and coefficient space `W = A` finite-dimensional,
the evaluations `(c, w) ↦ c(g) − (ρ(g) − 1) w` have common kernel `(0, W^Γ)`, and a list of at most
`dim V + dim W` of them already has that kernel. -/
theorem ex_limits_outer_evaluation_detecting {k G : Type u} [Field k] [Group G] (A : Rep.{u} k G)
    (V : Submodule k (G → A)) (hV : V ⊓ groupCohomology.coboundaries₁ A = ⊥)
    [FiniteDimensional k V] [FiniteDimensional k A] :
    ∃ L : List G, L.length ≤ Module.finrank k V + Module.finrank k A ∧
      (⨅ g ∈ L, LinearMap.ker (pairEvaluation A V g)) =
        (⊥ : Submodule k V).prod A.ρ.invariants :=
  exists_detecting_list_pairEvaluation A V hV

/-- **(5.3): the outer quotient `𝒪_∞` is a DVR with uniformizer two and characteristic-zero
fraction field** (tex 4663–4666, 4719–4730).  PROVED (`instIsDiscreteValuationRing`,
`maximalIdeal_eq_span_algebraMap`, `instCharZero`, `charZero_fractionRing`).

Stated for copies `𝒪_j = R` of any DVR `R` with uniformizer `ϖ` (Elliot: `R = 𝒪`, `ϖ = 2`),
any index set and any ultrafilter (nonprincipality is not needed); completeness is not claimed. -/
theorem ex_limits_outer_evaluation_DVR {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CharZero R] {ι : Type*} (U : Ultrafilter ι) (ϖ : R)
    [Fact (Irreducible ϖ)] :
    IsDiscreteValuationRing (OInf U ϖ) ∧
      maximalIdeal (OInf U ϖ) = Ideal.span {algebraMap R (OInf U ϖ) ϖ} ∧
      CharZero (OInf U ϖ) :=
  ⟨inferInstance, maximalIdeal_eq_span_algebraMap U ϖ, inferInstance⟩

/-- **(5.3) for Elliot's coefficient ring, uncompleted**: `Λ_{(2)}` (`Λ = ℤ₂[[t]]`) is a DVR with
uniformizer `2` and characteristic zero, so (5.3) applies to it.  PROVED.  (Elliot's `𝒪` is its
2-adic completion, again a DVR with uniformizer `2`: GLUE.) -/
theorem ex_limits_outer_evaluation_DVR_Lambda {ι : Type*} (U : Ultrafilter ι) :
    haveI : Fact (Irreducible (2 : Localization.AtPrime (Ideal.span {(2 : ScalarRing.Λ)}))) :=
      ⟨ScalarRing.irreducible_two⟩
    IsDiscreteValuationRing (OInf U (2 : Localization.AtPrime (Ideal.span {(2 : ScalarRing.Λ)}))) ∧
      CharZero (OInf U (2 : Localization.AtPrime (Ideal.span {(2 : ScalarRing.Λ)}))) := by
  have : Fact (Irreducible (2 : Localization.AtPrime (Ideal.span {(2 : ScalarRing.Λ)}))) :=
    ⟨ScalarRing.irreducible_two⟩
  exact ⟨inferInstance, inferInstance⟩

/-- **Approximate cycles suffice** (tex 4740–4742).  PROVED (`outer_isCrossedHom_of_approximate_cycle`).

If the crossed-homomorphism defect of `w_j` is an integral evaluation `e_j(x, y)(dw_j)` of a
coboundary vector with `v(dw_j) →_U ∞`, the image `w_∞` in `𝒪_∞` is an actual crossed homomorphism
of the product group for the outer representation. -/
theorem ex_limits_outer_evaluation_approximate_cycles {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ι : Type*} (U : Ultrafilter ι) {ϖ : R} (hϖ : Irreducible ϖ)
    {G : ι → Type*} [∀ j, Group (G j)] {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k]
    (ρ : ∀ j, G j →* Matrix n n R) (w : ∀ j, G j → n → R)
    (e : ∀ j, G j → G j → Matrix n k R) (dw : ι → k → R)
    (he : ∀ j (x y : G j), cocycleDefect ρ w j x y = e j x y *ᵥ dw j)
    (hdw : ∀ c, Filter.Tendsto (fun j => IsDiscreteValuationRing.addVal R (dw j c)) (U : Filter ι)
      (nhds ⊤))
    (g h : ∀ j, G j) :
    outerRep U ϖ ρ g *ᵥ outerCochain U ϖ w h - outerCochain U ϖ w (g * h) +
      outerCochain U ϖ w g = 0 :=
  outer_isCrossedHom_of_approximate_cycle U hϖ ρ w e dw he hdw g h

end ZInQ.Manuscript.RC.Limits
