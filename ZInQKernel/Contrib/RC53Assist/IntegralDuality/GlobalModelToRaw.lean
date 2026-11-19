import ZInQKernel.Contrib.RC53Assist.CalibrationModel.IntegralReplacement
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.TorsionFreeDualExactness
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.RetainedCupMap
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.NekovarIntegralGlobal

/-!
# From bounded finite free global models to the raw global cup adjoint

Finite generation and bounded support of cohomology construct the models and
both actual comparison maps. Scoped exactness of duals on torsion-free
complexes then cancels the comparisons from the printed model statement.
The final bridge has no raw duality, self-injectivity, or supplied comparison
quasi-isomorphism input.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.CalibrationModel
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.SwitchInputs

section Models
variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- The chosen integral Smith presentations, retaining their actual relations. -/
def cohomologyPresentations (A : GCx R)
    (hfg : ∀ n : ℤ, Module.Finite R (A.toCC.homology n)) :
    ∀ n : ℤ, FreeResolution (R := R) (A.toCC.homology n) :=
  fun n => (chosenPresentations A.toCC hfg n).toFreeResolution

/-- The chosen finite free resolution of the actual cohomology modules. -/
def cohomologyModel (A : GCx R) (hfg : ∀ n : ℤ, Module.Finite R (A.toCC.homology n)) : GCx R :=
  resolutionGCx A.toCC (cohomologyPresentations A hfg)

/-- The comparison obtained from lifted cohomology generators and relations. -/
def cohomologyModelComparison (A : GCx R)
    (hfg : ∀ n : ℤ, Module.Finite R (A.toCC.homology n)) : GHom (cohomologyModel A hfg) A :=
  relationHomOfCochainHom (resolutionComparison A.toCC (cohomologyPresentations A hfg))

/-- The relation-indexed comparison is exactly the constructed cochain comparison. -/
theorem cohomologyModelComparison_toCC (A : GCx R)
    (hfg : ∀ n : ℤ, Module.Finite R (A.toCC.homology n)) :
    GHom.toCC (cohomologyModelComparison A hfg) =
      resolutionComparison A.toCC (cohomologyPresentations A hfg) :=
  relationHomOfCochainHom_toCC _

/-- Its quasi-isomorphism is proved from finite cohomology, not supplied as data. -/
theorem cohomologyModelComparison_quasiIso (A : GCx R)
    (hfg : ∀ n : ℤ, Module.Finite R (A.toCC.homology n)) :
    QuasiIso (GHom.toCC (cohomologyModelComparison A hfg)) := by
  rw [cohomologyModelComparison_toCC]
  exact resolutionComparison_quasiIso A.toCC (cohomologyPresentations A hfg)

/-- Bounded cohomology makes the chosen model bounded, with the lower endpoint
shifted down by one to accommodate relations. -/
theorem cohomologyModel_boundedFiniteFree (A : GCx R)
    (hfg : ∀ n : ℤ, Module.Finite R (A.toCC.homology n))
    (hout : ∃ lo hi : ℤ, ∀ n, n < lo ∨ hi < n → Subsingleton (A.toCC.homology n)) :
    IsBoundedFiniteFree (cohomologyModel A hfg) := by
  obtain ⟨lo, hi, h⟩ := hout
  refine ⟨⟨lo - 1, hi, ?_⟩, ?_⟩
  · intro n hn
    have h0 := chosenDiagonalResolution_zero (hfg n) (h n (by omega))
    have h1 := chosenDiagonalResolution_zero (hfg (n + 1)) (h (n + 1) (by omega))
    change Subsingleton
      ((Fin (chosenDiagonalResolution (hfg n)).generators → R) ×
        (Fin (chosenDiagonalResolution (hfg (n + 1))).relations → R))
    rw [h0.1, h1.2]
    infer_instance
  · intro n
    exact resolutionComplex_finite_free A.toCC (cohomologyPresentations A hfg) n

/-- The constructed model has torsion-free terms over the domain. -/
theorem cohomologyModel_torsionFree (A : GCx R)
    (hfg : ∀ n : ℤ, Module.Finite R (A.toCC.homology n)) (n : ℤ) :
    Module.IsTorsionFree R ((cohomologyModel A hfg).X n) := by
  have : Module.Free R ((cohomologyModel A hfg).X n) :=
    (resolutionComplex_finite_free A.toCC (cohomologyPresentations A hfg) n).1
  infer_instance

/-- A nonzero cohomology class has a nonzero preimage under the constructed
comparison; the resolution cannot hide it in a zero model. -/
theorem cohomologyModel_nonzero_preimage (A : GCx R)
    (hfg : ∀ n : ℤ, Module.Finite R (A.toCC.homology n)) (n : ℤ)
    (y : A.toCC.homology n) (hy : y ≠ 0) :
    ∃ x : (cohomologyModel A hfg).toCC.homology n,
      (HomologicalComplex.homologyMap (GHom.toCC (cohomologyModelComparison A hfg)) n).hom x = y ∧
        x ≠ 0 := by
  letI := cohomologyModelComparison_quasiIso A hfg
  have hs : Function.Surjective
      (HomologicalComplex.homologyMap (GHom.toCC (cohomologyModelComparison A hfg)) n).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨x, hx⟩ := hs y
  refine ⟨x, hx, ?_⟩
  intro hzero
  apply hy
  rw [← hx, hzero, map_zero]

end Models

section Cancellation
variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]

/-- Cancel two actual model comparisons from the same pulled-back duality map.
The dual comparison is proved quasi-isomorphic by torsion-free exactness. -/
theorem rawDuality_quasiIso_of_comparisons {A B P Q : GCx R} (m : ℤ)
    (f : GHom A (dualCx B m)) (c : GHom P A) (c' : GHom Q B)
    (hc : QuasiIso (GHom.toCC c)) (hc' : QuasiIso (GHom.toCC c'))
    (hQ : ∀ n : ℤ, Module.IsTorsionFree R (Q.X n))
    (hB : ∀ n : ℤ, Module.IsTorsionFree R (B.X n))
    (hpull : QuasiIso (GHom.toCC (ghomComp (ghomComp c f) (dualHom c' m)))) :
    QuasiIso (GHom.toCC f) := by
  have := hc
  have := dualHom_quasiIso_torsionFree c' hQ hB m hc'
  have hcf : QuasiIso (GHom.toCC c ≫ GHom.toCC f) := by
    apply (quasiIso_iff_comp_right (GHom.toCC c ≫ GHom.toCC f)
      (GHom.toCC (dualHom c' m))).1
    simpa only [GHom.toCC_comp] using hpull
  exact (quasiIso_iff_comp_left (GHom.toCC c) (GHom.toCC f)).1 hcf

/-- A universal bounded-model duality statement implies raw duality once finite
cohomology and support construct the comparisons internally. -/
theorem rawDuality_quasiIso_of_finite_cohomology (A B : GCx R) (m : ℤ)
    (f : GHom A (dualCx B m))
    (hfgA : ∀ n : ℤ, Module.Finite R (A.toCC.homology n))
    (hfgB : ∀ n : ℤ, Module.Finite R (B.toCC.homology n))
    (houtA : ∃ lo hi : ℤ, ∀ n, n < lo ∨ hi < n → Subsingleton (A.toCC.homology n))
    (houtB : ∃ lo hi : ℤ, ∀ n, n < lo ∨ hi < n → Subsingleton (B.toCC.homology n))
    (hB : ∀ n : ℤ, Module.IsTorsionFree R (B.X n))
    (hmodels : ∀ (P Q : GCx R), IsBoundedFiniteFree P → IsBoundedFiniteFree Q →
      ∀ (c : GHom P A) (c' : GHom Q B),
        QuasiIso (GHom.toCC c) → QuasiIso (GHom.toCC c') →
          QuasiIso (GHom.toCC (ghomComp (ghomComp c f) (dualHom c' m)))) :
    QuasiIso (GHom.toCC f) := by
  let P := cohomologyModel A hfgA
  let Q := cohomologyModel B hfgB
  let c := cohomologyModelComparison A hfgA
  let c' := cohomologyModelComparison B hfgB
  have hc := cohomologyModelComparison_quasiIso A hfgA
  have hc' := cohomologyModelComparison_quasiIso B hfgB
  have hpull := hmodels P Q (cohomologyModel_boundedFiniteFree A hfgA houtA)
    (cohomologyModel_boundedFiniteFree B hfgB houtB) c c' hc hc'
  exact rawDuality_quasiIso_of_comparisons m f c c' hc hc'
    (cohomologyModel_torsionFree B hfgB) hB hpull

end Cancellation

section Cochains
variable {R : Type} [CommRing R] [IsDomain R]
  (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type) [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] [ContinuousSMul G M]
  [Module.IsTorsionFree R M]

/-- Continuous cochain terms inherit torsion-freeness by their actual pointwise inclusion. -/
theorem continuousCochain_torsionFree (n : ℕ) :
    Module.IsTorsionFree R (contCochain R G M n) := by
  have : Module.IsTorsionFree R
      ((groupCohomology.inhomogeneousCochains (rep R G M)).X n) :=
    inferInstanceAs (Module.IsTorsionFree R ((Fin n → G) → M))
  infer_instance

/-- The raw global continuous complex is torsion-free in every integer degree. -/
theorem rawGlobal_terms_torsionFree (n : ℤ) :
    Module.IsTorsionFree R ((globalCx R G M).X n) := by
  cases n with
  | ofNat n =>
    change Module.IsTorsionFree R (contCochain R G M n)
    exact continuousCochain_torsionFree G M n
  | negSucc n =>
    change Module.IsTorsionFree R PUnit
    infer_instance

end Cochains

section StrictCompact
variable {R : Type} [CommRing R] [IsDomain R]
  (GS : Type) [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
  {ι : Type} (Gv : ι → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →ₜ* GS)
  (M : Type) [AddCommGroup M] [Module R M] [DistribMulAction GS M] [SMulCommClass GS R M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] [ContinuousSMul GS M]
  [Module.IsTorsionFree R M]

/-- Restriction of the group action does not change the scalar torsion-freeness. -/
theorem rawLocal_terms_torsionFree (v : ι) (n : ℤ) :
    Module.IsTorsionFree R ((localCx R GS Gv loc M v).X n) := by
  have : Module.IsTorsionFree R (ResMod (loc v) M) :=
    inferInstanceAs (Module.IsTorsionFree R M)
  exact rawGlobal_terms_torsionFree (Gv v) (ResMod (loc v) M) n

/-- The actual product of local cochains has torsion-free terms, with no finite
rank assertion about those raw terms. -/
theorem rawLocalSum_terms_torsionFree (n : ℤ) :
    Module.IsTorsionFree R ((localSumCx R GS Gv loc M).X n) := by
  have : ∀ v, Module.IsTorsionFree R ((localCx R GS Gv loc M v).X n) :=
    fun v => rawLocal_terms_torsionFree GS Gv loc M v n
  change Module.IsTorsionFree R (∀ v, (localCx R GS Gv loc M v).X n)
  infer_instance

/-- The raw compact cone of the strict data has torsion-free terms. -/
theorem rawCompact_terms_torsionFree (n : ℤ) :
    Module.IsTorsionFree R ((compactCx (selData R GS Gv loc M
      (strictConditions R GS Gv loc M))).X n) := by
  have := rawGlobal_terms_torsionFree (R := R) GS M n
  have := rawLocalSum_terms_torsionFree (R := R) GS Gv loc M (n - 1)
  change Module.IsTorsionFree R
    ((globalCx R GS M).X n × (localSumCx R GS Gv loc M).X (n - 1))
  infer_instance

end StrictCompact

section Arithmetic

variable (K : Type) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K)))
  (M M' : Type)
  [AddCommGroup M] [Module ℤ_[2] M] [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) ℤ_[2] M]
  [TopologicalSpace M] [IsModuleTopology ℤ_[2] M]
  [ContinuousAdd M] [ContinuousConstSMul ℤ_[2] M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module ℤ_[2] M'] [Module.Free ℤ_[2] M'] [Module.Finite ℤ_[2] M']
  [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) ℤ_[2] M']
  [TopologicalSpace M'] [IsModuleTopology ℤ_[2] M']
  [ContinuousAdd M'] [ContinuousConstSMul ℤ_[2] M'] [ContinuousSMul (GKS K S) M']
  (β : M →ₗ[ℤ_[2]] M' →ₗ[ℤ_[2]] IntegralTate1 K S)
  (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun x : M × M' => β x.1 x.2)

/-- The actual raw global source, not a chosen replacement. -/
abbrev strictRawGlobal : GCx ℤ_[2] := globalCx ℤ_[2] (GKS K S) M

/-- The actual compact cochains of the strict data on the second coefficients. -/
abbrev strictRawCompact : GCx ℤ_[2] :=
  compactCx (selData ℤ_[2] (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) M'
    (strictConditions ℤ_[2] (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) M'))

/-- The printed global model duality yields quasi-isomorphism of the actual raw
strict global adjoint. Both models and their quasi-isomorphisms are constructed
from ordinary finite-generation and cohomological support hypotheses. -/
theorem strictRawGlobalDuality_quasiIso (hprint : NekovarIntegralGlobalDuality)
    (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hperfect : Function.Bijective β) (hperfect' : Function.Bijective β.flip)
    (tr : (coneCx (strictPairData ℤ_[2] (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) β hβ hβc).resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr : ∀ z, tr ((coneCx (strictPairData ℤ_[2] (GKS K S)
      (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ hβc).resE).d 2 3 rfl z) = 0)
    (htrace : InducesIsoH3 tr)
    (hfg : ∀ n : ℤ, Module.Finite ℤ_[2] ((strictRawGlobal K S M).toCC.homology n))
    (hfg' : ∀ n : ℤ, Module.Finite ℤ_[2] ((strictRawCompact K S M').toCC.homology n))
    (hout : ∃ lo hi : ℤ, ∀ n, n < lo ∨ hi < n →
      Subsingleton ((strictRawGlobal K S M).toCC.homology n))
    (hout' : ∃ lo hi : ℤ, ∀ n, n < lo ∨ hi < n →
      Subsingleton ((strictRawCompact K S M').toCC.homology n)) :
    QuasiIso (GHom.toCC (globalDualityMap (strictPairData ℤ_[2] (GKS K S)
      (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ hβc) tr htr)) := by
  have : Module.IsTorsionFree ℤ_[2] M' := inferInstance
  apply rawDuality_quasiIso_of_finite_cohomology (strictRawGlobal K S M)
    (strictRawCompact K S M') 3 _ hfg hfg' hout hout'
    (rawCompact_terms_torsionFree (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) M')
  intro P Q hP hQ c c' hc hc'
  exact hprint K hK S hS h2 M M' β hβ hβc hperfect hperfect' tr htr htrace
    P Q hP hQ c c' hc hc'

end Arithmetic

end ZInQ.Contrib.RC53Assist.IntegralDuality
