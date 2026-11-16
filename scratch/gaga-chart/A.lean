import ZInQKernel.OneProof.H.TailQ
import ZInQKernel.Contrib.OneProof.SmoothComplexManifoldEtale

open scoped Manifold ContDiff Topology
open Set Filter CategoryTheory AlgebraicGeometry Limits MonObj

set_option linter.unusedSectionVars false

noncomputable section

namespace GAGAAn

open UnifPrinted UnifTopology BPAnalytic BPAnalytic.Uniformization
open PkgI3 (AbVar)

/-- The complex-analytic manifold structure of `X^an`: a charted space on `X(ℂ)` (over the given
topology) that is an analytic manifold, in which regular functions are holomorphic on `U(ℂ)`, and
in which some regular functions are local holomorphic coordinates at every point. These are the
three clauses of `UnifTopology.SmoothComplexManifoldAn`. -/
def IsAnStr (X : Over (Spec (CommRingCat.of ℂ))) (n : ℕ) [TopologicalSpace (CPt X)]
    [ChartedSpace (Fin n → ℂ) (CPt X)] : Prop :=
  IsManifold 𝓘(ℂ, Fin n → ℂ) ω (CPt X) ∧
  (∀ (U : X.left.Opens) (f : Γ(X.left, U)),
    ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) ω (XevalAt X U f) {P | XPtIn X P U}) ∧
  (∀ P : CPt X, ∃ (U : X.left.Opens) (f : Fin n → Γ(X.left, U)), XPtIn X P U ∧
    IsLocalDiffeomorphAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω (fun Q i => XevalAt X U (f i) Q) P)

/-- **GAGA for maps of complex abelian varieties, chart form.** -/
def GAGAChart : Prop :=
  ∀ (A B : AbVar ℂ) (n m : ℕ),
    letI := analyticTopology A.X
    letI := analyticTopology B.X
    ∀ (_ : ChartedSpace (Fin n → ℂ) (CPt A.X)) (_ : ChartedSpace (Fin m → ℂ) (CPt B.X)),
      IsAnStr A.X n → IsAnStr B.X m →
      ∀ F : CPt A.X → CPt B.X, ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin m → ℂ) ω F →
        ∃ f : A.X ⟶ B.X, ∀ P, F P = P ≫ f


/-! ## Glue -/

section Glue

variable {X : Over (Spec (CommRingCat.of ℂ))}

/-- **Holomorphy into `X(ℂ)` from regular functions.** A map `G` into `X(ℂ)`, continuous at `x`,
such that every regular function composed with `G` is holomorphic at `x`, is holomorphic at `x`
(through the regular local coordinates of `IsAnStr`). -/
theorem contMDiffAt_of_regular {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {m : ℕ}
    [TopologicalSpace (CPt X)] [ChartedSpace (Fin m → ℂ) (CPt X)]
    (hX : IsAnStr X m) (G : M → CPt X) (x : M) (hc : ContinuousAt G x)
    (hreg : ∀ (U : X.left.Opens) (f : Γ(X.left, U)), XPtIn X (G x) U →
      ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (fun y => XevalAt X U f (G y)) x) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, Fin m → ℂ) ω G x := by
  obtain ⟨hMan, -, hcoords⟩ := hX
  have := hMan
  obtain ⟨U, f, hU, hloc⟩ := hcoords (G x)
  set c : CPt X → (Fin m → ℂ) := fun Q i => XevalAt X U (f i) Q
  have hcG : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, Fin m → ℂ) ω (fun y => c (G y)) x :=
    contMDiffAt_pi_module_iff.mpr fun i => hreg U (f i) hU
  have hinv := hloc.contMDiffAt_localInverse
  have heq : G =ᶠ[𝓝 x] (fun y => hloc.localInverse (c (G y))) := by
    have h2 := hloc.localInverse_eventuallyEq_left.comp_tendsto hc
    filter_upwards [h2] with y hy
    exact hy.symm
  exact (hinv.comp x hcG).congr_of_eventuallyEq heq

/-- An analytic homomorphism `ℂ^n → B(ℂ)` is continuous for the classical topology. -/
theorem continuous_analyticHom {B : AbVar ℂ} {n : ℕ} {ψ : (Fin n → ℂ) → CPt B.X}
    (hψ : ZInQ.HomLattice.IsAnalyticHom (RingHom.id ℂ) ψ) :
    Continuous[_, classicalTopology B.X] ψ := by
  let _ := classicalTopology B.X
  refine continuous_generateFrom_iff.mpr ?_
  rintro _ ⟨V, g, w, ε, rfl⟩
  have hev : ∀ z, XevalAt B.X V g (ψ z) = ZInQ.LeafPush2.cEvalAt (ψ z) V g := fun z =>
    (ZInQ.LeafPush2.cEvalAt_eq_evalAt B (ψ z) V g).symm
  have hO : IsOpen (ZInQ.LeafPush2.cDom ψ V ∩
      (fun z => ZInQ.LeafPush2.cEvalAt (ψ z) V g) ⁻¹' Metric.ball w ε) :=
    (hψ.2.2 V g).continuousOn.isOpen_inter_preimage (hψ.2.1 V) Metric.isOpen_ball
  convert hO using 1
  ext z
  simp only [mem_preimage, mem_inter_iff, Metric.mem_ball, dist_eq_norm, ← hev]
  rfl

/-- `φ⁻¹` is continuous for the classical topology (clause (iii) of a uniformization). -/
theorem continuousAt_symm {A : AbVar ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {φ : Torus Λ ≃+ Additive (A.Pt ℂ)} (hφ : IsUniformization A Λ φ) (P₀ : CPt A.X) :
    @ContinuousAt _ _ (classicalTopology A.X) _ (fun P : CPt A.X => φ.symm (Additive.ofMul P)) P₀ := by
  let _ := classicalTopology A.X
  set v₀ := (φ.symm (Additive.ofMul P₀)).out
  have hv₀ : proj Λ v₀ = φ.symm (Additive.ofMul P₀) := QuotientAddGroup.out_eq' _
  have hP₀ : Additive.toMul (φ (proj Λ v₀)) = P₀ := by
    rw [hv₀, AddEquiv.apply_symm_apply]; rfl
  intro N hN
  replace hN : N ∈ 𝓝 (proj Λ v₀) := by rw [hv₀]; exact hN
  obtain ⟨U, k, f, ε, hε, hU, hsep⟩ := hφ.open_map v₀ N hN
  rw [hP₀] at hU hsep
  set S := {P : CPt A.X | XPtIn A.X P U} ∩
    ⋂ i, {P | XPtIn A.X P U ∧ ‖XevalAt A.X U (f i) P - XevalAt A.X U (f i) P₀‖ < ε}
  have hS : IsOpen S :=
    (isOpen_ptIn U).inter (isOpen_iInter_of_finite fun i => isOpen_basic _ _ _)
  have hP₀S : P₀ ∈ S := ⟨hU, mem_iInter.mpr fun i => ⟨hU, by simpa using hε⟩⟩
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (hS.mem_nhds hP₀S) ?_
  rintro P ⟨hPU, hPi⟩
  obtain ⟨q, hq, hqP⟩ := hsep P hPU fun i => (mem_iInter.mp hPi i).2
  show φ.symm (Additive.ofMul P) ∈ N
  rw [← hqP]
  simpa using hq

end Glue

/-! ## Main theorem -/

/-- **`GAGAMorphism` from the chart form of GAGA (proved).** The hypothesis of `GAGAMorphism`
(an analytic homomorphism `ψ : ℂ^g → B(ℂ)` killing `Λ`, given through a strong uniformization `φ`
of `A`) gives a map `F : A(ℂ) → B(ℂ)`, `F (φ (proj v)) = ψ v`, holomorphic in any charts of `A^an`
and `B^an` (`IsAnStr`): near `P₀ = φ (proj v₀)`, `F = ψ ∘ L ∘ Θ` with `Θ` regular coordinates of `A`
(clause (ii) of the uniformization) and `L` the analytic local inverse of `Θ ∘ φ ∘ proj` (analytic
inverse function theorem). The charts exist by `SmoothComplexManifoldAn`; the analyticity of `ψ`
comes from a uniformization of `B` (`ψ = φ_B ∘ proj ∘ D`, `D` linear). -/
theorem gagaMorphism_of_chart (hU : UniformizationLeafAll) (hMan : SmoothComplexManifoldAn)
    (hG : GAGAChart) : ZInQ.HomLattice.GAGAMorphism := by
  intro A B g Λ _ φ hφs ψ hψ hker
  have hφ : IsUniformization A Λ φ := ZInQ.HomLattice.bp_of_isStrongUnif hφs
  obtain ⟨g', ΛB, hdB, -, φB, hφB⟩ := hU B
  obtain ⟨D, hD⟩ := ZInQ.HomLattice.exists_complexLinear_of_analytic_strong
    (ZInQ.HomLattice.isStrongUnif_of_bp hφB) hψ
  let tA : TopologicalSpace (CPt A.X) := analyticTopology A.X
  let tB : TopologicalSpace (CPt B.X) := analyticTopology B.X
  obtain ⟨n, cA, hA⟩ := hMan A.X inferInstance inferInstance inferInstance
  obtain ⟨m, cB, hB⟩ := hMan B.X inferInstance inferInstance inferInstance
  have hA' : IsAnStr A.X n := hA
  have hB' : IsAnStr B.X m := hB
  -- `ψ` is constant on `Λ`-cosets
  let ψ' : (Fin g → ℂ) → CPt B.X := ψ
  have hψ' : ZInQ.HomLattice.IsAnalyticHom (RingHom.id ℂ) ψ' := hψ
  have hψΛ : ∀ v w : Fin g → ℂ, v - w ∈ Λ → ψ' v = ψ' w := by
    intro v w h
    have := hψ.1 w (v - w)
    rw [add_sub_cancel, hker _ h, _root_.mul_one] at this
    exact this
  let Φ : (Fin g → ℂ) → CPt A.X := fun v => Additive.toMul (φ (proj Λ v))
  let F : CPt A.X → CPt B.X := fun P => ψ' (φ.symm (Additive.ofMul P)).out
  have hFψ : ∀ v, F (Φ v) = ψ' v := by
    intro v
    show ψ' (φ.symm (Additive.ofMul (Additive.toMul (φ (proj Λ v))))).out = ψ' v
    rw [ofMul_toMul, AddEquiv.symm_apply_apply]
    apply hψΛ
    have h := QuotientAddGroup.out_eq' (proj Λ v)
    rw [QuotientAddGroup.eq_iff_sub_mem] at h
    simpa using h
  have hDv : ∀ z, ψ' z = Additive.toMul (φB (proj ΛB (D z))) := fun z => (hD z).symm
  have hF : ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin m → ℂ) ω F := by
    intro P₀
    set q₀ := φ.symm (Additive.ofMul P₀) with hq₀
    set v₀ := q₀.out with hv₀def
    have hv₀ : proj Λ v₀ = q₀ := QuotientAddGroup.out_eq' _
    have hP₀ : Φ v₀ = P₀ := by
      show Additive.toMul (φ (proj Λ v₀)) = P₀
      rw [hv₀, hq₀, AddEquiv.apply_symm_apply]; rfl
    obtain ⟨U, fA, e, hU0, hder⟩ := hφ.coords v₀
    have hU : XPtIn A.X P₀ U := by rw [← hP₀]; exact hU0
    set Gf : (Fin g → ℂ) → (Fin g → ℂ) :=
      fun v i => evalAt A U (fA i) (Additive.toMul (φ (proj Λ v))) with hGf
    have hGa : AnalyticAt ℂ Gf v₀ := AnalyticAt.pi fun i => (hφ.holo U (fA i)).2 v₀ hU0
    have hGc : ContDiffAt ℂ ω Gf v₀ := hGa.contDiffAt
    have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
    set L := hGc.localInverse hder hn with hLdef
    have hL : ContDiffAt ℂ ω L (Gf v₀) := hGc.to_localInverse hder hn
    have hs' := hGc.hasStrictFDerivAt' hder hn
    have hLG : ∀ᶠ v in 𝓝 v₀, L (Gf v) = v := hs'.eventually_left_inverse
    have hLv₀ : L (Gf v₀) = v₀ := hGc.localInverse_apply_image hder hn
    set Θ : CPt A.X → (Fin g → ℂ) := fun P i => XevalAt A.X U (fA i) P with hΘdef
    have hΘG : ∀ v, Θ (Φ v) = Gf v := fun v => rfl
    have hΘP₀ : Θ P₀ = Gf v₀ := by rw [← hΘG v₀, hP₀]
    -- `F = ψ ∘ L ∘ Θ` near `P₀`
    have hloc : F =ᶠ[𝓝 P₀] fun P => ψ' (L (Θ P)) := by
      have h1 : proj Λ '' {v | L (Gf v) = v} ∈ 𝓝 q₀ := by
        rw [← hv₀]; exact QuotientAddGroup.isOpenMap_coe.image_mem_nhds hLG
      have hc : ContinuousAt (fun P : CPt A.X => φ.symm (Additive.ofMul P)) P₀ := by
        have := continuousAt_symm hφ P₀
        rwa [classicalTopology_eq_analyticTopology] at this
      filter_upwards [hc h1] with P hP
      obtain ⟨v, hv, hvP⟩ := hP
      have hPv : P = Φ v := by
        show P = Additive.toMul (φ (proj Λ v))
        rw [hvP, AddEquiv.apply_symm_apply]; rfl
      rw [hPv, hFψ, hΘG, hv]
    have hΘ : ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin g → ℂ) ω Θ P₀ := by
      refine contMDiffAt_pi_module_iff.mpr fun i => ?_
      exact (hA'.2.1 U (fA i) P₀ hU).contMDiffAt ((SGA1Etale.isOpen_ptIn_an U).mem_nhds hU)
    have hLΘ : ContinuousAt (fun P => L (Θ P)) P₀ := by
      have hLc : ContinuousAt L (Θ P₀) := by rw [hΘP₀]; exact hL.continuousAt
      exact hLc.comp hΘ.continuousAt
    have hLΘP₀ : L (Θ P₀) = v₀ := by rw [hΘP₀, hLv₀]
    refine contMDiffAt_of_regular hB' F P₀ ?_ ?_
    · have hψc : Continuous ψ' := by
        have := continuous_analyticHom (B := B) (ψ := ψ') hψ'
        rwa [classicalTopology_eq_analyticTopology] at this
      have h2 : ContinuousAt (fun P => ψ' (L (Θ P))) P₀ := hψc.continuousAt.comp hLΘ
      exact h2.congr hloc.symm
    · intro V g₀ hV
      have hFP₀ : F P₀ = ψ' v₀ := by rw [← hP₀, hFψ]
      have hh : AnalyticAt ℂ (fun z => XevalAt B.X V g₀ (ψ' z)) v₀ := by
        have hV' : PtIn B (Additive.toMul (φB (proj ΛB (D v₀)))) V := by
          rw [← hDv, ← hFP₀]; exact hV
        have h1 := (hφB.holo V g₀).2 (D v₀) hV'
        have h2 : AnalyticAt ℂ
            (fun z => evalAt B V g₀ (Additive.toMul (φB (proj ΛB (D z))))) v₀ :=
          h1.comp (D.analyticAt v₀)
        refine h2.congr (Eventually.of_forall fun z => ?_)
        show evalAt B V g₀ (Additive.toMul (φB (proj ΛB (D z)))) = XevalAt B.X V g₀ (ψ' z)
        rw [hDv z]; rfl
      have hcomp : ContDiffAt ℂ ω (fun w => XevalAt B.X V g₀ (ψ' (L w))) (Θ P₀) := by
        have hh' : ContDiffAt ℂ ω (fun z => XevalAt B.X V g₀ (ψ' z)) (L (Θ P₀)) := by
          rw [hLΘP₀]; exact hh.contDiffAt
        have hL' : ContDiffAt ℂ ω L (Θ P₀) := by rw [hΘP₀]; exact hL
        exact hh'.comp (Θ P₀) hL'
      have h3 := (contMDiffAt_iff_contDiffAt.mpr hcomp).comp P₀ hΘ
      refine h3.congr_of_eventuallyEq ?_
      filter_upwards [hloc] with P hP
      simp only [Function.comp_apply, hP]
  obtain ⟨f, hf⟩ := hG A B n m cA cB hA' hB' F hF
  refine ⟨f, fun z => ?_⟩
  exact (hFψ z).symm.trans (hf (Φ z))

end GAGAAn

#print axioms GAGAAn.gagaMorphism_of_chart
