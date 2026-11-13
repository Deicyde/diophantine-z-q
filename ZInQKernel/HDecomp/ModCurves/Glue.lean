import ZInQKernel.HDecomp.ModCurves.Leaves

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt3 from
`scratch/leaf-modcurves/ModCurveLeaves.lean`, §I-§J.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

noncomputable section

namespace LeafModCurves

open scoped MatrixGroups ModularForm
open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff HasNebentypus IsNormalizedEigenform scaleH
  oldSpace IsNewform)
open WeierstrassCurve AlgebraicGeometry
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 PkgI3.AbVar

/-! ## §I. G13: `ρ_{f,ι}` is a constituent of `V_ℓ(J₁(N)) ⊗ ℚ̄_ℓ` -/

section G13

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `V_ℓ(π)` for a homomorphism `π : J → A`. -/
def homV {J A : AbVar ℚ} (π : Hom J A) : J.V ℓ →ₗ[ℚ_[ℓ]] A.V ℓ :=
  (homT (ℓ := ℓ) π).baseChange ℚ_[ℓ]

/-- **Glue (standard): a surjective homomorphism of abelian varieties is surjective on `V_ℓ`.**
Not a literature leaf: glue. Proved in `ZInQKernel.HDecomp.ModCurves.E1Sub` as
`E1Sub.vSurjOfSurjective` from `FaltingsSemisimple`, `FaltingsTate` and `TateModuleFree`,
without Poincaré reducibility or isogeny theory (e1-sub §1): the image of `V_ℓ(π)` has a
Galois-stable complement, which Faltings' Tate theorem and the injectivity of `π^*` on
homomorphisms (`π` is dominant and `A` separated) force to vanish. -/
def VSurjOfSurjective : Prop :=
  ∀ (J A : AbVar ℚ) (π : Hom J A) (ℓ : ℕ) [Fact ℓ.Prime], Surjective π.hom.left →
    Function.Surjective (homV ℓ π)

/-- `V_ℓ(π)` is `G_ℚ`-equivariant (from the kernel's `homT_galT`). -/
theorem homV_galRep {J A : AbVar ℚ} (π : Hom J A) (σ : GQ) :
    homV ℓ π ∘ₗ J.galRep ℓ σ = A.galRep ℓ σ ∘ₗ homV ℓ π := by
  have h1 : homT (ℓ := ℓ) π ∘ₗ J.galT σ = A.galT σ ∘ₗ homT π :=
    LinearMap.ext fun t => homT_galT π σ t
  simp only [homV, galRep_apply]
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h1]

/-- Pulling functionals back along `V_ℓ(π)`. -/
def pullback {J A : AbVar ℚ} (π : Hom J A) :
    (A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) →ₗ[PadicAlgCl ℓ] (J.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) where
  toFun φ := φ ∘ₗ homV ℓ π
  map_add' _ _ := LinearMap.add_comp _ _ _
  map_smul' _ _ := LinearMap.smul_comp _ _ _

theorem pullback_injective {J A : AbVar ℚ} (π : Hom J A) (h : Function.Surjective (homV ℓ π)) :
    Function.Injective (pullback ℓ π) := by
  intro φ ψ e
  exact (LinearMap.cancel_right h).1 e

theorem pullback_dualAct {J A : AbVar ℚ} (π : Hom J A) (σ : GQ)
    (φ : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) :
    pullback ℓ π (dualAct ℓ A σ φ) = dualAct ℓ J σ (pullback ℓ π φ) := by
  change (φ ∘ₗ A.galRep ℓ σ) ∘ₗ homV ℓ π = (φ ∘ₗ homV ℓ π) ∘ₗ J.galRep ℓ σ
  rw [LinearMap.comp_assoc, LinearMap.comp_assoc, homV_galRep]

/-- **G13 (glue, proved from R16 and `VSurjOfSurjective`).** For a newform `f` of level `N`, a
`J₁(N)` `J`, a prime `ℓ` and an embedding `ι : K_f → ℚ̄_ℓ`: there is a 2-dimensional
`G_ℚ`-stable space `W` of `ℚ_ℓ`-linear functionals on `V_ℓ(J)` (i.e. a 2-dimensional quotient
`(V_ℓ(J) ⊗ ℚ̄_ℓ) ↠ W^∨`), on which every arithmetic Frobenius at `p ∤ Nℓ` acts by
`φ ↦ φ ∘ σ` with trace `ι(a_p(f))` and determinant `ι(χ(p))p`. This is R16's former
placeholder text ("a `G_ℚ`-stable two-dimensional subquotient of `V_ℓ(J₁(N)) ⊗ ℚ̄_ℓ`"). -/
theorem g13_constituent (hR16 : R16_EichlerShimuraJ1') (hV : VSurjOfSurjective) (N : ℕ)
    (hN : 0 < N) (χ : DirichletCharacter ℂ N) (f : CF N 2) (hf : IsNewform f χ) (J : AbVar ℚ)
    (hJ : IsJ1 N J) (ℓ : ℕ) [Fact ℓ.Prime] :
    ∀ emb : coeffField f →+* PadicAlgCl ℓ, ∃ W : Submodule (PadicAlgCl ℓ)
        (J.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ), Module.finrank (PadicAlgCl ℓ) W = 2 ∧
      ∃ hW : ∀ σ : GQ, ∀ φ ∈ W, dualAct ℓ J σ φ ∈ W,
      ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
        (∀ a : coeffField f, (a : ℂ) = coeff f p →
            LinearMap.trace (PadicAlgCl ℓ) W ((dualAct ℓ J σ).restrict (hW σ)) = emb a) ∧
        (∀ c : coeffField f, (c : ℂ) = χ (p : ZMod N) →
            LinearMap.det ((dualAct ℓ J σ).restrict (hW σ)) = emb c * p) := by
  obtain ⟨-, A, π, θ, hπ, -, hrest⟩ := hR16 N χ f J hN hf hJ
  intro emb
  obtain ⟨h2, hfr⟩ := hrest ℓ emb
  have hinj := pullback_injective ℓ π (hV J A π ℓ hπ)
  set E := eigenFun ℓ A θ emb
  let e := Submodule.equivMapOfInjective (pullback ℓ π) hinj E
  have hW : ∀ σ : GQ, ∀ φ ∈ E.map (pullback ℓ π), dualAct ℓ J σ φ ∈ E.map (pullback ℓ π) := by
    rintro σ _ ⟨ψ, hψ, rfl⟩
    exact ⟨dualAct ℓ A σ ψ, dualAct_mem ℓ A θ emb σ ψ hψ, pullback_dualAct ℓ π σ ψ⟩
  have hconj : ∀ σ : GQ, (dualAct ℓ J σ).restrict (hW σ) = e.conj (frobOn ℓ A θ emb σ) := by
    intro σ
    apply LinearMap.ext; intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    apply Subtype.ext
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.restrict_apply, e,
      Submodule.coe_equivMapOfInjective_apply]
    exact (pullback_dualAct ℓ π σ y).symm
  refine ⟨E.map (pullback ℓ π), ?_, hW, fun p hp hpN σ hσ => ?_⟩
  · rw [← e.finrank_eq, h2]
  · obtain ⟨htr, hdet⟩ := hfr p hp hpN σ hσ
    refine ⟨fun a ha => ?_, fun c hc => ?_⟩
    · rw [hconj σ, LinearMap.trace_conj']
      exact htr a ha
    · rw [hconj σ, LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj]
      exact hdet c hc

end G13

/-! ## §J. C9 bridge: R16's `ρ_{f,ι}` satisfies the `AttachedTo` trace clause of `Leaves.lean`

`Leaves.lean` (`PkgI4.GaloisRep.AttachedTo`, used by R14 `EigenformRepExists`) normalizes
coefficients through `ιC : ℚ̄ → ℂ` and `ιL : ℚ̄ → ℚ̄_ℓ`: at `p ∤ Nℓ` there is `α ∈ ℚ̄` with
`ιC α = a_p` and every arithmetic Frobenius has trace `ιL α`. R16 uses `ι : K_f → ℚ̄_ℓ`. The bridge
is `ι := ιL ∘ ιC⁻¹` on `K_f ⊆ ιC(ℚ̄)`. -/

section C9Bridge

/-- Every algebraic complex number is in the image of `ιC : ℚ̄ → ℂ`. -/
theorem exists_preimage (ιC : Qbar →ₐ[ℚ] ℂ) (a : ℂ) (ha : IsIntegral ℚ a) :
    ∃ α : Qbar, ιC α = a := by
  set q := minpoly ℚ a
  have hf : (q.map (algebraMap ℚ Qbar)).Splits := IsAlgClosed.splits _
  have hf0 : q.map (algebraMap ℚ Qbar) ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero ha)
  have hx : ((q.map (algebraMap ℚ Qbar)).map (ιC : Qbar →+* ℂ)).IsRoot a := by
    rw [Polynomial.map_map, ιC.comp_algebraMap, Polynomial.IsRoot,
      Polynomial.eval_map_algebraMap]
    exact minpoly.aeval ℚ a
  obtain ⟨α, hα⟩ := hf.mem_range_of_isRoot hf0 hx
  exact ⟨α, hα⟩

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `ιL ∘ ιC⁻¹` on a number field `K ⊆ ℂ`. -/
def embOf (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) (K : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ K] : K →+* PadicAlgCl ℓ :=
  have pre : ∀ a : K, ∃ α : Qbar, ιC α = a := fun a =>
    exists_preimage ιC a ((IsIntegral.of_finite ℚ a).map K.val)
  have hinj : Function.Injective ιC := ιC.toRingHom.injective
  { toFun := fun a => ιL (Classical.choose (pre a))
    map_one' := by
      rw [show Classical.choose (pre 1) = 1 from hinj ((Classical.choose_spec (pre 1)).trans
        (by simp)), map_one]
    map_mul' := fun a b => by
      rw [← map_mul, show Classical.choose (pre (a * b)) =
        Classical.choose (pre a) * Classical.choose (pre b) from hinj
          ((Classical.choose_spec (pre (a * b))).trans (by
            rw [map_mul, Classical.choose_spec (pre a), Classical.choose_spec (pre b)]; simp))]
    map_zero' := by
      rw [show Classical.choose (pre 0) = 0 from hinj ((Classical.choose_spec (pre 0)).trans
        (by simp)), map_zero]
    map_add' := fun a b => by
      rw [← map_add, show Classical.choose (pre (a + b)) =
        Classical.choose (pre a) + Classical.choose (pre b) from hinj
          ((Classical.choose_spec (pre (a + b))).trans (by
            rw [map_add, Classical.choose_spec (pre a), Classical.choose_spec (pre b)]; simp))] }

theorem embOf_spec (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) (K : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ K] (a : K) (α : Qbar) (h : ιC α = a) : embOf ℓ ιC ιL K a = ιL α := by
  have pre : ∃ β : Qbar, ιC β = a := ⟨α, h⟩
  change ιL (Classical.choose _) = ιL α
  congr 1
  exact ιC.toRingHom.injective ((Classical.choose_spec
    (exists_preimage ιC a ((IsIntegral.of_finite ℚ a).map K.val))).trans h.symm)

/-- **C9 bridge (proved from R16).** For a newform `f` of level `N`, any `J₁(N)`, a prime `ℓ` and
embeddings `ιC : ℚ̄ → ℂ`, `ιL : ℚ̄ → ℚ̄_ℓ`: Shimura's `A_f` and a 2-dimensional representation
`ρ = rhoF` of `G_ℚ` over `ℚ̄_ℓ` (the `ιL ∘ ιC⁻¹`-component of `V_ℓ(A_f)`) such that for every
prime `p ∤ Nℓ` there is `α ∈ ℚ̄` with `ιC α = a_p(f)` and every arithmetic Frobenius at a place
above `p` (in the sense of `Leaves.lean`, `PkgI4.IsArithFrob`) has trace `ιL α`: the trace clause
of `PkgI4.GaloisRep.AttachedTo`. Together with R14's attached representation and Brauer–Nesbitt
this identifies the two (C9), once both are known semisimple and continuous. -/
theorem rhoF_attached (hR16 : R16_EichlerShimuraJ1') (N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (f : CF N 2) (hf : IsNewform f χ) (J : AbVar ℚ) (hJ : IsJ1 N J)
    (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) :
    ∃ (_ : FiniteDimensional ℚ (coeffField f)) (A : AbVar ℚ) (π : Hom J A)
      (θ : coeffField f →+* A.End0), Surjective π.hom.left ∧
      Module.finrank (PadicAlgCl ℓ)
        (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ (embOf ℓ ιC ιL (coeffField f)))) = 2 ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ∃ α : Qbar, ιC α = coeff f p ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) σ) =
            ιL α := by
  obtain ⟨hfin, A, π, θ, hπ, -, hrest⟩ := hR16 N χ f J hN hf hJ
  refine ⟨hfin, A, π, θ, hπ, ?_⟩
  set emb := embOf ℓ ιC ιL (coeffField f)
  obtain ⟨h2, hfr⟩ := hrest ℓ emb
  refine ⟨finrank_rhoF ℓ A θ emb h2, fun p hp hpN => ?_⟩
  obtain ⟨α, hα⟩ := exists_preimage ιC (coeff f p)
    ((IsIntegral.of_finite ℚ (⟨coeff f p, coeff_mem_coeffField f p⟩ : coeffField f)).map
      (coeffField f).val)
  refine ⟨α, hα, fun v σ hv hσ => ?_⟩
  have hF := isFrobAt_of_isArithFrob σ v p hp hv hσ
  rw [trace_rhoF ℓ A θ emb h2, (hfr p hp hpN σ hF).1 ⟨coeff f p, coeff_mem_coeffField f p⟩ rfl]
  exact embOf_spec ℓ ιC ιL (coeffField f) _ α hα

end C9Bridge

end LeafModCurves
