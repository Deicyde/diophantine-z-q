import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.SelmerSES
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.SignAxes
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.OuterMinors
import ZInQKernel.Contrib.CloudB3RC53.UniformSwitch.Outer

/-!
# RC53 SwitchInputs: the switch inputs plugged into the UniformSwitch GLUE structures

Proposition `ex:limits-uniform-lower-bound`, the switching paragraphs (tex L4927–4972 for the outer
process, L4976–5195 for the height-one process). The files `UniformSwitch/Regularity.lean` and
`UniformSwitch/Outer.lean` build RC16's switching processes from GLUE inputs (`NonquadDims`,
`QuadMixedDims`, `QuadSingleDims`, `HeightOneSwitchData`, `OuterSwitchData.minor_link`). This file
produces those inputs from the Selmer-level results of `SwitchInputs`:

* `nonquadDims_of_selmerData` (tex L4997–5003, L5055–5086): an actual `NonquadDims` from Selmer data
  of a switch (the relaxed localization and its finite and singular sides, `SelmerSES`), the
  localization-duality GLUE input and the rank-two detection `F ≤ U`; also
  `NonquadSwitchDims.toNonquadDims`.
* `SwitchSide.h1_exact`, `SwitchSide.eF`/`eS`, `SwitchSide.range_gamma`, `SwitchSide.lam_gamma_F`/`_S`
  (PROVED, tex L5076–5083): the cohomology-level exactness and localization squares of a switch side,
  derived from the change-of-local-conditions short exact sequences, in the coordinates `k² × k²`.
* `quadMixedDims_of_selmerSides`, `quadSingleDims_of_selmerSides` (tex L5003–5136): actual
  `QuadMixedDims` / `QuadSingleDims` from the Selmer data of the two sides, where the exactness data
  of `SignAxes.quadMixedDimsOfInputs` are now PROVED; what remains in the type: the involutions on the
  cohomology groups and their compatibility with the switch maps (they come from the Galois cocycle
  involution being compatible with the change of local conditions — GLUE `GaloisCocycleInvolution`
  supplies the involution on one Selmer complex, not on the whole diagram), the identification of the
  two strict cohomology groups, duality and detection (GLUE).
* `SelmerNonquadStep`, `SelmerQuadMixedStep`, `SelmerSwitchData`, `SelmerSwitchData.toSwitchData`,
  `regular_of_selmerSwitchData` (tex L4976–5195): `HeightOneSwitchData` whose dimension inputs are
  Selmer-level switch data with the fiber identifications, and RC16's regularity from it.
* `ModelStage`, `ModelStage.toOuterStage`, `ModelStage.minorLink`, `OuterSwitchData.ofModels`
  (tex L4706–4714, L4957–4959): outer stages built from the genuine outer model (the entrywise image
  of the inner integral models in `Frac 𝒪_∞`, RC6), whose `minor_link` field is PROVED (from
  `OuterMinors`) in its round-3 shape: the inner minors at the position of a nonzero outer minor are
  integral, not negligible, and nonzero on an outer-large set.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Module Matrix Filter ZInQ.Manuscript.RC.Uniform
  ZInQ.Manuscript.RC.Uniform.QuadraticCase ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.UniformSwitch ZInQ.Manuscript.RC.Limits
  ZInQ.Contrib.CloudB3RC53.SelmerDuality

/-! ### The nonquadratic switch dimensions -/

section Nonquad

variable {k : Type} [Field k]

/-- `NonquadSwitchDims` (ExactSequences) is UniformSwitch's `NonquadDims`. PROVED. -/
def NonquadSwitchDims.toNonquadDims {s s' : ℕ} (X : NonquadSwitchDims k s s') :
    NonquadDims (k := k) s s' :=
  ⟨X.U, X.hU, X.k0, X.hs, X.hs'⟩

theorem finiteDimensional_side {R : RelaxedLocalization k}
    {P : Submodule k ((Fin 2 → k) × (Fin 2 → k))} (S : SwitchSide R P)
    [FiniteDimensional k (R.D.G.X 1)] [FiniteDimensional k (R.D.L.X 0)]
    [FiniteDimensional k (S.U₁.X 1)] :
    FiniteDimensional k ((selCx S.Dside).toCC.homology 1) := by
  have : FiniteDimensional k (S.Dside.U.X 1) := by
    change FiniteDimensional k (S.U₁.X 1); infer_instance
  have : FiniteDimensional k (S.Dside.G.X 1) := by
    change FiniteDimensional k (R.D.G.X 1); infer_instance
  have : FiniteDimensional k (S.Dside.L.X 0) := by
    change FiniteDimensional k (R.D.L.X 0); infer_instance
  exact finiteDimensional_h1_selCx S.Dside

/-- **The nonquadratic switch dimensions from Selmer data** (tex L4997–5003, L5055–5086). For the
relaxed localization `R` of a switch with finite side `S_F` and singular side `S_S` sharing the
strict dimension `k₀` (`hk0`), the localization duality `U = U^⊥` (GLUE input
`LocalizationDualityInput`) and the rank-two detection `F ≤ U` give UniformSwitch's
`NonquadDims s s'` with `s = dim H¹(C(U_F))`, `s' = dim H¹(C(U_S))`. Classification: PROVED (from
the GLUE input and the detection hypothesis in its type). -/
def nonquadDims_of_selmerData (R : RelaxedLocalization k)
    (SF : SwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k)))
    (SS : SwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k)))
    [FiniteDimensional k (R.D.G.X 1)] [FiniteDimensional k (R.D.L.X 0)]
    [FiniteDimensional k (SF.U₁.X 1)] [FiniteDimensional k (SS.U₁.X 1)]
    (hk0 : finrank k ((selCx SF.Dstr).toCC.homology 1) =
      finrank k ((selCx SS.Dstr).toCC.homology 1))
    (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1)
    (hdual : LocalizationDualityInput ε σ J hε hσ hJ2 R.U)
    (hdet : finPlane k (Fin 2 → k) (Fin 2 → k) ≤ R.U) :
    NonquadDims (k := k) (finrank k ((selCx SF.Dside).toCC.homology 1))
      (finrank k ((selCx SS.Dside).toCC.homology 1)) where
  U := R.U
  hU := relaxedImageFinite_proof k ε σ J hε hσ hJ2 R.U hdual hdet
  k0 := finrank k ((selCx SF.Dstr).toCC.homology 1)
  hs := (switchDims_of_selmerData R SF SS).1
  hs' := by rw [hk0]; exact (switchDims_of_selmerData R SF SS).2

end Nonquad

/-! ### Cohomology-level exactness of a switch side -/

section Side

variable {k : Type} [Field k]

/-- `H¹` of a relation-indexed chain map. -/
abbrev H1 {A B : GCx k} (f : GHom A B) : A.toCC.homology 1 →ₗ[k] B.toCC.homology 1 :=
  (HomologicalComplex.homologyMap (GHom.toCC f) 1).hom

/-- The relaxed localization `λ : H¹(C_rel) → F ⊕ S = k² × k²`. -/
def RelaxedLocalization.lam (R : RelaxedLocalization k) :
    (selCx R.D).toCC.homology 1 →ₗ[k] (Fin 2 → k) × (Fin 2 → k) :=
  ((h1Equiv R.Wrel R.hWrel).trans R.eR).toLinearMap ∘ₗ H1 (quotMap R.D R.gR)

/-- The relaxed localization image is `U`. PROVED. -/
theorem RelaxedLocalization.range_lam (R : RelaxedLocalization k) :
    LinearMap.range R.lam = R.U := by
  rw [RelaxedLocalization.lam, LinearMap.range_comp]; rfl

variable {R : RelaxedLocalization k} {P : Submodule k ((Fin 2 → k) × (Fin 2 → k))}

/-- **Exactness of a switch side in cohomology** (tex L5080–5083): `H¹(C(U_str)) → H¹(C(U₁))` is
injective with image the kernel of the side localization, and `H¹(C(U₁)) → H¹(C_rel)` has image the
kernel of `H¹(C_rel) → H¹(W₂)`. PROVED (long exact sequences of the two change-of-condition
sequences). -/
theorem SwitchSide.h1_exact (S : SwitchSide R P) :
    Function.Injective (H1 (changeMap S.Dside S.fs)) ∧
    LinearMap.range (H1 (changeMap S.Dside S.fs)) = LinearMap.ker (H1 (quotMap S.Dside S.g₁)) ∧
    LinearMap.range (H1 (changeMap R.D S.f₁)) = LinearMap.ker (H1 (quotMap R.D S.g₂)) := by
  have h1 := S.ses₁
  have h2 := S.ses₂
  refine ⟨?_, (h1.homology_exact₂ 1).moduleCat_range_eq_ker,
    (h2.homology_exact₂ 1).moduleCat_range_eq_ker⟩
  have h0 : Subsingleton ((changeSES S.Dside S.fs S.g₁ S.hfg₁).X₃.homology 0) :=
    subsingleton_h0 S.hW₁
  have mono1 : Mono (HomologicalComplex.homologyMap (changeSES S.Dside S.fs S.g₁ S.hfg₁).f 1) :=
    (h1.homology_exact₁ 0 1 (by simp)).mono_g
      ((@Limits.IsZero.of_iso _ _ _ _ (ModuleCat.isZero_of_subsingleton _) (Iso.refl _)).eq_of_src
        _ _)
  exact (ModuleCat.mono_iff_injective _).mp mono1

/-- The side localization in cohomology is the side quotient map composed with `i`, at the level of
the relaxed localization: `H¹(C(U₁) → W₁)` then `H¹(i)`. -/
theorem SwitchSide.H1_comm (S : SwitchSide R P) (v : (selCx S.Dside).toCC.homology 1) :
    H1 (quotMap R.D R.gR) (H1 (changeMap R.D S.f₁) v) = H1 S.i (H1 (quotMap S.Dside S.g₁) v) := by
  calc H1 (quotMap R.D R.gR) (H1 (changeMap R.D S.f₁) v)
      = (HomologicalComplex.homologyMap
          (GHom.toCC (changeMap R.D S.f₁) ≫ GHom.toCC (quotMap R.D R.gR)) 1).hom v := by
        rw [HomologicalComplex.homologyMap_comp]; rfl
    _ = (HomologicalComplex.homologyMap
          (GHom.toCC (quotMap S.Dside S.g₁) ≫ GHom.toCC S.i) 1).hom v :=
        congrArg (fun f => ModuleCat.Hom.hom (HomologicalComplex.homologyMap f 1) v) S.comm_lam
    _ = H1 S.i (H1 (quotMap S.Dside S.g₁) v) := by
        rw [HomologicalComplex.homologyMap_comp]; rfl

theorem SwitchSide.H1_fac (S : SwitchSide R P) (v : (selCx R.D).toCC.homology 1) :
    H1 (quotMap R.D S.g₂) v = H1 S.p (H1 (quotMap R.D R.gR) v) := by
  calc H1 (quotMap R.D S.g₂) v
      = (HomologicalComplex.homologyMap
          (GHom.toCC (quotMap R.D R.gR) ≫ GHom.toCC S.p) 1).hom v := by
        rw [S.fac_p]
    _ = H1 S.p (H1 (quotMap R.D R.gR) v) := by
        rw [HomologicalComplex.homologyMap_comp]; rfl

/-- Membership in the side plane is membership in the image of `e_R ∘ i¹`. -/
theorem SwitchSide.mem_P (S : SwitchSide R P) (z : (Fin 2 → k) × (Fin 2 → k)) :
    z ∈ LinearMap.range (R.eR.toLinearMap ∘ₗ S.i.f 1 1 rfl) ↔ z ∈ P := by
  rw [S.hP]

/-- **The comparison has image the kernel of the complementary localization** (tex L5080–5083):
if `P = ker π` in `k² × k²`, then `im(H¹(C(U₁)) → H¹(C_rel)) = ker(π ∘ λ)`. PROVED. -/
theorem SwitchSide.range_gamma (S : SwitchSide R P)
    (π : (Fin 2 → k) × (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (hπ : ∀ z, z ∈ P ↔ π z = 0) :
    LinearMap.range (H1 (changeMap R.D S.f₁)) = LinearMap.ker (π ∘ₗ R.lam) := by
  rw [S.h1_exact.2.2]
  obtain ⟨-, -, hpi⟩ := degreeOne_hypotheses S.hW₁ R.hWrel S.hW₂ S.i S.p S.i_inj S.ip_exact
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_ker, S.H1_fac]
  set y := H1 (quotMap R.D R.gR) v
  have hlam : R.lam v = R.eR (h1Equiv R.Wrel R.hWrel y) := rfl
  rw [LinearMap.comp_apply, hlam]
  constructor
  · intro hy
    have hy' : y ∈ LinearMap.ker (H1 S.p) := hy
    rw [hpi] at hy'
    obtain ⟨x, hx⟩ := hy'
    rw [← hx, h1Equiv_natural S.hW₁ R.hWrel]
    have : R.eR (S.i.f 1 1 rfl (h1Equiv S.W₁ S.hW₁ x)) ∈ P :=
      (S.mem_P _).1 ⟨_, rfl⟩
    exact (hπ _).mp this
  · intro h0
    have hmem : R.eR (h1Equiv R.Wrel R.hWrel y) ∈ P := (hπ _).mpr h0
    obtain ⟨w, hw⟩ := (S.mem_P _).2 hmem
    have hw' : S.i.f 1 1 rfl w = h1Equiv R.Wrel R.hWrel y := R.eR.injective hw
    have hy : y ∈ LinearMap.range (H1 S.i) := by
      refine ⟨(h1Equiv S.W₁ S.hW₁).symm w, (h1Equiv R.Wrel R.hWrel).injective ?_⟩
      rw [h1Equiv_natural S.hW₁ R.hWrel, LinearEquiv.apply_symm_apply, hw']
    rw [← hpi] at hy
    exact hy

/-- Finite-side coordinates `W₁¹ ≃ k²` with `e_R ∘ i = inl ∘ e_F`. -/
def SwitchSide.eF (S : SwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k))) :
    S.W₁.X 1 ≃ₗ[k] (Fin 2 → k) :=
  LinearEquiv.ofBijective (LinearMap.fst k _ _ ∘ₗ (R.eR.toLinearMap ∘ₗ S.i.f 1 1 rfl)) (by
    have hmem : ∀ x, (R.eR (S.i.f 1 1 rfl x)).2 = 0 := fun x => by
      have : (R.eR.toLinearMap ∘ₗ S.i.f 1 1 rfl) x ∈ finPlane k (Fin 2 → k) (Fin 2 → k) :=
        (S.mem_P _).1 (LinearMap.mem_range_self _ x)
      exact (mem_finPlane).1 this
    refine ⟨fun x y hxy => ?_, fun v => ?_⟩
    · have : R.eR (S.i.f 1 1 rfl x) = R.eR (S.i.f 1 1 rfl y) :=
        Prod.ext hxy (by rw [hmem, hmem])
      exact S.i_inj (R.eR.injective this)
    · have : ((v, 0) : (Fin 2 → k) × (Fin 2 → k)) ∈ finPlane k (Fin 2 → k) (Fin 2 → k) :=
        (mem_finPlane).2 rfl
      obtain ⟨x, hx⟩ := (S.mem_P _).2 this
      exact ⟨x, by simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hx ⊢; rw [hx]; rfl⟩)

theorem SwitchSide.eF_spec (S : SwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k)))
    (x : S.W₁.X 1) : R.eR (S.i.f 1 1 rfl x) = inlF (S.eF x) := by
  have : (R.eR.toLinearMap ∘ₗ S.i.f 1 1 rfl) x ∈ finPlane k (Fin 2 → k) (Fin 2 → k) :=
    (S.mem_P _).1 (LinearMap.mem_range_self _ x)
  exact Prod.ext rfl ((mem_finPlane).1 this)

/-- Singular-side coordinates `W₁¹ ≃ k²` with `e_R ∘ i = inr ∘ e_S`. -/
def SwitchSide.eS (S : SwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k))) :
    S.W₁.X 1 ≃ₗ[k] (Fin 2 → k) :=
  LinearEquiv.ofBijective (LinearMap.snd k _ _ ∘ₗ (R.eR.toLinearMap ∘ₗ S.i.f 1 1 rfl)) (by
    have hmem : ∀ x, (R.eR (S.i.f 1 1 rfl x)).1 = 0 := fun x => by
      have : (R.eR.toLinearMap ∘ₗ S.i.f 1 1 rfl) x ∈ singPlane k (Fin 2 → k) (Fin 2 → k) :=
        (S.mem_P _).1 (LinearMap.mem_range_self _ x)
      exact (mem_singPlane).1 this
    refine ⟨fun x y hxy => ?_, fun v => ?_⟩
    · have : R.eR (S.i.f 1 1 rfl x) = R.eR (S.i.f 1 1 rfl y) :=
        Prod.ext (by rw [hmem, hmem]) hxy
      exact S.i_inj (R.eR.injective this)
    · have : ((0, v) : (Fin 2 → k) × (Fin 2 → k)) ∈ singPlane k (Fin 2 → k) (Fin 2 → k) :=
        (mem_singPlane).2 rfl
      obtain ⟨x, hx⟩ := (S.mem_P _).2 this
      exact ⟨x, by simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hx ⊢; rw [hx]; rfl⟩)

theorem SwitchSide.eS_spec (S : SwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k)))
    (x : S.W₁.X 1) : R.eR (S.i.f 1 1 rfl x) = inrS (S.eS x) := by
  have : (R.eR.toLinearMap ∘ₗ S.i.f 1 1 rfl) x ∈ singPlane k (Fin 2 → k) (Fin 2 → k) :=
    (S.mem_P _).1 (LinearMap.mem_range_self _ x)
  exact Prod.ext ((mem_singPlane).1 this) rfl

/-- The finite localization `β : H¹(C(U_F)) → F = k²`. -/
def SwitchSide.βF (S : SwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k))) :
    (selCx S.Dside).toCC.homology 1 →ₗ[k] (Fin 2 → k) :=
  ((h1Equiv S.W₁ S.hW₁).trans S.eF).toLinearMap ∘ₗ H1 (quotMap S.Dside S.g₁)

/-- The singular localization `β' : H¹(C(U_S)) → S = k²`. -/
def SwitchSide.βS (S : SwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k))) :
    (selCx S.Dside).toCC.homology 1 →ₗ[k] (Fin 2 → k) :=
  ((h1Equiv S.W₁ S.hW₁).trans S.eS).toLinearMap ∘ₗ H1 (quotMap S.Dside S.g₁)

/-- **The finite localization square** `λ ∘ γ = inl ∘ β` (tex L5076–5083). PROVED. -/
theorem SwitchSide.lam_gamma_F (S : SwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k))) :
    R.lam ∘ₗ H1 (changeMap R.D S.f₁) = inlF ∘ₗ S.βF := by
  ext1 v
  simp only [LinearMap.comp_apply, RelaxedLocalization.lam, SwitchSide.βF, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply]
  rw [S.H1_comm v, h1Equiv_natural S.hW₁ R.hWrel, S.eF_spec]
  rfl

/-- **The singular localization square** `λ ∘ γ' = inr ∘ β'`. PROVED. -/
theorem SwitchSide.lam_gamma_S (S : SwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k))) :
    R.lam ∘ₗ H1 (changeMap R.D S.f₁) = inrS ∘ₗ S.βS := by
  ext1 v
  simp only [LinearMap.comp_apply, RelaxedLocalization.lam, SwitchSide.βS, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply]
  rw [S.H1_comm v, h1Equiv_natural S.hW₁ R.hWrel, S.eS_spec]
  rfl

theorem SwitchSide.range_alpha_F (S : SwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k))) :
    LinearMap.range (H1 (changeMap S.Dside S.fs)) = LinearMap.ker S.βF := by
  rw [SwitchSide.βF, LinearEquiv.ker_comp]; exact S.h1_exact.2.1

theorem SwitchSide.range_alpha_S (S : SwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k))) :
    LinearMap.range (H1 (changeMap S.Dside S.fs)) = LinearMap.ker S.βS := by
  rw [SwitchSide.βS, LinearEquiv.ker_comp]; exact S.h1_exact.2.1

end Side

/-! ### The quadratic switch dimensions from the Selmer data of the two sides -/

section Quad

variable {k : Type} [Field k]

/-- **The equivariant Selmer data of a quadratic switch** (tex L5003–5086). The relaxed
localization `R` with its finite and singular sides, an identification `eK` of the two strict
cohomology groups (the strict condition `D⁰` is shared, tex L5072–5075), and involutions on the four
cohomology groups compatible with the switch maps and with the local involution `(x, y) ↦ (Jx, −Jy)`
on `F ⊕ S`. The involutions and their compatibilities are the cohomology-level form of the Galois
cocycle involution (`GaloisCocycleInvolution`, GLUE) acting compatibly on the change-of-condition
diagram; they are stated here, not derived. -/
structure SelmerQuadSwitch (k : Type) [Field k] (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) where
  R : RelaxedLocalization k
  SF : SwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k))
  SS : SwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k))
  fG : FiniteDimensional k (R.D.G.X 1)
  fL : FiniteDimensional k (R.D.L.X 0)
  fF : FiniteDimensional k (SF.U₁.X 1)
  fS : FiniteDimensional k (SS.U₁.X 1)
  eK : (selCx SS.Dstr).toCC.homology 1 ≃ₗ[k] (selCx SF.Dstr).toCC.homology 1
  σK : (selCx SF.Dstr).toCC.homology 1 →ₗ[k] (selCx SF.Dstr).toCC.homology 1
  σV : (selCx SF.Dside).toCC.homology 1 →ₗ[k] (selCx SF.Dside).toCC.homology 1
  σV' : (selCx SS.Dside).toCC.homology 1 →ₗ[k] (selCx SS.Dside).toCC.homology 1
  σr : (selCx R.D).toCC.homology 1 →ₗ[k] (selCx R.D).toCC.homology 1
  hK : σK ∘ₗ σK = LinearMap.id
  hV : σV ∘ₗ σV = LinearMap.id
  hV' : σV' ∘ₗ σV' = LinearMap.id
  hr : σr ∘ₗ σr = LinearMap.id
  hα' : H1 (changeMap SF.Dside SF.fs) ∘ₗ σK = σV ∘ₗ H1 (changeMap SF.Dside SF.fs)
  hβ' : SF.βF ∘ₗ σV = J ∘ₗ SF.βF
  hγ' : H1 (changeMap R.D SF.f₁) ∘ₗ σV = σr ∘ₗ H1 (changeMap R.D SF.f₁)
  hα'' : (H1 (changeMap SS.Dside SS.fs) ∘ₗ eK.symm.toLinearMap) ∘ₗ σK =
    σV' ∘ₗ (H1 (changeMap SS.Dside SS.fs) ∘ₗ eK.symm.toLinearMap)
  hβ'' : SS.βS ∘ₗ σV' = (-J) ∘ₗ SS.βS
  hγ'' : H1 (changeMap R.D SS.f₁) ∘ₗ σV' = σr ∘ₗ H1 (changeMap R.D SS.f₁)
  hl : R.lam ∘ₗ σr = localInv J ∘ₗ R.lam

variable {J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)}

theorem SelmerQuadSwitch.fin_V (X : SelmerQuadSwitch k J) :
    FiniteDimensional k ((selCx X.SF.Dside).toCC.homology 1) := by
  have := X.fG; have := X.fL; have := X.fF; exact finiteDimensional_side X.SF

theorem SelmerQuadSwitch.fin_V' (X : SelmerQuadSwitch k J) :
    FiniteDimensional k ((selCx X.SS.Dside).toCC.homology 1) := by
  have := X.fG; have := X.fL; have := X.fS; exact finiteDimensional_side X.SS

theorem SelmerQuadSwitch.alphaS_inj (X : SelmerQuadSwitch k J) :
    Function.Injective (H1 (changeMap X.SS.Dside X.SS.fs) ∘ₗ X.eK.symm.toLinearMap) :=
  X.SS.h1_exact.1.comp X.eK.symm.injective

theorem SelmerQuadSwitch.alphaS_range (X : SelmerQuadSwitch k J) :
    LinearMap.range (H1 (changeMap X.SS.Dside X.SS.fs) ∘ₗ X.eK.symm.toLinearMap) =
      LinearMap.ker X.SS.βS := by
  exact (LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range X.eK.symm)).trans
    X.SS.range_alpha_S

/-- **The mixed-sign quadratic switch dimensions from Selmer data** (tex L5003–5122): UniformSwitch's
`QuadMixedDims` for the sign dimensions of `V = H¹(C(U_F))` and `V' = H¹(C(U_S))`. The exactness
inputs of `quadMixedDimsOfInputs` are PROVED from the Selmer data (`SwitchSide.h1_exact`,
`range_gamma`, `lam_gamma_F/S`); in the type remain the equivariance data (`SelmerQuadSwitch`),
the duality `U = U^⊥` (GLUE, Nekovář 6.3.3–6.3.4) and the detecting prime (GLUE `DetectingPrime`).
Classification: PROVED (from those inputs). -/
noncomputable def SelmerQuadSwitch.toQuadMixedDims (X : SelmerQuadSwitch k J) (h2 : (2 : k) ≠ 0)
    (ε : k) (hε : ε ≠ 0) (hJ2 : J ∘ₗ J = LinearMap.id) (ep em : Fin 2 → k) (hp : J ep = ep)
    (hm : J em = -em) (he : e₂ ep em ≠ 0)
    (hU : ∀ u, u ∈ X.R.U ↔ ∀ w ∈ X.R.U, localPair ε J u w = 0)
    (cp cm : (selCx X.SF.Dside).toCC.homology 1) (hcp : X.σV cp = cp) (hcm : X.σV cm = -cm)
    (hdet : DetectingPrime X.σV (X.R.lam ∘ₗ H1 (changeMap X.R.D X.SF.f₁)) cp cm) :
    QuadMixedDims (k := k) (finrank k ↥(signPart X.σV (1 : k))) (finrank k ↥(signPart X.σV (-1 : k)))
      (finrank k ↥(signPart X.σV' (1 : k))) (finrank k ↥(signPart X.σV' (-1 : k))) :=
  haveI := X.fin_V
  haveI := X.fin_V'
  quadMixedDimsOfInputs h2 ε hε J hJ2 ep em hp hm he
    (H1 (changeMap X.SF.Dside X.SF.fs)) X.SF.βF (H1 (changeMap X.R.D X.SF.f₁))
    (H1 (changeMap X.SS.Dside X.SS.fs) ∘ₗ X.eK.symm.toLinearMap) X.SS.βS
    (H1 (changeMap X.R.D X.SS.f₁)) X.R.lam X.σK X.σV X.σV' X.σr X.hK X.hV X.hV' X.hr
    X.hα' X.hβ' X.hγ' X.hα'' X.hβ'' X.hγ'' X.hl
    X.SF.h1_exact.1 X.SF.range_alpha_F
    (X.SF.range_gamma (LinearMap.snd k _ _) (fun _ => mem_finPlane)) X.SF.lam_gamma_F
    X.alphaS_inj X.alphaS_range
    (X.SS.range_gamma (LinearMap.fst k _ _) (fun _ => mem_singPlane)) X.SS.lam_gamma_S
    (fun u => by rw [X.R.range_lam]; exact hU u) cp cm hcp hcm hdet _ _ _ _ rfl rfl rfl rfl

/-- **The single-sign quadratic switch dimensions from Selmer data** (tex L5123–5136):
UniformSwitch's `QuadSingleDims`, with the same proved exactness inputs; in the type remain the
equivariance data, duality (GLUE) and the `+`-sign detecting prime (GLUE `DetectingPrimePlus`).
Classification: PROVED (from those inputs). -/
noncomputable def SelmerQuadSwitch.toQuadSingleDims (X : SelmerQuadSwitch k J) (h2 : (2 : k) ≠ 0)
    (ε : k) (hε : ε ≠ 0) (hJ2 : J ∘ₗ J = LinearMap.id) (ep em : Fin 2 → k) (hp : J ep = ep)
    (hm : J em = -em) (he : e₂ ep em ≠ 0)
    (hU : ∀ u, u ∈ X.R.U ↔ ∀ w ∈ X.R.U, localPair ε J u w = 0)
    (cp : (selCx X.SF.Dside).toCC.homology 1) (hcp : X.σV cp = cp)
    (hdet : DetectingPrimePlus X.σV (X.R.lam ∘ₗ H1 (changeMap X.R.D X.SF.f₁)) cp)
    (hs1 : 1 < finrank k ↥(signPart X.σV (1 : k)))
    (hs0 : 0 = finrank k ↥(signPart X.σV (-1 : k))) :
    QuadSingleDims (k := k) (finrank k ↥(signPart X.σV (1 : k)))
      (finrank k ↥(signPart X.σV' (1 : k))) (finrank k ↥(signPart X.σV' (-1 : k))) :=
  haveI := X.fin_V
  haveI := X.fin_V'
  quadSingleDimsOfInputs h2 ε hε J hJ2 ep em hp hm he
    (H1 (changeMap X.SF.Dside X.SF.fs)) X.SF.βF (H1 (changeMap X.R.D X.SF.f₁))
    (H1 (changeMap X.SS.Dside X.SS.fs) ∘ₗ X.eK.symm.toLinearMap) X.SS.βS
    (H1 (changeMap X.R.D X.SS.f₁)) X.R.lam X.σK X.σV X.σV' X.σr X.hK X.hV X.hV' X.hr
    X.hα' X.hβ' X.hγ' X.hα'' X.hβ'' X.hγ'' X.hl
    X.SF.h1_exact.1 X.SF.range_alpha_F
    (X.SF.range_gamma (LinearMap.snd k _ _) (fun _ => mem_finPlane)) X.SF.lam_gamma_F
    X.alphaS_inj X.alphaS_range
    (X.SS.range_gamma (LinearMap.fst k _ _) (fun _ => mem_singPlane)) X.SS.lam_gamma_S
    (fun u => by rw [X.R.range_lam]; exact hU u) cp hcp hdet _ _ _ hs1 rfl hs0 rfl rfl

end Quad

/-! ### Height-one switching data from Selmer-level switch data -/

section HeightOne

variable {k : Type} [Field k]

/-- **One nonquadratic switch at the Selmer level** (tex L4997–5003, L5055–5086): the relaxed
localization and its two sides with finite-dimensionality, a shared strict dimension, the duality
GLUE input and rank-two detection. -/
structure SelmerNonquadStep (k : Type) [Field k] where
  R : RelaxedLocalization k
  SF : SwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k))
  SS : SwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k))
  fG : FiniteDimensional k (R.D.G.X 1)
  fL : FiniteDimensional k (R.D.L.X 0)
  fF : FiniteDimensional k (SF.U₁.X 1)
  fS : FiniteDimensional k (SS.U₁.X 1)
  hk0 : finrank k ((selCx SF.Dstr).toCC.homology 1) = finrank k ((selCx SS.Dstr).toCC.homology 1)
  ε : k
  σ : k
  J : Matrix (Fin 2) (Fin 2) k
  hε : ε ≠ 0
  hσ : σ ≠ 0
  hJ2 : J * J = 1
  hdual : LocalizationDualityInput ε σ J hε hσ hJ2 R.U
  hdet : finPlane k (Fin 2 → k) (Fin 2 → k) ≤ R.U

/-- `NonquadDims` from a Selmer-level step and the identification of the two fiber dimensions with
the side cohomology dimensions. PROVED. -/
def SelmerNonquadStep.toNonquadDims (X : SelmerNonquadStep k) {s s' : ℕ}
    (hs : s = finrank k ((selCx X.SF.Dside).toCC.homology 1))
    (hs' : s' = finrank k ((selCx X.SS.Dside).toCC.homology 1)) : NonquadDims (k := k) s s' :=
  haveI := X.fG; haveI := X.fL; haveI := X.fF; haveI := X.fS
  let N := nonquadDims_of_selmerData X.R X.SF X.SS X.hk0 X.ε X.σ X.J X.hε X.hσ X.hJ2 X.hdual X.hdet
  ⟨N.U, N.hU, N.k0, hs.trans N.hs, hs'.trans N.hs'⟩

/-- **One mixed-sign quadratic switch at the Selmer level** (tex L5003–5122). -/
structure SelmerQuadMixedStep (k : Type) [Field k] where
  h2 : (2 : k) ≠ 0
  ε : k
  hε : ε ≠ 0
  J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)
  hJ2 : J ∘ₗ J = LinearMap.id
  ep : Fin 2 → k
  em : Fin 2 → k
  hp : J ep = ep
  hm : J em = -em
  he : e₂ ep em ≠ 0
  X : SelmerQuadSwitch k J
  hU : ∀ u, u ∈ X.R.U ↔ ∀ w ∈ X.R.U, localPair ε J u w = 0
  cp : (selCx X.SF.Dside).toCC.homology 1
  cm : (selCx X.SF.Dside).toCC.homology 1
  hcp : X.σV cp = cp
  hcm : X.σV cm = -cm
  hdet : DetectingPrime X.σV (X.R.lam ∘ₗ H1 (changeMap X.R.D X.SF.f₁)) cp cm

/-- **One single-sign quadratic switch at the Selmer level** (tex L5123–5136). -/
structure SelmerQuadSingleStep (k : Type) [Field k] where
  h2 : (2 : k) ≠ 0
  ε : k
  hε : ε ≠ 0
  J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)
  hJ2 : J ∘ₗ J = LinearMap.id
  ep : Fin 2 → k
  em : Fin 2 → k
  hp : J ep = ep
  hm : J em = -em
  he : e₂ ep em ≠ 0
  X : SelmerQuadSwitch k J
  hU : ∀ u, u ∈ X.R.U ↔ ∀ w ∈ X.R.U, localPair ε J u w = 0
  cp : (selCx X.SF.Dside).toCC.homology 1
  hcp : X.σV cp = cp
  hdet : DetectingPrimePlus X.σV (X.R.lam ∘ₗ H1 (changeMap X.R.D X.SF.f₁)) cp
  hs1 : 1 < finrank k ↥(signPart X.σV (1 : k))
  hs0 : 0 = finrank k ↥(signPart X.σV (-1 : k))

/-- Transport of `QuadMixedDims` along equalities of its indices. -/
def QuadMixedDims.cast' {a b c d a' b' c' d' : ℕ} (Q : QuadMixedDims (k := k) a b c d)
    (ha : a' = a) (hb : b' = b) (hc : c' = c) (hd : d' = d) : QuadMixedDims (k := k) a' b' c' d' :=
  { Q with hVp := ha.trans Q.hVp, hVm := hb.trans Q.hVm, hVp' := hc.trans Q.hVp',
           hVm' := hd.trans Q.hVm' }

/-- Transport of `QuadSingleDims` along equalities of its indices. -/
def QuadSingleDims.cast' {s a b s' a' b' : ℕ} (Q : QuadSingleDims (k := k) s a b)
    (hs : s' = s) (ha : a' = a) (hb : b' = b) : QuadSingleDims (k := k) s' a' b' :=
  { Q with hs := hs ▸ Q.hs, hVp := hs.trans Q.hVp, hVp' := ha.trans Q.hVp',
           hVm' := hb.trans Q.hVm' }

variable {A F : Type*} [CommRing A] [Field F]

/-- **Height-one switching data from Selmer-level switch data** (tex L4976–5195). The same data as
UniformSwitch's `HeightOneSwitchData`, except that every dimension input of a switch is given at
the Selmer level — a `SelmerNonquadStep`, `SelmerQuadMixedStep` or `SelmerQuadSingleStep` — together
with the identification of the stage dimensions with the Selmer cohomology dimensions (the stage's
two-term model computes the fiber cohomology of the Selmer complex of that configuration: GLUE
identification, stated per step). The coordinate steps (`CoordStep`) and the sign decomposition
of the stage dimensions stay as in `HeightOneSwitchData`.

Caveat: the stages are not tied to the genuine fibre models; a one-stage datum of fibre dimension 1
(no switch demanded) satisfies the structure, so as a hypothesis it is equivalent to its conclusion
(compare RC's `regularityInputsS_iff`). Linking the stages to the genuine fibre models is pending.
The free `Nonempty (CoordStep …)` inputs reduce to bookkeeping. -/
structure SelmerSwitchData (ι : A →+* F) (ρ : A →+* k) where
  Stage : Type
  stage : Stage → TwoTermStage ι
  quadratic : Prop
  sp : Stage → ℕ
  sm : Stage → ℕ
  sign_sum : quadratic → ∀ S, sp S + sm S = (stage S).fiberDim ρ
  primitive : ∀ S, ∃ i, ρ ((stage S).z i) ≠ 0
  switch_mixed : ∀ S, (¬ quadratic ∨ (0 < sp S ∧ 0 < sm S)) → 1 < (stage S).fiberDim ρ →
    ∃ S', Nonempty (CoordStep ι (stage S).u (stage S').u) ∧
      (quadratic → ∃ Y : SelmerQuadMixedStep k,
        sp S = finrank k ↥(signPart Y.X.σV (1 : k)) ∧ sm S = finrank k ↥(signPart Y.X.σV (-1 : k)) ∧
        sp S' = finrank k ↥(signPart Y.X.σV' (1 : k)) ∧
        sm S' = finrank k ↥(signPart Y.X.σV' (-1 : k))) ∧
      (¬ quadratic → ∃ X : SelmerNonquadStep k,
        (stage S).fiberDim ρ = finrank k ((selCx X.SF.Dside).toCC.homology 1) ∧
        (stage S').fiberDim ρ = finrank k ((selCx X.SS.Dside).toCC.homology 1))
  switch_single : ∀ S, quadratic → ¬ (0 < sp S ∧ 0 < sm S) → 1 < (stage S).fiberDim ρ →
    ∃ S' a b, Nonempty (CoordStep ι (stage S).u (stage S').u) ∧
      (∃ Y : SelmerQuadSingleStep k, (stage S).fiberDim ρ = finrank k ↥(signPart Y.X.σV (1 : k)) ∧
        a = finrank k ↥(signPart Y.X.σV' (1 : k)) ∧ b = finrank k ↥(signPart Y.X.σV' (-1 : k))) ∧
      ((sp S' = a ∧ sm S' = b) ∨ (sp S' = b ∧ sm S' = a))

/-- **The UniformSwitch switching data from the Selmer-level data**: every dimension input of
`HeightOneSwitchData` is produced from the Selmer data. PROVED. -/
noncomputable def SelmerSwitchData.toSwitchData {ι : A →+* F} {ρ : A →+* k}
    (P : SelmerSwitchData ι ρ) : HeightOneSwitchData ι ρ where
  Stage := P.Stage
  stage := P.stage
  quadratic := P.quadratic
  sp := P.sp
  sm := P.sm
  sign_sum := P.sign_sum
  primitive := P.primitive
  switch_mixed S h1 h2 := by
    obtain ⟨S', hc, hq, hn⟩ := P.switch_mixed S h1 h2
    refine ⟨S', hc, fun q => ?_, fun nq => ?_⟩
    · obtain ⟨Y, e1, e2, e3, e4⟩ := hq q
      exact ⟨QuadMixedDims.cast' (Y.X.toQuadMixedDims Y.h2 Y.ε Y.hε Y.hJ2 Y.ep Y.em Y.hp Y.hm Y.he
        Y.hU Y.cp Y.cm Y.hcp Y.hcm Y.hdet) e1 e2 e3 e4⟩
    · obtain ⟨X, e1, e2⟩ := hn nq
      exact ⟨X.toNonquadDims e1 e2⟩
  switch_single S q h1 h2 := by
    obtain ⟨S', a, b, hc, ⟨Y, e1, e2, e3⟩, hab⟩ := P.switch_single S q h1 h2
    exact ⟨S', a, b, hc, ⟨QuadSingleDims.cast' (Y.X.toQuadSingleDims Y.h2 Y.ε Y.hε Y.hJ2 Y.ep Y.em
      Y.hp Y.hm Y.he Y.hU Y.cp Y.hcp Y.hdet Y.hs1 Y.hs0) e1 e2 e3⟩, hab⟩

/-- **Regularity at the height-one prime from Selmer-level switch data** (tex L4976–5195), through
UniformSwitch's `regular_of_switchData` (RC16's `regular_of_switchProcess`): every stage coordinate
lies in `ι(A)`. Classification: PROVED (from the inputs in `SelmerSwitchData`). -/
theorem regular_of_selmerSwitchData [IsLocalRing A] {ι : A →+* F} (hι : Function.Injective ι)
    {ρ : A →+* k} (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) (P : SelmerSwitchData ι ρ)
    (S : P.Stage) : ∃ a : A, ι a = (P.stage S).u :=
  regular_of_switchData hι hρ P.toSwitchData S

end HeightOne

/-! ### The outer process: stages from the genuine outer model -/

section Outer

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}
  [Fact (Irreducible ϖ)] {J : Type} (𝒰 : Ultrafilter J)
  {K : Type} [Field K] [Algebra R K] (v : AddValuation K (WithTop ℤ))

/-- **An outer stage built from integral inner models** (tex L4706–4714, L4927–4940): the inner
models `M j` over `R`, the outer model their entrywise image in `Frac 𝒪_∞` (RC6 `outerMatrix`),
a nonzero outer kernel vector, inner cycles, closed functionals and admissible complements over
`K`. (No good-family condition is needed: the `minor_link` field asks the inner minors to be
nonzero only on an outer-large set, which is what the genuine outer model gives.) -/
structure ModelStage (ϖ : R) (K : Type) [Field K] [Algebra R K] where
  n : ℕ
  M : J → Matrix (Fin (n + 1)) (Fin (n + 1)) R
  zout : Fin (n + 1) → FractionRing (OInf 𝒰 ϖ)
  hzout : (outerMatrix 𝒰 ϖ M).map (algebraMap (OInf 𝒰 ϖ) (FractionRing (OInf 𝒰 ϖ))) *ᵥ zout = 0
  hzout0 : zout ≠ 0
  z : J → Fin (n + 1) → K
  lam : J → Fin (n + 1) → K
  w : J → Fin n → Fin (n + 1) → K
  y : J → Fin (n + 1) → K
  hz : ∀ j, (M j).map (algebraMap R K) *ᵥ z j = 0
  hlam : ∀ j, lam j ᵥ* (M j).map (algebraMap R K) = 0
  hden : ∀ j, detCols (colsDWY ((M j).map (algebraMap R K)) (w j) (y j)) ≠ 0

variable {𝒰}

/-- The outer stage of UniformSwitch attached to a model stage. -/
def ModelStage.toOuterStage (X : ModelStage 𝒰 ϖ K) : OuterStage (FractionRing (OInf 𝒰 ϖ)) K J where
  m := X.n
  Dout := (outerMatrix 𝒰 ϖ X.M).map (algebraMap (OInf 𝒰 ϖ) (FractionRing (OInf 𝒰 ϖ)))
  zout := X.zout
  hzout := X.hzout
  hzout0 := X.hzout0
  n := X.n
  D j := (X.M j).map (algebraMap R K)
  z := X.z
  lam := X.lam
  w := X.w
  y := X.y
  hz := X.hz
  hlam := X.hlam
  hden := X.hden

theorem ModelStage.minorLink_core (hinj : Function.Injective (algebraMap R K))
    (hv : IsPiAdicOn ϖ v) (X : ModelStage 𝒰 ϖ K) (k0 j0 : Fin (X.n + 1))
    (h : (((outerMatrix 𝒰 ϖ X.M).map (algebraMap (OInf 𝒰 ϖ) (FractionRing (OInf 𝒰 ϖ)))).submatrix
      k0.succAbove j0.succAbove).det ≠ 0) :
    ∃ (k1 j1 : Fin (X.n + 1)),
      (∀ᶠ j in (𝒰 : Filter J),
        (((X.M j).map (algebraMap R K)).submatrix k1.succAbove j1.succAbove).det ≠ 0) ∧
      (∀ᶠ j in (𝒰 : Filter J),
        (0 : WithTop ℤ) ≤ v ((((X.M j).map (algebraMap R K)).submatrix k1.succAbove
          j1.succAbove).det)) ∧
      ¬ OuterNegligible v 𝒰
        (fun j => (((X.M j).map (algebraMap R K)).submatrix k1.succAbove j1.succAbove).det) := by
  obtain ⟨hne, hint, hneg⟩ :=
    minorLinkEventually_proof 𝒰 v (ϖ := ϖ) (K := K) X.n X.M hinj hv k0 j0 h
  exact ⟨k0, j0, hne, Eventually.of_forall hint, hneg⟩

/-- **The `minor_link` field for a model stage** (tex L4706–4714, L4957–4959): a nonzero maximal minor
of the outer model gives the inner minors at the same position, nonzero on an outer-large set,
integral, and not outer-negligible — exactly the `minor_link` clause of `OuterSwitchData`.
PROVED (from `OuterMinors`). -/
theorem ModelStage.minorLink (hinj : Function.Injective (algebraMap R K)) (hv : IsPiAdicOn ϖ v)
    (X : ModelStage 𝒰 ϖ K) (k0 j0 : Fin (X.toOuterStage.m + 1))
    (h : (X.toOuterStage.Dout.submatrix k0.succAbove j0.succAbove).det ≠ 0) :
    ∃ (k1 j1 : Fin (X.toOuterStage.n + 1)),
      (∀ᶠ j in (𝒰 : Filter J), ((X.toOuterStage.D j).submatrix k1.succAbove j1.succAbove).det ≠ 0) ∧
      (∀ᶠ j in (𝒰 : Filter J),
        (0 : WithTop ℤ) ≤ v (((X.toOuterStage.D j).submatrix k1.succAbove j1.succAbove).det)) ∧
      ¬ OuterNegligible v 𝒰 (fun j => ((X.toOuterStage.D j).submatrix k1.succAbove j1.succAbove).det) :=
  X.minorLink_core v hinj hv k0 j0 h

/-- **Outer switching data from model stages** (tex L4927–4964): UniformSwitch's `OuterSwitchData`
whose `minor_link` field is PROVED from the genuine outer model (`ModelStage.minorLink`); the inner
integrality, the functional bound and the switch inputs remain as in `OuterSwitchData` (for the
switch's `NonquadDims` over `Frac 𝒪_∞`, `SelmerNonquadStep.toNonquadDims` applies). PROVED. -/
def OuterSwitchData.ofModels (hinj : Function.Injective (algebraMap R K)) (hv : IsPiAdicOn ϖ v)
    {a : ℕ} (Stage : Type) (stage : Stage → ModelStage 𝒰 ϖ K)
    (cycle_integral : ∀ S j i, (0 : WithTop ℤ) ≤ v ((stage S).toOuterStage.z j i))
    (functional_bound : ∀ S j i, (((-a : ℤ)) : WithTop ℤ) ≤ v ((stage S).toOuterStage.lam j i))
    (switch : ∀ S, 1 < (stage S).toOuterStage.outerDim → ∃ S',
      Nonempty (NonquadDims (k := FractionRing (OInf 𝒰 ϖ)) (stage S).toOuterStage.outerDim
        (stage S').toOuterStage.outerDim) ∧
      ∀ᶠ j in (𝒰 : Filter J), ∃ X : SwitchCoordData K,
        v X.μF = 0 ∧ v X.μS = 0 ∧ (stage S).toOuterStage.coord j = X.uF ∧
          (stage S').toOuterStage.coord j = X.uS) :
    OuterSwitchData (Kout := FractionRing (OInf 𝒰 ϖ)) v 𝒰 a where
  Stage := Stage
  stage S := (stage S).toOuterStage
  minor_link S := (stage S).minorLink v hinj hv
  cycle_integral := cycle_integral
  functional_bound := functional_bound
  switch := switch

end Outer

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
