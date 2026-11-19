import ZInQKernel.Contrib.CloudB3E1TameKummer.TameKummerPlace
import ZInQKernel.Contrib.OneProof.RC.Local.TameLocalQuotientStage
import ZInQKernel.Contrib.RC53Assist.ResidualFiniteness.StageResidual
import ZInQKernel.Contrib.OneProof.RC.Local.TameRingChange

/-!
# Dévissage of the tame comparison along the `2`-adic filtration

Manuscript `diophantine_zq.tex`, tex 3470–3487 (the tame local free model (4.4) and the
comparison of continuous cochains with it), at the finite coefficient stages of the inner limit
(tex 4385–4451).

The comparison `tameCochainMap` is natural in the coefficients (`tameCochainMap_natural`), and both
of its sides are exact functors of finite discrete coefficient modules: a short exact sequence
`0 → M₁ → M₂ → M₃ → 0` of discrete modules gives short exact sequences of continuous cochains
(a continuous cochain into the discrete `M₃` lifts through any set-theoretic section) and of tame
free models. The five lemma along the long exact cohomology sequences then shows that the
comparison for `M₂` is a quasi-isomorphism when it is one for `M₁` and `M₃`. Along
`0 → M[2] → M → 2M → 0` this reduces a coefficient module of `2`-power exponent to modules
killed by `2`.

* `quasiIso_τ₂_of_shortExact`: for a morphism of short exact sequences of `ℤ`-indexed cochain
  complexes in an abelian category, quasi-isomorphisms on the outer terms give one in the middle
  (the five lemma along the long exact homology sequences; Mathlib proves the third-term version).
* `tameInfl`: the comparison for inflated coefficients (`Φ = (φ • ·)`, `g = 1`);
  **`quasiIso_tameInfl_of_ses`**: its quasi-isomorphism property passes from the outer terms of a
  short exact sequence of coefficient modules to the middle;
  **`quasiIso_tameInfl_transport`**: and along equivariant linear bijections.
* `subRep`, `subTor`, `subTwo`, `torIncl`, `twoProj`: inside a finite discrete representation `Y`
  of `Gal(K_w^ur/K_w)` over a ring `A`, the sub-representations on the stable submodules `H`,
  `H[2]`, `2H` and the sequence `0 → H[2] → H → 2H → 0` of inflated coefficient modules;
  **`quasiIso_tameSub_of_base`**: the dévissage, by induction on the exponent.
* `TwoTorsionTameAt`: the comparison for inflated coefficients killed by `2` over every ring;
  **`quasiIso_inflation_of_twoTorsion`**: the comparison for every inflated coefficient module of
  `2`-power exponent over any ring from it; **`twoTorsionTameAt_of_milne`** (lane E1's field case
  at `ZMod 2` with the change of rings of `TameRingChange.lean`) and
  **`quasiIso_inflation_ring_of_milne`**: from the PRINT `MilneADT_I_2_8` alone.
* **`exists_retract_localQuotient_place_stage_milne`**,
  **`exists_retract_twoPlaces_place_stage_milne`**: lane RC31's retractions of the local
  quotients at the stage rings onto the singular blocks, with `TameCochainQuasiIso` replaced by
  `MilneADT_I_2_8`; their inputs are `MilneADT_I_2_8`, `IwasawaGenerators` and
  `GenuineCochainsInjective`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Local

open CategoryTheory CategoryTheory.Limits
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.ResidualFiniteness (isIso_toCC_of_bijective)

/-! ### The five lemma in the middle term -/

section FiveLemma

variable {C : Type*} [Category C] [Abelian C] {S₁ S₂ : ShortComplex (CochainComplex C ℤ)}
  (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

include hS₁ hS₂ in
/-- **The five lemma for the middle term** (tex 3470–3487): for a morphism of short exact
sequences of `ℤ`-indexed cochain complexes in an abelian category, if the maps of the first and
the third complexes are quasi-isomorphisms, so is the map of the middle complexes. Kind: PROVED. -/
theorem quasiIso_τ₂_of_shortExact (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₂ := by
  have hI₁ : ∀ j, IsIso (HomologicalComplex.homologyMap φ.τ₁ j) := fun j =>
    (quasiIsoAt_iff_isIso_homologyMap φ.τ₁ j).1 (h₁.quasiIsoAt j)
  have hI₃ : ∀ j, IsIso (HomologicalComplex.homologyMap φ.τ₃ j) := fun j =>
    (quasiIsoAt_iff_isIso_homologyMap φ.τ₃ j).1 (h₃.quasiIsoAt j)
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hrel : (ComplexShape.up ℤ).Rel (i - 1) i := by simp
  have hrel' : (ComplexShape.up ℤ).Rel i (i + 1) := by simp
  have hmono : Mono (HomologicalComplex.homologyMap φ.τ₂ i) := by
    have := hI₃ (i - 1)
    have := hI₁ i
    have := hI₃ i
    exact Abelian.mono_of_epi_of_mono_of_mono
      ((ComposableArrows.δ₀Functor ⋙ ComposableArrows.δ₀Functor).map
        (HomologicalComplex.HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ (i - 1) i hrel))
      (HomologicalComplex.HomologySequence.composableArrows₅_exact hS₁ (i - 1) i hrel).δ₀.δ₀
      (HomologicalComplex.HomologySequence.composableArrows₅_exact hS₂ (i - 1) i hrel).δ₀.δ₀
      (inferInstanceAs (Epi (HomologicalComplex.homologyMap φ.τ₃ (i - 1))))
      (inferInstanceAs (Mono (HomologicalComplex.homologyMap φ.τ₁ i)))
      (inferInstanceAs (Mono (HomologicalComplex.homologyMap φ.τ₃ i)))
  have hepi : Epi (HomologicalComplex.homologyMap φ.τ₂ i) := by
    have := hI₁ i
    have := hI₃ i
    have := hI₁ (i + 1)
    exact Abelian.epi_of_epi_of_epi_of_mono
      ((ComposableArrows.δlastFunctor ⋙ ComposableArrows.δlastFunctor).map
        (HomologicalComplex.HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ i (i + 1) hrel'))
      (HomologicalComplex.HomologySequence.composableArrows₅_exact hS₁ i (i + 1) hrel').δlast.δlast
      (HomologicalComplex.HomologySequence.composableArrows₅_exact hS₂ i (i + 1) hrel').δlast.δlast
      (inferInstanceAs (Epi (HomologicalComplex.homologyMap φ.τ₁ i)))
      (inferInstanceAs (Epi (HomologicalComplex.homologyMap φ.τ₃ i)))
      (inferInstanceAs (Mono (HomologicalComplex.homologyMap φ.τ₁ (i + 1))))
  exact isIso_of_mono_of_epi _

end FiveLemma

/-! ### The comparison for inflated coefficients along short exact sequences -/

section Generic

variable {A : Type} [CommRing A] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (A) in
/-- **The tame comparison for inflated coefficients** (tex 3470–3487): `tameCochainMap` with
`Φ = (φ • ·)` and `g = 1`, for a discrete module on which `σ` acts trivially. Kind: definition. -/
abbrev tameInfl (M : Type) [AddCommGroup M] [Module A M] [DistribMulAction G M]
    [SMulCommClass G A M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
    (φ σ : G) (q : ℕ) (hq : Odd q) (hσ : ∀ m : M, σ • m = m) (hrel : φ * σ * φ⁻¹ = σ ^ q) :=
  tameCochainMap (DistribSMul.toLinearMap A M φ) LinearMap.id φ σ q hq (fun _ => rfl)
    (fun m => (hσ m).symm) (LinearMap.id_comp _)
    ((LinearMap.comp_id _).trans (LinearMap.id_comp _).symm) hrel

section Cochain

variable {M : Type} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulCommClass G A M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

variable (A G M) in
/-- A continuous cochain read as a function `Gⁿ → M` (tex 3455–3463). Kind: definition. -/
abbrev cfun {n : ℕ} (c : (contCochains A G M).X n) : (Fin n → G) → M :=
  asFun A G M (((contSubCx A G M).el c : contCochain A G M n) :
    (groupCohomology.inhomogeneousCochains (rep A G M)).X n)

/-- Continuous cochains with the same values are equal (tex 3455–3463). Kind: PROVED. -/
theorem cochain_ext {n : ℕ} {c c' : (contCochains A G M).X n}
    (h : ∀ x, cfun A G M c x = cfun A G M c' x) : c = c' :=
  Subtype.ext (funext h)

variable (A G M) in
/-- A continuous function `Gⁿ → M` as a continuous cochain (tex 3455–3463). Kind: definition. -/
def mkCochain {n : ℕ} (F : (Fin n → G) → M) (hF : Continuous F) : (contCochains A G M).X n :=
  (contSubCx A G M).ofSub (⟨F, hF⟩ : contCochain A G M n)

/-- The values of `mkCochain` (tex 3455–3463). Kind: PROVED. -/
theorem cfun_mkCochain {n : ℕ} (F : (Fin n → G) → M) (hF : Continuous F) :
    cfun A G M (mkCochain A G M F hF) = F :=
  rfl

/-- The zero cochain has value zero (tex 3455–3463). Kind: PROVED. -/
theorem cfun_zero {n : ℕ} (x : Fin n → G) : cfun A G M (0 : (contCochains A G M).X n) x = 0 :=
  rfl

end Cochain

section Maps

variable {M₁ M₂ : Type} [AddCommGroup M₁] [Module A M₁] [DistribMulAction G M₁]
  [SMulCommClass G A M₁] [TopologicalSpace M₁] [DiscreteTopology M₁] [ContinuousSMul G M₁]
  [AddCommGroup M₂] [Module A M₂] [DistribMulAction G M₂] [SMulCommClass G A M₂]
  [TopologicalSpace M₂] [DiscreteTopology M₂] [ContinuousSMul G M₂]

/-- The map of cochains of an equivariant linear map acts by composition (tex 3470–3480).
Kind: PROVED. -/
theorem cfun_coef (f : M₁ →ₗ[A] M₂) (hf : ∀ (x : G) (m : M₁), f (x • m) = x • f m) {n : ℕ}
    (c : (contCochains A G M₁).X n) (x : Fin n → G) :
    cfun A G M₂ (((coefCochainMap f continuous_of_discreteTopology hf).f n).hom c) x =
      f (cfun A G M₁ c x) :=
  rfl

/-- The map of the comparison's model of an equivariant linear map (tex 3470–3474).
Kind: definition. -/
abbrev modelInfl (f : M₁ →ₗ[A] M₂) (hf : ∀ (x : G) (m : M₁), f (x • m) = x • f m) (φ : G)
    (q : ℕ) (hq : Odd q) :=
  tameFreeModelMap (DistribSMul.toLinearMap A M₁ φ) LinearMap.id (DistribSMul.toLinearMap A M₂ φ)
    LinearMap.id q hq ((LinearMap.comp_id _).trans (LinearMap.id_comp _).symm)
    (LinearMap.id_comp _) ((LinearMap.comp_id _).trans (LinearMap.id_comp _).symm)
    (LinearMap.id_comp _) f (LinearMap.ext fun m => hf φ m)
    ((LinearMap.comp_id _).trans (LinearMap.id_comp _).symm)

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M₁] [DiscreteTopology M₁]
  [ContinuousSMul G M₁] [TopologicalSpace M₂] [DiscreteTopology M₂] [ContinuousSMul G M₂] in
/-- The model map is the coefficient map in each slot (tex 3470–3474). Kind: PROVED. -/
theorem modelInfl_f (f : M₁ →ₗ[A] M₂) (hf : ∀ (x : G) (m : M₁), f (x • m) = x • f m) (φ : G)
    (q : ℕ) (hq : Odd q) (i : ℤ) (y : cx3X (A := A) M₁ (M₁ × M₁) M₁ i) :
    (modelInfl f hf φ q hq).f i i rfl y = modelCoefF f i y := by
  rcases i with (_ | _ | _ | n) | n <;> rfl

/-- **The naturality square of the comparison for inflated coefficients** (tex 3470–3487).
Kind: PROVED. -/
theorem tameInfl_natural (f : M₁ →ₗ[A] M₂) (hf : ∀ (x : G) (m : M₁), f (x • m) = x • f m)
    (φ σ : G) (q : ℕ) (hq : Odd q) (hσ₁ : ∀ m : M₁, σ • m = m) (hσ₂ : ∀ m : M₂, σ • m = m)
    (hrel : φ * σ * φ⁻¹ = σ ^ q) :
    GHom.toCC (natHom (coefCochainMap f continuous_of_discreteTopology hf)) ≫
        GHom.toCC (tameInfl A M₂ φ σ q hq hσ₂ hrel) =
      GHom.toCC (tameInfl A M₁ φ σ q hq hσ₁ hrel) ≫ GHom.toCC (modelInfl f hf φ q hq) := by
  rw [GHom.toCC_comp, GHom.toCC_comp]
  refine GHom.toCC_ext fun i x => ?_
  change (tameInfl A M₂ φ σ q hq hσ₂ hrel).f i i rfl
      ((natHom (coefCochainMap f continuous_of_discreteTopology hf)).f i i rfl x) =
    (modelInfl f hf φ q hq).f i i rfl ((tameInfl A M₁ φ σ q hq hσ₁ hrel).f i i rfl x)
  refine (tameCochainMap_natural f continuous_of_discreteTopology hf
    (DistribSMul.toLinearMap A M₁ φ) LinearMap.id (DistribSMul.toLinearMap A M₂ φ) LinearMap.id
    φ σ q hq
    (fun _ => rfl) (fun m => (hσ₁ m).symm) (LinearMap.id_comp _)
    ((LinearMap.comp_id _).trans (LinearMap.id_comp _).symm) (fun _ => rfl)
    (fun m => (hσ₂ m).symm) (LinearMap.id_comp _)
    ((LinearMap.comp_id _).trans (LinearMap.id_comp _).symm) hrel i x).trans ?_
  exact (modelInfl_f f hf φ q hq i _).symm

end Maps

section SES

variable {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [Module A M₁] [DistribMulAction G M₁]
  [SMulCommClass G A M₁] [TopologicalSpace M₁] [DiscreteTopology M₁] [ContinuousSMul G M₁]
  [AddCommGroup M₂] [Module A M₂] [DistribMulAction G M₂] [SMulCommClass G A M₂]
  [TopologicalSpace M₂] [DiscreteTopology M₂] [ContinuousSMul G M₂]
  [AddCommGroup M₃] [Module A M₃] [DistribMulAction G M₃] [SMulCommClass G A M₃]
  [TopologicalSpace M₃] [DiscreteTopology M₃] [ContinuousSMul G M₃]
  (ι : M₁ →ₗ[A] M₂) (π : M₂ →ₗ[A] M₃)
  (hιG : ∀ (x : G) (m : M₁), ι (x • m) = x • ι m) (hπG : ∀ (x : G) (m : M₂), π (x • m) = x • π m)

/-- The cochain maps of a complex of coefficient modules compose to zero (tex 3455–3463).
Kind: PROVED. -/
theorem cochainSES_zero (hπι : ∀ m, π (ι m) = 0) :
    GHom.toCC (natHom (coefCochainMap ι continuous_of_discreteTopology hιG)) ≫
      GHom.toCC (natHom (coefCochainMap π continuous_of_discreteTopology hπG)) = 0 := by
  rw [GHom.toCC_comp]
  ext i c
  rcases i with n | n
  · refine cochain_ext (M := M₃) (n := n) fun x => ?_
    change π (ι (cfun A G M₁ c x)) = 0
    exact hπι _
  · rfl

/-- **The continuous cochains of a short exact sequence of discrete coefficient modules form a
short exact sequence** (tex 3455–3463): injectivity and surjectivity hold degreewise, a cochain
killed by `π` takes values in the image of `ι`, and a cochain into `M₃` lifts through a
set-theoretic section (continuity is automatic, the modules being discrete). Kind: PROVED. -/
theorem cochainSES_shortExact (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hπι : ∀ m, π (ι m) = 0) (hex : ∀ m, π m = 0 → ∃ m', ι m' = m) :
    (ShortComplex.mk _ _ (cochainSES_zero ι π hιG hπG hπι)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_
  rcases i with n | n
  · refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.moduleCat_exact_iff]
      intro c hc
      have hc' : ∀ x, π (cfun A G M₂ c x) = 0 := fun x =>
        congrArg (fun d : (contCochains A G M₃).X n => cfun A G M₃ d x) hc
      let sec : M₂ → M₁ := Function.invFun ι
      have hsec : ∀ x, ι (sec (cfun A G M₂ c x)) = cfun A G M₂ c x := fun x =>
        Function.invFun_eq (hex _ (hc' x))
      have hcont : Continuous (cfun A G M₂ c) := ((contSubCx A G M₂).el c).2
      refine ⟨mkCochain A G M₁ (sec ∘ cfun A G M₂ c)
        (continuous_of_discreteTopology.comp hcont), ?_⟩
      refine cochain_ext (M := M₂) (n := n) fun x => ?_
      exact hsec x
    · rw [ModuleCat.mono_iff_injective]
      intro c c' h
      refine cochain_ext (M := M₁) (n := n) fun x => hι ?_
      exact congrArg (fun d : (contCochains A G M₂).X n => cfun A G M₂ d x) h
    · rw [ModuleCat.epi_iff_surjective]
      intro c
      have hcont : Continuous (cfun A G M₃ c) := ((contSubCx A G M₃).el c).2
      refine ⟨mkCochain A G M₂ (Function.surjInv hπ ∘ cfun A G M₃ c)
        (continuous_of_discreteTopology.comp hcont), ?_⟩
      refine cochain_ext (M := M₃) (n := n) fun x => ?_
      exact Function.surjInv_eq hπ _
  · refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.moduleCat_exact_iff]
      intro c _
      exact ⟨PUnit.unit, rfl⟩
    · rw [ModuleCat.mono_iff_injective]
      intro a b _
      rfl
    · rw [ModuleCat.epi_iff_surjective]
      intro c
      exact ⟨PUnit.unit, rfl⟩

variable (φ : G) (q : ℕ) (hq : Odd q)

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M₁] [DiscreteTopology M₁]
  [ContinuousSMul G M₁] [TopologicalSpace M₂] [DiscreteTopology M₂] [ContinuousSMul G M₂]
  [TopologicalSpace M₃] [DiscreteTopology M₃] [ContinuousSMul G M₃] in
/-- The model maps of a complex of coefficient modules compose to zero (tex 3470–3474).
Kind: PROVED. -/
theorem modelSES_zero (hπι : ∀ m, π (ι m) = 0) :
    GHom.toCC (modelInfl ι hιG φ q hq) ≫ GHom.toCC (modelInfl π hπG φ q hq) = 0 := by
  rw [GHom.toCC_comp]
  ext i y
  rcases i with (_ | _ | _ | n) | n
  · change π (ι y) = 0
    exact hπι _
  · change (π.prodMap π) ((ι.prodMap ι) y) = 0
    exact Prod.ext (hπι _) (hπι _)
  · change π (ι y) = 0
    exact hπι _
  · rfl
  · rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M₁] [DiscreteTopology M₁]
  [ContinuousSMul G M₁] [TopologicalSpace M₂] [DiscreteTopology M₂] [ContinuousSMul G M₂]
  [TopologicalSpace M₃] [DiscreteTopology M₃] [ContinuousSMul G M₃] in
/-- **The tame free models of a short exact sequence of coefficient modules form a short exact
sequence** (tex 3470–3474): degreewise `M`, `M × M`, `M`. Kind: PROVED. -/
theorem modelSES_shortExact (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hπι : ∀ m, π (ι m) = 0) (hex : ∀ m, π m = 0 → ∃ m', ι m' = m) :
    (ShortComplex.mk _ _ (modelSES_zero ι π hιG hπG φ q hq hπι)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    rcases i with (_ | _ | _ | n) | n
    · intro y hy
      obtain ⟨m, hm⟩ := hex y hy
      exact ⟨m, hm⟩
    · intro y hy
      have h1 : π y.1 = 0 := congrArg Prod.fst hy
      have h2 : π y.2 = 0 := congrArg Prod.snd hy
      obtain ⟨m1, hm1⟩ := hex _ h1
      obtain ⟨m2, hm2⟩ := hex _ h2
      exact ⟨(m1, m2), Prod.ext hm1 hm2⟩
    · intro y hy
      obtain ⟨m, hm⟩ := hex y hy
      exact ⟨m, hm⟩
    · intro y _
      exact ⟨PUnit.unit, rfl⟩
    · intro y _
      exact ⟨PUnit.unit, rfl⟩
  · rw [ModuleCat.mono_iff_injective]
    rcases i with (_ | _ | _ | n) | n
    · exact hι
    · intro a b h
      exact Prod.ext (hι (congrArg Prod.fst h)) (hι (congrArg Prod.snd h))
    · exact hι
    · intro a b _
      rfl
    · intro a b _
      rfl
  · rw [ModuleCat.epi_iff_surjective]
    rcases i with (_ | _ | _ | n) | n
    · exact hπ
    · intro y
      obtain ⟨m1, hm1⟩ := hπ y.1
      obtain ⟨m2, hm2⟩ := hπ y.2
      exact ⟨(m1, m2), Prod.ext hm1 hm2⟩
    · exact hπ
    · intro y
      exact ⟨PUnit.unit, rfl⟩
    · intro y
      exact ⟨PUnit.unit, rfl⟩

variable (σ : G) (hrel : φ * σ * φ⁻¹ = σ ^ q) (hσ₁ : ∀ m : M₁, σ • m = m)
  (hσ₂ : ∀ m : M₂, σ • m = m) (hσ₃ : ∀ m : M₃, σ • m = m)

/-- **The comparison as a morphism of short exact sequences** (tex 3470–3487): from the
continuous cochains of `0 → M₁ → M₂ → M₃ → 0` to the tame free models. Kind: definition. -/
def tameSESHom (hπι : ∀ m, π (ι m) = 0) :
    ShortComplex.mk _ _ (cochainSES_zero ι π hιG hπG hπι) ⟶
      ShortComplex.mk _ _ (modelSES_zero ι π hιG hπG φ q hq hπι) where
  τ₁ := GHom.toCC (tameInfl A M₁ φ σ q hq hσ₁ hrel)
  τ₂ := GHom.toCC (tameInfl A M₂ φ σ q hq hσ₂ hrel)
  τ₃ := GHom.toCC (tameInfl A M₃ φ σ q hq hσ₃ hrel)
  comm₁₂ := (tameInfl_natural ι hιG φ σ q hq hσ₁ hσ₂ hrel).symm
  comm₂₃ := (tameInfl_natural π hπG φ σ q hq hσ₂ hσ₃ hrel).symm

include hιG hπG in
/-- **The comparison is a quasi-isomorphism in the middle of a short exact sequence of
coefficient modules when it is one at the ends** (tex 3470–3487): the five lemma along the long
exact cohomology sequences of the cochains and of the models. Kind: PROVED. -/
theorem quasiIso_tameInfl_of_ses (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hπι : ∀ m, π (ι m) = 0) (hex : ∀ m, π m = 0 → ∃ m', ι m' = m)
    (h₁ : QuasiIso (GHom.toCC (tameInfl A M₁ φ σ q hq hσ₁ hrel)))
    (h₃ : QuasiIso (GHom.toCC (tameInfl A M₃ φ σ q hq hσ₃ hrel))) :
    QuasiIso (GHom.toCC (tameInfl A M₂ φ σ q hq hσ₂ hrel)) :=
  quasiIso_τ₂_of_shortExact (tameSESHom ι π hιG hπG φ q hq σ hrel hσ₁ hσ₂ hσ₃ hπι)
    (cochainSES_shortExact ι π hιG hπG hι hπ hπι hex)
    (modelSES_shortExact ι π hιG hπG φ q hq hι hπ hπι hex) h₁ h₃

end SES

section Transport

variable {M₁ M₂ : Type} [AddCommGroup M₁] [Module A M₁] [DistribMulAction G M₁]
  [SMulCommClass G A M₁] [TopologicalSpace M₁] [DiscreteTopology M₁] [ContinuousSMul G M₁]
  [AddCommGroup M₂] [Module A M₂] [DistribMulAction G M₂] [SMulCommClass G A M₂]
  [TopologicalSpace M₂] [DiscreteTopology M₂] [ContinuousSMul G M₂]
  (e : M₁ →ₗ[A] M₂) (heG : ∀ (x : G) (m : M₁), e (x • m) = x • e m)

/-- The cochain map of an equivariant linear bijection is bijective in every degree
(tex 3455–3463). Kind: PROVED. -/
theorem natHom_coef_bijective (he : Function.Bijective e) (i : ℤ) :
    Function.Bijective
      ((natHom (coefCochainMap e continuous_of_discreteTopology heG)).f i i rfl) := by
  rcases i with n | n
  · refine ⟨fun c c' h => cochain_ext (M := M₁) (n := n) fun x => he.1 ?_, fun c => ?_⟩
    · exact congrArg (fun d : (contCochains A G M₂).X n => cfun A G M₂ d x) h
    · have hcont : Continuous (cfun A G M₂ c) := ((contSubCx A G M₂).el c).2
      refine ⟨mkCochain A G M₁ (Function.surjInv he.2 ∘ cfun A G M₂ c)
        (continuous_of_discreteTopology.comp hcont), ?_⟩
      refine cochain_ext (M := M₂) (n := n) fun x => ?_
      exact Function.surjInv_eq he.2 _
  · exact ⟨fun _ _ _ => rfl, fun y => ⟨PUnit.unit, rfl⟩⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M₁] [DiscreteTopology M₁]
  [ContinuousSMul G M₁] [TopologicalSpace M₂] [DiscreteTopology M₂] [ContinuousSMul G M₂] in
/-- The model map of a linear bijection is bijective in every degree (tex 3470–3474).
Kind: PROVED. -/
theorem modelInfl_bijective (he : Function.Bijective e) (φ : G) (q : ℕ) (hq : Odd q) (i : ℤ) :
    Function.Bijective ((modelInfl e heG φ q hq).f i i rfl) := by
  rcases i with (_ | _ | _ | n) | n
  · exact he
  · exact he.prodMap he
  · exact he
  · exact ⟨fun _ _ _ => rfl, fun y => ⟨PUnit.unit, rfl⟩⟩
  · exact ⟨fun _ _ _ => rfl, fun y => ⟨PUnit.unit, rfl⟩⟩

include heG in
/-- **The comparison is a quasi-isomorphism for isomorphic coefficient modules simultaneously**
(tex 3470–3487): along an equivariant linear bijection the naturality square has isomorphisms as
vertical maps. Kind: PROVED. -/
theorem quasiIso_tameInfl_transport (he : Function.Bijective e) (φ σ : G) (q : ℕ) (hq : Odd q)
    (hσ₁ : ∀ m : M₁, σ • m = m) (hσ₂ : ∀ m : M₂, σ • m = m) (hrel : φ * σ * φ⁻¹ = σ ^ q) :
    QuasiIso (GHom.toCC (tameInfl A M₁ φ σ q hq hσ₁ hrel)) ↔
      QuasiIso (GHom.toCC (tameInfl A M₂ φ σ q hq hσ₂ hrel)) := by
  have h1 := isIso_toCC_of_bijective _ (natHom_coef_bijective e heG he)
  have h2 := isIso_toCC_of_bijective _ (modelInfl_bijective e heG he φ q hq)
  exact quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (@asIso _ _ _ _ _ h1) (@asIso _ _ _ _ _ h2)
      (tameInfl_natural e heG φ σ q hq hσ₁ hσ₂ hrel))

end Transport

end Generic

/-! ### Inflated coefficients at a place and their `2`-adic filtration -/

section Place

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

open NumberField IsDedekindDomain TauCeti ValuativeRel
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex (resUr)
open ZInQ.Contrib.CloudB3RC53.RankCounts (GUr)

variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)}
  {A : Type} [CommRing A] [TopologicalSpace A]

variable (K w) in
/-- **The coefficient module inflated from a representation `Y` of `Gal(K_w^ur/K_w)`**
(tex 3470–3480): `Y` with `G_{K_w}` acting through `resUr`. Kind: definition. -/
abbrev CMod (Y : TopRep.{0} A (GUr K w)) : Type := ResMod (resUr K w) Y.V

/-- Inertia acts trivially on an inflated module (tex 3470–3480). Kind: PROVED. -/
theorem cmod_inertia (Y : TopRep.{0} A (GUr K w)) {σ : Gloc K w}
    (hσ : σ ∈ inertiaSubgroup (w.adicCompletion K)) (m : CMod K w Y) : σ • m = m := by
  rw [ResMod.smul_def, resUr_of_mem_inertia hσ, one_smul]

/-- **The sub-representation on a stable submodule** (tex 3470–3480). Kind: definition. -/
def subRep (Y : TopRep.{0} A (GUr K w)) (H : Submodule A Y.V)
    (hH : ∀ (γ : GUr K w) (x : Y.V), x ∈ H → Y.ρ γ x ∈ H) : TopRep.{0} A (GUr K w) :=
  TopRep.of (ContRepresentation.ofMonoidHom
    { toFun := fun γ => ((Y.ρ γ).comp H.subtypeL).codRestrict H (fun x => hH γ x.1 x.2)
      map_one' := by
        ext x
        change Y.ρ 1 x.1 = x.1
        rw [map_one]
        rfl
      map_mul' := fun γ δ => by
        ext x
        change Y.ρ (γ * δ) x.1 = Y.ρ γ (Y.ρ δ x.1)
        rw [map_mul]
        rfl } : ContRepresentation A (GUr K w) H)

variable (Y : TopRep.{0} A (GUr K w)) (H : Submodule A Y.V)
  (hH : ∀ (γ : GUr K w) (x : Y.V), x ∈ H → Y.ρ γ x ∈ H)

/-- The element of `Y` underlying an element of the sub-representation (tex 3470–3480).
Kind: definition. -/
abbrev subVal (x : (subRep Y H hH).V) : Y.V := (show H from x).1

/-- The action on the sub-representation is the restricted action (tex 3470–3480).
Kind: PROVED. -/
theorem subRep_smul_val (γ : GUr K w) (x : (subRep Y H hH).V) :
    subVal Y H hH (γ • x) = Y.ρ γ (subVal Y H hH x) :=
  rfl

instance subRep_discreteTopology [DiscreteTopology Y.V] :
    DiscreteTopology (subRep Y H hH).V :=
  inferInstanceAs (DiscreteTopology H)

instance subRep_finite [Finite Y.V] : Finite (subRep Y H hH).V :=
  inferInstanceAs (Finite H)

instance subRep_continuousSMul [ContinuousSMul (GUr K w) Y.V] :
    ContinuousSMul (GUr K w) (subRep Y H hH).V where
  continuous_smul := by
    have h : Continuous (fun p : GUr K w × Y.V => Y.ρ p.1 p.2) := continuous_smul
    exact Continuous.subtype_mk (h.comp (continuous_fst.prodMk
      ((continuous_subtype_val (p := fun x => x ∈ H)).comp continuous_snd))) _

instance cmod_finite [Finite Y.V] : Finite (CMod K w Y) := inferInstanceAs (Finite Y.V)

variable (A) in
/-- Multiplication by `2` (tex 3470–3480). Kind: definition. -/
abbrev twoMap (V : Type) [AddCommGroup V] [Module A V] : V →ₗ[A] V := (2 : ℕ) • LinearMap.id

/-- The `2`-torsion of a stable submodule (tex 3470–3480). Kind: definition. -/
abbrev subTor : Submodule A Y.V := H ⊓ LinearMap.ker (twoMap A Y.V)

/-- The double of a stable submodule (tex 3470–3480). Kind: definition. -/
abbrev subTwo : Submodule A Y.V := H.map (twoMap A Y.V)

include hH in
/-- The `2`-torsion is stable (tex 3470–3480). Kind: PROVED. -/
theorem subTor_stable : ∀ (γ : GUr K w) (x : Y.V), x ∈ subTor Y H → Y.ρ γ x ∈ subTor Y H := by
  intro γ x hx
  refine ⟨hH γ x hx.1, ?_⟩
  have h0 : (2 : ℕ) • x = 0 := hx.2
  change (2 : ℕ) • Y.ρ γ x = 0
  rw [← map_nsmul, h0, map_zero]

include hH in
/-- The double is stable (tex 3470–3480). Kind: PROVED. -/
theorem subTwo_stable : ∀ (γ : GUr K w) (x : Y.V), x ∈ subTwo Y H → Y.ρ γ x ∈ subTwo Y H := by
  intro γ x hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨Y.ρ γ y, hH γ y hy, ?_⟩
  change (2 : ℕ) • Y.ρ γ y = Y.ρ γ ((2 : ℕ) • y)
  rw [map_nsmul]

/-- The inclusion of the `2`-torsion (tex 3470–3480). Kind: definition. -/
abbrev torIncl : CMod K w (subRep Y (subTor Y H) (subTor_stable Y H hH)) →ₗ[A]
    CMod K w (subRep Y H hH) :=
  Submodule.inclusion inf_le_left

/-- Multiplication by `2` onto the double (tex 3470–3480). Kind: definition. -/
abbrev twoProj : CMod K w (subRep Y H hH) →ₗ[A]
    CMod K w (subRep Y (subTwo Y H) (subTwo_stable Y H hH)) :=
  LinearMap.codRestrict (subTwo Y H) ((twoMap A Y.V).comp H.subtype)
    (fun x => Submodule.mem_map_of_mem x.2)

/-- The inclusion is equivariant (tex 3470–3480). Kind: PROVED. -/
theorem torIncl_equivariant (g : Gloc K w)
    (m : CMod K w (subRep Y (subTor Y H) (subTor_stable Y H hH))) :
    torIncl Y H hH (g • m) = g • torIncl Y H hH m :=
  rfl

/-- Multiplication by `2` is equivariant (tex 3470–3480). Kind: PROVED. -/
theorem twoProj_equivariant (g : Gloc K w) (m : CMod K w (subRep Y H hH)) :
    twoProj Y H hH (g • m) = g • twoProj Y H hH m := by
  apply Subtype.ext
  change (2 : ℕ) • Y.ρ (resUr K w g) (subVal Y H hH m) =
    Y.ρ (resUr K w g) ((2 : ℕ) • subVal Y H hH m)
  rw [map_nsmul]

/-! ### The dévissage -/

section Devissage

variable (Y : TopRep.{0} A (GUr K w)) [ContinuousSMul (GUr K w) Y.V] [DiscreteTopology Y.V]
  (φ σ : Gloc K w) (q : ℕ) (hq : Odd q)
  (hσ : σ ∈ inertiaSubgroup (w.adicCompletion K)) (hrel : φ * σ * φ⁻¹ = σ ^ q)

/-- The comparison for the sub-representation on a stable submodule (tex 3470–3487).
Kind: definition. -/
abbrev tameSub (H : Submodule A Y.V) (hH : ∀ (γ : GUr K w) (x : Y.V), x ∈ H → Y.ρ γ x ∈ H) :=
  tameInfl A (CMod K w (subRep Y H hH)) φ σ q hq (cmod_inertia _ hσ) hrel

/-- **The dévissage along `0 → H[2] → H → 2H → 0`** (tex 3470–3487, 4385–4451): if the comparison
is a quasi-isomorphism for every stable submodule killed by `2`, it is one for every stable
submodule killed by a power of `2`, by induction on the exponent with
`quasiIso_tameInfl_of_ses`. Kind: PROVED. -/
theorem quasiIso_tameSub_of_base
    (hbase : ∀ (H : Submodule A Y.V) (hH : ∀ (γ : GUr K w) (x : Y.V), x ∈ H → Y.ρ γ x ∈ H),
      (∀ x ∈ H, (2 : ℕ) • x = 0) → QuasiIso (GHom.toCC (tameSub Y φ σ q hq hσ hrel H hH))) :
    ∀ (e : ℕ) (H : Submodule A Y.V) (hH : ∀ (γ : GUr K w) (x : Y.V), x ∈ H → Y.ρ γ x ∈ H),
      (∀ x ∈ H, (2 ^ e : ℕ) • x = 0) → QuasiIso (GHom.toCC (tameSub Y φ σ q hq hσ hrel H hH)) := by
  intro e
  induction e with
  | zero =>
    intro H hH h
    refine hbase H hH fun x hx => ?_
    have h0 : x = 0 := by simpa using h x hx
    rw [h0, smul_zero]
  | succ e ih =>
    intro H hH h
    refine quasiIso_tameInfl_of_ses (torIncl Y H hH) (twoProj Y H hH)
      (torIncl_equivariant Y H hH) (twoProj_equivariant Y H hH) φ q hq σ hrel
      (cmod_inertia _ hσ) (cmod_inertia _ hσ) (cmod_inertia _ hσ) ?_ ?_ ?_ ?_
      (hbase (subTor Y H) (subTor_stable Y H hH) fun x hx => hx.2)
      (ih (subTwo Y H) (subTwo_stable Y H hH) fun x hx => ?_)
    · exact Submodule.inclusion_injective _
    · intro z
      obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.mp (show subTwo Y H from z).2
      exact ⟨(show H from ⟨y, hy⟩), Subtype.ext hyz⟩
    · intro m
      apply Subtype.ext
      exact (show subTor Y H from m).2.2
    · intro m hm
      have h2 : (2 : ℕ) • (show H from m).1 = 0 := congrArg Subtype.val hm
      exact ⟨(show subTor Y H from ⟨(show H from m).1, (show H from m).2, h2⟩), rfl⟩
    · obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      change (2 ^ e : ℕ) • ((2 : ℕ) • y) = 0
      rw [← mul_smul, ← pow_succ]
      exact h y hy

end Devissage

/-! ### The two-torsion case and the comparison over a coefficient ring -/

variable (K w) in
/-- **The comparison at `w` for inflated coefficients killed by `2`, over every coefficient ring**
(tex 3470–3487): the base case of the dévissage. Kind: definition. -/
def TwoTorsionTameAt (h2 : (2 : 𝓞 K) ∉ w.asIdeal) : Prop :=
  ∀ (A : Type) [CommRing A] [TopologicalSpace A] (Y : TopRep.{0} A (GUr K w))
    [ContinuousSMul (GUr K w) Y.V] [DiscreteTopology Y.V] [Finite Y.V],
    (∀ y : Y.V, (2 : ℕ) • y = 0) → ∀ {φ σ : Gloc K w} {P : Subgroup (Gloc K w)}
      (hI : IsIwasawaTriple K w φ σ P),
      QuasiIso (GHom.toCC (tameInfl A (CMod K w Y) φ σ (Nat.card 𝓀[w.adicCompletion K])
        (odd_natCard_residueField h2) (cmod_inertia Y hI.mem_inertia) hI.rel))

/-- **The comparison at `w` over a coefficient ring, from the two-torsion case** (tex 3470–3487,
4385–4451): for a finite discrete coefficient module `M` of `2`-power exponent over any
commutative ring `A`, inflated from a finite discrete representation `X` of `Gal(K_w^ur/K_w)`
by an `A`-linear equivariant bijection `f`, the comparison `tameCochainMap` (`Φ = (φ • ·)`,
`g = 1`) is a quasi-isomorphism: the dévissage `quasiIso_tameSub_of_base` inside `X` and the
transport along `f`. Kind: PROVED. -/
theorem quasiIso_inflation_of_twoTorsion {h2 : (2 : 𝓞 K) ∉ w.asIdeal}
    (hT : TwoTorsionTameAt K w h2) (A : Type) [CommRing A] [TopologicalSpace A] (M : Type)
    [AddCommGroup M] [Module A M] [DistribMulAction (Gloc K w) M] [SMulCommClass (Gloc K w) A M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Gloc K w) M] [Finite M]
    (X : TopRep.{0} A (GUr K w)) [ContinuousSMul (GUr K w) X.V] [DiscreteTopology X.V]
    [Finite X.V] (f : X.V →ₗ[A] M)
    (hf : ∀ (g : Gloc K w) (x : X.V), f (resUr K w g • x) = g • f x)
    (hbij : Function.Bijective f) {φ σ : Gloc K w} {P : Subgroup (Gloc K w)}
    (hI : IsIwasawaTriple K w φ σ P) (he : ∃ e : ℕ, ∀ m : M, 2 ^ e • m = 0) :
    QuasiIso (GHom.toCC (tameCochainMap (DistribSMul.toLinearMap A M φ) LinearMap.id φ σ
      (Nat.card 𝓀[w.adicCompletion K]) (odd_natCard_residueField h2) (fun _ => rfl)
      (fun m => (smul_eq_self_of_mem_inertia_of_inflation f hf hbij.2 hI.mem_inertia m).symm)
      (LinearMap.id_comp _) ((LinearMap.comp_id _).trans (LinearMap.id_comp _).symm) hI.rel)) := by
  obtain ⟨e, he⟩ := he
  have hTop : ∀ (γ : GUr K w) (x : X.V), x ∈ (⊤ : Submodule A X.V) →
      X.ρ γ x ∈ (⊤ : Submodule A X.V) :=
    fun _ _ _ => Submodule.mem_top
  have hX : ∀ x ∈ (⊤ : Submodule A X.V), (2 ^ e : ℕ) • x = 0 := fun x _ => by
    apply hbij.1
    rw [map_nsmul, he, map_zero]
  have hbase : ∀ (H : Submodule A X.V) (hH : ∀ (γ : GUr K w) (x : X.V), x ∈ H → X.ρ γ x ∈ H),
      (∀ x ∈ H, (2 : ℕ) • x = 0) → QuasiIso (GHom.toCC (tameSub X φ σ _
        (odd_natCard_residueField h2) hI.mem_inertia hI.rel H hH)) := fun H hH h2H =>
    hT A (subRep X H hH) (fun y => Subtype.ext (h2H _ (show H from y).2)) hI
  have hsub := quasiIso_tameSub_of_base X φ σ _ (odd_natCard_residueField h2) hI.mem_inertia
    hI.rel hbase e ⊤ hTop hX
  let tr : CMod K w (subRep X ⊤ hTop) →ₗ[A] M := f ∘ₗ (⊤ : Submodule A X.V).subtype
  have htrG : ∀ (g : Gloc K w) (m : CMod K w (subRep X ⊤ hTop)), tr (g • m) = g • tr m :=
    fun g m => hf g (show (⊤ : Submodule A X.V) from m).1
  have htrB : Function.Bijective tr := by
    refine ⟨fun a b hab => Subtype.ext (hbij.1 hab), fun m => ?_⟩
    obtain ⟨x, rfl⟩ := hbij.2 m
    exact ⟨(show (⊤ : Submodule A X.V) from ⟨x, Submodule.mem_top⟩), rfl⟩
  exact (quasiIso_tameInfl_transport tr htrG htrB φ σ _ (odd_natCard_residueField h2)
    (cmod_inertia _ hI.mem_inertia)
    (fun m => smul_eq_self_of_mem_inertia_of_inflation f hf hbij.2 hI.mem_inertia m)
    hI.rel).1 hsub

/-! ### From the literature: `MilneADT_I_2_8` -/

/-- **The two-torsion case from Milne** (tex 3470–3487): lane E1's field case over `ZMod 2` with
the change of coefficient ring (`quasiIso_inflation_two_torsion`). Kind: PROVED (from the PRINT
`MilneADT_I_2_8`). -/
theorem twoTorsionTameAt_of_milne (h28 : ZInQ.Manuscript.RC.Limits.MilneADT_I_2_8)
    (h2 : (2 : 𝓞 K) ∉ w.asIdeal) : TwoTorsionTameAt K w h2 := by
  intro A _ _ Y _ _ _ hY φ σ P hI
  exact quasiIso_inflation_two_torsion h28 h2 A (CMod K w Y) Y (toResMod (k := A) (resUr K w))
    (toResMod_compat (resUr K w)) ⟨fun _ _ h => h, fun m => ⟨m, rfl⟩⟩ hY hI

/-- **The comparison at a place over a coefficient ring, from Milne** (tex 3470–3487, 4385–4451):
for a finite discrete coefficient module of `2`-power exponent over any commutative ring,
inflated from a finite discrete representation of `Gal(K_w^ur/K_w)` by a linear equivariant
bijection, `tameCochainMap` is a quasi-isomorphism, given the PRINT `MilneADT_I_2_8` only — the
dévissage along `0 → M[2] → M → 2M → 0` of `quasiIso_inflation_of_twoTorsion` with lane E1's field
case at `ZMod 2`. This is the instance of `TameCochainQuasiIso` consumed at the stage rings.
Kind: PROVED (from the PRINT). -/
theorem quasiIso_inflation_ring_of_milne (h28 : ZInQ.Manuscript.RC.Limits.MilneADT_I_2_8)
    (h2 : (2 : 𝓞 K) ∉ w.asIdeal) (A : Type) [CommRing A] [TopologicalSpace A] (M : Type)
    [AddCommGroup M] [Module A M] [DistribMulAction (Gloc K w) M] [SMulCommClass (Gloc K w) A M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Gloc K w) M] [Finite M]
    (X : TopRep.{0} A (GUr K w)) [ContinuousSMul (GUr K w) X.V] [DiscreteTopology X.V]
    [Finite X.V] (f : X.V →ₗ[A] M)
    (hf : ∀ (g : Gloc K w) (x : X.V), f (resUr K w g • x) = g • f x)
    (hbij : Function.Bijective f) {φ σ : Gloc K w} {P : Subgroup (Gloc K w)}
    (hI : IsIwasawaTriple K w φ σ P) (he : ∃ e : ℕ, ∀ m : M, 2 ^ e • m = 0) :
    QuasiIso (GHom.toCC (tameCochainMap (DistribSMul.toLinearMap A M φ) LinearMap.id φ σ
      (Nat.card 𝓀[w.adicCompletion K]) (odd_natCard_residueField h2) (fun _ => rfl)
      (fun m => (smul_eq_self_of_mem_inertia_of_inflation f hf hbij.2 hI.mem_inertia m).symm)
      (LinearMap.id_comp _) ((LinearMap.comp_id _).trans (LinearMap.id_comp _).symm) hI.rel)) :=
  quasiIso_inflation_of_twoTorsion (twoTorsionTameAt_of_milne h28 h2) A M X f hf hbij hI he

end Place

/-! ### The local quotients at the stage rings, from Milne -/

section PlaceStageMilne

attribute [local instance] TopRep.distribMulAction

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Limits
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
open ZInQ.Contrib.CloudB3RC53.RankCounts (GUr)

/-- **The local quotient at a place retracts onto the singular block at a stage ring, from the
literature** (tex 3470–3480, 4176–4184, 4385–4451): lane RC31's
`exists_retract_localQuotient_place_stage` with `TameCochainQuasiIso` replaced by
`quasiIso_inflation_ring_of_milne`; the inputs are the PRINTs `MilneADT_I_2_8`,
`IwasawaGenerators` and `GenuineCochainsInjective`. Kind: PROVED. -/
theorem exists_retract_localQuotient_place_stage_milne (h28 : MilneADT_I_2_8)
    (hI : IwasawaGenerators) (hInj : GenuineCochainsInjective)
    {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {k : Type}
    [CommRing k] [TopologicalSpace k] [IsNoetherianRing k] [Module.Injective k k]
    {M : Type} [AddCommGroup M] [Module k M] [Module.Free k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M] [Finite M]
    (w : Places K S) (X : TopRep.{0} k (GUr K w.1)) [ContinuousSMul (GUr K w.1) X.V]
    [DiscreteTopology X.V] [Finite X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x)
    (hbij : Function.Bijective f) (hexp : ∃ n : ℕ, ∀ m : M, (2 ^ n) • m = 0)
    (q : ℕ) (hq : Odd q) (hqcard : q = Nat.card (𝓞 K ⧸ w.1.asIdeal))
    (E : SplitInclusion (ofCC (urCx K w.1 X))
      (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M w))
    (hE : E.i = ofCCHom (urToLocal_galois K S w X f hf)) :
    Nonempty (GRetract E.quotientCx (singCx (frob (eUr K w.1) X) q)) := by
  have h2 : (2 : 𝓞 K) ∉ w.1.asIdeal := two_not_mem_of_odd_card (hqcard ▸ hq)
  obtain ⟨φ, σ, P, hIw⟩ := hI K w.1 h2
  have hq' := hqcard.trans (natCard_residueField_adicCompletion K w.1).symm
  subst hq'
  have : Finite (ResMod (locMap K S w.1) M) := inferInstanceAs (Finite M)
  have hexp' : ∃ e : ℕ, ∀ m : ResMod (locMap K S w.1) M, 2 ^ e • m = 0 := hexp
  let f' : X.V →ₗ[k] ResMod (locMap K S w.1) M := f
  have hbij' : Function.Bijective f' := hbij
  have hf' : ∀ (g : Gloc K w.1) (x : X.V), f' (resUr K w.1 g • x) = g • f' x := hf
  have hQ := quasiIso_inflation_ring_of_milne h28 h2 k (ResMod (locMap K S w.1) M) X f' hf'
    hbij' hIw hexp'
  have : Module.Free k X.V := Module.Free.of_equiv (LinearEquiv.ofBijective f hbij).symm
  have : Module.Finite k X.V := Module.Finite.equiv (LinearEquiv.ofBijective f hbij).symm
  obtain ⟨R, -⟩ := exists_retract_localQuotient_kInj (eUr K w.1) (resUr K w.1) X
    (G := Gloc K w.1) (M := ResMod (locMap K S w.1) M) f' hbij' hf' _ φ σ _ hq _
    (resUr_of_isArithFrobeniusLift hIw.frob) (resUr_of_mem_inertia hIw.mem_inertia) hIw.rel
    E hE hQ (hInj K S k M w)
  exact ⟨R⟩

/-- **The two local quotients retract onto the two singular blocks over the stage ring, from the
literature** (tex 4176–4184, 4385–4451): lane RC31's `exists_retract_twoPlaces_place_stage` with
the inputs `MilneADT_I_2_8`, `IwasawaGenerators` and `GenuineCochainsInjective` only.
Kind: PROVED. -/
theorem exists_retract_twoPlaces_place_stage_milne (h28 : MilneADT_I_2_8)
    (hI : IwasawaGenerators) (hInj : GenuineCochainsInjective)
    {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {k : Type}
    [CommRing k] [TopologicalSpace k] [IsNoetherianRing k] [Module.Injective k k]
    {M : Type} [AddCommGroup M] [Module k M] [Module.Free k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M] [Finite M]
    (hexp : ∃ n : ℕ, ∀ m : M, (2 ^ n) • m = 0) (q : ℕ) (hq : Odd q)
    (F : Matrix (Fin 2) (Fin 2) k) (z zi : k)
    (w₁ : Places K S) (X₁ : TopRep.{0} k (GUr K w₁.1)) [ContinuousSMul (GUr K w₁.1) X₁.V]
    [DiscreteTopology X₁.V] [Finite X₁.V] (f₁ : X₁.V →ₗ[k] M)
    (hf₁ : ∀ (g : Gloc K w₁.1) (x : X₁.V), f₁ (resUr K w₁.1 g • x) = locMap K S w₁.1 g • f₁ x)
    (hbij₁ : Function.Bijective f₁) (hq₁ : q = Nat.card (𝓞 K ⧸ w₁.1.asIdeal))
    (E₁ : SplitInclusion (ofCC (urCx K w₁.1 X₁))
      (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M w₁))
    (hE₁ : E₁.i = ofCCHom (urToLocal_galois K S w₁ X₁ f₁ hf₁))
    (b₁ : X₁.V ≃ₗ[k] (Fin 2 → k))
    (hb₁ : ∀ v, b₁ (frob (eUr K w₁.1) X₁ v) = Matrix.toLin' (z • F) (b₁ v))
    (w₂ : Places K S) (X₂ : TopRep.{0} k (GUr K w₂.1)) [ContinuousSMul (GUr K w₂.1) X₂.V]
    [DiscreteTopology X₂.V] [Finite X₂.V] (f₂ : X₂.V →ₗ[k] M)
    (hf₂ : ∀ (g : Gloc K w₂.1) (x : X₂.V), f₂ (resUr K w₂.1 g • x) = locMap K S w₂.1 g • f₂ x)
    (hbij₂ : Function.Bijective f₂) (hq₂ : q = Nat.card (𝓞 K ⧸ w₂.1.asIdeal))
    (E₂ : SplitInclusion (ofCC (urCx K w₂.1 X₂))
      (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M w₂))
    (hE₂ : E₂.i = ofCCHom (urToLocal_galois K S w₂ X₂ f₂ hf₂))
    (b₂ : X₂.V ≃ₗ[k] (Fin 2 → k))
    (hb₂ : ∀ v, b₂ (frob (eUr K w₂.1) X₂ v) = Matrix.toLin' (zi • F) (b₂ v)) :
    Nonempty (GRetract (prodGCx E₁.quotientCx E₂.quotientCx) (twoSingCx F q z zi)) := by
  obtain ⟨R₁⟩ := exists_retract_localQuotient_place_stage_milne h28 hI hInj w₁ X₁ f₁ hf₁ hbij₁
    hexp q hq hq₁ E₁ hE₁
  obtain ⟨R₂⟩ := exists_retract_localQuotient_place_stage_milne h28 hI hInj w₂ X₂ f₂ hf₂ hbij₂
    hexp q hq hq₂ E₂ hE₂
  exact ⟨GRetract.twoPlaces _ _ F q z zi b₁ hb₁ b₂ hb₂ R₁ R₂⟩

end PlaceStageMilne

end ZInQ.Manuscript.RC.Local
