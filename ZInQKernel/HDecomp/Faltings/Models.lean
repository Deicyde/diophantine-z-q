import ZInQKernel.HDecomp.Faltings.IdealLines
import ZInQKernel.HDecomp.Objects

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt3 from
`scratch/def-faltings/Faltings.lean`, §15-§17.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

namespace ZInQ.DefFaltings

open NumberField MeasureTheory

/-! ## 15. Abelian varieties and smooth group models (copied from `bp-faltings/Models.lean`) -/

section ModelsSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ExteriorAlgebra

/-! `AbVar`, `AbVar.baseChange`, `AbVar.dim` (copied in the draft from `Objects.lean`) are
`PkgI3`'s, from `ZInQKernel.HDecomp.Objects`. -/
open PkgI3 (AbVar)

/-- The generic fibre `𝒢_L` of a scheme `𝒢` over `𝓞_L`. -/
noncomputable def genericFibre (L : Type) [Field L] [NumberField L]
    (G : Over (Spec (CommRingCat.of (𝓞 L)))) : Over (Spec (CommRingCat.of L)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).obj G

/-- **Node M1** (copied from `bp-faltings/Models.lean`). A smooth, separated, quasi-compact group
scheme over `𝓞_L` with an isomorphism of group schemes from its generic fibre to `A_L`. -/
structure GroupModel {K : Type} [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L]
    [Algebra K L] where
  /-- the model -/
  G : Over (Spec (CommRingCat.of (𝓞 L)))
  [grp : GrpObj G]
  [smooth : Smooth G.hom]
  [separated : IsSeparated G.hom]
  [qc : QuasiCompact G.hom]
  /-- the identification of the generic fibre with `A_L` -/
  gen : genericFibre L G ≅ (A.baseChange L).X
  /-- ... as group schemes -/
  gen_hom : letI : GrpObj (genericFibre L G) := Functor.grpObjObj
    IsMonHom gen.hom

attribute [instance] GroupModel.grp GroupModel.smooth GroupModel.separated GroupModel.qc

/-- The generic point of `Spec 𝓞_L`. -/
def genericPt (L : Type) [Field L] [NumberField L] : Spec (CommRingCat.of (𝓞 L)) :=
  (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (𝓞 L))

/-! ## 16. The Hodge line of a smooth group model (nodes AV3, M2, M3)

Let `e : S = Spec 𝓞_L → 𝒢` be the unit section and `ξ = e(η_S)` the image of the generic point
(the identity of the generic fibre `𝒢_L ≅ A_L`). The local ring `𝒪_{𝒢,ξ}` is the local ring of
`A_L` at its origin, so `cotangent = 𝔪_ξ/𝔪_ξ²` is `ω_{A_L} = e*Ω¹_{A_L/L}` (an `L`-space of
dimension `g`; STANDARD, not proved here). For a point `s ∈ S`, `x = e(s)` specializes from `ξ`,
and `I_x = ker(𝒪_{𝒢,x} → 𝒪_{S,s})` is the ideal of the section at `x`; the image of `I_x` in
`𝔪_ξ/𝔪_ξ²` is the stalk at `s` of the conormal sheaf `e*(I/I²) = e*Ω¹_{𝒢/S}` (`𝒢/S` smooth;
EGA IV 17.2.5, UNVERIFIED locator). A locally free sheaf on the integral scheme `S` has global
sections the intersection of its stalks inside the generic stalk, hence

`ω_𝒢 = Γ(S, e*Ω¹_{𝒢/S}) = ⋂_s image(I_{e(s)})`   (`GroupModel.omega`).

Every module structure below is definitional (no proof obligations): the `𝓞_L`-module structure
on `cotangent` is restriction of scalars along the structure map `𝓞_L → 𝒪_{𝒢,ξ}`, and the
`L`-line is `hodgeSpace g = L ⊗_{𝓞_L} ⋀^g_{𝓞_L} cotangent` (`≅ ⋀^g_L ω_{A_L}` since `cotangent`
is an `L`-space; STANDARD). -/

namespace GroupModel

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- The unit section `e : Spec 𝓞_L → 𝒢`. -/
noncomputable def unitSection : Spec (CommRingCat.of (𝓞 L)) ⟶ 𝒢.G.left :=
  (η[𝒢.G] : 𝟙_ (Over (Spec (CommRingCat.of (𝓞 L)))) ⟶ 𝒢.G).left

/-- `ξ = e(generic point)`: the identity of the generic fibre. -/
noncomputable def genericUnit : 𝒢.G.left := 𝒢.unitSection (genericPt L)

/-- The local ring `𝒪_{𝒢,ξ} = 𝒪_{A_L,0}`. -/
noncomputable abbrev genStalk : CommRingCat := 𝒢.G.left.presheaf.stalk 𝒢.genericUnit

/-- The structure map `𝓞_L = Γ(S) → Γ(𝒢) → 𝒪_{𝒢,ξ}`. -/
noncomputable def structMap : 𝓞 L →+* 𝒢.genStalk :=
  ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv ≫ 𝒢.G.hom.appTop ≫
    𝒢.G.left.presheaf.germ ⊤ 𝒢.genericUnit trivial).hom

/-- **Node AV3.** `ω_{A_L} = 𝔪_ξ/𝔪_ξ²`, the invariant differentials of the generic fibre. -/
def cotangent : Type := IsLocalRing.CotangentSpace 𝒢.genStalk

noncomputable instance : AddCommGroup 𝒢.cotangent :=
  inferInstanceAs (AddCommGroup (IsLocalRing.CotangentSpace 𝒢.genStalk))

noncomputable instance : Module 𝒢.genStalk 𝒢.cotangent :=
  inferInstanceAs (Module 𝒢.genStalk (IsLocalRing.CotangentSpace 𝒢.genStalk))

noncomputable instance : Module (𝓞 L) 𝒢.cotangent := Module.compHom _ 𝒢.structMap

/-- `df ∈ 𝔪_ξ/𝔪_ξ²` for a germ `f ∈ 𝔪_ξ`. -/
noncomputable def dCls (f : IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.cotangent :=
  (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent f

/-- `ξ ⤳ e(s)` for every `s ∈ Spec 𝓞_L`. -/
theorem specializes_genericUnit (s : Spec (CommRingCat.of (𝓞 L))) :
    𝒢.genericUnit ⤳ 𝒢.unitSection s :=
  ((PrimeSpectrum.le_iff_specializes (genericPt L) s).mp bot_le).map
    𝒢.unitSection.continuous

/-- The stalk at `s` of `e*Ω¹_{𝒢/S}` inside `ω_{A_L}`: the `𝓞_L`-span of the image of
`I_{e(s)} = ker(𝒪_{𝒢,e(s)} → 𝒪_{S,s})` under specialization `𝒪_{𝒢,e(s)} → 𝒪_{𝒢,ξ}`. (The
condition that the image lies in `𝔪_ξ` always holds; it is imposed so that no proof is needed in
the definition. The image is already an `𝒪_{S,s}`-module, so the span adds nothing.) -/
noncomputable def omegaAt (s : Spec (CommRingCat.of (𝓞 L))) : Submodule (𝓞 L) 𝒢.cotangent :=
  Submodule.span (𝓞 L) {m | ∃ f ∈ RingHom.ker (𝒢.unitSection.stalkMap s).hom,
    ∃ h : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) f ∈
      IsLocalRing.maximalIdeal 𝒢.genStalk, m = 𝒢.dCls ⟨_, h⟩}

/-- Sanity check of `omegaAt`: at the generic point of `Spec 𝓞_L` the local lattice is all of
`ω_{A_L}` (the stalk of `e*Ω¹` at the generic point is the generic stalk), so `omega` is the
intersection of genuine local lattices at the closed points. Proved. -/
theorem omegaAt_genericPt : 𝒢.omegaAt (genericPt L) = ⊤ := by
  rw [eq_top_iff]
  rintro m -
  obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective m
  have hspec : ∀ x, (𝒢.G.left.presheaf.stalkSpecializes
      (𝒢.specializes_genericUnit (genericPt L))).hom x = x := by
    intro x
    rw [show 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit (genericPt L)) =
      𝟙 _ from TopCat.Presheaf.stalkSpecializes_refl _ _]
    rfl
  have hfield : IsField ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk (genericPt L)) := by
    have : genericPt L = genericPoint (Spec (CommRingCat.of (𝓞 L))) :=
      (genericPoint_eq_bot_of_affine (CommRingCat.of (𝓞 L))).symm
    rw [this]
    exact Field.toIsField _
  apply Submodule.subset_span
  refine ⟨(f : 𝒢.genStalk), ?_, ?_, ?_⟩
  · show (𝒢.unitSection.stalkMap (genericPt L)).hom (f : 𝒢.genStalk) = 0
    have hloc : (𝒢.unitSection.stalkMap (genericPt L)).hom (f : 𝒢.genStalk) ∈
        IsLocalRing.maximalIdeal _ :=
      map_nonunit _ _ ((IsLocalRing.mem_maximalIdeal _).mp f.2)
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield] at hloc
    exact hloc
  · convert f.2 using 1
    exact hspec _
  · unfold dCls
    congr 1
    exact Subtype.ext (hspec _).symm

/-- **Node M2.** `ω_𝒢 = Γ(Spec 𝓞_L, e*Ω¹_{𝒢/𝓞_L}) = ⋂_s (ω_𝒢)_s ⊆ ω_{A_L}`. -/
noncomputable def omega : Submodule (𝓞 L) 𝒢.cotangent := ⨅ s, 𝒢.omegaAt s

/-- **Node AV4.** The Hodge line `⋀^g ω_{A_L}`, as `L ⊗_{𝓞_L} ⋀^g_{𝓞_L} (𝔪_ξ/𝔪_ξ²)`. -/
abbrev hodgeSpace (g : ℕ) : Type :=
  TensorProduct (𝓞 L) L (exteriorPower (𝓞 L) g 𝒢.cotangent)

/-- **Node M3.** The Hodge lattice `⋀^g ω_𝒢 ⊆ ⋀^g ω_{A_L}`: the `𝓞_L`-span of the wedges of
elements of `ω_𝒢`. -/
noncomputable def detLattice (g : ℕ) : Submodule (𝓞 L) (𝒢.hodgeSpace g) :=
  Submodule.span (𝓞 L) (Set.range fun v : Fin g → 𝒢.omega =>
    (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => (v i : 𝒢.cotangent)))

/-- The wedge `1 ⊗ df₁ ∧ ⋯ ∧ df_g ∈ hodgeSpace g` of germs `f_i ∈ 𝔪_ξ`. -/
noncomputable def wedge {g : ℕ} (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.hodgeSpace g :=
  (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => 𝒢.dCls (f i))

/-! ## 17. Complex points and the analytic uniformization (node AN3: the gap)

For `τ : L → ℂ`, the `ℂ`-points of `A_L` at `τ` are the `𝓞_L`-morphisms `Spec ℂ → 𝒢` with
`Spec ℂ → Spec 𝓞_L` given by `τ|_{𝓞_L}` (they factor through the generic fibre since `τ` is
injective). Mathlib gives them a group structure (`MonObj.Hom.group`). A regular function
`s ∈ Γ(U, 𝒪_𝒢)` has a value `evalAt p U s ∈ ℂ` at a point `p ∈ U(ℂ)`.

**`IsAnalyticUniformization 𝒢 τ Λ Φ`** says: `Φ : ℂ^g → 𝒢(ℂ)_τ` is a group homomorphism, onto,
with kernel exactly `Λ`; each `Φ⁻¹(U(ℂ))` is open and each regular function is holomorphic along
`Φ` there. With `Λ` a full lattice, `Φ` is then continuous for the analytic topology, so it
induces a continuous bijection of the compact `ℂ^g/Λ` onto the Hausdorff `A_τ(ℂ)`, a
homeomorphism, holomorphic, hence biholomorphic. Any two such `(Λ, Φ)` differ by a `ℂ`-linear
automorphism of `ℂ^g` (a holomorphic homomorphism of complex tori lifts to a linear map). These
are STANDARD facts of complex analysis, not proved here.

**The gap (AN3).** That such `(Λ, Φ)` *exists* is `AnalyticUniformizationExists` below: a
precisely stated Prop over Mathlib's objects, unproved (it is the uniformization theorem
`A(ℂ) ≅ ℂ^g/Λ`, Mumford, *Abelian varieties* §1, with GAGA-type input; locator UNVERIFIED). The
definition of the height does **not** assume it: the infimum ranges over models *together with*
a uniformization satisfying the Prop. Without the theorem one cannot prove the index set
nonempty, i.e. that the height is `< ⊤`. -/

/-- `Spec ℂ` over `Spec 𝓞_L` via `τ`. -/
noncomputable def ptC (τ : L →+* ℂ) : Over (Spec (CommRingCat.of (𝓞 L))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L))))

/-- The complex points `𝒢(ℂ)_τ = A_L(ℂ)_τ`, a group (`MonObj.Hom.group`). -/
noncomputable abbrev Pts (τ : L →+* ℂ) : Type := ptC τ ⟶ 𝒢.G

noncomputable example (τ : L →+* ℂ) : Group (𝒢.Pts τ) := inferInstance

/-- The value `s(p) ∈ ℂ` of a regular function `s ∈ Γ(U, 𝒪_𝒢)` at a complex point `p ∈ U(ℂ)`
(and `0` if `p ∉ U(ℂ)`). -/
noncomputable def evalAt {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens)
    (s : Γ(𝒢.G.left, U)) : ℂ := by
  classical
  exact if h : ⊤ ≤ p.left ⁻¹ᵁ U then
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.left.appLE U ⊤ h s) else 0

/-- `Φ⁻¹(U(ℂ)) ⊆ ℂ^g`. -/
def dom {τ : L →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ) (U : 𝒢.G.left.Opens) :
    Set (Fin g → ℂ) := {z | ⊤ ≤ (Φ z).left ⁻¹ᵁ U}

/-- **The analytic uniformization at `τ`** (the Prop that pins down the archimedean data). -/
def IsAnalyticUniformization (τ : L →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ) : Prop :=
  (∀ z w, Φ (z + w) = Φ z * Φ w) ∧
  (∀ z, Φ z = 1 ↔ z ∈ Λ) ∧
  Function.Surjective Φ ∧
  (∀ U, IsOpen (𝒢.dom Φ U)) ∧
  (∀ U (s : Γ(𝒢.G.left, U)), DifferentiableOn ℂ (fun z => 𝒢.evalAt (Φ z) U s) (𝒢.dom Φ U))

theorem exists_rep (t : 𝒢.genStalk) : ∃ (U : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ U)
    (s : Γ(𝒢.G.left, U)), 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s = t :=
  TopCat.Presheaf.exists_germ_eq _ t

/-- A germ `t ∈ 𝒪_{𝒢,ξ}` composed with `Φ`, through a chosen representative `(U, s)`. Since
`Φ(0) = 1` lies over `ξ` and `Φ⁻¹(U(ℂ))` is open, the germ at `0` of this function, hence its
derivative at `0`, does not depend on the representative (for an analytic uniformization). -/
noncomputable def germAlong {τ : L →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (t : 𝒢.genStalk) : (Fin g → ℂ) → ℂ := fun z =>
  𝒢.evalAt (Φ z) (𝒢.exists_rep t).choose (𝒢.exists_rep t).choose_spec.choose_spec.choose

/-- `det(∂(f_i ∘ Φ)/∂z_j (0))`: the coefficient of `Φ*(df₁ ∧ ⋯ ∧ df_g)` on `dz₁ ∧ ⋯ ∧ dz_g`
(an invariant form is determined by its value at `0`). -/
noncomputable def jacDet {τ : L →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) : ℂ :=
  (Matrix.of fun i j : Fin g =>
    fderiv ℂ (𝒢.germAlong Φ (f i : 𝒢.genStalk)) 0 (Pi.single j 1)).det

end GroupModel

/-- **The gap AN3, stated.** For every smooth group model `𝒢` of `A_L` and every `τ : L → ℂ` there
are `g`, a full lattice `Λ ⊂ ℂ^g` and an analytic uniformization `Φ : ℂ^g → 𝒢(ℂ)_τ` with kernel
`Λ`. (The uniformization theorem for complex abelian varieties; unproved, absent from Mathlib:
it needs the analytification of `A_τ` as a compact complex Lie group.) -/
def AnalyticUniformizationExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ), ∃ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
      (Φ : (Fin g → ℂ) → 𝒢.Pts τ),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ 𝒢.IsAnalyticUniformization τ Λ Φ

/-- **The uniqueness half of AN3, stated.** Two analytic uniformizations differ by a `ℂ`-linear
automorphism `T` of `ℂ^g`: `Φ' = Φ ∘ T`, `Λ' = T⁻¹Λ`. (A holomorphic homomorphism of complex
tori lifts to a linear map; unproved.) With `HodgeData.modelHeight_recoord` this is what makes the
model height independent of the uniformization. -/
def AnalyticUniformizationUnique : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ Λ' : Submodule ℤ (Fin g → ℂ))
    (Φ Φ' : (Fin g → ℂ) → 𝒢.Pts τ),
    𝒢.IsAnalyticUniformization τ Λ Φ → 𝒢.IsAnalyticUniformization τ Λ' Φ' →
    ∃ T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ z, Φ' z = Φ (T z)) ∧ (∀ z, z ∈ Λ' ↔ T z ∈ Λ)

/-- **The algebraic half (AV2-AV4, M2-M3), stated.** For a model of relative dimension `g`
(`g` = the dimension of `A`), `hodgeSpace g` is an `L`-line and `detLattice g` is a full
`𝓞_L`-lattice in it. (Smoothness: `ω_𝒢` is projective of rank `g`; unproved.) -/
def HodgeLatticeTheorem : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (g : ℕ), A.dim = g →
    Module.finrank L (𝒢.hodgeSpace g) = 1 ∧
      ∃ s ∈ 𝒢.detLattice g, s ≠ 0 ∧ secIndex (𝒢.detLattice g) s ≠ 0


end ModelsSec

end ZInQ.DefFaltings
