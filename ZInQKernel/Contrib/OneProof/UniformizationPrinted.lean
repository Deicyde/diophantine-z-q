import ZInQKernel.HDecomp.Analytic.Uniformization

/-!
# unif-printed: `UniformizationLeafAll` from four printed leaves

`BPAnalytic.Uniformization.UniformizationLeafAll` (field `uniformizationLeafAll` of the open textbook bundle,
`ZInQKernel/HDecomp/Analytic/Uniformization.lean`) is AN3 in coordinate form: for every complex abelian variety
`A` there are a lattice `Λ ⊂ ℂ^g` and a group isomorphism `φ : ℂ^g ⧸ Λ ≃ A(ℂ)` such that regular functions pull
back to holomorphic functions, `g` regular functions are local holomorphic coordinates, and `φ⁻¹` is continuous
for the topology of regular functions. Its source is Mumford's §1 theorem applied to `A^an`, through
analytification; Mathlib has no analytification, so `A^an` cannot be named. This file proves the field from
four printed statements over Mathlib's definitions (complex analytic manifolds `IsManifold 𝓘(ℂ, ℂ^n) ω`, Lie groups
`LieGroup 𝓘(ℂ, ℂ^n) ω`, `IsLocalDiffeomorphAt`) and one concrete definition, the classical topology of `X(ℂ)`
(`classicalTopology`: the coarsest topology in which every `U(ℂ)` is open and every regular function is
continuous on `U(ℂ)`):

* `MumfordComplexTorus`: a compact connected complex Lie group is `ℂ^g ⧸ Λ` (Mumford, *Abelian varieties*, §1);
* `SmoothComplexManifold`: for `X` smooth, proper, irreducible over `ℂ`, `X(ℂ)` with its classical topology is a
  complex manifold, regular functions are holomorphic and give local coordinates (Shafarevich, *Basic algebraic
  geometry 2*, VII §1.1; SGA 1, XII 1.1, 3.1);
* `ProperCompact`: `X` proper ⇒ `X(ℂ)` compact (Serre, GAGA §2 Prop. 6; SGA 1, XII 3.2);
* `ConnectedConnected`: `X` proper and irreducible ⇒ `X(ℂ)` connected (Shafarevich VII §2.1 Thm. 1; SGA 1,
  XII 2.4).

Proved glue (all locators of the leaves UNVERIFIED):
* stage 1, `uniformizationLeafAll_of_lieGroup`: from Mumford §1 and the analytic Lie group structure of `A(ℂ)`
  to the coordinate form (the projection `ℂ^g → ℂ^g ⧸ Λ` is a local biholomorphism, `isLocalDiffeomorphAt_proj`);
* stage 2a: the classical topology (neighbourhoods are cut out by finitely many regular functions,
  `nhds_classical`), regular maps are continuous and holomorphic (`contMDiff_comp`);
* stage 2b: a right inverse of an injective holomorphic map with surjective differential is holomorphic
  (`contMDiffAt_rightInverse`: implicit function theorem for injectivity of the differential, then the analytic
  inverse function theorem); surjectivity from sections (`surjective_mfderiv_of_sections`);
* stage 2c, `abVarAnalyticLieGroup_of_printed`: applying `SmoothComplexManifold` to `A` and to `A × A`, the
  multiplication `A(ℂ) × A(ℂ) → A(ℂ)` is `μ ∘ σ` with `σ` the inverse of `(A × A)(ℂ) → A(ℂ) × A(ℂ)`, holomorphic by
  2b; inversion is a regular map; `T₂` from `T₁` and the group structure.

Main theorem: `UnifPrinted.uniformizationLeafAll_of_printed`. The field `gagaMorphism` is not used. Generated
from `scratch/unif-printed/Stage*.lean` (docs/research/unif-printed.md).
-/

-- ===== Stage1 =====
open scoped Manifold ContDiff Topology
open Set Filter CategoryTheory AlgebraicGeometry Limits MonObj

set_option linter.unusedSectionVars false

noncomputable section

namespace UnifPrinted

open BPAnalytic BPAnalytic.Uniformization
open PkgI3 (AbVar)

/-- **Mumford, *Abelian varieties*, §1 (printed form).** A compact connected complex Lie group `X` of
dimension `g` is a complex torus: there are a lattice `Λ ⊂ ℂ^g` and a biholomorphic group isomorphism
`ℂ^g ⧸ Λ ≃ X`. (Mumford, *Abelian varieties*, 2nd ed. (1974), §1, Theorem on p. 1-2; Birkenhake–Lange,
*Complex abelian varieties*, 2nd ed., §1.1; locators UNVERIFIED.) Stated over Mathlib's complex
analytic manifolds (`IsManifold 𝓘(ℂ, ℂ^g) ω`) and Lie groups (`LieGroup 𝓘(ℂ, ℂ^g) ω`); the torus is
bp-analytic's `Torus Λ` with its analytic structure (`ZInQKernel/HDecomp/Analytic/Torus.lean`). -/
def MumfordComplexTorus : Prop :=
  ∀ (g : ℕ) (X : Type) [TopologicalSpace X] [ChartedSpace (Fin g → ℂ) X] [Group X],
    IsManifold 𝓘(ℂ, Fin g → ℂ) ω X → LieGroup 𝓘(ℂ, Fin g → ℂ) ω X → T2Space X →
    CompactSpace X → ConnectedSpace X →
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ)
      (e : Torus Λ ≃ₘ^ω⟮𝓘(ℂ, Fin g → ℂ), 𝓘(ℂ, Fin g → ℂ)⟯ X), ∀ a b, e (a + b) = e a * e b

/-- The analytic structure on `A(ℂ)` (a topology and a complex atlas) is the one given by regular
functions: (1) `U(ℂ)` is open for every Zariski open `U`; (2) regular functions are holomorphic on
`U(ℂ)`; (3) at every point, `g` regular functions are local holomorphic coordinates; (4) the topology
is the one defined by regular functions. -/
structure IsAnalyticStr (A : AbVar ℂ) (g : ℕ) [TopologicalSpace (A.Pt ℂ)]
    [ChartedSpace (Fin g → ℂ) (A.Pt ℂ)] : Prop where
  isOpen_ptIn : ∀ U : A.X.left.Opens, IsOpen {P | PtIn A P U}
  holo : ∀ (U : A.X.left.Opens) (f : Γ(A.X.left, U)),
    ContMDiffOn 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, ℂ) ω (evalAt A U f) {P | PtIn A P U}
  coords : ∀ P : A.Pt ℂ, ∃ (U : A.X.left.Opens) (f : Fin g → Γ(A.X.left, U)), PtIn A P U ∧
    IsLocalDiffeomorphAt 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin g → ℂ) ω (fun Q i => evalAt A U (f i) Q) P
  nhds : ∀ (P₀ : A.Pt ℂ), ∀ N ∈ 𝓝 P₀, ∃ (U : A.X.left.Opens) (k : ℕ) (f : Fin k → Γ(A.X.left, U))
    (ε : ℝ), 0 < ε ∧ PtIn A P₀ U ∧ ∀ P : A.Pt ℂ, PtIn A P U →
      (∀ i, ‖evalAt A U (f i) P - evalAt A U (f i) P₀‖ < ε) → P ∈ N

/-- **(composite; reduced in stage 2)** `A(ℂ)`, with its analytic structure, is a compact connected
complex Lie group. -/
def AbVarAnalyticLieGroup : Prop :=
  ∀ A : AbVar ℂ, ∃ (g : ℕ) (_ : TopologicalSpace (A.Pt ℂ)) (_ : ChartedSpace (Fin g → ℂ) (A.Pt ℂ)),
    IsManifold 𝓘(ℂ, Fin g → ℂ) ω (A.Pt ℂ) ∧ LieGroup 𝓘(ℂ, Fin g → ℂ) ω (A.Pt ℂ) ∧
    T2Space (A.Pt ℂ) ∧ CompactSpace (A.Pt ℂ) ∧ ConnectedSpace (A.Pt ℂ) ∧ IsAnalyticStr A g

section Torus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (Λ : Submodule ℤ E)
  [DiscreteTopology Λ]

/-- The chart `chartOf Λ v`, inverted: a partial diffeomorphism `E → E ⧸ Λ` agreeing with `proj`. -/
def projPartialDiffeo (v : E) : PartialDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E) E (Torus Λ) ω where
  toPartialEquiv := (chartOf Λ v).symm.toPartialEquiv
  open_source := (chartOf Λ v).open_target
  open_target := (chartOf Λ v).open_source
  contMDiffOn_toFun := by
    refine (contMDiff_proj Λ).contMDiffOn.congr fun z _ => ?_
    exact chartOf_symm_apply Λ v z
  contMDiffOn_invFun := by
    have hmem : chartOf Λ v ∈ atlas E (Torus Λ) := ⟨v, rfl⟩
    exact contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hmem)

/-- **The projection `E → E ⧸ Λ` is a local biholomorphism.** -/
theorem isLocalDiffeomorphAt_proj (v : E) :
    IsLocalDiffeomorphAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (proj Λ) v :=
  ⟨projPartialDiffeo Λ v, self_mem_chartOf_target Λ v, fun z _ => (chartOf_symm_apply Λ v z).symm⟩

end Torus

/-- **Stage 1 (proved).** The coordinate form `UniformizationLeaf A` from Mumford §1 and an analytic
Lie group structure on `A(ℂ)` given by regular functions. -/
theorem uniformizationLeaf_of_lieGroup (hM : MumfordComplexTorus) (A : AbVar ℂ) (g : ℕ)
    [TopologicalSpace (A.Pt ℂ)] [ChartedSpace (Fin g → ℂ) (A.Pt ℂ)]
    (hMan : IsManifold 𝓘(ℂ, Fin g → ℂ) ω (A.Pt ℂ)) (hLie : LieGroup 𝓘(ℂ, Fin g → ℂ) ω (A.Pt ℂ))
    (hT2 : T2Space (A.Pt ℂ)) (hC : CompactSpace (A.Pt ℂ)) (hK : ConnectedSpace (A.Pt ℂ))
    (hS : IsAnalyticStr A g) : UniformizationLeaf A := by
  obtain ⟨Λ, hd, hz, e, he⟩ := hM g (A.Pt ℂ) hMan hLie hT2 hC hK
  let φ : Torus Λ ≃+ Additive (A.Pt ℂ) :=
    { toFun := fun q => Additive.ofMul (e q)
      invFun := fun P => e.symm (Additive.toMul P)
      left_inv := fun q => by simp
      right_inv := fun P => by simp
      map_add' := fun a b => by simp only [he]; rfl }
  have hφ : ∀ q, Additive.toMul (φ q) = e q := fun q => rfl
  have hcont : Continuous (fun v : Fin g → ℂ => e (proj Λ v)) :=
    e.continuous.comp (isLocalHomeomorph_proj Λ).continuous
  refine ⟨g, Λ, hd, hz, φ, ⟨fun U f => ?_, fun v₀ => ?_, fun v₀ N hN => ?_⟩⟩
  · -- (i) regular functions are holomorphic
    simp only [hφ]
    have hopen : IsOpen {v : Fin g → ℂ | PtIn A (e (proj Λ v)) U} :=
      (hS.isOpen_ptIn U).preimage hcont
    refine ⟨hopen, ?_⟩
    have h1 : ContMDiffOn 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, ℂ) ω (fun v => evalAt A U f (e (proj Λ v)))
        {v : Fin g → ℂ | PtIn A (e (proj Λ v)) U} :=
      (hS.holo U f).comp (e.contMDiff.comp (contMDiff_proj Λ)).contMDiffOn (fun v hv => hv)
    have h2 := (contMDiffOn_iff_contDiffOn.mp h1).analyticOn
    exact hopen.analyticOn_iff_analyticOnNhd.mp h2
  · -- (ii) local coordinates
    obtain ⟨U, f, hU, hloc⟩ := hS.coords (e (proj Λ v₀))
    have hep : IsLocalDiffeomorphAt 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin g → ℂ) ω
        (fun v => e (proj Λ v)) v₀ :=
      (isLocalDiffeomorphAt_proj Λ v₀).comp (K := 𝓘(ℂ, Fin g → ℂ)) (P := A.Pt ℂ)
        (e.isLocalDiffeomorph (proj Λ v₀))
    have hF := hep.comp (K := 𝓘(ℂ, Fin g → ℂ)) (P := Fin g → ℂ) hloc
    obtain ⟨L, hL⟩ := hF.isInvertible_mfderiv (by simp)
    let L' : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) := L
    have hL' : (L' : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) =
        mfderiv 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin g → ℂ)
          ((fun Q i => evalAt A U (f i) Q) ∘ fun v => e (proj Λ v)) v₀ := hL
    refine ⟨U, f, L', by simpa [hφ] using hU, ?_⟩
    have hd' := (hF.mdifferentiableAt (by simp)).hasMFDerivAt
    rw [hasMFDerivAt_iff_hasFDerivAt] at hd'
    rw [hL']
    exact hd'
  · -- (iii) `φ⁻¹` is continuous for the topology of regular functions
    have hN' : e '' N ∈ 𝓝 (e (proj Λ v₀)) := e.toHomeomorph.isOpenMap.image_mem_nhds hN
    obtain ⟨U, k, f, ε, hε, hU, hsep⟩ := hS.nhds _ _ hN'
    refine ⟨U, k, f, ε, hε, by simpa [hφ] using hU, fun P hP hPi => ?_⟩
    obtain ⟨q, hq, rfl⟩ := hsep P hP (by simpa [hφ] using hPi)
    exact ⟨q, hq, rfl⟩

/-- **Stage 1 (proved).** `UniformizationLeafAll` from `MumfordComplexTorus` and
`AbVarAnalyticLieGroup`. -/
theorem uniformizationLeafAll_of_lieGroup (hM : MumfordComplexTorus) (hA : AbVarAnalyticLieGroup) :
    UniformizationLeafAll := by
  intro A
  obtain ⟨g, t, cs, hMan, hLie, hT2, hC, hK, hS⟩ := hA A
  exact uniformizationLeaf_of_lieGroup hM A g hMan hLie hT2 hC hK hS

end UnifPrinted

-- ===== Stage2a =====
open scoped Manifold ContDiff Topology
open Set Filter CategoryTheory AlgebraicGeometry Limits MonObj

set_option linter.unusedSectionVars false

noncomputable section

namespace UnifPrinted

open BPAnalytic BPAnalytic.Uniformization
open PkgI3 (AbVar)

/-- `ℂ`-points of a `ℂ`-scheme: `ℂ`-morphisms `Spec ℂ → X` (for `X = A.X` this is `A.Pt ℂ`). -/
abbrev CPt (X : Over (Spec (CommRingCat.of ℂ))) : Type := AbVar.ptObj (K := ℂ) ℂ ⟶ X

variable (X : Over (Spec (CommRingCat.of ℂ)))

/-- The `ℂ`-point `P` lies in the Zariski open `U` (bp-analytic's `PtIn`, for any `ℂ`-scheme). -/
def XPtIn (P : CPt X) (U : X.left.Opens) : Prop := ⊤ ≤ P.left ⁻¹ᵁ U

open Classical in
/-- The value at a `ℂ`-point of a regular function (bp-analytic's `evalAt`, for any `ℂ`-scheme). -/
def XevalAt (U : X.left.Opens) (f : Γ(X.left, U)) (P : CPt X) : ℂ :=
  if h : XPtIn X P U then
    ((P.left.appLE U ⊤ h) ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom f
  else 0

theorem xPtIn_eq (A : AbVar ℂ) : XPtIn A.X = PtIn A := rfl
theorem xevalAt_eq (A : AbVar ℂ) : XevalAt A.X = evalAt A := rfl

/-- The basic open sets `{P ∈ U(ℂ) : |f(P) - z| < ε}`. -/
def basicSets : Set (Set (CPt X)) :=
  {S | ∃ (U : X.left.Opens) (f : Γ(X.left, U)) (z : ℂ) (ε : ℝ),
    S = {P | XPtIn X P U ∧ ‖XevalAt X U f P - z‖ < ε}}

/-- **The classical (analytic) topology on `X(ℂ)`**: the coarsest topology in which every `U(ℂ)` is
open and every regular function on `U` is continuous on `U(ℂ)`. On an affine open `U ⊂ 𝔸^m` it is the
subspace topology of `U(ℂ) ⊂ ℂ^m` (the coordinates are regular, and every regular function on a
Zariski open of `U` is locally a quotient of polynomials). -/
def classicalTopology : TopologicalSpace (CPt X) := TopologicalSpace.generateFrom (basicSets X)

/-! ## The printed leaves -/

/-- **LEAF (printed form): the complex manifold `X(ℂ)` of a smooth variety.** For a smooth irreducible
`ℂ`-scheme `X` (stated here only for `X` proper over `ℂ`, a special case), the set `X(ℂ)` with its classical topology is a complex (analytic) manifold, regular
functions are holomorphic on `U(ℂ)`, and at every point there are local holomorphic coordinates given
by regular functions (local parameters). Shafarevich, *Basic algebraic geometry 2*, 2nd ed. (1994),
Ch. VII §1.1 (a nonsingular variety `X` gives a complex manifold `X(ℂ)`, local parameters are local
coordinates); Serre, GAGA (1956) §2; SGA 1, Exp. XII, 1.1 and 3.1 (`X` smooth iff `X^an` smooth);
locators UNVERIFIED. Stated with Mathlib's `IsManifold 𝓘(ℂ, ℂ^n) ω`, `IsLocalDiffeomorphAt`. -/
def SmoothComplexManifold : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of ℂ))), Smooth X.hom → IsProper X.hom → IrreducibleSpace X.left →
    letI := classicalTopology X
    ∃ (n : ℕ) (_ : ChartedSpace (Fin n → ℂ) (CPt X)),
      IsManifold 𝓘(ℂ, Fin n → ℂ) ω (CPt X) ∧
      (∀ (U : X.left.Opens) (f : Γ(X.left, U)),
        ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) ω (XevalAt X U f) {P | XPtIn X P U}) ∧
      (∀ P : CPt X, ∃ (U : X.left.Opens) (f : Fin n → Γ(X.left, U)), XPtIn X P U ∧
        IsLocalDiffeomorphAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω
          (fun Q i => XevalAt X U (f i) Q) P)

/-- **LEAF (printed form): proper implies compact.** For `X` proper over `ℂ`, `X(ℂ)` is compact in the
classical topology. Serre, GAGA (1956), §2, Prop. 6; SGA 1, Exp. XII, Prop. 3.2; Shafarevich, *Basic
algebraic geometry 2*, Ch. VII §2.1 (complete varieties); locators UNVERIFIED. -/
def ProperCompact : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of ℂ))), IsProper X.hom →
    @CompactSpace (CPt X) (classicalTopology X)

/-- **LEAF (printed form): irreducible implies connected.** For `X` irreducible (Zariski topology) and
proper over `ℂ` (a special case of the printed hypotheses), `X(ℂ)` is connected in the classical
topology. Shafarevich, *Basic algebraic geometry 2*, 2nd ed., Ch. VII §2.1, Thm. 1 (an irreducible
variety `X` has `X(ℂ)` connected); SGA 1, Exp. XII, Prop. 2.4 (`X` locally of finite type over `ℂ` is
connected iff `X^an` is); locators UNVERIFIED. -/
def ConnectedConnected : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of ℂ))), IsProper X.hom → IrreducibleSpace X.left →
    @ConnectedSpace (CPt X) (classicalTopology X)

/-! ## Glue: the classical topology -/

variable {X}

theorem isOpen_basic {U : X.left.Opens} (f : Γ(X.left, U)) (z : ℂ) (ε : ℝ) :
    IsOpen[classicalTopology X] {P | XPtIn X P U ∧ ‖XevalAt X U f P - z‖ < ε} :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, f, z, ε, rfl⟩

theorem isOpen_ptIn (U : X.left.Opens) : IsOpen[classicalTopology X] {P | XPtIn X P U} := by
  have := isOpen_basic (X := X) (0 : Γ(X.left, U)) 0 1
  convert this using 1
  ext P
  constructor
  · intro h
    refine ⟨h, ?_⟩
    unfold XevalAt
    simp [h]
  · exact fun h => h.1

/-- Restriction of a regular function. -/
def res {U V : X.left.Opens} (h : V ≤ U) (f : Γ(X.left, U)) : Γ(X.left, V) :=
  X.left.presheaf.map (homOfLE h).op f

theorem xPtIn_mono {U V : X.left.Opens} (h : V ≤ U) {P : CPt X} (hP : XPtIn X P V) :
    XPtIn X P U :=
  hP.trans (fun _ hx => h hx)

theorem xevalAt_res {U V : X.left.Opens} (h : V ≤ U) (f : Γ(X.left, U)) {P : CPt X}
    (hP : XPtIn X P V) : XevalAt X V (res h f) P = XevalAt X U f P := by
  unfold XevalAt
  rw [dif_pos hP, dif_pos (xPtIn_mono h hP)]
  have key : X.left.presheaf.map (homOfLE h).op ≫ P.left.appLE V ⊤ hP =
      P.left.appLE U ⊤ (xPtIn_mono h hP) := Scheme.Hom.map_appLE _ _ (homOfLE h).op
  simp only [res]
  rw [← key]
  rfl

/-- Every classical open set contains, around each of its points, a set
`{P ∈ U(ℂ) : |f_i(P) - f_i(P₀)| < ε for all i}` defined by finitely many regular functions. -/
def Good (S : Set (CPt X)) : Prop :=
  ∀ P₀ ∈ S, ∃ (U : X.left.Opens) (k : ℕ) (f : Fin k → Γ(X.left, U)) (ε : ℝ), 0 < ε ∧
    XPtIn X P₀ U ∧ ∀ P, XPtIn X P U →
      (∀ i, ‖XevalAt X U (f i) P - XevalAt X U (f i) P₀‖ < ε) → P ∈ S

theorem good_of_isOpen {S : Set (CPt X)} (hS : IsOpen[classicalTopology X] S) : Good S := by
  induction hS with
  | basic s hs =>
    obtain ⟨U, f, z, ε, rfl⟩ := hs
    rintro P₀ ⟨hP₀, hlt⟩
    refine ⟨U, 1, fun _ => f, ε - ‖XevalAt X U f P₀ - z‖, by linarith, hP₀, fun P hP hi => ?_⟩
    refine ⟨hP, ?_⟩
    have h1 := hi 0
    calc ‖XevalAt X U f P - z‖
        ≤ ‖XevalAt X U f P - XevalAt X U f P₀‖ + ‖XevalAt X U f P₀ - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε := by linarith
  | univ =>
    intro P₀ _
    refine ⟨⊤, 0, Fin.elim0, 1, one_pos, fun x _ => trivial, fun P _ _ => trivial⟩
  | inter s t _ _ hs ht =>
    rintro P₀ ⟨h₁, h₂⟩
    obtain ⟨U, k, f, ε, hε, hU, hsep⟩ := hs P₀ h₁
    obtain ⟨U', k', f', ε', hε', hU', hsep'⟩ := ht P₀ h₂
    refine ⟨U ⊓ U', k + k', Fin.append (fun i => res inf_le_left (f i))
      (fun i => res inf_le_right (f' i)), min ε ε', lt_min hε hε', ?_, fun P hP hi => ?_⟩
    · intro x hx
      exact ⟨hU hx, hU' hx⟩
    · have hPU : XPtIn X P U := xPtIn_mono inf_le_left hP
      have hPU' : XPtIn X P U' := xPtIn_mono inf_le_right hP
      have hP₀ : XPtIn X P₀ (U ⊓ U') := fun x hx => ⟨hU hx, hU' hx⟩
      refine ⟨hsep P hPU fun i => ?_, hsep' P hPU' fun i => ?_⟩
      · have := hi (Fin.castAdd k' i)
        rw [Fin.append_left, xevalAt_res _ _ hP, xevalAt_res _ _ hP₀] at this
        exact lt_of_lt_of_le this (min_le_left _ _)
      · have := hi (Fin.natAdd k i)
        rw [Fin.append_right, xevalAt_res _ _ hP, xevalAt_res _ _ hP₀] at this
        exact lt_of_lt_of_le this (min_le_right _ _)
  | sUnion S _ hS =>
    rintro P₀ ⟨s, hs, hP₀⟩
    obtain ⟨U, k, f, ε, hε, hU, hsep⟩ := hS s hs P₀ hP₀
    exact ⟨U, k, f, ε, hε, hU, fun P hP hi => ⟨s, hs, hsep P hP hi⟩⟩

theorem nhds_classical (P₀ : CPt X) (N : Set (CPt X)) (hN : N ∈ @nhds _ (classicalTopology X) P₀) :
    ∃ (U : X.left.Opens) (k : ℕ) (f : Fin k → Γ(X.left, U)) (ε : ℝ), 0 < ε ∧
      XPtIn X P₀ U ∧ ∀ P, XPtIn X P U →
        (∀ i, ‖XevalAt X U (f i) P - XevalAt X U (f i) P₀‖ < ε) → P ∈ N := by
  letI := classicalTopology X
  obtain ⟨S, hSN, hS, hP₀⟩ := mem_nhds_iff.mp hN
  obtain ⟨U, k, f, ε, hε, hU, hsep⟩ := good_of_isOpen hS P₀ hP₀
  exact ⟨U, k, f, ε, hε, hU, fun P hP hi => hSN (hsep P hP hi)⟩

/-! ## Glue: regular maps on `ℂ`-points -/

variable {Y : Over (Spec (CommRingCat.of ℂ))}

theorem xevalAt_comp (α : X ⟶ Y) (U : Y.left.Opens) (f : Γ(Y.left, U)) (P : CPt X) :
    XevalAt Y U f (P ≫ α) = XevalAt X (α.left ⁻¹ᵁ U) (α.left.app U f) P := by
  have hiff : XPtIn Y (P ≫ α) U ↔ XPtIn X P (α.left ⁻¹ᵁ U) := Iff.rfl
  unfold XevalAt
  by_cases h : XPtIn X P (α.left ⁻¹ᵁ U)
  · simp only [hiff.mpr h, h, ↓reduceDIte]
    simp [Over.comp_left, Scheme.Hom.comp_appLE]
    rfl
  · simp only [mt hiff.mp h, h, ↓reduceDIte]

/-- Regular maps are continuous for the classical topologies. -/
theorem continuous_comp (α : X ⟶ Y) :
    Continuous[classicalTopology X, classicalTopology Y] (fun P : CPt X => P ≫ α) := by
  letI := classicalTopology X
  letI := classicalTopology Y
  refine continuous_generateFrom_iff.mpr ?_
  rintro _ ⟨U, f, z, ε, rfl⟩
  have : (fun P : CPt X => P ≫ α) ⁻¹' {Q | XPtIn Y Q U ∧ ‖XevalAt Y U f Q - z‖ < ε} =
      {P | XPtIn X P (α.left ⁻¹ᵁ U) ∧ ‖XevalAt X (α.left ⁻¹ᵁ U) (α.left.app U f) P - z‖ < ε} := by
    ext P
    simp only [mem_preimage, mem_setOf_eq, xevalAt_comp]
    rfl
  rw [this]
  exact isOpen_basic _ _ _

/-- **Regular maps are holomorphic.** If `X(ℂ)` and `Y(ℂ)` carry complex structures for which regular
functions are holomorphic and (on `Y`) regular functions give local coordinates, then
`P ↦ P ≫ α` is holomorphic. -/
theorem contMDiff_comp {n m : ℕ} [tX : TopologicalSpace (CPt X)] [tY : TopologicalSpace (CPt Y)]
    (htX : tX = classicalTopology X) (htY : tY = classicalTopology Y)
    [ChartedSpace (Fin n → ℂ) (CPt X)] [ChartedSpace (Fin m → ℂ) (CPt Y)]
    (holoX : ∀ (U : X.left.Opens) (f : Γ(X.left, U)),
      ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) ω (XevalAt X U f) {P | XPtIn X P U})
    (coordsY : ∀ Q : CPt Y, ∃ (U : Y.left.Opens) (f : Fin m → Γ(Y.left, U)), XPtIn Y Q U ∧
      IsLocalDiffeomorphAt 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) ω (fun Q i => XevalAt Y U (f i) Q) Q)
    (α : X ⟶ Y) :
    ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin m → ℂ) ω (fun P : CPt X => P ≫ α) := by
  subst htX htY
  letI := classicalTopology X
  letI := classicalTopology Y
  intro P₀
  obtain ⟨U, f, hU, hloc⟩ := coordsY (P₀ ≫ α)
  set c : CPt Y → (Fin m → ℂ) := fun Q i => XevalAt Y U (f i) Q
  have hF : Continuous (fun P : CPt X => P ≫ α) := continuous_comp α
  -- `c ∘ F` is holomorphic near `P₀`
  have hcF : ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin m → ℂ) ω (fun P => c (P ≫ α)) P₀ := by
    have hopen := isOpen_ptIn (X := X) (α.left ⁻¹ᵁ U)
    refine contMDiffAt_pi_module_iff.mpr fun i => ?_
    have h := holoX (α.left ⁻¹ᵁ U) (α.left.app U (f i))
    have h' := (h P₀ hU).contMDiffAt (hopen.mem_nhds hU)
    refine h'.congr_of_eventuallyEq (Eventually.of_forall fun P => ?_)
    simp only [c, xevalAt_comp]
  have hinv := hloc.contMDiffAt_localInverse
  have heq : (fun P : CPt X => P ≫ α) =ᶠ[𝓝 P₀] (fun P => hloc.localInverse (c (P ≫ α))) := by
    have h1 := hloc.localInverse_eventuallyEq_left
    have h2 := h1.comp_tendsto (hF.tendsto P₀)
    filter_upwards [h2] with P hP
    exact hP.symm
  exact (hinv.comp P₀ hcF).congr_of_eventuallyEq heq

end UnifPrinted

-- ===== Stage2b =====
open scoped Manifold ContDiff Topology
open Set Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace UnifPrinted

section InvFun

variable {E2 F : Type*} [NormedAddCommGroup E2] [NormedSpace ℂ E2] [FiniteDimensional ℂ E2]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- **Implicit function theorem, injectivity form.** A map with surjective strict derivative that is
injective near the point has injective derivative. -/
theorem ker_eq_bot_of_injOn {Ψ : E2 → F} {D : E2 →L[ℂ] F} {z₀ : E2} (hΨ : HasStrictFDerivAt Ψ D z₀)
    (hD : D.range = ⊤) {W : Set E2} (hW : W ∈ 𝓝 z₀) (hinj : InjOn Ψ W) : D.ker = ⊥ := by
  by_contra hne
  haveI : Nontrivial D.ker := Submodule.nontrivial_iff_ne_bot.mpr hne
  set h := hΨ.implicitToOpenPartialHomeomorph Ψ D hD
  have h0 : h z₀ = (Ψ z₀, 0) := hΨ.implicitToOpenPartialHomeomorph_self hD
  have hsrc : z₀ ∈ h.source := hΨ.mem_implicitToOpenPartialHomeomorph_source hD
  have htgt : (Ψ z₀, (0 : D.ker)) ∈ h.target := hΨ.mem_implicitToOpenPartialHomeomorph_target hD
  have hsymm0 : h.symm (Ψ z₀, 0) = z₀ := by rw [← h0]; exact h.left_inv hsrc
  have hc : Continuous (fun k : D.ker => (Ψ z₀, k)) := continuous_const.prodMk continuous_id
  have hK : {k : D.ker | (Ψ z₀, k) ∈ h.target ∧ h.symm (Ψ z₀, k) ∈ W} ∈ 𝓝 (0 : D.ker) := by
    have h1 : h.target ∈ 𝓝 (Ψ z₀, (0 : D.ker)) := h.open_target.mem_nhds htgt
    have h2 : h.symm ⁻¹' W ∈ 𝓝 (Ψ z₀, (0 : D.ker)) := by
      apply h.continuousAt_symm htgt
      rw [hsymm0]; exact hW
    exact (hc.tendsto 0) (Filter.inter_mem h1 h2)
  have hne' : (𝓝[≠] (0 : D.ker)).NeBot := inferInstance
  obtain ⟨k, ⟨hkt, hkW⟩, hk0⟩ :=
    Filter.nonempty_of_mem (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds hK)
      (self_mem_nhdsWithin : ({0}ᶜ : Set D.ker) ∈ 𝓝[≠] (0 : D.ker)))
  have hz1 : h (h.symm (Ψ z₀, k)) = (Ψ z₀, k) := h.right_inv hkt
  have hΨ1 : Ψ (h.symm (Ψ z₀, k)) = Ψ z₀ := by
    have := congrArg Prod.fst hz1
    rwa [hΨ.implicitToOpenPartialHomeomorph_fst] at this
  have heq := hinj hkW (mem_of_mem_nhds hW) hΨ1
  rw [heq, h0] at hz1
  exact hk0 (congrArg Prod.snd hz1).symm

variable {H : Type*} [TopologicalSpace H] {IN : ModelWithCorners ℂ F H}
  {M2 : Type*} [TopologicalSpace M2] [ChartedSpace E2 M2] [IsManifold 𝓘(ℂ, E2) ω M2]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold IN ω N]

/-- **Holomorphy of a right inverse.** -/
theorem contMDiffAt_rightInverse (pr : M2 → N) (x₀ : M2) (hpr : ContMDiffAt 𝓘(ℂ, E2) IN ω pr x₀)
    (hinj : Function.Injective pr) (hsurj : Function.Surjective (mfderiv 𝓘(ℂ, E2) IN pr x₀))
    (σ : N → M2) (hσ : ∀ y, pr (σ y) = y) : ContMDiffAt IN 𝓘(ℂ, E2) ω σ (pr x₀) := by
  set e2 := extChartAt 𝓘(ℂ, E2) x₀ with he2
  set eN := extChartAt IN (pr x₀) with heN
  set Ψ : E2 → F := eN ∘ pr ∘ e2.symm with hΨdef
  set z₀ := e2 x₀ with hz₀
  have hcont : ContinuousAt pr x₀ := hpr.continuousAt
  have hΨc : ContDiffAt ℂ ω Ψ z₀ := by
    have h := (contMDiffAt_iff.mp hpr).2
    simp only [modelWithCornersSelf_coe, range_id] at h
    exact contDiffWithinAt_univ.mp h
  have hΨz₀ : Ψ z₀ = eN (pr x₀) := by
    simp only [hΨdef, Function.comp_apply, hz₀, he2, extChartAt_to_inv]
  set D := fderiv ℂ Ψ z₀ with hD
  have hstrict : HasStrictFDerivAt Ψ D z₀ := hΨc.hasStrictFDerivAt (by simp)
  have hmf : ∀ v, mfderiv 𝓘(ℂ, E2) IN pr x₀ v = D v := by
    intro v
    rw [(hpr.mdifferentiableAt (by simp)).mfderiv]
    simp [modelWithCornersSelf_coe, range_id, fderivWithin_univ, writtenInExtChartAt, hD, hΨdef,
      he2, heN, hz₀, tangentSpaceCastModel]
    rfl
  have hrange : D.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro w
    obtain ⟨v, hv⟩ := hsurj w
    exact ⟨v, (hmf v).symm.trans hv⟩
  set W : Set E2 := e2.target ∩ e2.symm ⁻¹' (pr ⁻¹' eN.source) with hWdef
  have hW : W ∈ 𝓝 z₀ := by
    refine Filter.inter_mem (extChartAt_target_mem_nhds x₀) ?_
    apply continuousAt_extChartAt_symm x₀
    rw [extChartAt_to_inv]
    exact hcont (extChartAt_source_mem_nhds (pr x₀))
  have hinjW : InjOn Ψ W := by
    intro z hz z' hz' heq
    have h1 : pr (e2.symm z) = pr (e2.symm z') := eN.injOn hz.2 hz'.2 heq
    exact e2.symm.injOn (by simpa using hz.1) (by simpa using hz'.1) (hinj h1)
  have hker : D.ker = ⊥ := ker_eq_bot_of_injOn hstrict hrange hW hinjW
  let L : E2 ≃L[ℂ] F := (LinearEquiv.ofBijective (D : E2 →ₗ[ℂ] F)
    ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hrange⟩).toContinuousLinearEquiv
  have hL : (L : E2 →L[ℂ] F) = D := by ext v; rfl
  have hfd : HasFDerivAt Ψ (L : E2 →L[ℂ] F) z₀ := by rw [hL]; exact hstrict.hasFDerivAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  set G := hΨc.localInverse hfd hn with hGdef
  have hG : ContDiffAt ℂ ω G (Ψ z₀) := hΨc.to_localInverse hfd hn
  have hs' := hΨc.hasStrictFDerivAt' hfd hn
  have hGimg : G (Ψ z₀) = z₀ := hΨc.localInverse_apply_image hfd hn
  have t1 : Tendsto eN (𝓝 (pr x₀)) (𝓝 (Ψ z₀)) := by
    rw [hΨz₀]; exact continuousAt_extChartAt (pr x₀)
  have ev1 := t1.eventually hs'.eventually_right_inverse
  have ev2 := t1.eventually (hs'.localInverse_tendsto.eventually hW)
  have ev3 : ∀ᶠ y in 𝓝 (pr x₀), y ∈ eN.source := extChartAt_source_mem_nhds _
  have heq : σ =ᶠ[𝓝 (pr x₀)] fun y => e2.symm (G (eN y)) := by
    filter_upwards [ev1, ev2, ev3] with y h1 h2 h3
    have h4 : pr (e2.symm (G (eN y))) = y := eN.injOn h2.2 h3 h1
    exact hinj (by rw [hσ y, h4])
  have c1 : ContMDiffAt IN 𝓘(ℂ, F) ω eN (pr x₀) := contMDiffAt_extChartAt
  have c2 : ContMDiffAt 𝓘(ℂ, F) 𝓘(ℂ, E2) ω G (eN (pr x₀)) := by
    rw [← hΨz₀]; exact contMDiffAt_iff_contDiffAt.mpr hG
  have hGz : G (eN (pr x₀)) = z₀ := by rw [← hΨz₀]; exact hGimg
  have c3 : ContMDiffAt 𝓘(ℂ, E2) 𝓘(ℂ, E2) ω e2.symm (G (eN (pr x₀))) := by
    rw [hGz]
    exact (contMDiffOn_extChartAt_symm x₀ z₀ (mem_extChartAt_target x₀)).contMDiffAt
      (extChartAt_target_mem_nhds x₀)
  exact (ContMDiffAt.comp (pr x₀) c3 (c2.comp (pr x₀) c1)).congr_of_eventuallyEq heq

end InvFun

section Sections

variable {E E2 : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E2]
  [NormedSpace ℂ E2]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {M2 : Type*} [TopologicalSpace M2] [ChartedSpace E2 M2]

theorem mfderiv_section_aux {N' : Type*} [TopologicalSpace N'] {F' : Type*} [NormedAddCommGroup F']
    [NormedSpace ℂ F'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℂ F' H'}
    [ChartedSpace H' N'] (pr : M2 → N') (x₀ : M2)
    (hpr : MDifferentiableAt 𝓘(ℂ, E2) I' pr x₀) (s : M → M2) (P₀ : M)
    (hs : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E2) s P₀) (hs0 : s P₀ = x₀) (f : M → N')
    (hf : pr ∘ s = f) (u : E) :
    mfderiv 𝓘(ℂ, E2) I' pr x₀ (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E2) s P₀ u) =
      mfderiv 𝓘(ℂ, E) I' f P₀ u := by
  subst hs0 hf
  rw [mfderiv_comp P₀ hpr hs]
  rfl

/-- **Surjectivity of `dpr` from sections.** -/
theorem surjective_mfderiv_of_sections (pr : M2 → M × M) (x₀ : M2)
    (hpr : MDifferentiableAt 𝓘(ℂ, E2) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) pr x₀) (s t : M → M2) (P₀ Q₀ : M)
    (hs : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E2) s P₀) (ht : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E2) t Q₀)
    (hs0 : s P₀ = x₀) (ht0 : t Q₀ = x₀) (hs' : ∀ P, pr (s P) = (P, Q₀))
    (ht' : ∀ Q, pr (t Q) = (P₀, Q)) :
    Function.Surjective (mfderiv 𝓘(ℂ, E2) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) pr x₀) := by
  have e1 : ∀ u : E, mfderiv 𝓘(ℂ, E2) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) pr x₀
      (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E2) s P₀ u) = ((u, 0) : E × E) := by
    intro u
    rw [mfderiv_section_aux pr x₀ hpr s P₀ hs hs0 _ (funext hs'), mfderiv_prod_left]
    rfl
  have e2 : ∀ v : E, mfderiv 𝓘(ℂ, E2) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) pr x₀
      (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E2) t Q₀ v) = ((0, v) : E × E) := by
    intro v
    rw [mfderiv_section_aux pr x₀ hpr t Q₀ ht ht0 _ (funext ht'), mfderiv_prod_right]
    rfl
  rintro ⟨u, v⟩
  let a : TangentSpace 𝓘(ℂ, E2) x₀ := mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E2) s P₀ u
  let b : TangentSpace 𝓘(ℂ, E2) x₀ := mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E2) t Q₀ v
  refine ⟨a + b, ?_⟩
  rw [map_add]
  rw [show mfderiv 𝓘(ℂ, E2) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) pr x₀ a = ((u, 0) : E × E) from e1 u,
    show mfderiv 𝓘(ℂ, E2) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) pr x₀ b = ((0, v) : E × E) from e2 v]
  exact Prod.ext (add_zero u) (zero_add v)

end Sections

end UnifPrinted

-- ===== Stage2c =====
open scoped Manifold ContDiff Topology
open Set Filter CategoryTheory AlgebraicGeometry Limits MonObj MonoidalCategory
  CartesianMonoidalCategory

set_option linter.unusedSectionVars false

noncomputable section

namespace UnifPrinted

open BPAnalytic BPAnalytic.Uniformization
open PkgI3 (AbVar)

/-! ## The scheme `A × A` and its `ℂ`-points -/

section Product

variable (A : AbVar ℂ)

instance irreducibleSpace_abVar : IrreducibleSpace A.X.left :=
  GeometricallyIrreducible.irreducibleSpace_of_subsingleton A.X.hom

instance isIntegral_abVar : IsIntegral A.X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom

theorem smooth_prod : Smooth (A.X ⊗ A.X).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

theorem isProper_prod : IsProper (A.X ⊗ A.X).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

instance irreducibleSpace_prod : IrreducibleSpace (A.X ⊗ A.X).left := by
  rw [Over.tensorObj_left]
  infer_instance

theorem ptObj_hom : (AbVar.ptObj (K := ℂ) ℂ).hom = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ)) = 𝟙 _
  rw [show CommRingCat.ofHom (algebraMap ℂ ℂ) = 𝟙 (CommRingCat.of ℂ) from rfl, Spec.map_id]

instance isIso_toUnit_ptObj : IsIso (toUnit (AbVar.ptObj (K := ℂ) ℂ)) := by
  have : IsIso ((Over.forget _).map (toUnit (AbVar.ptObj (K := ℂ) ℂ))) := by
    change IsIso (toUnit (AbVar.ptObj (K := ℂ) ℂ)).left
    rw [Over.toUnit_left, ptObj_hom]
    exact IsIso.id _
  exact isIso_of_reflects_iso _ (Over.forget _)

/-- The section `P ↦ (P, Q)` of `A × A → A`, as a morphism of schemes. -/
def secL (Q : CPt A.X) : A.X ⟶ A.X ⊗ A.X :=
  lift (𝟙 A.X) (toUnit A.X ≫ inv (toUnit (AbVar.ptObj (K := ℂ) ℂ)) ≫ Q)

/-- The section `Q ↦ (P, Q)`. -/
def secR (P : CPt A.X) : A.X ⟶ A.X ⊗ A.X :=
  lift (toUnit A.X ≫ inv (toUnit (AbVar.ptObj (K := ℂ) ℂ)) ≫ P) (𝟙 A.X)

theorem toUnit_inv_comp (P Q : CPt A.X) :
    P ≫ toUnit A.X ≫ inv (toUnit (AbVar.ptObj (K := ℂ) ℂ)) ≫ Q = Q := by
  rw [← Category.assoc, comp_toUnit, IsIso.hom_inv_id_assoc]

theorem comp_secL (P Q : CPt A.X) : P ≫ secL A Q = lift P Q := by
  rw [secL, comp_lift, Category.comp_id, toUnit_inv_comp]

theorem comp_secR (P Q : CPt A.X) : Q ≫ secR A P = lift P Q := by
  rw [secR, comp_lift, Category.comp_id, toUnit_inv_comp]

end Product

/-! ## Assembly -/

/-- **`A(ℂ)` is a compact connected complex Lie group with the analytic structure of regular functions**
(proved from the printed leaves `SmoothComplexManifold`, `ProperCompact`, `ConnectedConnected`). -/
theorem abVarAnalyticLieGroup_of_printed (hMan : SmoothComplexManifold) (hPC : ProperCompact)
    (hCC : ConnectedConnected) : AbVarAnalyticLieGroup := by
  intro A
  letI tA : TopologicalSpace (CPt A.X) := classicalTopology A.X
  letI tA2 : TopologicalSpace (CPt (A.X ⊗ A.X)) := classicalTopology (A.X ⊗ A.X)
  obtain ⟨g, csA, hMA, holoA, coordsA⟩ := hMan A.X inferInstance inferInstance inferInstance
  obtain ⟨n, cs2, hM2, holo2, coords2⟩ := hMan (A.X ⊗ A.X) (smooth_prod A) (isProper_prod A) inferInstance
  -- regular maps are holomorphic
  have hreg : ∀ α : A.X ⟶ A.X, ContMDiff 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin g → ℂ) ω
      (fun P : CPt A.X => P ≫ α) :=
    fun α => contMDiff_comp rfl rfl holoA coordsA α
  have hreg21 : ∀ α : A.X ⊗ A.X ⟶ A.X, ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin g → ℂ) ω
      (fun P : CPt (A.X ⊗ A.X) => P ≫ α) :=
    fun α => contMDiff_comp rfl rfl holo2 coordsA α
  have hreg12 : ∀ α : A.X ⟶ A.X ⊗ A.X, ContMDiff 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin n → ℂ) ω
      (fun P : CPt A.X => P ≫ α) :=
    fun α => contMDiff_comp rfl rfl holoA coords2 α
  -- the comparison map `ι : (A × A)(ℂ) → A(ℂ) × A(ℂ)` and its inverse
  set pr : CPt (A.X ⊗ A.X) → CPt A.X × CPt A.X := fun R => (R ≫ fst _ _, R ≫ snd _ _) with hprdef
  set σ : CPt A.X × CPt A.X → CPt (A.X ⊗ A.X) := fun x => lift x.1 x.2 with hσdef
  have hprσ : ∀ x, pr (σ x) = x := fun x => by simp [hprdef, hσdef]
  have hprinj : Function.Injective pr := by
    intro R R' h
    simp only [hprdef, Prod.mk.injEq] at h
    exact CartesianMonoidalCategory.hom_ext _ _ h.1 h.2
  have hpr : ContMDiff 𝓘(ℂ, Fin n → ℂ) (𝓘(ℂ, Fin g → ℂ).prod 𝓘(ℂ, Fin g → ℂ)) ω pr :=
    (hreg21 (fst _ _)).prodMk (hreg21 (snd _ _))
  have hσ : ContMDiff (𝓘(ℂ, Fin g → ℂ).prod 𝓘(ℂ, Fin g → ℂ)) 𝓘(ℂ, Fin n → ℂ) ω σ := by
    rintro ⟨P₀, Q₀⟩
    have hsurj := surjective_mfderiv_of_sections pr (lift P₀ Q₀) ((hpr _).mdifferentiableAt (by simp))
      (fun P => P ≫ secL A Q₀) (fun Q => Q ≫ secR A P₀) P₀ Q₀
      ((hreg12 _ _).mdifferentiableAt (by simp)) ((hreg12 _ _).mdifferentiableAt (by simp))
      (comp_secL A P₀ Q₀) (comp_secR A P₀ Q₀) (fun P => by simp [hprdef, comp_secL])
      (fun Q => by simp [hprdef, comp_secR])
    have := contMDiffAt_rightInverse pr (lift P₀ Q₀) (hpr _) hprinj hsurj σ hprσ
    simpa [hprdef] using this
  -- the Lie group structure
  have hmul : ContMDiff ((𝓘(ℂ, Fin g → ℂ)).prod 𝓘(ℂ, Fin g → ℂ)) 𝓘(ℂ, Fin g → ℂ) ω
      (fun p : CPt A.X × CPt A.X => p.1 * p.2) := by
    have h := (hreg21 μ[A.X]).comp hσ
    refine h.congr fun p => ?_
    simp [hσdef, Hom.mul_def]
  have hinv : ContMDiff 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin g → ℂ) ω (fun P : CPt A.X => P⁻¹) := by
    refine (hreg ι[A.X]).congr fun P => ?_
    simp [Hom.inv_def]
  haveI hLie : LieGroup 𝓘(ℂ, Fin g → ℂ) ω (A.Pt ℂ) :=
    { toIsManifold := hMA, contMDiff_mul := hmul, contMDiff_inv := hinv }
  haveI : T1Space (CPt A.X) := ChartedSpace.t1Space (Fin g → ℂ) (CPt A.X)
  haveI := topologicalGroup_of_lieGroup 𝓘(ℂ, Fin g → ℂ) ω (G := A.Pt ℂ)
  have hT2 : T2Space (A.Pt ℂ) := IsTopologicalGroup.t2Space_iff_one_closed.mpr isClosed_singleton
  refine ⟨g, tA, csA, hMA, hLie, hT2, hPC A.X inferInstance, hCC A.X inferInstance inferInstance,
    ⟨fun U => isOpen_ptIn U, holoA, coordsA, fun P₀ N hN => nhds_classical P₀ N hN⟩⟩

/-- **Main reduction (proved).** `UniformizationLeafAll` from four printed leaves. -/
theorem uniformizationLeafAll_of_printed (hM : MumfordComplexTorus) (hMan : SmoothComplexManifold)
    (hPC : ProperCompact) (hCC : ConnectedConnected) : UniformizationLeafAll :=
  uniformizationLeafAll_of_lieGroup hM (abVarAnalyticLieGroup_of_printed hMan hPC hCC)

end UnifPrinted
