import ZInQKernel.HDecomp.Analytic.Uniformization

/-! # unif-printed, stage 2a: the classical topology of `X(ℂ)`, the printed analytic leaves, regular maps -/

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
